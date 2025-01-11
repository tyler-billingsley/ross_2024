import Mathlib.Tactic --imports basic tactics

class RossRing (Z : Type) extends Zero Z, One Z, Add Z, Mul Z, Neg Z : Type where
  add_comm       : ∀ a b : Z, a + b = b + a
  mul_comm       : ∀ a b : Z, a * b = b * a
  add_assoc      : ∀ a b c : Z, a + b + c = a + (b + c)
  mul_assoc      : ∀ a b c : Z, a * b * c = a * (b * c)
  mul_add        : ∀ a b c : Z, a * (b + c) = a * b + a * c
  add_zero       : ∀ a : Z, a + 0 = a
  add_neg_self   : ∀ a : Z, a + -a = 0
  mul_one        : ∀ a : Z, a * 1 = a
-- the Ross Ring axioms

namespace RossRing

variable {Z: Type} [RossRing Z]

lemma add_on_right : ∀ a b c : Z, a = b → a + c = b + c := by
  intro a b c h
  rw [h]

lemma add_on_left : ∀ a b c : Z, a = b → c + a = c + b := by
  intro a b c h
  rw [h]

lemma mul_on_left: ∀ a b c : Z, a = b → c * a = c * b := by
  intro a b c h
  rw [h]

lemma mul_on_right: ∀ a b c : Z, a = b → a * c = b * c := by
  intro a b c h
  rw [mul_comm,mul_comm b]
  apply mul_on_left a b c at h
  assumption

lemma one_mul : ∀ a : Z, 1 * a = a := by
  intro a
  rw [mul_comm,mul_one]

  /-
  Podasip 1:  ∀ b ∈ ℤ, if ∀ a ∈ ℤ, a + b = a, then b = 0. Similarly, if  a * b = a, then b = 1.
  -/

theorem zero_unique : ∀ b : Z, (∀ a : Z, a + b = a) → b = 0 := by
  intro b h1
  have h2 : 0 + b = 0 := by
    apply h1
  rw [add_comm,add_zero] at h2
  assumption

theorem one_unique: ∀ b : Z, (∀ a : Z, a * b = a) → b = 1 := by
  intro b h1
  have h2 : 1 * b = 1 := by
    apply h1
  rw [mul_comm, mul_one] at h2
  assumption

/-
Podasip 3: ∀ a,b,c ∈ ℤ, if a + b = a + c, then b = c.
-/

theorem left_add_cancel : ∀ a b c : Z, a + b = a + c → b = c := by
  intro a b c h
  rw [add_comm] at h
  nth_rewrite 2 [add_comm] at h
  apply add_on_right (b+a) (c+a) (-a) at h
  rw [add_assoc,
    add_assoc,
    add_neg_self,
    add_zero,
    add_zero] at h
  assumption

/- Compliment to left_add_cancel -/

lemma right_add_cancel : ∀ a b c : Z, b + a = b + c → a = c := by
  intro a b c h
  apply add_on_left (b+a) (b+c) (-b) at h
  repeat rw [← add_assoc] at h
  rw [add_comm (-b) b,
    add_neg_self,
    add_comm,
    add_comm 0 c,
    add_zero,
    add_zero] at h
  assumption

/-
Podasip 4a: ∀ a,b ∈ ℤ, we have -(-a) = a
-/

theorem neg_neg : ∀ a : Z, - -a = a := by
  intro a
  have h : a + -a = 0 := by
    rw [add_neg_self]
  apply add_on_right (a + -a) 0 (- -a) at h
  rw [add_assoc,
    add_neg_self,
    add_zero,
    add_comm,
    add_zero] at h
  symm at h
  assumption

/-
Podasip 4b: ∀ a,b ∈ ℤ, -(ab) = (-a)(b) and -(ab) = a(-b)
-/

/-
This will be helpful. Set 1 Podasip 10 : ∀ b ∈ ℤ, b * 0 = 0.
-/

theorem mul_zero : ∀ a : Z, a * 0 = 0 := by
  intro a
  have h : a * (1 + 0) = a := by
    rw [add_zero,mul_one]
  rw [mul_add,mul_one] at h
  apply add_on_left (a + a * 0) a (-a) at h
  rw [← add_assoc,
    add_comm (-a) a,
    add_neg_self,
    add_comm,
    add_zero] at h
  assumption

theorem zero_mul : ∀ a : Z, 0 * a = 0 := by
  intro a
  rw [mul_comm,mul_zero]


theorem neg_mul_left : ∀ a b : Z, -(a * b) = (-a) * b := by
  intro a b
  have h : a * b + -(a * b) = 0 := by
    rw [add_neg_self]
  apply add_on_left (a*b + -(a*b)) 0 (-a*b) at h
  rw [← add_assoc, add_zero,mul_comm]  at h
  nth_rewrite 2 [mul_comm] at h
  rw [<- mul_add b (-a) a] at h
  nth_rewrite 2 [add_comm] at h
  rw [add_neg_self,mul_zero,add_comm,add_zero] at h
  nth_rewrite 2 [mul_comm] at h
  assumption

theorem neg_mul_right : ∀ a b : Z, -(a * b) = a * (-b) := by
  intro a b
  have h : -(b * a) = (-b) * a := by
    rw [neg_mul_left]
  rw [mul_comm] at h
  nth_rewrite 2 [mul_comm] at h
  assumption

/-
Podasip 4c: ∀ a,b ∈ ℤ, (-a)(-b) = ab
-/

theorem neg_mul_neg : ∀ a b : Z, (-a) * (-b) = a * b := by
  intro a b
  have h : (-a) * (-b) = -( a * (-b)) := by
    rw [neg_mul_left]
  rw [neg_mul_right, neg_neg] at h
  exact h

/-
Podasip 4d: ∀ a ∈ ℤ, (-1) * a = -a
-/

theorem mul_neg_one : ∀ a : Z, (-1) * a = -a := by
  intro a
  have h : (-1) * a = -(1 * a) := by
    rw [neg_mul_left]
  nth_rewrite 2 [mul_comm] at h
  rw [mul_one] at h
  exact h

lemma neg_zero : (-0 : Z) = 0 := by
  rw [← mul_neg_one,mul_zero]

lemma add_neg_zero : ∀ a : Z, a + -0 = a := by
  intro a
  rw [neg_zero,add_zero]


lemma neg_zero_add : ∀ a : Z, -0 + a = a := by
  intro a
  rw [add_comm,add_neg_zero]

class RossOrderedRing (Z : Type) extends RossRing Z, LE Z, LT Z, HPow Z ℕ Z, Dvd Z : Type where
  Zplus : Set Z
  pos_nonempty: ∃ a : Z, a ∈ Zplus
  add_closure : ∀ a b : Z, a ∈ Zplus ∧ b ∈ Zplus → (a + b) ∈ Zplus
  mul_closure : ∀ a b : Z, a ∈ Zplus ∧ b ∈ Zplus → (a * b) ∈ Zplus
  non_trivial : 0 ∉ Zplus
  trichotomy  : ∀ a : Z,
    ( a ∈ Zplus ∧ a ≠ 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a = 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a ≠ 0 ∧ (-a) ∈ Zplus )
  lt_def   : ∀ a b : Z, a < b ↔ b + (-a) ∈ Zplus
  le_def  : ∀ a b : Z, a ≤ b ↔ (a = b ∨ a < b)
  dvd_def     : ∀ a b : Z, a ∣ b ↔ ∃ c : Z, b = a * c
  pow_zero    : ∀ a : Z, a ^ 0 = 1
  pow_succ    : ∀ n : ℕ, ∀ a : Z,  a ^ ( Nat.succ n ) = a * a ^ n

namespace RossOrderedRing

variable {Z: Type} [RossOrderedRing Z]

/-
Podasip 2: We need the order axioms to prove: 1 ≠ 0
-/

theorem one_neq_zero : (1 : Z) ≠ 0 := by
  intro h1
  have h2 : ∃ a : Z, a ∈ Zplus := by
    apply pos_nonempty
  rcases h2 with ⟨a, h3⟩
  have h4 : a * 1 = a := by
    rw [mul_one]
  rw [h1, mul_zero] at h4
  rw [← h4] at h3
  apply non_trivial at h3
  exact h3

/-
Podasip 7: 1 ∈ Zplus and -1 ∉ Zplus
-/

theorem one_is_positive : (0:Z) < 1 := by
  rw [lt_def,← mul_neg_one,mul_zero,add_zero]
  have h : (1 : Z) ≠ 0 := by
    apply one_neq_zero
  have tri := trichotomy (1 : Z)
  rcases tri with ⟨ t1, _, _ ⟩ | ⟨ _, t2, _ ⟩  | ⟨ _, _ ,t3 ⟩
  assumption
  tauto
  have and_t3 := And.intro t3 t3
  apply mul_closure (-1 : Z) (-1 : Z) at and_t3
  rw [neg_mul_neg (1 : Z) (1 : Z), mul_one] at and_t3
  assumption

theorem neg_one_negative : (-1 : Z) < 0 := by
  rw [lt_def,neg_neg,add_comm,add_zero]
  have h : (0 : Z) < 1 := one_is_positive
  rw [lt_def,neg_zero,add_zero] at h
  assumption

/-
Podasip 8: Check out the definitions of ≤ and < in the RossOrderedRing class.
Then, show that ∀ a, b, c ∈ Z, a ≤ b ∧ b ≤ c → a ≤ c.
-/

lemma le_trans : ∀ a b c : Z, (a ≤ b) ∧ ( b ≤ c) → a ≤ c := by
  intro a b c h
  rcases h with ⟨ h1, h2 ⟩
  rw [le_def] at h1 h2
  rcases h1 with h1a | h1b
  rcases h2 with h2a | h2b
  rw [le_def]
  left
  rw [h1a]
  assumption
  rw [le_def]
  right
  rw [lt_def,← h1a] at h2b
  rw [lt_def]
  assumption
  rcases h2 with h2a | h2b
  rw [le_def]
  right
  rw [lt_def,h2a] at h1b
  rw [lt_def]
  exact h1b
  rw [lt_def] at h1b h2b
  rw [le_def]
  right
  rw [lt_def]
  have h3 := And.intro h2b h1b
  apply add_closure (c + -b) (b + -a) at h3
  rw [← add_assoc,
     add_assoc c (-b) b,
     add_comm (-b) b,
     add_neg_self,
     add_zero]
     at h3
  assumption


/- Because it's useful later ... -/

lemma lt_trans : ∀ a b c : Z, (a < b) ∧ ( b < c) → (a < c) := by
  intro a b c h
  rcases h with ⟨ h1, h2 ⟩
  rw [lt_def] at h1 h2
  have both_pos := And.intro h2 h1
  apply add_closure at both_pos
  rw [add_assoc,
    ← add_assoc (-b),
    add_comm (-b),
    add_neg_self,
    add_comm 0,
    add_zero] at both_pos
  rw [lt_def]
  assumption

/-
Podasip 9: Prove the following trichotomy variant:
∀ a,b ∈ Z, exactly one of the following is true: a < b, a = b, or b < a.
-/

lemma neg_add_self : ∀ a : Z, -a + a = 0 := by
  intro a
  rw [add_comm,add_neg_self]

lemma neg_of_add_neg_dist : ∀ a b : Z, - (a + -b) = -a + b := by
  intro a b
  rw [← mul_neg_one,mul_add,neg_mul_neg,mul_neg_one,one_mul]

theorem lt_trichotomy : ∀ a b : Z,
  (¬(a < b) ∧ a ≠ b ∧ b < a) ∨
  (¬(a < b) ∧ a = b ∧ ¬(b < a)) ∨
  (  a < b  ∧ a ≠ b ∧ ¬(b < a)) := by
  intro a b
  by_cases h1 : a = b
  have k1: ¬(a<b) := by
    rw [lt_def,h1,add_neg_self]
    exact non_trivial
  have k2: ¬(b < a) := by
    rw [lt_def,h1,add_neg_self]
    exact non_trivial
  tauto --Concludes a = b case. Now assume a ≠ b
  by_cases h2: a < b
  have k1: ¬(b < a) := by
    rw [lt_def]
    rw [lt_def] at h2
    by_contra k
    contrapose h1
    push_neg
    apply right_add_cancel a (-b) b
    rw [neg_add_self,add_comm]
    rw [add_comm,← neg_of_add_neg_dist] at h2
    have trich := trichotomy (a+-b)
    tauto
  tauto  --Concludes a < b case. Now assume a ≥ b. Proof is the same in both cases?
  have h3: b < a := by
    rw [lt_def]
    rw [lt_def] at h2
    contrapose h1
    push_neg
    apply right_add_cancel a (-b) b
    rw [neg_add_self,add_comm]
    rw [add_comm,← neg_of_add_neg_dist] at h2
    have trich := trichotomy (a+-b)
    tauto
  tauto

/-
Podasip 10: ∀ a, b, x, y ∈ Z, if a ≤ b and x ≤ y then a + x ≤ b + y.
Also, ∀ a, b, x, y ∈ Z, if a ≤ b and x ≤ y then ax ≤ by. (This requires some salvaging!)
-/

lemma le_is_refl : ∀ a : Z, a ≤ a := by
  intro a
  rw [le_def]
  left
  rfl

theorem add_on_right_le : ∀ a b x y : Z, a ≤ b →  x ≤ y → (a + x ≤ b + y) := by
  intro a b x y h1 h2
  rw [le_def] at h1 h2
  rcases h1 with h1a | h1b
  rcases h2 with h2a | h2b
  rw [h1a,h2a]
  apply le_is_refl -- why apply and not rw?
  rw [lt_def] at h2b
  rw [le_def]
  right
  rw [lt_def,h1a]
  rw [← mul_neg_one,
    mul_add,
    mul_neg_one,
    mul_neg_one,
    add_assoc,
    ← add_assoc y (-b) (-x),
    add_comm y (-b),
    ← add_assoc,
    ← add_assoc b (-b) y,
    add_neg_self,
    add_comm 0 y,
    add_zero
    ] -- just to simplify
  assumption
  rcases h2 with h2a | h2b
  rw [lt_def] at h1b
  rw [le_def]
  right
  rw [h2a]
  rw [lt_def]
  rw [← mul_neg_one,
    mul_add,
    mul_neg_one,
    mul_neg_one,
    add_assoc,
    add_comm (-a) (-y),
    ← add_assoc y (-y) (-a),
    add_neg_self,
    add_comm 0 (-a),
    add_zero] -- more simpifying
  exact h1b
  rw [lt_def] at h1b h2b
  rw [le_def]
  right
  rw [lt_def]
  rw [← mul_neg_one,
    mul_add,
    mul_neg_one,
    mul_neg_one,
    add_assoc,
    ← add_assoc y (-a) (-x),
    add_comm y (-a),
    add_assoc (-a) y (-x),
    ← add_assoc
  ] -- yet more simplifying
  apply add_closure -- sufficient condition
  tauto

lemma add_on_right_lt : ∀ a b x y : Z,  a < b →  x < y → (a + x < b + y ) := by
  intro a b x y a_lt_b x_lt_y
  rw [lt_def]
  rw [lt_def] at a_lt_b x_lt_y
  rw [← mul_neg_one,
    mul_add,
    mul_neg_one,
    mul_neg_one,
    add_assoc,
    ← add_assoc y,
    add_comm y,
    ← add_assoc,
    ← add_assoc,
    add_assoc]
  apply add_closure
  tauto
-------------------------------------------------------------
----------------------------Set 1----------------------------
-------------------------------------------------------------

/-
In Set 1, the Well-Ordering Principle (WOP) begins to be required.
We extend our class one more time and add some additional definitions (to RossOrderedRing).
Some things to note:
 - Powers are defined with a natural number exponent. Powers can be worked with exactly
   how you worked with naturals in the NNG - to call functions from NNG, do Nat.(function).
   See Nat.succ below for an example. The only exception to this is induction, which is
   called with induction'.
 - The divisibility symbol is not |, the symbol you get by hitting Shift + \ . To get this symbol, type \| or \mid.
-/

class RossWellOrderedRing (Z : Type) extends RossOrderedRing Z: Type where
  WOP : ∀ S ⊆ Zplus, S ≠ ∅ → ∃ m ∈ S, ∀ x ∈ S, m ≤ x

namespace RossWellOrderedRing

variable {Z: Type} [RossWellOrderedRing Z]

/-
NIBZO (no integer between zero and one) is an important fact in well-ordered rings.
Feel free to try to prove it - it's difficult!
Alternatively, leave it sorried out and feel free to use it wherever you'd like.
-/

lemma mul_on_right_le : ∀ a b x y : Z, ( a ∈ Zplus ∧ b ∈ Zplus ∧ x ∈ Zplus ∧ y ∈ Zplus) → ( a ≤ b ∧ x ≤ y ) → ( a * x ≤ b * y) := by
  intro a b x y h
  rcases h with ⟨ _, B, X, Y ⟩
  intro lt
  rcases lt with ⟨ ltab, ltxy ⟩
  rw [le_def] at ltab ltxy
  rw [le_def]
  rcases ltab with ltab1 | ltab2
  rcases ltxy with ltxy1 | ltxy2
  left
  rw [ltab1,ltxy1]
  right
  rw [ltab1,
    lt_def,
    ← mul_neg_one,
    ← mul_assoc,
    mul_comm (-1) b,
    mul_assoc,
    ← mul_add,
    mul_neg_one]
  apply mul_closure
  rw [lt_def] at ltxy2
  tauto
  rcases ltxy with ltxy1 | ltxy2
  right
  rw [ltxy1,
    lt_def,
    mul_comm,
    mul_comm a y,
    neg_mul_right,
    ← mul_add
  ]
  apply mul_closure
  rw [lt_def] at ltab2
  tauto
  right
  rw [lt_def] at ltab2 ltxy2
  rw [lt_def,
    ← add_zero y,
    ← add_neg_self x,
    add_comm x (-x),
    ← add_assoc,
    mul_add,
    mul_comm a x,
    neg_mul_right,
    mul_comm b x,
    add_assoc,
    ← mul_add
  ]
  apply add_closure
  constructor
  apply mul_closure
  tauto
  apply mul_closure
  tauto

lemma pos_def : ∀ a : Z, a ∈ Zplus ↔ 0 < a := by
  intro a
  constructor
  intro h
  rw [lt_def,neg_zero,add_zero]
  assumption
  intro h
  rw [lt_def,neg_zero,add_zero] at h
  assumption

lemma dichotomy : ∀ a : Z, a ≠ 0 → (a ∈ Zplus ∨ -a ∈ Zplus) := by
  intro a h
  have tri :
    ( a ∈ Zplus ∧ a ≠ 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a = 0 ∧ (-a) ∉ Zplus ) ∨
    ( a ∉ Zplus ∧ a ≠ 0 ∧ (-a) ∈ Zplus ) := by
    apply trichotomy
  rcases tri with ⟨ t1 , _ ,_ ⟩ | ⟨_, t2, _ ⟩ | ⟨ _, _, t3 ⟩
  left
  assumption
  by_contra
  apply h at t2
  assumption
  right
  assumption

/-
Set 2 Podasip 9 : ∀ a,b ∈ ℤ , if a ≠ 0 and b ≠ 0, then ab ≠ 0.
-/

theorem no_zero_divisors : ∀ a b : Z, (a ≠ 0 ∧ b ≠ 0) → a * b ≠ 0 := by
  intro a b h
  rcases h with ⟨ a_nonzero, b_nonzero ⟩
  apply dichotomy at a_nonzero
  apply dichotomy at b_nonzero
  rcases a_nonzero with a_pos | neg_a_pos
  rcases b_nonzero with b_pos | neg_b_pos
  have ab_pos : a * b ∈ Zplus := by
    apply mul_closure
    tauto
  by_contra this
  rw [this] at ab_pos
  apply non_trivial at ab_pos
  assumption
  have ab_pos : a * -b ∈ Zplus := by
    apply mul_closure
    tauto
  by_contra this
  rw [← neg_mul_right] at ab_pos
  rw [this,← mul_neg_one,mul_zero] at ab_pos
  apply non_trivial at ab_pos
  assumption
  rcases b_nonzero with b_pos | neg_b_pos
  have ab_pos : -a * b ∈ Zplus := by
    apply mul_closure
    tauto
  by_contra this
  rw [← neg_mul_left,this,← mul_neg_one,mul_zero] at ab_pos
  apply non_trivial at ab_pos
  assumption
  have ab_pos : -a * -b ∈ Zplus := by
    apply mul_closure
    tauto
  by_contra this
  rw [neg_mul_neg,this] at ab_pos
  apply non_trivial at ab_pos
  assumption

theorem left_mul_cancel : ∀ a b c : Z, ( a ∈ Zplus ∧ a * b = a * c) → b = c := by
  intro a b c h
  rcases h with ⟨ a_pos, ab_is_ac ⟩
  apply add_on_right (a * b) (a * c) (-(a*c)) at ab_is_ac
  rw [add_neg_self,
    neg_mul_right,
    ← mul_add] at ab_is_ac
  by_contra this
  apply no_zero_divisors at ab_is_ac
  assumption
  constructor
  by_contra this
  rw [this] at a_pos
  apply non_trivial at a_pos
  assumption
  by_contra that
  apply add_on_right (b + -c) 0 c at that
  rw [add_assoc,
    add_comm (-c) c,
    add_neg_self,
    add_zero,
    add_comm,
    add_zero] at that
  apply this at that
  assumption

theorem nibzo : ¬ (∃ x : Z, 0 < x ∧ x < 1) := by
  intro this
  rcases this with ⟨ x, x_bzo ⟩
  let S := { y : Z | 0 < y ∧ y < 1}
  have x_in_S : x ∈ S := x_bzo
  have build_S : S ≠ ∅  := by
    by_contra! this
    rw[this] at x_in_S
    assumption
  have S_WOP : S ⊆ Zplus := by
    intro y belongs
    rcases belongs with ⟨ y_pos, _ ⟩
    rw[lt_def,neg_zero,add_zero] at y_pos
    assumption
  apply WOP at S_WOP
  apply S_WOP at build_S
  rcases build_S with ⟨m, m_in_S, m_is_glb⟩
  rcases m_in_S with ⟨m_pos, m_lt_one⟩
  have m_mul_self : m * m ≤ 1 * m := by
    apply mul_on_right_le
    rw[← pos_def] at m_pos
    have one_pos : (1:Z) ∈ Zplus := by
      rw[pos_def]
      apply one_is_positive
    tauto
    constructor
    rw[le_def]
    right
    assumption
    rw[le_def]
    left
    tauto
  rw[le_def] at m_mul_self
  rcases m_mul_self with one_eq_m | m_mul_self_lt_m
  rw[mul_comm (1:Z) m] at one_eq_m
  rw[← pos_def] at m_pos
  have m_pos_and_eq := And.intro  m_pos one_eq_m
  apply left_mul_cancel at m_pos_and_eq
  rw[m_pos_and_eq] at m_lt_one
  rw[lt_def,add_neg_self] at m_lt_one
  apply non_trivial at m_lt_one
  assumption
  have m_mul_self_in_S : m * m ∈ S := by
    constructor
    rw [← pos_def] at m_pos
    rw [← pos_def]
    apply mul_closure
    tauto
    rw [one_mul] at m_mul_self_lt_m
    have m_trans_apply := And.intro m_mul_self_lt_m m_lt_one
    apply lt_trans at m_trans_apply
    assumption
  apply m_is_glb at m_mul_self_in_S
  rw[le_def] at m_mul_self_in_S
  rcases m_mul_self_in_S with one_eq_m | m_lt_m_mul_self
  rw[← one_eq_m,one_mul,lt_def,add_neg_self] at m_mul_self_lt_m
  apply non_trivial at m_mul_self_lt_m
  assumption
  rw[one_mul] at m_mul_self_lt_m
  have finale := And.intro m_mul_self_lt_m m_lt_m_mul_self
  apply lt_trans at finale
  rw[lt_def,add_neg_self] at finale
  apply non_trivial at finale
  assumption

/-
Podasip 6 : ∀ a ∈ Z, a ∣ a.
-/

theorem dvd_refl : ∀ a : Z, a ∣ a := by
  intro a
  rw [dvd_def]
  use 1
  rw [mul_one]
/-
Podasip 7: ∀ a, b, c ∈ Z, if a ∣ b then a ∣ bc.
-/

theorem dvd_mul : ∀ a b c : Z, a ∣ b → a ∣ b * c := by
  intro a b c h
  rw [dvd_def] at h
  rcases h with ⟨ d , h2 ⟩
  rw [dvd_def]
  use d * c
  rw [← mul_assoc,← h2]


/-
Podasip 8: ∀ a, b, k ∈ Z, if k ∣ a and k ∣ b then k ∣ (a+b).
-/

theorem dvd_add : ∀ a b c : Z, c ∣ a → c ∣ b → c ∣ (a + b) := by
  intro a b c c_dvd_a c_dvd_b
  rw [dvd_def] at c_dvd_a c_dvd_b
  rcases c_dvd_a with ⟨ i, ci ⟩
  rcases c_dvd_b with ⟨ k, ck ⟩
  rw [dvd_def]
  use i + k
  rw [mul_add,← ci, ← ck]


/-
Podasip 9: ∀ a, b, c ∈ Z, if a ∣ b and b ∣ c then a ∣ c.
-/

theorem dvd_trans : ∀ a b c : Z, a ∣ b ∧ b ∣ c → a ∣ c := by
  intro a b c ⟨ h1, h2 ⟩
  rw [dvd_def]
  rw [dvd_def] at h1 h2
  rcases h1 with ⟨ d, ad ⟩
  rcases h2 with ⟨ e, be ⟩
  use d * e
  rw [← mul_assoc,← ad]
  assumption


/-
Podasip 12: ∀ a, b ∈ ℤ , if a ∣ b then a ≤ b. (Requires salvaging & WOP!)
-/

/-
The following lemmas may be helpful
-/

lemma mul_on_left : ∀ a b c : Z, a = b → c * a = c * b := by
  intro a b c h
  rw [h]

lemma mul_pos_neg : ∀ a b : Z, 0 < a →  b < 0 → a * b < 0 := by
  intro a b a_pos b_neg
  by_contra this
  rw [lt_def,add_comm,add_zero] at this
  rw [← pos_def] at a_pos
  rw [lt_def,add_comm,add_zero] at b_neg
  rw [neg_mul_right] at this
  have that := And.intro a_pos b_neg
  apply mul_closure at that
  tauto

lemma pos_mul_pos : ∀ a b : Z, 0 < a ∧ 0 < a * b → 0 < b := by
  intro a b ⟨ a_pos, ab_pos ⟩
  have b_neq_zero : b ≠ 0 := by
    by_contra! this
    rw [this,mul_zero] at ab_pos
    rw [lt_def,neg_zero,add_zero] at ab_pos
    apply non_trivial at ab_pos
    assumption
  apply dichotomy at b_neq_zero
  rcases b_neq_zero with b_pos | b_neg
  rw [← pos_def]
  assumption
  rw [← pos_def] at a_pos
  have this := And.intro a_pos b_neg
  apply mul_closure at this
  rw [← neg_mul_right] at this
  rw [← pos_def] at ab_pos
  have that := And.intro ab_pos this
  apply add_closure at that
  rw [add_neg_self] at that
  apply non_trivial at that
  cases that

lemma dichotomy_not_pos : ∀ a : Z, a ∉ Zplus → a = 0 ∨ a < 0 := by
  intro a h
  have tri := trichotomy a
  rcases tri with ⟨ t1,_,_⟩ | ⟨_,t2,_⟩ | ⟨ _,_,t3⟩
  tauto
  left
  assumption
  right
  rw [lt_def,add_comm,add_zero]
  assumption

lemma pos_mul_neg : ∀ a b : Z, 0 < a ∧ a * b < 0 → b < 0 := by
  intro a b ⟨ a_pos, ab_neg ⟩
  by_contra this
  rw [lt_def] at this
  apply dichotomy_not_pos at this
  rcases this with b_zero | zero_lt_b
  rw [add_comm,
    add_zero] at b_zero
  apply mul_on_left (-b) 0 (-1) at b_zero
  rw [mul_zero,
    neg_mul_neg,
    mul_comm,
    mul_one] at b_zero
  rw [b_zero,mul_zero] at ab_neg
  rw [lt_def,neg_zero,add_zero] at ab_neg
  apply non_trivial at ab_neg
  assumption
  rw [lt_def,
    add_comm,
    add_zero,
    add_comm,
    add_zero,
    neg_neg] at zero_lt_b
  rw [← pos_def] at a_pos
  have ab_pos := And.intro a_pos zero_lt_b
  apply mul_closure at ab_pos
  rw [lt_def,
    add_comm,
    add_zero,
    ] at ab_neg
  have not_possible := And.intro ab_pos ab_neg
  apply add_closure at not_possible
  rw [add_neg_self] at not_possible
  apply non_trivial at not_possible
  assumption

theorem dvd_le : ∀ a b : Z, a ∣ b → b ∈ Zplus → a ≤ b := by
  intro a b a_dvd_b b_pos
  by_cases a_pos : a ∈ Zplus
  by_contra this
  rw [le_def] at this
  push_neg at this
  rcases this with ⟨ neq, b_lte_a⟩
  rw [lt_def] at b_lte_a
  rw[dvd_def] at a_dvd_b
  rcases a_dvd_b with ⟨ c , b_eq_ac ⟩
  rw [b_eq_ac,
    ← mul_one (-a),
    ← neg_mul_left,
    neg_mul_right,
    ← mul_add] at b_lte_a
  rw [b_eq_ac] at b_pos
  rw [pos_def] at b_pos
  have c_pos :  0 < c := by
    rw [pos_def] at a_pos
    have want := And.intro a_pos b_pos
    apply pos_mul_pos at want
    assumption
  apply dichotomy_not_pos at b_lte_a
  rcases b_lte_a with  eq_zero | lt_zero
  apply no_zero_divisors at eq_zero
  assumption
  constructor
  by_contra this
  rw [this] at a_pos
  apply non_trivial at a_pos
  assumption
  by_contra this
  apply add_on_right (c + -1) (0:Z) (1:Z) at this
  rw [add_assoc,add_comm (-1),add_neg_self,add_zero,add_comm,add_zero] at this
  rw [this,mul_one] at b_eq_ac
  tauto
  rw [pos_def] at a_pos
  have this := And.intro a_pos lt_zero
  apply pos_mul_neg at this
  rw [lt_def,
    add_comm,
    add_zero,
    ← mul_neg_one,
    mul_add,
    neg_mul_neg,
    mul_one,
    mul_neg_one,
    add_comm,
    ← lt_def] at this --simplifying
  have not_possible := And.intro c_pos this
  have finale : ∃ x : Z, 0 < x ∧ x < 1 := by
    use c
  apply nibzo at finale
  assumption
  apply dichotomy_not_pos at a_pos
  rcases a_pos with zero | lt_zero
  rw [zero,le_def]
  right
  rw [← pos_def]
  assumption
  rw [le_def]
  right
  rw [pos_def] at b_pos
  have want := And.intro lt_zero b_pos
  apply lt_trans at want
  assumption

-------------------------------------------------------------
----------------------------Primes---------------------------
-------------------------------------------------------------

/-
We need a definition of prime. Here's the one we work with in Ross Sets.
-/

def Prime (p : Z) : Prop := 1 < p ∧ (∀ a b : Z, a ∈ Zplus → b ∈ Zplus → p = a * b → a = 1 ∨ b = 1)

/-
Here's the first theorem we need on our march toward FTA.
-/

lemma pos_neq_one : ∀ a : Z, a ∈ Zplus → a ≠ 1 → 1 < a := by
  intro a a_pos a_neq_one
  rw [lt_def]
  have tri := trichotomy (a + -1)
  rcases tri with ⟨ t_1,_,_⟩ | ⟨_, t2, _⟩ | ⟨ _, _, t3 ⟩
  assumption
  apply add_on_right (a + -1) 0 1 at t2
  rw [add_assoc,
    add_comm (-1),
    add_neg_self,
    add_zero,
    add_comm,
    add_zero] at t2
  tauto
  rw [pos_def] at a_pos
  rw [← mul_neg_one,
    mul_add,
    mul_neg_one,
    mul_neg_one,
    neg_neg,
    add_comm,
    ← lt_def] at t3
  have not_possible : ∃ (x : Z), 0 < x ∧ x < 1 := by
    use a
  apply nibzo at not_possible
  tauto

theorem prime_dvd_gt_one : ∀ a : Z, 1 < a → ∃ p : Z, Prime p ∧ p ∣ a := by
  intro a a_gt_one
  by_contra! this
  let S := { b : Z | 1 < b ∧ ∀ (p : Z), Prime p → ¬ p ∣ b}
  have a_in_S : a ∈ S := by
    constructor
    repeat assumption
  have S_nonempty : S ≠ ∅ := by
    by_contra that
    rw [that] at a_in_S
    assumption
  have SWOP : S ⊆ Zplus := by
    intro b ⟨ one_lt_b, _⟩
    have zero_lt_one : (0:Z) < 1 := one_is_positive
    have hyp := And.intro zero_lt_one one_lt_b
    apply lt_trans at hyp
    rw [pos_def]
    assumption
  apply WOP at SWOP
  apply SWOP at S_nonempty
  rcases S_nonempty with ⟨ m, m_in_S, m_is_glb ⟩
  have m_belong_s := m_in_S
  rcases m_in_S with ⟨ one_lt_m, not_p_dvd_m ⟩
  by_cases h: Prime m
  apply not_p_dvd_m m at h
  have m_dvd_m := dvd_refl m
  tauto
  rw [Prime] at h
  push_neg at h
  have h' := h one_lt_m
  rcases h' with ⟨ b, ⟨ c, b_pos, c_pos , m_bc, b_neq_one, c_neq_one ⟩ ⟩
  have b_dvd_m : b ∣ m := by
    rw [dvd_def]
    use c
  have m_pos : m ∈ Zplus := by
    have one_pos : (0 : Z) < 1 := one_is_positive
    have zero_lt_one_lt_m := And.intro one_pos one_lt_m
    apply lt_trans at zero_lt_one_lt_m
    rw [lt_def,neg_zero,add_zero] at zero_lt_one_lt_m
    assumption
  have bm_pos := And.intro b_pos m_pos
  have b_dvd_m_keep := b_dvd_m
  apply dvd_le at b_dvd_m
  have b_le_m := b_dvd_m bm_pos.right
  rw [le_def] at b_le_m
  rcases b_le_m with b_eq_m | b_lt_m
  rw [b_eq_m] at m_bc
  nth_rewrite 1 [← mul_one m] at m_bc
  have m_pos_and_m_bc := And.intro m_pos m_bc
  apply left_mul_cancel at m_pos_and_m_bc
  tauto
  have b_not_in_S : b ∉ S := by
    by_contra this
    apply m_is_glb at this
    rw [le_def] at this
    rcases this with this | that
    rw [this] at b_lt_m
    rw [lt_def,add_neg_self] at b_lt_m
    apply non_trivial at b_lt_m
    assumption
    have not_possible := And.intro b_lt_m that
    apply lt_trans at not_possible
    rw [lt_def,add_neg_self] at not_possible
    apply non_trivial at not_possible
    assumption
  have q_dvd_b : ∃ (q : Z), Prime q ∧ q ∣ b := by
    by_contra! this
    have b_in_S : b ∈ S := by
      apply pos_neq_one at b_pos
      apply b_pos at b_neq_one
      tauto
    tauto
  rcases q_dvd_b with ⟨ q, q_prime, q_dvd_b ⟩
  have q_dvd_b_and_b_dvd_m := And.intro q_dvd_b b_dvd_m_keep
  apply dvd_trans q b m at q_dvd_b_and_b_dvd_m
  apply not_p_dvd_m at q_prime
  tauto


-------------------------------------------------------------
-----------------------------GCDs----------------------------
-------------------------------------------------------------

/-
The theorem below asserts that GCDs exist.
-/

lemma dvd_zero : ∀ a : Z, a ∣ 0 := by
  intro a
  rw [dvd_def]
  use 0
  rw [mul_zero]

lemma lt_gt : ∀ a b : Z, a < b ∧ b < a → False := by
  intro a b ⟨ a_lt_b, b_lt_a ⟩
  rw [lt_def] at a_lt_b b_lt_a
  have impossible : b + -a ∈ Zplus ∧ a + -b ∈ Zplus := by
    tauto
  apply add_closure at impossible
  rw [add_assoc,
    ← add_assoc (-a),
    add_comm (-a),
    add_neg_self,
    add_comm 0,
    add_zero,
    add_neg_self] at impossible
  apply non_trivial at impossible
  assumption

lemma pos_le : ∀ a b : Z, a ∈ Zplus ∧ a ≤ b → b ∈ Zplus := by
  intro a b ⟨ a_pos, a_le_b ⟩
  rw [le_def] at a_le_b
  rcases a_le_b with eq | lt
  rw [← eq]
  assumption
  rw [pos_def] at a_pos
  have want := And.intro a_pos lt
  apply lt_trans at want
  rw [pos_def]
  assumption

lemma not_empty_implies_exists : (A : Set ZZ) ≠ ∅ → ∃ a : ZZ, a ∈ A := by
  contrapose! -- new tactic
  intro h
  ext a -- new tactic ``extensionality''
  constructor --new tactic
  intro h'
  apply h at h'
  exact h'
  intro h'
  cases h'

lemma POW : ∀ (S : Set Z), S ≠ ∅ → (∃ ub : Z, ∀ s : Z, (s ∈ S) → s < ub) → (∃ lub : Z, lub ∈ S ∧ ∀ s : Z, s ∈ S → s ≤ lub) := by
  intro S S_nonempty bnd
  rcases bnd with ⟨ b, b_is_ub ⟩
  let P := { b + -s | s ∈ S }
  have P_sub_Zplus : P ⊆ Zplus := by
    intro a a_in_P
    rcases a_in_P with ⟨ x, ⟨ x_in_S, bs_x ⟩ ⟩
    have bx_pos : 0 < b + -x := by
      apply b_is_ub at x_in_S
      rw [lt_def] at x_in_S
      rw [← pos_def]
      assumption
    rw [bs_x,← pos_def] at bx_pos
    assumption
  have P_nonempty : P ≠ ∅ := by
    apply not_empty_implies_exists at S_nonempty
    rcases S_nonempty with ⟨ a, a_in_S ⟩
    have want : b + -a ∈ P := by
      tauto
    by_contra that
    rw [that] at want
    assumption
  have hWOP := WOP P P_sub_Zplus P_nonempty
  rcases hWOP with ⟨ m, m_in_P, m_is_glb ⟩
  use b + -m
  constructor
  rcases m_in_P with ⟨ s ,sx_in_S, s_bm ⟩
  apply add_on_right (b + -s) m (-m) at s_bm
  rw [add_neg_self,
    add_assoc,
    add_comm (-s),
    ← add_assoc] at s_bm
  apply add_on_right (b + -m + -s) 0 s at s_bm
  rw [add_assoc,
    add_comm (-s),
    add_neg_self,
    add_comm 0,
    add_zero,
    add_zero] at s_bm
  rw [← s_bm] at sx_in_S
  tauto
  intro s s_in_S
  rw [le_def]
  by_contra! that
  rcases that with ⟨ sup_s, impossible ⟩
  rw [lt_def] at impossible
  apply dichotomy_not_pos at impossible
  rcases impossible with imp1 | imp2
  apply add_on_right (b +-m + -s) 0 s at imp1
  rw [add_assoc,
    add_comm (-s),
    add_neg_self,
    add_zero,
    add_comm 0,
    add_zero] at imp1
  tauto
  have want : b + -s ∈ P := by
    tauto
  apply m_is_glb at want
  rw [le_def] at want
  rcases want with mbs | m_lt_bs
  apply add_on_right m (b + -s) s at mbs
  rw [add_assoc,
    add_comm (-s),
    add_neg_self,
    add_zero] at mbs
  apply add_on_left (m+s) b (-m) at mbs
  rw [
    ← add_assoc,
    add_comm (-m),
    add_neg_self,
    add_comm,
    add_zero,
    add_comm
  ] at mbs
  tauto
  rw [add_assoc,
    add_comm (-m),
    ← add_assoc] at imp2
  rw [lt_def] at imp2 m_lt_bs
  rw [add_comm,add_zero] at imp2
  have want := And.intro m_lt_bs imp2
  apply add_closure at want
  rw [add_neg_self] at want
  apply non_trivial at want
  assumption

lemma one_dvd : ∀ a : Z, 1 ∣ a := by
  intro a
  rw [dvd_def]
  use a
  rw [mul_comm,mul_one]

lemma add_one_lt : ∀ a : Z, a < a + 1 := by
  intro a
  rw [lt_def,
      add_assoc,
      add_comm 1,
      ← add_assoc,
      add_neg_self,
      add_comm,
      add_zero,
      pos_def]
  apply one_is_positive

lemma le_ge : ∀ a b : Z, a ≤ b ∧ b ≤ a → a = b := by
  intro a b ⟨ a_le_b, b_le_a ⟩
  rw [le_def] at a_le_b b_le_a
  rcases a_le_b with ab | a_lt_b
  assumption
  rcases b_le_a with ba | b_lt_a
  tauto
  have impossible : a < b ∧ b < a := by
    tauto
  apply lt_gt at impossible
  cases impossible

theorem gcd_exists : ∀ a b : Z, a ∈ Zplus ∧ b ∈ Zplus → (∃! g : Z, g ∣ a ∧ g ∣ b ∧ (∀ d : Z, d ∣ a → d ∣ b → d ≤ g)) := by
  intro a b ⟨ _, b_pos ⟩
  let S:= { d: Z | d ∣ a ∧ d ∣ b }
  have S_bnd : ∀ s : Z, (s ∈ S) → s ≤ b := by
    intro s s_in_S
    by_cases s_pos : 0 < s
    rcases s_in_S with ⟨_, s_dvd_b ⟩
    apply dvd_le at s_dvd_b
    repeat tauto
    rw [lt_def,neg_zero,add_zero] at s_pos
    apply dichotomy_not_pos at s_pos
    rcases s_pos with s_zero | s_neg
    rw [s_zero,le_def]
    right
    rw [← pos_def]
    assumption
    rw [pos_def] at b_pos
    have want := And.intro s_neg b_pos
    apply lt_trans at want
    rw [le_def]
    right
    assumption
  have SPOW : ∃ ub : Z, ∀ s : Z, (s ∈ S) → s < ub := by
    use b + 1
    intro s s_in_S
    apply S_bnd at s_in_S
    rw [le_def] at s_in_S
    rcases s_in_S with sb | s_lt_b
    rw [sb]
    apply add_one_lt
    have b_lt_b_add_one : b < b + 1 := by
      apply add_one_lt
    have want := And.intro s_lt_b b_lt_b_add_one
    apply lt_trans at want
    assumption
  apply POW at SPOW
  rcases SPOW with ⟨ lub, ⟨ lub_in_S, lub_is_sup ⟩ ⟩
  use lub
  have lub_belongs_S : lub ∈ S := lub_in_S
  rcases lub_in_S with ⟨ lub_dvd_a, lub_dvd_b ⟩
  repeat constructor
  tauto
  repeat constructor
  tauto
  intro d d_dvd_a d_dvd_b
  have d_in_S : d ∈ S := by
    tauto
  apply lub_is_sup at d_in_S
  assumption
  intro g ⟨ g_dvd_a, g_dvd_b, g_is_lub⟩
  have g_le_lub : g ≤ lub := by
    have g_dvd_ab := And.intro g_dvd_a g_dvd_b
    have g_in_S : g ∈ S := by
      tauto
    apply lub_is_sup at g_in_S
    assumption
  have lub_le_g : lub ≤ g := by
    apply g_is_lub at lub_dvd_a
    apply g_is_lub at lub_dvd_b
    repeat assumption
    rcases lub_belongs_S with ⟨ lub_dvd_a, _⟩
    repeat assumption
  have want := And.intro g_le_lub lub_le_g
  apply le_ge at want
  assumption
  have one_dvd_a : 1 ∣ a := by
    apply one_dvd
  have one_dvd_b : 1 ∣ b := by
    apply one_dvd
  have one_in_S : 1 ∈ S := by
    tauto
  by_contra that
  rw [that] at one_in_S
  assumption



/-
To smoothly use GCDs, we'll extend our class one more time. -/

class RossGCDWellOrderedRing (Z : Type) extends RossWellOrderedRing Z: Type where
  --Given a, b ∈ Z, gcd a b has type Z
  gcd : Z → Z → Z
  --Below are the three properties you verify in gcd_exists_unique.
  gcd_dvd_left : ∀ a b : Z, gcd a b ∣ a
  gcd_dvd_right : ∀ a b : Z, gcd a b ∣ b
  dvd_le_gcd : ∀ d a b : Z, d ∣ a → d ∣ b → d ≤ gcd a b


namespace RossGCDWellOrderedRing

variable {Z: Type} [RossGCDWellOrderedRing Z]

/-
GCDs aren't needed to verify the division algorithm, but they're needed for our first
big GCD result - Bézout's Identity.

The standard proof of the division algorithm makes use of the positive case to prove the negative
case. To simplify this, the two versions are separated. Of course, in practice, only dvd_alg will
need to be used.
-/

lemma gcd_pos (a b : Z) : 0 < gcd a b := by
  have one_dvd_a : 1 ∣ a := by
    rw [dvd_def]
    use a
    rw [one_mul]
  have one_dvd_b : 1 ∣ b := by
    rw [dvd_def]
    use b
    rw [one_mul]
  apply dvd_le_gcd 1 a b at one_dvd_a
  apply one_dvd_a at one_dvd_b
  have one_pos : (0:Z) < 1 := one_is_positive
  rw [le_def] at one_dvd_b
  rcases one_dvd_b with eq_one | gt_one
  rw [eq_one] at one_pos
  assumption
  have want := And.intro one_pos gt_one
  apply lt_trans at want
  assumption

lemma zero_add (a : Z) : 0 + a = a := by
  rw [add_comm,add_zero]

lemma zero_mul (a : Z) : 0 * a = 0 := by
  rw [mul_comm,mul_zero]

lemma add_mul (a b c : Z) : (a+b)*c = a*c+b*c := by
  rw [mul_comm,mul_add,mul_comm,mul_comm c b]

lemma one_pos_min : ∀ a : Z, a ∈ Zplus ↔ 1 ≤ a := by
  intro a
  constructor
  intro apos
  rw [le_def]
  rcases lt_trichotomy a 1 with tri1 | tri2 | tri3
  tauto
  tauto
  exfalso
  rcases tri3 with ⟨ a_lt_one, _, _ ⟩
  have a_gt_zero : 0 < a := by
    rw [lt_def,neg_zero,add_zero]
    exact apos
  have nbzo : ¬ (∃ x : Z, (0 :Z) < x ∧ x < (1 : Z)) := by exact nibzo
  push_neg at nbzo
  apply nbzo a at a_gt_zero
  tauto
  intro one_le_a
  rw [le_def] at one_le_a
  rcases one_le_a with aone | one_lt_a
  rw [← aone,pos_def]
  exact one_is_positive
  rw [lt_def] at one_lt_a
  have one_pos : (0:Z) < 1 := by exact one_is_positive
  have both := And.intro one_lt_a one_pos
  rw [← pos_def] at both
  apply add_closure at both
  rw [add_assoc, neg_add_self,add_zero] at both
  exact both

lemma zero_lt_iff_neg_lt_zero : ∀ a : Z, 0 < a ↔ -a < 0 := by
  intro a
  constructor
  intro h
  rw [lt_def,neg_neg,add_comm,add_zero]
  rw [lt_def,neg_zero,add_zero] at h
  exact h
  intro h
  rw [lt_def,neg_zero,add_zero]
  rw [lt_def,neg_neg,add_comm,add_zero] at h
  exact h

theorem lt_add_left: ∀ a b x : Z, a < b ↔ a + x < b + x := by
  intro a b x
  constructor
  intro h
  rw [lt_def, ← mul_neg_one,mul_add,mul_neg_one,mul_neg_one,add_comm (-a) (-x),
    ← add_assoc, add_assoc b x (-x), add_neg_self,add_zero]
  rw [lt_def] at h
  exact h
  intro h
  rw [lt_def, ← mul_neg_one,mul_add,mul_neg_one,mul_neg_one,add_comm (-a) (-x),
    ← add_assoc, add_assoc b x (-x), add_neg_self,add_zero] at h
  rw [lt_def]
  exact h

lemma le_refl : ∀ a : Z, a ≤ a := by
  intro a
  rw [le_def]
  tauto

lemma dvd_alg_pos : ∀ a b : Z, 0 < a → 0 < b → ∃ q r : Z, a = q*b + r ∧ 0 ≤ r ∧ r < b := by
  intro a b
  intro apos bpos
  let S := { k : Z | ∃ q : Z, k +- 1 = a + -(q*b) ∧  0 < k  }
  have h1 : S ⊆ Zplus := by -- k+-1 is the remainder
    intro y hy
    rcases hy with ⟨ q, _, hy2 ⟩
    rw [lt_def,neg_zero,add_zero] at hy2
    exact hy2
  have h2 : S ≠ ∅ := by
    intro h
    have h3 : a + 1 ∈ S := by
      use 0
      constructor
      rw [zero_mul,neg_zero,add_zero,add_assoc,add_neg_self,add_zero]
      rw [lt_def,neg_zero,add_zero] at apos
      rw [lt_def,neg_zero,add_zero]
      apply add_closure
      have one_pos : (0:Z) < 1 := by exact one_is_positive
      nth_rw 2 [pos_def]
      tauto
    rw [h] at h3
    tauto
  apply WOP at h1
  apply h1 at h2
  rcases h2 with ⟨ l, ⟨ q, qle, lineq ⟩, hrwop ⟩ --l is r+1
  use q
  use (l+-1)
  constructor
  rw [qle,add_comm a (-(q*b)), ← add_assoc, add_neg_self, zero_add]
  constructor
  rw [le_def]
  by_cases h: l = 1
  left
  rw [h,add_neg_self]
  right
  rw [lt_def,neg_zero,add_zero] at lineq
  apply (one_pos_min l).mp at lineq
  rw [le_def] at lineq
  rw [lt_def,neg_zero,add_zero,← lt_def]
  tauto
  by_contra h
  rw [qle,lt_def,← mul_neg_one,mul_add,mul_neg_one,mul_neg_one,
    neg_neg,add_comm (-a) (q*b),← add_assoc] at h
  nth_rw 1 [← one_mul b] at h
  rw [← add_mul,add_comm 1 q,← neg_neg ((q+1)*b),← mul_neg_one] at h
  nth_rw 3 [← mul_neg_one] at h
  rw [← mul_add,mul_neg_one,add_comm] at h
  have m : 0 ≤ a + -((q + 1) * b) := by
    rw [le_def, lt_def,neg_zero,add_zero]
    have trich := trichotomy (a + -((q + 1) * b))
    tauto
  apply add_on_right_le 1 1 at m
  rw [add_zero,add_comm] at m
  have k : a + -((q+1)*b) +1∈ S := by
    use q+1
    constructor
    rw [add_assoc, add_neg_self,add_zero]
    rw [lt_def,one_pos_min,neg_zero,add_zero]
    exact m
  have negbneg : -b < 0 := by
    rw [zero_lt_iff_neg_lt_zero] at bpos
    exact bpos
  have almost : a + -((q+1)*b) < l+-1 := by
    rw [lt_add_left (-b) 0 (a + -(q*b)),zero_add,← mul_neg_one,← add_assoc, add_comm (-1*b) a,
      add_assoc] at negbneg
    nth_rw 2 [← mul_neg_one] at negbneg
    rw [← mul_add,mul_neg_one] at negbneg
    nth_rw 1 [← one_mul b] at negbneg
    rw [← add_mul, add_comm 1 q,← qle] at negbneg
    exact negbneg
  rw [lt_add_left ( a+ -((q + 1) * b)) (l + -1) 1, add_assoc l (-1) 1, neg_add_self,add_zero] at almost
  apply hrwop at k
  rw [le_def] at k
  have final_trich := lt_trichotomy (a + -((q + 1) * b) + 1) l
  tauto
  exact le_refl 1

lemma trich_simple : ∀ a : Z, a < 0 ∨ a = 0 ∨ 0 < a := by
  intro a
  rw [lt_def, lt_def,zero_add,neg_zero,add_zero]
  have trich_a := trichotomy a
  tauto

lemma neg_add_dist: ∀ a b : Z, -(a+b) = -a+-b := by
  intro a b
  rw [←mul_neg_one, mul_add,mul_neg_one, mul_neg_one]

lemma lt_add_right: ∀ a b x : Z, a < b ↔ x + a < x + b := by
  intro a b x
  rw [add_comm,add_comm x b]
  exact lt_add_left a b x

theorem dvd_alg : ∀ a b : Z, 0 < b → ∃ q r : Z, a = q * b + r ∧ 0 ≤ r ∧ r < b := by
  intro a b bpos
  have bpos_copy := bpos
  rcases trich_simple a with aneg | azero | apos
  have negapos : 0 < -a := by
    rw [← neg_neg a,← zero_lt_iff_neg_lt_zero] at aneg
    exact aneg
  apply dvd_alg_pos (-a) b at negapos
  apply negapos at bpos
  rcases bpos with ⟨ q, r, division, r_nonneg, r_lt_b ⟩
  rw [le_def] at r_nonneg
  rcases r_nonneg with zero_eq_r | zero_lt_r
  use (-q)
  use 0
  constructor
  rw [← zero_eq_r,add_zero] at division
  apply mul_on_left (-a) (q*b) (-1) at division
  rw [mul_neg_one,mul_neg_one,neg_neg,neg_mul_left] at division
  rw [add_zero]
  exact division
  rw [le_def]
  tauto
  use (-q+-1)
  use (b+-r)
  constructor
  rw [← neg_neg a, division,add_mul,mul_neg_one,← add_assoc, add_assoc (-q*b) (-b) b,
    neg_add_self,add_zero,neg_add_dist,neg_mul_left]
  constructor
  rw [lt_add_left r b (-r),add_neg_self] at r_lt_b
  rw [le_def]
  tauto
  nth_rw 2 [← add_zero b]
  rw [← lt_add_right (-r) 0 b]
  rw [← zero_lt_iff_neg_lt_zero]
  exact zero_lt_r
  use 0
  use 0
  constructor
  rw [azero, zero_mul, add_zero]
  rw [le_def]
  tauto
  apply dvd_alg_pos
  exact apos
  exact bpos

lemma le_antisymm : ∀ a b : Z, a ≤ b → b ≤ a → a = b := by
  intro a b  a_le_b b_le_a
  rw [le_def] at a_le_b b_le_a
  rcases a_le_b with ab | a_lt_b
  assumption
  rcases b_le_a with ba | b_lt_a
  tauto
  have impossible : a < b ∧ b < a := by
    tauto
  apply lt_gt at impossible
  cases impossible

theorem bezout : ∀ a b : Z, (a ≠ 0 ∨ b ≠ 0) → ∃ m n : Z, m * a + n * b = gcd a b := by
  intro a b nzo
  let S := { k : Z | ∃ m n : Z, k = m * a + n * b ∧ 0 < k }
  have h1 : S ⊆ Zplus := by
    intro y hy
    rcases hy with ⟨ m, n, _, hy2 ⟩
    rw [lt_def,neg_zero,add_zero] at hy2
    exact hy2
  have h2 : S ≠ ∅ := by
    intro k
    rcases nzo with a_nonzero | b_nonzero
    have trich_a := trich_simple a
    rcases trich_a with a1 | a2 | a3
    have l : -a ∈ S:= by
      use (-1)
      use 0
      rw [zero_mul,add_zero,mul_neg_one]
      constructor
      rfl
      rw [← neg_neg a,← zero_lt_iff_neg_lt_zero] at a1
      exact a1
    rw [k] at l
    tauto
    tauto
    have l : a ∈ S := by
      use 1
      use 0
      rw [zero_mul,one_mul,add_zero]
      tauto
    rw [k] at l
    tauto
    have trich_b := trich_simple b
    rcases trich_b with b1 | b2 | b3
    have l : -b ∈ S := by
      use 0
      use -1
      rw [zero_mul,mul_neg_one,zero_add,zero_lt_iff_neg_lt_zero,neg_neg]
      tauto
    rw [k] at l
    tauto
    tauto
    have l : b ∈ S := by
      use 0
      use 1
      rw [zero_mul,one_mul,zero_add]
      tauto
    rw [k] at l
    tauto
  apply WOP at h1
  apply h1 at h2
  rcases h2 with ⟨ d, ⟨ ⟨ m, ⟨ n, ⟨ d_lc, d_pos ⟩ ⟩ ⟩, d_wop ⟩ ⟩
  have d_dvd_a : d ∣ a := by
    apply dvd_alg a d at d_pos
    rcases d_pos with ⟨q, ⟨ r, ⟨ a_eq_qd_add_r, r_nonneg, r_le_d ⟩ ⟩ ⟩
    rw [le_def] at r_nonneg
    rcases r_nonneg with zero_r | zero_lt_r
    rw [← zero_r,add_zero] at a_eq_qd_add_r
    rw [dvd_def]
    use q
    rw [mul_comm]
    exact a_eq_qd_add_r
    exfalso
    rw [d_lc] at a_eq_qd_add_r
    have r_in_S : r ∈ S := by
      use 1 + -(q*m)
      use -(q*n)
      constructor
      apply add_on_left a (q * (m * a + n * b) + r) (-(q * (m * a + n * b))) at a_eq_qd_add_r
      rw [← add_assoc,neg_add_self,zero_add,mul_add,← mul_neg_one,mul_add,
        add_assoc (-1 * (q * (m * a))) (-1 * (q * (n * b))) a,
        add_comm  (-1 * (q * (n * b))) a,
        ← add_assoc,mul_neg_one,neg_mul_left,← mul_assoc] at a_eq_qd_add_r
      nth_rw 2 [← one_mul a] at a_eq_qd_add_r
      rw [← add_mul,← neg_mul_left,add_comm (-(q*m)) 1,
        mul_neg_one, ← mul_assoc q n b,neg_mul_left (q*n) b] at a_eq_qd_add_r
      symm at a_eq_qd_add_r
      exact a_eq_qd_add_r
      exact zero_lt_r
    apply d_wop at r_in_S
    rw [le_def] at r_in_S
    have trich_dr := lt_trichotomy d r
    tauto
  have d_dvd_b : d ∣ b := by
    apply dvd_alg b d at d_pos
    rcases d_pos with ⟨q, ⟨ r, ⟨ b_eq_qd_add_r, r_nonneg, r_le_d ⟩ ⟩ ⟩
    rw [le_def] at r_nonneg
    rcases r_nonneg with zero_r | zero_lt_r
    rw [← zero_r,add_zero] at b_eq_qd_add_r
    rw [dvd_def]
    use q
    rw [mul_comm]
    exact b_eq_qd_add_r
    exfalso
    rw [d_lc] at b_eq_qd_add_r
    have r_in_S : r ∈ S := by
      use -(q*m)
      use 1+ -(q*n)
      constructor
      apply add_on_left b (q * (m * a + n * b) + r) (-(q * (m * a + n * b))) at b_eq_qd_add_r
      rw [← add_assoc,neg_add_self,zero_add,mul_add,← mul_neg_one,mul_add,
        add_assoc,
        mul_neg_one,← mul_assoc,neg_mul_left,← mul_assoc,← mul_assoc] at b_eq_qd_add_r
      nth_rw 2 [← one_mul b] at b_eq_qd_add_r
      rw [← add_mul,mul_neg_one] at b_eq_qd_add_r
      nth_rw 2 [← neg_mul_left] at b_eq_qd_add_r
      rw [add_comm (-(q*n)) 1] at b_eq_qd_add_r
      symm at b_eq_qd_add_r
      exact b_eq_qd_add_r
      exact zero_lt_r
    apply d_wop at r_in_S
    rw [le_def] at r_in_S
    have trich_dr := lt_trichotomy d r
    tauto
  have d_le_gcd : d ≤ gcd a b := by
    apply dvd_le_gcd  d a b at d_dvd_a
    apply d_dvd_a at d_dvd_b
    exact d_dvd_b
  have gcd_le_d : gcd a b ≤ d := by
    apply dvd_le
    rw [d_lc]
    apply dvd_add
    rw [mul_comm]
    apply dvd_mul
    exact gcd_dvd_left a b
    rw [mul_comm]
    apply dvd_mul
    exact gcd_dvd_right a b
    rw [lt_def,neg_zero,add_zero] at d_pos
    exact d_pos
  apply le_antisymm at d_le_gcd
  apply d_le_gcd at gcd_le_d
  use m
  use n
  rw [← d_lc,←gcd_le_d]

/-
The Fundamental Lemma wasn't included with Day 9, but it could've been!
A proof using Bézout isn't too difficult - try it.
-/

theorem fundamental_lemma : ∀ a b c : Z, (a ≠ 0 ∨ b ≠ 0) → a ∣ b * c → gcd a b = 1 → a ∣ c := by
  intro a b c notzero a_dvd_bc gcd_ab_one
  apply bezout at notzero
  rcases notzero with ⟨m, ⟨ n , bezout⟩⟩
  rw [gcd_ab_one] at bezout
  rw [dvd_def]
  rw [dvd_def] at a_dvd_bc
  rcases a_dvd_bc with ⟨ k , ak_bc⟩
  apply mul_on_left (m * a + n * b) 1 c at bezout
  rw [mul_one,
    mul_add] at bezout
  nth_rewrite 3 [mul_comm] at bezout
  rw [mul_assoc,ak_bc] at bezout
  rw [mul_comm,mul_comm n,mul_comm m,mul_assoc,mul_assoc,← mul_add] at bezout
  use m* c + k * n
  tauto

-----------------------------------------
-----------Prime Factorization-----------
-----------------------------------------

/-
How can one make sense out of a prime factorization in Lean?
One way is to use a Lean `List` and put all the prime factors in there.
Definitions that help us achieve this are given below.
-/

open List --Makes it easier to call List theorems from the library

/- Lists are an inductive type, so they admit recursive definitions.
For Lists, you can define properties based on the empty list [] and on
lists of the form (x :: l) for x : Z and l : List Z (this is the List with
x in the first slot and the elements of List l following it). Definitions like
this work because l always has smaller length than (x :: l), so the process
terminates through repeated application.
-/
def list_product : List Z → Z
| []             => (1:Z) --The product of the empty list is the empty product: 1.
| (head :: tail) => head * list_product tail

/-
Our prime factorization lists will have the property below.
The symbol ∈ gives List membership just like it gives Set membership.
-/
def prime_list (S : List Z) := ∀ s ∈ S, Prime s

/-
Three theorems are given below that contain proofs of common-sense facts
that we'd expect to be true of products of elements of Z.
-/

--rw is the tactic to use to apply the recursive definition of list_product.
theorem prod_singleton : ∀ a : Z, list_product [a] = a := by
  intro a
  rw [list_product,list_product,mul_one]

/-
- For Lists S and T, S ++ T is the list with the elements of S first and the elements
of T following it - in programming terminology, we append T to S.
- You can induct on Lists. In the induction below, the base case is S = []. After you close
that goal, the induction hypothesis (tail_ih) assumes that the desired conclusion is true for all lists
S = tail, then you're tasked with proving that it holds for lists one larger - lists of the form
(d :: tail).
- Some library theorems for Lists are used here - nil_append and cons_append.
The Mathlib 4 documentation can be used to browse what can be done with lists:
https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html
-/

theorem prod_append : ∀ S T : List Z, list_product (S ++ T) = list_product S * list_product T := by
  intro S T
  induction' S with d tail tail_ih
  rw [nil_append,list_product,one_mul]
  rw [cons_append,list_product,tail_ih,list_product,mul_assoc]

-- Use the library - what's going on here?
theorem prod_rep_eq_pow : ∀ a : Z, ∀ n : ℕ, list_product (replicate n a) = a^n := by
  intro a n
  induction' n with d hd
  rw [replicate,list_product,pow_zero]
  rw [replicate_add,prod_append,hd,replicate_succ,replicate,
  prod_singleton,pow_succ,mul_comm]

/-
Our big finale is below! At the time of writing this, we have a nice proof of existence, but
not of uniqueness. Typical uniqueness proofs require ordering the prime lists least-to-greatest, something
we haven't figured out yet; in fact, since Lists are ordered, the most "obvious" uniqueness
statement (using the unique existence quantifier ∃! instead of ∃) isn't even true here.

Can you provide the full proof? :)

(Note: [] is vacuously a prime_list, so the theorem even holds for a = 1 - no need to salvage.)
-/

lemma le_ge : ∀ a b : Z, a ≤ b ∧ b ≤ a → a = b := by
  intro a b ⟨ a_le_b, b_le_a ⟩
  rw [le_def] at a_le_b b_le_a
  rcases a_le_b with ab | a_lt_b
  assumption
  rcases b_le_a with ba | b_lt_a
  tauto
  have impossible : a < b ∧ b < a := by
    tauto
  apply lt_gt at impossible
  cases impossible

theorem prime_factorization_exists : ∀ a : Z, a ∈ Zplus → ∃ l : List Z, prime_list l ∧ list_product l = a := by
  let S := {n : Z | n ∈ Zplus ∧ ¬ ∃ l : List Z, prime_list l ∧ list_product l = n}
  intro a hap
  by_cases want : S ≠ ∅
  have s_pos : S ⊆ Zplus := by
    intro s s_in_S
    rcases s_in_S with ⟨ s_pos, _ ⟩
    tauto
  have hwop := WOP S s_pos want
  rcases hwop with ⟨m, ⟨hms, m_min⟩⟩
  exfalso
  apply hms.right
  by_cases hm1: m=1
  use []
  tauto
  have mg1 : 1 < m := by
    rcases hms with ⟨ m_pos, _⟩
    push_neg at hm1
    rw [one_pos_min] at m_pos
    rw [le_def] at m_pos
    rcases m_pos with m_one | m_gt_one
    repeat tauto
  have m_divisor := prime_dvd_gt_one m mg1
  rcases m_divisor with ⟨p, ⟨p_prime, p_div_m⟩⟩
  rw [dvd_def] at p_div_m
  rcases p_div_m with ⟨c, hc⟩
  have c_factorization : ∃ l : List Z, prime_list l ∧ list_product l = c := by
    by_contra this
    rcases hms with ⟨ m_pos,_⟩
    have p_is_prime := p_prime
    rcases p_prime with ⟨ p_gt_one,_⟩
    have p_pos : 0 < p := by
        have zero_lt_one : (0:Z) < 1 := by
          apply one_is_positive
        have want := And.intro zero_lt_one p_gt_one
        apply lt_trans at want
        tauto
    have m_positive := m_pos
    rw [pos_def,hc] at m_pos
    have want := And.intro p_pos m_pos
    apply pos_mul_pos at want
    rw [← pos_def] at want
    have impossible1 : c ∈ S := by
      tauto
    apply m_min at impossible1
    have impossible2 : c ∣ m := by
      rw [dvd_def]
      use p
      rw [mul_comm]
      assumption
    have finale := And.intro want m_positive
    apply dvd_le at impossible2
    apply impossible2 at m_positive
    have impossible := And.intro impossible1 m_positive
    apply le_ge at impossible
    rw [impossible] at hc
    nth_rewrite 1 [← mul_one c] at hc
    rw [mul_comm p] at hc
    have actual_finale := And.intro want hc
    apply left_mul_cancel at actual_finale
    rw [← actual_finale] at p_is_prime
    rw [Prime] at p_is_prime
    rcases p_is_prime with ⟨ cooked,_⟩
    rw [lt_def,add_neg_self] at cooked
    apply non_trivial at cooked
    assumption
  rcases c_factorization with ⟨l, ⟨l_prime, l_prod⟩⟩
  use ( p :: l )
  constructor
  rw [prime_list]
  intro s hs
  rcases hs with s1 | ⟨ s2 , mem ⟩
  assumption
  apply l_prime at mem
  assumption
  rw [list_product, l_prod]
  symm
  assumption
  push_neg at want
  have h : a ∉ S := by
    intro f
    rw [want] at f
    exact f
  have finale : ∃ l, prime_list l ∧ list_product l = a := by
    by_contra f
    have f1 : a ∈ S := by
      constructor
      repeat assumption
    tauto
  exact finale

--towards uniqueness

lemma one_pos : (1:Z) ∈ Zplus := by
  rw [pos_def]
  exact one_is_positive

theorem prime_dvd_mul : ∀ p a b : Z, Prime p → p ∣ a * b → p ∣ a ∨ p ∣ b := by
  intro p a b p_prime p_dvd_ab
  by_cases p_dvd_a : p ∣ a
  tauto
  set g:= gcd p a
  have g_dvd_p : g ∣ p := by
    apply gcd_dvd_left
  have g_dvd_a : g ∣ a := by
    apply gcd_dvd_right
  rw [dvd_def] at g_dvd_p
  have gcd_pa : g = 1 := by
    rw [Prime] at p_prime
    rcases g_dvd_p with ⟨ c, p_gc⟩
    rcases p_prime with ⟨ p_gt_one, irred⟩
    have g_pos : 0 < g := by
      apply gcd_pos
    have c_pos : 0 < c := by
      have p_pos : 0 < p := by
        have one_pos : (0:Z) < 1 := one_is_positive
        have want := And.intro one_pos p_gt_one
        apply lt_trans at want
        assumption
      rw [p_gc] at p_pos
      have want := And.intro g_pos p_pos
      apply pos_mul_pos at want
      assumption
    rw [← pos_def] at g_pos c_pos
    apply irred g at c_pos
    have p_eq_gc := p_gc
    apply c_pos at p_gc
    rcases p_gc with g_one | c_one
    assumption
    exfalso
    rw [c_one,mul_one] at p_eq_gc
    rw [p_eq_gc] at p_dvd_a
    repeat tauto
  apply fundamental_lemma p a b at gcd_pa
  tauto
  left
  rw [Prime] at p_prime
  rcases p_prime with ⟨ pos ⟩
  by_contra this
  rw [this] at pos
  have that : (0:Z) < 1 := by
    rw [lt_def,add_neg_zero]
    exact one_pos
  have impossible := And.intro pos that
  apply lt_trans at impossible
  rw [lt_def,add_neg_self] at impossible
  apply non_trivial at impossible
  repeat assumption


lemma prime_dvd_prime : ∀ p q : Z, Prime p → Prime q → p ∣ q → p = q := by
  intro p q p_prime q_prime p_dvd_q
  rw [dvd_def] at p_dvd_q
  rcases p_dvd_q with ⟨ c, q_pc ⟩
  have q_eq_pc := q_pc
  rw [Prime] at q_prime p_prime
  rcases q_prime with ⟨ one_lt_q, q_irred ⟩
  rcases p_prime with ⟨ one_lt_p, p_irred ⟩
  have p_pos : 0 < p := by
    have one_pos : (0:Z) < 1 := one_is_positive
    have want := And.intro one_pos one_lt_p
    apply lt_trans at want
    assumption
  have q_pos : 0 < q := by
    have one_pos : (0:Z) < 1 := one_is_positive
    have want := And.intro one_pos one_lt_q
    apply lt_trans at want
    assumption
  have c_pos : 0 < c := by
    rw [q_pc] at q_pos
    have want:= And.intro p_pos q_pos
    apply pos_mul_pos at want
    assumption
  rw [← pos_def] at p_pos q_pos c_pos
  apply q_irred p c at p_pos
  apply p_pos at c_pos
  apply c_pos at q_pc
  rcases q_pc with p_one | c_one
  rw [p_one,lt_def,add_neg_self] at one_lt_p
  apply non_trivial at one_lt_p
  tauto
  rw [c_one,mul_one] at q_eq_pc
  tauto

lemma prime_factor_of_prime_dvd_product : ∀ p : Z, ∀ S : List Z, Prime p → prime_list S → p ∣ list_product S → ∃ q ∈ S, p = q := by
  intro p S p_prime S_prime p_dvd_prod_S
  induction' S with q tail htail
  --base case
  exfalso
  rw [list_product] at p_dvd_prod_S
  have p_le_one : p ≤ 1 := by
    apply dvd_le
    exact p_dvd_prod_S
    exact one_pos
  rcases p_prime with ⟨ p1, p2 ⟩
  rw [le_def] at p_le_one
  have trich_p := lt_trichotomy 1 p
  tauto
  --inductive step
  rw [list_product] at p_dvd_prod_S
  have p_dvd_q_or_tail : p ∣ q ∨ p ∣ list_product tail := by
    apply prime_dvd_mul p q (list_product tail) at p_prime
    apply p_prime at p_dvd_prod_S
    exact p_dvd_prod_S
  rcases p_dvd_q_or_tail with p_dvd_q | p_dvd_tail
  have q_prime : Prime q := by
    rw [prime_list] at S_prime
    apply S_prime q
    tauto
  have p_eq_q : p = q := by
    apply prime_dvd_prime
    repeat assumption
  use p
  rw [p_eq_q]
  tauto
  have prime_tail : prime_list tail := by
    rw [prime_list] at S_prime
    rw [prime_list]
    intro s s_tail
    apply S_prime s
    tauto
  apply htail prime_tail at p_dvd_tail
  rcases p_dvd_tail with ⟨ q', q'_eq_p ⟩
  use q'
  tauto

lemma prime_tail_of_prime_list : ∀ a : Z, ∀ S : List Z, prime_list (a::S) → prime_list S := by
  intro a S h
  tauto

lemma prime_list_remove_prime : ∀ L : List Z, ∀ l : Z, prime_list L → l ∈ L →
  ∃ S : List Z, prime_list S ∧ list_product L = list_product (l :: S) := by
  intro L l L_prime l_in_L
  induction' L with d tail h
  exfalso
  tauto
  have tail_prime : prime_list tail := by
    exact prime_tail_of_prime_list d tail L_prime
  rcases l_in_L with l_eq_d | ⟨ _, l_in_tail ⟩ --what is the first argument doing???
  use tail
  apply h tail_prime at l_in_tail
  rcases l_in_tail with ⟨ ans, ans_prop ⟩
  use (d :: ans)
  constructor
  rw [prime_list]
  intro s hs
  rcases hs with s_eq_d | ⟨ _, s_in_ans ⟩
  tauto
  tauto
  rcases ans_prop with ⟨ _, tail_eq_l_ans ⟩
  rw [list_product,list_product,list_product,tail_eq_l_ans,
  ← mul_assoc,mul_comm l d, mul_assoc, ← list_product, ← list_product, ← list_product]

lemma prime_factor_of_prime_dvd_prod : ∀ p : Z, ∀ S : List Z, Prime p → prime_list S →
  p ∣ list_product S → ∃ q ∈ S, p = q := by
  intro p S p_prime S_prime p_dvd_prod_S
  induction' S with q tail htail
  --base case
  exfalso
  rw [list_product] at p_dvd_prod_S
  have p_le_one : p ≤ 1 := by
    apply dvd_le
    exact p_dvd_prod_S
    exact one_pos
  rcases p_prime with ⟨ p1, p2 ⟩
  rw [le_def] at p_le_one
  have trich_p := lt_trichotomy 1 p
  tauto
  --inductive step
  rw [list_product] at p_dvd_prod_S
  have p_dvd_q_or_tail : p ∣ q ∨ p ∣ list_product tail := by
    apply prime_dvd_mul p q (list_product tail) at p_prime
    apply p_prime at p_dvd_prod_S
    exact p_dvd_prod_S
  rcases p_dvd_q_or_tail with p_dvd_q | p_dvd_tail
  have q_prime : Prime q := by
    rw [prime_list] at S_prime
    apply S_prime q
    tauto
  have p_eq_q : p = q := by
    apply prime_dvd_prime
    repeat assumption
  use p
  rw [p_eq_q]
  tauto
  have prime_tail : prime_list tail := by
    rw [prime_list] at S_prime
    rw [prime_list]
    intro s s_tail
    apply S_prime s
    tauto
  apply htail prime_tail at p_dvd_tail
  rcases p_dvd_tail with ⟨ q', q'_eq_p ⟩
  use q'
  tauto

lemma not_head_in_tail : ∀ L : List Z, ∀ l s : Z, s ∈ ( l :: L) → s ≠ l → s ∈ L := by
  intro L l s h1 h2
  by_contra! this
  rcases h1 with A | B
  repeat tauto

lemma prime_list_head : ∀ L : List Z, ∀ l : Z, prime_list L → l ∈ L → ∃ S : List Z, prime_list S ∧ L ~ (l :: S) := by
  intro L l L_prime l_in_L
  induction' L with d tail h
  tauto
  have tail_prime : prime_list tail := by
    exact prime_tail_of_prime_list d tail L_prime
  rcases l_in_L with l_eq_d | ⟨ wtf, l_in_tail ⟩
  use tail
  apply h tail_prime at l_in_tail
  rcases l_in_tail with ⟨ ans, ans_prop ⟩
  use (d :: ans)
  constructor
  have d_prime : Prime d := by
    tauto
  rcases ans_prop with ⟨ ans_prime, tla ⟩
  rw [prime_list]
  intro s h
  by_cases sd : s = d
  rw [← sd] at d_prime
  assumption
  push_neg at sd
  apply not_head_in_tail at h
  apply h at sd
  tauto
  rcases ans_prop with ⟨ _,tla ⟩
  apply Perm.append_left [d] at tla
  have lda : [d] ++ l :: ans ~ [l] ++ [d] ++ ans := perm_middle
  exact .trans tla lda


lemma prod_primelist_one : ∀ P : List Z, prime_list P → list_product P = 1 → P = [] := by
  intro P P_prime prod_one
  induction' P with p tail htail
  tauto
  exfalso
  rw [list_product] at prod_one
  have p_dvd_one : p ∣ 1 := by
    rw [dvd_def]
    use list_product tail
    tauto
  have p_in_P : p ∈ (p :: tail) := by
    tauto
  have p_prime : Prime p := by
    tauto
  apply dvd_le at p_dvd_one
  have one_plus : (1:Z) ∈ Zplus := by
    rw [pos_def]
    exact one_is_positive
  apply p_dvd_one at one_plus
  rw [Prime] at p_prime
  rcases p_prime with ⟨ want,_⟩
  rw [le_def] at one_plus
  rcases one_plus with imp1 | imp2
  rw [imp1,lt_def,add_neg_self] at want
  apply non_trivial at want
  assumption
  have one_lt_p_lt_one := And.intro want imp2
  apply lt_trans at one_lt_p_lt_one
  rw [lt_def,add_neg_self] at one_lt_p_lt_one
  apply non_trivial at one_lt_p_lt_one
  assumption

lemma perm_tails {ptail Q qtail : List Z} {p : Z} (h1: Q ~ (p :: qtail) ) (h2: ptail ~ qtail) : Q ~ (p :: ptail) := by
  induction h2
  tauto
  case cons q L M LM _ =>
    have want : Q ~ ([p,q] ++ L) := by
      apply Perm.append_left [p,q] at LM
      symm
      symm at h1
      exact Perm.trans LM h1
    tauto
  case trans L M N LM MN R1 R2 =>
    have pNM: p :: N ~ p :: M := by
      apply Perm.append_left [p] at MN
      tauto
    have pML: p :: M ~ p :: L := by
      apply Perm.append_left [p] at LM
      tauto
    have QpM : Q ~ p :: M := Perm.trans h1 pNM
    exact Perm.trans QpM pML
  case swap q r L =>
    have qrL : [q] ++ r :: L ~ r :: q :: L := perm_middle
    have pqrL : [p] ++ [q] ++ r :: L ~ [p] ++ r :: q :: L := by
      apply Perm.append_left [p] at qrL
      tauto
    exact Perm.trans h1 pqrL

lemma perm_list_product {P Q : List Z} (h : P ~ Q) : list_product P = list_product Q := by
  induction h with
  | nil =>
    tauto
  | cons x a a_ih =>
    repeat rw [list_product]
    tauto
  | swap x y l =>
    repeat rw [list_product]
    rw [← mul_assoc,mul_comm y,mul_assoc]
  | trans eq1 eq2 a_ih1 a_ih2 =>
    rw [a_ih1,a_ih2]

lemma prime_pos : ∀ p : Z, Prime p → p ∈ Zplus := by
  intro a h
  rw [Prime] at h
  rcases h with ⟨ pos, _⟩
  have one_plus : (1:Z) ∈ Zplus := one_pos
  rw [pos_def] at one_plus
  have want := And.intro one_plus pos
  apply lt_trans at want
  rw [pos_def]
  assumption

theorem prime_factorization_unique : ∀ P Q : List Z, prime_list P → prime_list Q → list_product P = list_product Q → P ~ Q := by
  intro P Q P_prime Q_prime ep
  induction' P with p ptail htail generalizing Q
  --base case
  rw [list_product] at ep
  symm at ep
  apply prod_primelist_one at ep
  rw [ep]
  assumption
  --inductive step
  rw [list_product] at ep
  have p_dvd_Q : p ∣ list_product Q := by
    symm at ep
    rw [dvd_def]
    use list_product ptail
  apply prime_factor_of_prime_dvd_product at p_dvd_Q
  have p_in_Q : p ∈ Q := by
    rcases p_dvd_Q with ⟨ q, ⟨ q_in_Q, qp ⟩ ⟩
    rw [← qp] at q_in_Q
    assumption
  apply prime_list_head at p_in_Q
  rcases p_in_Q with ⟨ qtail, ⟨ qtail_prime, eq⟩ ⟩
  have teq : list_product ptail = list_product qtail := by
    apply perm_list_product at eq
    rw [list_product,← ep] at eq
    have p_prime : Prime p := by
      have p_in_P : p ∈ (p :: ptail) := by
        tauto
      apply P_prime at p_in_P
      assumption
    have p_pos : p ∈ Zplus := by
      apply prime_pos at p_prime
      assumption
    have want := And.intro p_pos eq
    apply left_mul_cancel at want
    assumption
  have pqtail : ptail ~ qtail := by
    apply htail at teq
    repeat tauto
  symm
  exact perm_tails eq pqtail
  repeat tauto
