-- Prove2me | Definitions.Def_EinsteinN_algebra
-- name    : EinsteinN_algebra
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T23:53:50.784378+00:00
-- url     : https://prove2.me/theorems/89094b4b-8c19-4a2c-aeef-2560520e4da0
-- title:
--   Algebraic hierarchy (Semiring to OrderedField)
-- statement:
--   The algebraic hierarchy used by the development: semirings, rings, commutative rings, integral domains, fields and ordered fields, with their basic cancellation and sign lemmas. Transcribed from the source project's algebra layer.
-- source:
--   https://github.com/TataSatyaPratheek/mathematical-physics-lean/blob/main/MathPhysics/Algebra/Ring.lean ; MathPhysics/Algebra/OrderedField.lean

namespace EinsteinN
universe u
class Semiring (α : Type u) where
  add : α → α → α
  add_assoc : ∀ (a b c : α), add (add a b) c = add a (add b c)
  zero : α
  zero_add : ∀ (a : α), add zero a = a
  add_zero : ∀ (a : α), add a zero = a
  add_comm : ∀ (a b : α), add a b = add b a
  mul : α → α → α
  mul_assoc : ∀ (a b c : α), mul (mul a b) c = mul a (mul b c)
  one : α
  one_mul : ∀ (a : α), mul one a = a
  mul_one : ∀ (a : α), mul a one = a
  left_distrib : ∀ (a b c : α), mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ (a b c : α), mul (add a b) c = add (mul a c) (mul b c)
  zero_mul : ∀ (a : α), mul zero a = zero
  mul_zero : ∀ (a : α), mul a zero = zero
class Ring (α : Type u) extends Semiring α where
  neg : α → α
  add_left_neg : ∀ (a : α), add (neg a) a = zero
namespace Ring
variable {R : Type u} [Ring R]
theorem add_right_neg (a : R) : Semiring.add a (Ring.neg a) = Semiring.zero := by
  rw [Semiring.add_comm, add_left_neg]
theorem add_left_cancel (x y z : R) (h : Semiring.add x y = Semiring.add x z) : y = z := by
  have h1 : Semiring.add (Ring.neg x) (Semiring.add x y) = Semiring.add (Ring.neg x) (Semiring.add x z) := by rw [h]
  rw [← Semiring.add_assoc, add_left_neg, Semiring.zero_add] at h1
  rw [← Semiring.add_assoc, add_left_neg, Semiring.zero_add] at h1
  exact h1
theorem add_right_cancel (x y z : R) (h : Semiring.add y x = Semiring.add z x) : y = z := by
  apply add_left_cancel x
  rw [Semiring.add_comm x y, Semiring.add_comm x z]
  exact h
theorem neg_neg (a : R) : Ring.neg (Ring.neg a) = a := by
  apply add_left_cancel (Ring.neg a)
  rw [add_left_neg, Semiring.add_comm, add_left_neg]
theorem neg_zero : Ring.neg (Semiring.zero : R) = Semiring.zero := by
  calc Ring.neg (Semiring.zero : R) = Semiring.add (Ring.neg (Semiring.zero : R)) Semiring.zero := by rw [Semiring.add_zero]
    _ = Semiring.zero := by rw [add_left_neg]
theorem neg_mul (a b : R) : Semiring.mul (Ring.neg a) b = Ring.neg (Semiring.mul a b) := by
  apply add_right_cancel (Semiring.mul a b)
  rw [add_left_neg, ← Semiring.right_distrib, add_left_neg, Semiring.zero_mul]
theorem mul_neg (a b : R) : Semiring.mul a (Ring.neg b) = Ring.neg (Semiring.mul a b) := by
  apply add_right_cancel (Semiring.mul a b)
  rw [add_left_neg, ← Semiring.left_distrib, add_left_neg, Semiring.mul_zero]
theorem neg_add (a b : R) : Ring.neg (Semiring.add a b) = Semiring.add (Ring.neg b) (Ring.neg a) := by
  apply add_left_cancel (Semiring.add a b)
  rw [add_right_neg]
  rw [Semiring.add_assoc, ← Semiring.add_assoc b (Ring.neg b) (Ring.neg a)]
  rw [add_right_neg, Semiring.zero_add, add_right_neg]
theorem unique_neg (a b : R) (h : Semiring.add a b = Semiring.zero) : b = Ring.neg a := by
  apply add_left_cancel a
  rw [h, add_right_neg]
def sub (a b : R) : R := Semiring.add a (Ring.neg b)
theorem neg_mul_neg (a b : R) : Semiring.mul (Ring.neg a) (Ring.neg b) = Semiring.mul a b := by
  rw [neg_mul, mul_neg, neg_neg]
theorem mul_sub (a b c : R) : Semiring.mul a (sub b c) = sub (Semiring.mul a b) (Semiring.mul a c) := by
  show Semiring.mul a (Semiring.add b (Ring.neg c)) = Semiring.add (Semiring.mul a b) (Ring.neg (Semiring.mul a c))
  rw [Semiring.left_distrib, mul_neg]
theorem sub_mul (a b c : R) : Semiring.mul (sub a b) c = sub (Semiring.mul a c) (Semiring.mul b c) := by
  show Semiring.mul (Semiring.add a (Ring.neg b)) c = Semiring.add (Semiring.mul a c) (Ring.neg (Semiring.mul b c))
  rw [Semiring.right_distrib, neg_mul]
theorem neg_add_cancel_left (a b : R) : Semiring.add (Ring.neg a) (Semiring.add a b) = b := by
  rw [← Semiring.add_assoc, add_left_neg, Semiring.zero_add]
theorem add_neg_cancel_right (a b : R) : Semiring.add (Semiring.add a b) (Ring.neg b) = a := by
  rw [Semiring.add_assoc, add_right_neg, Semiring.add_zero]
theorem neg_sub (a b : R) : Ring.neg (sub a b) = sub b a := by
  show Ring.neg (Semiring.add a (Ring.neg b)) = Semiring.add b (Ring.neg a)
  rw [neg_add, neg_neg]
end Ring
class CommutativeRing (α : Type u) extends Ring α where
  mul_comm : ∀ (a b : α), mul a b = mul b a
namespace CommutativeRing
variable {R : Type u} [CommutativeRing R]
theorem mul_left_comm (a b c : R) : Semiring.mul a (Semiring.mul b c) = Semiring.mul b (Semiring.mul a c) := by
  rw [← Semiring.mul_assoc, ← Semiring.mul_assoc, mul_comm a b]
theorem mul_right_comm (a b c : R) : Semiring.mul (Semiring.mul a b) c = Semiring.mul (Semiring.mul a c) b := by
  rw [Semiring.mul_assoc, mul_comm b c, ← Semiring.mul_assoc]
end CommutativeRing
class IntegralDomain (α : Type u) extends CommutativeRing α where
  no_zero_divisors : ∀ (a b : α), mul a b = zero → a = zero ∨ b = zero
  one_ne_zero : ¬(one = zero)
class Field (α : Type u) extends IntegralDomain α where
  field_inv : α → α
  mul_inv_cancel : ∀ (a : α), ¬(a = zero) → mul a (field_inv a) = one
namespace Field
variable {F : Type u} [Field F]
theorem inv_mul_cancel (a : F) (ha : ¬(a = Semiring.zero)) : Semiring.mul (Field.field_inv a) a = Semiring.one := by
  rw [CommutativeRing.mul_comm]; exact mul_inv_cancel a ha
theorem inv_inv (a : F) (ha : ¬(a = Semiring.zero)) : Field.field_inv (Field.field_inv a) = a := by
  have h_inv_ne_zero : ¬(Field.field_inv a = Semiring.zero) := by
    intro h; have := mul_inv_cancel a ha; rw [h, Semiring.mul_zero] at this
    exact IntegralDomain.one_ne_zero this.symm
  have h1 := mul_inv_cancel (Field.field_inv a) h_inv_ne_zero
  have h2 := inv_mul_cancel a ha
  have h3 : Semiring.mul (Field.field_inv a) (Semiring.add (Field.field_inv (Field.field_inv a)) (Ring.neg a)) = Semiring.zero := by
    rw [Semiring.left_distrib, Ring.mul_neg, h1, h2, Ring.add_right_neg]
  cases IntegralDomain.no_zero_divisors _ _ h3 with
  | inl h => exact absurd h h_inv_ne_zero
  | inr h =>
    have : Semiring.add (Field.field_inv (Field.field_inv a)) (Ring.neg a) = Semiring.add a (Ring.neg a) := by rw [h, Ring.add_right_neg]
    exact Ring.add_right_cancel _ _ _ this
def div (a b : F) : F := Semiring.mul a (Field.field_inv b)
theorem div_self (a : F) (ha : ¬(a = Semiring.zero)) : div a a = Semiring.one := mul_inv_cancel a ha
theorem one_div (a : F) : div Semiring.one a = Field.field_inv a := Semiring.one_mul (Field.field_inv a)
theorem div_one (a : F) : div a Semiring.one = a := by
  show Semiring.mul a (Field.field_inv Semiring.one) = a
  have h_inv_one : Field.field_inv (Semiring.one : F) = Semiring.one := by
    have h1 := mul_inv_cancel (Semiring.one : F) (fun h => IntegralDomain.one_ne_zero h)
    rw [Semiring.one_mul] at h1; exact h1
  rw [h_inv_one, Semiring.mul_one]
end Field
theorem IntegralDomain.nonzero_mul_nonzero {α : Type u} [IntegralDomain α] (a b : α) (ha : ¬(a = Semiring.zero)) (hb : ¬(b = Semiring.zero)) : ¬(Semiring.mul a b = Semiring.zero) := by
  intro h
  cases IntegralDomain.no_zero_divisors a b h with
  | inl h => exact ha h
  | inr h => exact hb h
theorem IntegralDomain.mul_left_cancel {α : Type u} [IntegralDomain α] (a b c : α) (ha : ¬(a = Semiring.zero)) (h : Semiring.mul a b = Semiring.mul a c) : b = c := by
  have : Semiring.mul a (Semiring.add b (Ring.neg c)) = Semiring.zero := by
    rw [Semiring.left_distrib, Ring.mul_neg, h, Ring.add_right_neg]
  cases IntegralDomain.no_zero_divisors a _ this with
  | inl h => exact absurd h ha
  | inr h => exact Ring.add_right_cancel (Ring.neg c) b c (by rw [h, Ring.add_right_neg])
class OrderedField (F : Type u) extends Field F where
  le : F → F → Prop
  le_refl : ∀ (a : F), le a a
  le_trans : ∀ (a b c : F), le a b → le b c → le a c
  le_antisymm : ∀ (a b : F), le a b → le b a → a = b
  le_total : ∀ (a b : F), le a b ∨ le b a
  add_le_add_left : ∀ (a b c : F), le a b → le (add c a) (add c b)
  mul_nonneg : ∀ (a b : F), le zero a → le zero b → le zero (mul a b)
namespace OrderedField
variable {F : Type u} [OrderedField F]
def lt (a b : F) : Prop := le a b ∧ ¬(a = b)
theorem add_le_add_right (a b c : F) (h : le a b) : le (Semiring.add a c) (Semiring.add b c) := by
  rw [Semiring.add_comm a c, Semiring.add_comm b c]
  exact add_le_add_left a b c h
theorem nonneg_or_nonpos (a : F) : le Semiring.zero a ∨ le a Semiring.zero := le_total Semiring.zero a
theorem neg_nonneg_of_nonpos (a : F) (h : le a Semiring.zero) : le Semiring.zero (Ring.neg a) := by
  have h1 := add_le_add_right a Semiring.zero (Ring.neg a) h
  rw [Ring.add_right_neg, Semiring.zero_add] at h1
  exact h1
theorem neg_nonpos_of_nonneg (a : F) (h : le Semiring.zero a) : le (Ring.neg a) Semiring.zero := by
  have h1 := add_le_add_right Semiring.zero a (Ring.neg a) h
  rw [Ring.add_right_neg, Semiring.zero_add] at h1
  exact h1
theorem neg_le_neg (a b : F) (h : le a b) : le (Ring.neg b) (Ring.neg a) := by
  have h1 := add_le_add_right a b (Ring.neg b) h
  rw [Ring.add_right_neg] at h1
  have h2 := add_le_add_right (Semiring.add a (Ring.neg b)) Semiring.zero (Ring.neg a) h1
  rw [Semiring.add_assoc, Semiring.add_comm (Ring.neg b) (Ring.neg a), ← Semiring.add_assoc, Ring.add_right_neg, Semiring.zero_add, Semiring.zero_add] at h2
  exact h2
theorem square_nonneg (a : F) : le Semiring.zero (Semiring.mul a a) := by
  cases nonneg_or_nonpos a with
  | inl h => exact mul_nonneg a a h h
  | inr h =>
    rw [← Ring.neg_mul_neg a a]
    exact mul_nonneg (Ring.neg a) (Ring.neg a) (neg_nonneg_of_nonpos a h) (neg_nonneg_of_nonpos a h)
theorem zero_le_one : le (Semiring.zero : F) (Semiring.one : F) := by
  have := square_nonneg (Semiring.one : F)
  rw [Semiring.one_mul] at this
  exact this
theorem one_pos : lt Semiring.zero (Semiring.one : F) := ⟨zero_le_one, fun h => IntegralDomain.one_ne_zero h.symm⟩
theorem inv_pos (a : F) (ha_ne : ¬(a = Semiring.zero)) (ha : le Semiring.zero a) : le Semiring.zero (Field.field_inv a) := by
  cases nonneg_or_nonpos (Field.field_inv a) with
  | inl h => exact h
  | inr h =>
    have h1 := neg_nonneg_of_nonpos _ h
    have h2 := mul_nonneg a (Ring.neg (Field.field_inv a)) ha h1
    rw [Ring.mul_neg, Field.mul_inv_cancel a ha_ne] at h2
    have h3 := neg_le_neg _ _ h2
    rw [Ring.neg_neg, Ring.neg_zero] at h3
    exact absurd (le_antisymm _ _ h3 zero_le_one) IntegralDomain.one_ne_zero
theorem add_nonneg (a b : F) (ha : le Semiring.zero a) (hb : le Semiring.zero b) : le Semiring.zero (Semiring.add a b) := by
  have h := add_le_add_right Semiring.zero a b ha
  rw [Semiring.zero_add] at h
  exact le_trans _ _ _ hb h
theorem mul_pos (a b : F) (ha : lt Semiring.zero a) (hb : lt Semiring.zero b) : lt Semiring.zero (Semiring.mul a b) := by
  constructor
  · exact mul_nonneg a b ha.1 hb.1
  · intro h
    cases IntegralDomain.no_zero_divisors a b h.symm with
    | inl h => exact ha.2 h.symm
    | inr h => exact hb.2 h.symm
theorem sq_pos (a : F) (ha : ¬(a = Semiring.zero)) : lt Semiring.zero (Semiring.mul a a) :=
  ⟨square_nonneg a, fun h => by
    cases IntegralDomain.no_zero_divisors a a h.symm with
    | inl h => exact ha h
    | inr h => exact ha h⟩
theorem lt_irrefl (a : F) : ¬lt a a := fun ⟨_, h⟩ => h rfl
theorem lt_trans (a b c : F) (hab : lt a b) (hbc : lt b c) : lt a c :=
  ⟨le_trans a b c hab.1 hbc.1, fun h => by rw [h] at hab; exact hbc.2 (le_antisymm _ _ hbc.1 hab.1)⟩
theorem pos_of_one_le (a : F) (h : le Semiring.one a) : lt Semiring.zero a :=
  ⟨le_trans _ _ _ zero_le_one h, fun h0 => by
    have h' : le Semiring.one (Semiring.zero : F) := by
      have := h; rw [← h0] at this; exact this
    exact IntegralDomain.one_ne_zero (le_antisymm _ _ h' zero_le_one)⟩
end OrderedField
end EinsteinN


