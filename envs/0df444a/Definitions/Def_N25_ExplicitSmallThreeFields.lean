-- Prove2me | Definitions.Def_N25_ExplicitSmallThreeFields
-- name    : N25_ExplicitSmallThreeFields
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:49.332831+00:00
-- url     : https://prove2.me/theorems/407725b0-991e-4988-8367-7d1bb4ca9fd4
-- title:
--   Certified field structures on the $9$- and $27$-element tables
-- statement:
--   The file equips the executable polynomial-basis carriers for $𝔽_9$ and $𝔽_{27}$ with genuine characteristic-three field structures. Their ring laws are reduced to symbolic coordinate identities, while only the terminal inverse laws are checked over the $8$ and $26$ nonzero elements; the file also identifies each table operation with the resulting field operation. This supplies the semantic fields needed for the small characteristic-three point counts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitF81Field
/-!
# The small executable ternary extensions as actual fields

The characteristic-three point counts over `F3`, `F9`, and `F27` were
originally phrased using polynomial-basis operation tables.  This file equips
those same types with genuine field structures and proves that the table
operations are their field operations.

The proof is structural.  All additive, multiplicative, associative, and
distributive laws reduce to polynomial identities over the already certified
prime field `Trit`.  Finite computation is used only for the terminal inverse
laws on the 8 and 26 nonzero elements of the two extension fields.
-/

namespace MazurProof.RationalPointsN25QuotientWeilThree

/-! ## The quadratic extension `F9` -/

/-- Recursive exponentiation in the quadratic table before its field
structure is assembled. -/
private def f9TablePow (a : F9) : ℕ → F9
  | 0 => f9Operations.one
  | n + 1 => f9Mul (f9TablePow a n) a

private instance f9AddInst : Add F9 := ⟨f9Add⟩
private instance f9MulInst : Mul F9 := ⟨f9Mul⟩
private instance f9NegInst : Neg F9 := ⟨f9Neg⟩
private instance f9InvInst : Inv F9 := ⟨fun a => f9TablePow a 7⟩
private instance f9ZeroInst : Zero F9 := ⟨f9Operations.zero⟩
private instance f9OneInst : One F9 := ⟨f9Operations.one⟩

/-! The quadratic ring laws are coordinatewise consequences of
`u²=u+1`.  After translating trit operations to field operations, `ring`
checks the polynomial identities without inspecting extension elements. -/

/-- Quadratic-table addition is associative. -/
private theorem F9.add_assoc (a b c : F9) : a + b + c = a + (b + c) := by
  change f9Add (f9Add a b) c = f9Add a (f9Add b c)
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  rcases c with ⟨c0, c1⟩
  simp [f9Add, _root_.add_assoc]

/-- The declared quadratic zero is a left additive identity. -/
private theorem F9.zero_add (a : F9) : 0 + a = a := by
  change f9Add f9Operations.zero a = a
  rcases a with ⟨a0, a1⟩
  simp [f9Add, f9Operations]

/-- The declared quadratic negation cancels under addition. -/
private theorem F9.neg_add_cancel (a : F9) : -a + a = 0 := by
  change f9Add (f9Neg a) a = f9Operations.zero
  rcases a with ⟨a0, a1⟩
  simp [f9Add, f9Neg, f9Operations]

/-- Reduced quadratic multiplication is commutative. -/
private theorem F9.mul_comm (a b : F9) : a * b = b * a := by
  change f9Mul a b = f9Mul b a
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  simp only [f9Mul, F9.mk.injEq, tritAdd_eq_add, tritMul_eq_mul]
  constructor <;> ring

/-- The declared quadratic one is a left multiplicative identity. -/
private theorem F9.one_mul (a : F9) : 1 * a = a := by
  change f9Mul f9Operations.one a = a
  rcases a with ⟨a0, a1⟩
  simp [f9Mul, f9Operations]

/-- Reduced quadratic multiplication distributes over addition. -/
private theorem F9.left_distrib (a b c : F9) : a * (b + c) = a * b + a * c := by
  change f9Mul a (f9Add b c) = f9Add (f9Mul a b) (f9Mul a c)
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  rcases c with ⟨c0, c1⟩
  simp only [f9Add, f9Mul, F9.mk.injEq, tritAdd_eq_add, tritMul_eq_mul]
  constructor <;> ring

/-- Reduced quadratic multiplication is associative. -/
private theorem F9.mul_assoc (a b c : F9) : a * b * c = a * (b * c) := by
  change f9Mul (f9Mul a b) c = f9Mul a (f9Mul b c)
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  rcases c with ⟨c0, c1⟩
  simp only [f9Mul, F9.mk.injEq, tritAdd_eq_add, tritMul_eq_mul]
  constructor <;> ring

/-- The terminal eight-element certificate verifies the prescribed
seventh-power inverse on every nonzero quadratic element. -/
private theorem F9.mul_inv_cancel : ∀ a : F9, a ≠ 0 → a * a⁻¹ = 1 := by

    decide +kernel

/-- The prescribed quadratic inverse sends zero to zero. -/
private theorem F9.inv_zero : (0 : F9)⁻¹ = 0 := by

    decide +kernel

/-- The quadratic table is nontrivial. -/
private theorem F9.exists_pair_ne : ∃ x y : F9, x ≠ y := by
  exact ⟨0, 1, by decide⟩

/-- The actual field structure on the executable quadratic table. -/
instance f9Field : Field F9 :=
  Field.ofMinimalAxioms F9 F9.add_assoc F9.zero_add F9.neg_add_cancel
    F9.mul_assoc F9.mul_comm F9.one_mul F9.mul_inv_cancel F9.inv_zero
    F9.left_distrib F9.exists_pair_ne

/-- The quadratic field has characteristic three. -/
instance f9CharP : CharP F9 3 :=
  charP_of_card_eq_prime_pow (by decide : Fintype.card F9 = 3 ^ 2)

/-- The quadratic table zero is the field zero. -/
theorem f9Operations_zero_eq : f9Operations.zero = (0 : F9) := rfl

/-- The quadratic table one is the field one. -/
theorem f9Operations_one_eq : f9Operations.one = (1 : F9) := rfl

/-- Quadratic table addition is field addition. -/
theorem f9Operations_add_eq (a b : F9) : f9Operations.add a b = a + b := rfl

/-- Quadratic table negation is field negation. -/
theorem f9Operations_neg_eq (a : F9) : f9Operations.neg a = -a := rfl

/-- Quadratic table multiplication is field multiplication. -/
theorem f9Operations_mul_eq (a b : F9) : f9Operations.mul a b = a * b := rfl

/-! ## The cubic extension `F27` -/

/-- Recursive exponentiation in the cubic table before its field structure
is assembled. -/
private def f27TablePow (a : F27) : ℕ → F27
  | 0 => f27Operations.one
  | n + 1 => f27Mul (f27TablePow a n) a

private instance f27AddInst : Add F27 := ⟨f27Add⟩
private instance f27MulInst : Mul F27 := ⟨f27Mul⟩
private instance f27NegInst : Neg F27 := ⟨f27Neg⟩
private instance f27InvInst : Inv F27 := ⟨fun a => f27TablePow a 25⟩
private instance f27ZeroInst : Zero F27 := ⟨f27Operations.zero⟩
private instance f27OneInst : One F27 := ⟨f27Operations.one⟩

/-! The cubic ring laws are coordinatewise consequences of
`v³=v+2` and `v⁴=v²+2v`.  As in the quadratic case, all non-inverse laws
are symbolic polynomial identities over the certified prime field. -/

/-- Cubic-table addition is associative. -/
private theorem F27.add_assoc (a b c : F27) : a + b + c = a + (b + c) := by
  change f27Add (f27Add a b) c = f27Add a (f27Add b c)
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  rcases c with ⟨c0, c1, c2⟩
  simp [f27Add, _root_.add_assoc]

/-- The declared cubic zero is a left additive identity. -/
private theorem F27.zero_add (a : F27) : 0 + a = a := by
  change f27Add f27Operations.zero a = a
  rcases a with ⟨a0, a1, a2⟩
  simp [f27Add, f27Operations]

/-- The declared cubic negation cancels under addition. -/
private theorem F27.neg_add_cancel (a : F27) : -a + a = 0 := by
  change f27Add (f27Neg a) a = f27Operations.zero
  rcases a with ⟨a0, a1, a2⟩
  simp [f27Add, f27Neg, f27Operations]

/-- Reduced cubic multiplication is commutative. -/
private theorem F27.mul_comm (a b : F27) : a * b = b * a := by
  change f27Mul a b = f27Mul b a
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  simp only [f27Mul, tritDouble, F27.mk.injEq, tritAdd_eq_add,
    tritMul_eq_mul]
  constructor
  · ring
  constructor <;> ring

/-- The declared cubic one is a left multiplicative identity. -/
private theorem F27.one_mul (a : F27) : 1 * a = a := by
  change f27Mul f27Operations.one a = a
  rcases a with ⟨a0, a1, a2⟩
  simp [f27Mul, f27Operations, tritDouble]

/-- Reduced cubic multiplication distributes over addition. -/
private theorem F27.left_distrib (a b c : F27) :
    a * (b + c) = a * b + a * c := by
  change f27Mul a (f27Add b c) = f27Add (f27Mul a b) (f27Mul a c)
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  rcases c with ⟨c0, c1, c2⟩
  simp only [f27Add, f27Mul, tritDouble, F27.mk.injEq,
    tritAdd_eq_add, tritMul_eq_mul]
  constructor
  · ring
  constructor <;> ring

/-- Reduced cubic multiplication is associative. -/
private theorem F27.mul_assoc (a b c : F27) : a * b * c = a * (b * c) := by
  change f27Mul (f27Mul a b) c = f27Mul a (f27Mul b c)
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  rcases c with ⟨c0, c1, c2⟩
  simp only [f27Mul, tritDouble, F27.mk.injEq, tritAdd_eq_add,
    tritMul_eq_mul]
  constructor
  · ring
  constructor <;> ring

/-- The terminal twenty-six-element certificate verifies the prescribed
twenty-fifth-power inverse on every nonzero cubic element. -/
private theorem F27.mul_inv_cancel : ∀ a : F27, a ≠ 0 → a * a⁻¹ = 1 := by

    decide +kernel

/-- The prescribed cubic inverse sends zero to zero. -/
private theorem F27.inv_zero : (0 : F27)⁻¹ = 0 := by

    decide +kernel

/-- The cubic table is nontrivial. -/
private theorem F27.exists_pair_ne : ∃ x y : F27, x ≠ y := by
  exact ⟨0, 1, by decide⟩

/-- The actual field structure on the executable cubic table. -/
instance f27Field : Field F27 :=
  Field.ofMinimalAxioms F27 F27.add_assoc F27.zero_add F27.neg_add_cancel
    F27.mul_assoc F27.mul_comm F27.one_mul F27.mul_inv_cancel F27.inv_zero
    F27.left_distrib F27.exists_pair_ne

/-- The cubic field has characteristic three. -/
instance f27CharP : CharP F27 3 :=
  charP_of_card_eq_prime_pow (by decide : Fintype.card F27 = 3 ^ 3)

/-- The cubic table zero is the field zero. -/
theorem f27Operations_zero_eq : f27Operations.zero = (0 : F27) := rfl

/-- The cubic table one is the field one. -/
theorem f27Operations_one_eq : f27Operations.one = (1 : F27) := rfl

/-- Cubic table addition is field addition. -/
theorem f27Operations_add_eq (a b : F27) :
    f27Operations.add a b = a + b := rfl

/-- Cubic table negation is field negation. -/
theorem f27Operations_neg_eq (a : F27) : f27Operations.neg a = -a := rfl

/-- Cubic table multiplication is field multiplication. -/
theorem f27Operations_mul_eq (a b : F27) :
    f27Operations.mul a b = a * b := rfl

end MazurProof.RationalPointsN25QuotientWeilThree


