-- Prove2me | Definitions.Def_N25_ExplicitF81Field
-- name    : N25_ExplicitF81Field
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:45.242302+00:00
-- url     : https://prove2.me/theorems/0e23e791-5aad-4467-b8d1-847834c3d0a9
-- title:
--   A genuine field structure on the executable $81$-element table
-- statement:
--   The file constructs an auxiliary polynomial-basis field $$𝔽_3[q]/(q^4+2q^3+2),$$ proves its ring laws symbolically, and checks the prescribed $79$th-power inverse on the $80$ nonzero elements. It then gives a coordinatewise equivalence with the executable four-trit carrier and transports the field and characteristic-three structures to that carrier. This permits structural finite-field and Kummer theorems to be applied directly to the table used by the point-count computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Field.MinimalAxioms
import Definitions.Def_N25_ExplicitWeilThreeDefs
/-!
# The executable `F_81` table as an actual field

The level-25 point count originally used `F81` only as an executable table.
This file equips that same type with a genuine characteristic-three field
structure, so structural finite-field theorems can be applied to the table.

The construction deliberately separates algebra from computation.  Addition,
multiplication, associativity, and distributivity are transported through four
`ZMod 3` coordinates and proved by polynomial identities.  The only terminal
finite certificate checks that the prescribed inverse `a^79` works for the 80
nonzero elements.  Thus the field laws are not established by a cubic
enumeration of triples of elements.
-/

namespace MazurProof.RationalPointsN25QuotientWeilThree

/-! ## A polynomial-basis model over `ZMod 3` -/

/-- The prime field used by the auxiliary polynomial-basis model. -/
private abbrev F3Z := ZMod 3

/-- Four coefficients representing `c₀+c₁q+c₂q²+c₃q³`, with the relation
`q⁴=q³+1`.  This duplicates only the representation of `F81`; its purpose is
to inherit the established ring structure of `ZMod 3` in symbolic proofs. -/
private structure F81Z where
  c0 : F3Z
  c1 : F3Z
  c2 : F3Z
  c3 : F3Z
deriving DecidableEq, Fintype

/-- Coefficientwise addition in the auxiliary polynomial-basis model. -/
private def F81Z.add (a b : F81Z) : F81Z :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

/-- Coefficientwise additive inverse in the auxiliary model. -/
private def F81Z.neg (a : F81Z) : F81Z :=
  ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩

/-- Polynomial multiplication reduced by `q⁴=q³+1`, and hence by
`q⁵=q³+q+1` and `q⁶=q³+q²+q+1`. -/
private def F81Z.mul (a b : F81Z) : F81Z :=
  let c0 := a.c0 * b.c0
  let c1 := a.c0 * b.c1 + a.c1 * b.c0
  let c2 := (a.c0 * b.c2 + a.c1 * b.c1) + a.c2 * b.c0
  let c3 := ((a.c0 * b.c3 + a.c1 * b.c2) + a.c2 * b.c1) + a.c3 * b.c0
  let c4 := (a.c1 * b.c3 + a.c2 * b.c2) + a.c3 * b.c1
  let c5 := a.c2 * b.c3 + a.c3 * b.c2
  let c6 := a.c3 * b.c3
  ⟨((c0 + c4) + c5) + c6,
    (c1 + c5) + c6,
    c2 + c6,
    ((c3 + c4) + c5) + c6⟩

/-- Exponentiation before a `Pow` instance is available. -/
private def F81Z.pow (a : F81Z) : ℕ → F81Z
  | 0 => ⟨1, 0, 0, 0⟩
  | n + 1 => F81Z.mul (F81Z.pow a n) a

private instance f81ZAddInst : Add F81Z := ⟨F81Z.add⟩
private instance f81ZMulInst : Mul F81Z := ⟨F81Z.mul⟩
private instance f81ZNegInst : Neg F81Z := ⟨F81Z.neg⟩
private instance f81ZInvInst : Inv F81Z := ⟨fun a => F81Z.pow a 79⟩
private instance f81ZZeroInst : Zero F81Z := ⟨⟨0, 0, 0, 0⟩⟩
private instance f81ZOneInst : One F81Z := ⟨⟨1, 0, 0, 0⟩⟩

/-! The ring laws below are coordinatewise polynomial identities.  In
particular, associativity and distributivity use `ring`; they do not inspect
all tuples of field elements. -/

/-- Addition in the auxiliary model is associative. -/
private theorem F81Z.add_assoc (a b c : F81Z) : a + b + c = a + (b + c) := by
  change F81Z.add (F81Z.add a b) c = F81Z.add a (F81Z.add b c)
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  rcases c with ⟨c0, c1, c2, c3⟩
  simp [F81Z.add, _root_.add_assoc]

/-- The declared zero is a left additive identity. -/
private theorem F81Z.zero_add (a : F81Z) : 0 + a = a := by
  change F81Z.add ⟨0, 0, 0, 0⟩ a = a
  rcases a with ⟨a0, a1, a2, a3⟩
  simp [F81Z.add]

/-- The declared negation cancels under addition. -/
private theorem F81Z.neg_add_cancel (a : F81Z) : -a + a = 0 := by
  change F81Z.add (F81Z.neg a) a = ⟨0, 0, 0, 0⟩
  rcases a with ⟨a0, a1, a2, a3⟩
  simp [F81Z.neg, F81Z.add]

/-- Reduced polynomial multiplication is commutative. -/
private theorem F81Z.mul_comm (a b : F81Z) : a * b = b * a := by
  change F81Z.mul a b = F81Z.mul b a
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp only [F81Z.mul, F81Z.mk.injEq]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The declared one is a left multiplicative identity. -/
private theorem F81Z.one_mul (a : F81Z) : 1 * a = a := by
  change F81Z.mul ⟨1, 0, 0, 0⟩ a = a
  rcases a with ⟨a0, a1, a2, a3⟩
  simp [F81Z.mul]

/-- Reduced polynomial multiplication distributes over addition. -/
private theorem F81Z.left_distrib (a b c : F81Z) : a * (b + c) = a * b + a * c := by
  change F81Z.mul a (F81Z.add b c) = F81Z.add (F81Z.mul a b) (F81Z.mul a c)
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  rcases c with ⟨c0, c1, c2, c3⟩
  simp only [F81Z.add, F81Z.mul, F81Z.mk.injEq]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Reduced polynomial multiplication is associative. -/
private theorem F81Z.mul_assoc (a b c : F81Z) : a * b * c = a * (b * c) := by
  change F81Z.mul (F81Z.mul a b) c = F81Z.mul a (F81Z.mul b c)
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  rcases c with ⟨c0, c1, c2, c3⟩
  simp only [F81Z.mul, F81Z.mk.injEq]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The terminal 80-element certificate: every nonzero auxiliary element
multiplied by its prescribed `79`th-power inverse is one. -/
private theorem F81Z.mul_inv_cancel : ∀ a : F81Z, a ≠ 0 → a * a⁻¹ = 1 := by

    decide +kernel

/-- The prescribed power inverse sends zero to zero. -/
private theorem F81Z.inv_zero : (0 : F81Z)⁻¹ = 0 := by

    decide +kernel

/-- Zero and one witness that the auxiliary field is nontrivial. -/
private theorem F81Z.exists_pair_ne : ∃ x y : F81Z, x ≠ y := by
  exact ⟨0, 1, by decide⟩

/-- The field structure assembled from the symbolic ring laws and the small
inverse certificate. -/
private instance F81Z.field : Field F81Z :=
  Field.ofMinimalAxioms F81Z F81Z.add_assoc F81Z.zero_add
    F81Z.neg_add_cancel F81Z.mul_assoc F81Z.mul_comm F81Z.one_mul
    F81Z.mul_inv_cancel F81Z.inv_zero F81Z.left_distrib F81Z.exists_pair_ne

/-- The recursive auxiliary power agrees with the standard monoid power. -/
private theorem F81Z.pow_eq_pow (a : F81Z) : ∀ n : ℕ, F81Z.pow a n = a ^ n
  | 0 => rfl
  | n + 1 => by
      change F81Z.mul (F81Z.pow a n) a = a ^ (n + 1)
      rw [F81Z.pow_eq_pow]
      exact (pow_succ a n).symm

/-- Cardinality `3⁴` gives the auxiliary field characteristic three. -/
private instance F81Z.charP : CharP F81Z 3 :=
  charP_of_card_eq_prime_pow (by decide : Fintype.card F81Z = 3 ^ 4)

/-! ## Transport to the executable `Trit` table -/

/-- The canonical embedding of an executable trit into `ZMod 3`. -/
private def tritToF3Z : Trit → F3Z
  | .zero => 0
  | .one => 1
  | .two => 2

/-- The inverse map from the three residues to executable trits. -/
private def f3ZToTrit (a : F3Z) : Trit :=
  if a = 0 then .zero else if a = 1 then .one else .two

/-- The explicit bijection between the two models of the prime field. -/
private def tritEquivF3Z : Trit ≃ F3Z where
  toFun := tritToF3Z
  invFun := f3ZToTrit
  left_inv a := by cases a <;> decide
  right_inv := by decide +kernel

/-- Trit addition maps to addition in `ZMod 3`. -/
private theorem tritEquivF3Z_map_add (a b : Trit) :
    tritEquivF3Z (tritAdd a b) = tritEquivF3Z a + tritEquivF3Z b := by
  cases a <;> cases b <;> decide

/-- Trit negation maps to negation in `ZMod 3`. -/
private theorem tritEquivF3Z_map_neg (a : Trit) :
    tritEquivF3Z (tritNeg a) = -tritEquivF3Z a := by
  cases a <;> decide

/-- Trit multiplication maps to multiplication in `ZMod 3`. -/
private theorem tritEquivF3Z_map_mul (a b : Trit) :
    tritEquivF3Z (tritMul a b) = tritEquivF3Z a * tritEquivF3Z b := by
  cases a <;> cases b <;> decide

/-- Coordinatewise equivalence between the executable and auxiliary
polynomial-basis representations. -/
private def f81EquivF81Z : F81 ≃ F81Z where
  toFun a := ⟨tritEquivF3Z a.c0, tritEquivF3Z a.c1,
    tritEquivF3Z a.c2, tritEquivF3Z a.c3⟩
  invFun a := ⟨tritEquivF3Z.symm a.c0, tritEquivF3Z.symm a.c1,
    tritEquivF3Z.symm a.c2, tritEquivF3Z.symm a.c3⟩
  left_inv a := by
    rcases a with ⟨a0, a1, a2, a3⟩
    simp
  right_inv a := by
    rcases a with ⟨a0, a1, a2, a3⟩
    simp

/-- The table zero maps to the auxiliary zero. -/
private theorem f81EquivF81Z_map_zero :
    f81EquivF81Z f81Operations.zero = (0 : F81Z) := by
  rfl

/-- The table one maps to the auxiliary one. -/
private theorem f81EquivF81Z_map_one :
    f81EquivF81Z f81Operations.one = (1 : F81Z) := by
  rfl

/-- The coordinate equivalence respects table addition. -/
private theorem f81EquivF81Z_map_add (a b : F81) :
    f81EquivF81Z (f81Add a b) = f81EquivF81Z a + f81EquivF81Z b := by
  change f81EquivF81Z (f81Add a b) =
    F81Z.add (f81EquivF81Z a) (f81EquivF81Z b)
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp [f81EquivF81Z, f81Add, F81Z.add, tritEquivF3Z_map_add]

/-- The coordinate equivalence respects table negation. -/
private theorem f81EquivF81Z_map_neg (a : F81) :
    f81EquivF81Z (f81Neg a) = -f81EquivF81Z a := by
  change f81EquivF81Z (f81Neg a) = F81Z.neg (f81EquivF81Z a)
  rcases a with ⟨a0, a1, a2, a3⟩
  simp [f81EquivF81Z, f81Neg, F81Z.neg, tritEquivF3Z_map_neg]

/-- The coordinate equivalence respects reduced table multiplication. -/
private theorem f81EquivF81Z_map_mul (a b : F81) :
    f81EquivF81Z (f81Mul a b) = f81EquivF81Z a * f81EquivF81Z b := by
  change f81EquivF81Z (f81Mul a b) =
    F81Z.mul (f81EquivF81Z a) (f81EquivF81Z b)
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp [f81EquivF81Z, f81Mul, F81Z.mul,
    tritEquivF3Z_map_add, tritEquivF3Z_map_mul]

/-- The field structure on the executable `F81` type, transported from the
symbolic polynomial-basis model. -/
instance f81Field : Field F81 := f81EquivF81Z.field

/-- The executable zero is the zero of the transported field. -/
theorem f81Operations_zero_eq : f81Operations.zero = (0 : F81) := by
  apply f81EquivF81Z.injective
  calc
    f81EquivF81Z f81Operations.zero = (0 : F81Z) := f81EquivF81Z_map_zero
    _ = f81EquivF81Z (0 : F81) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_zero f81EquivF81Z.ringEquiv).symm

/-- The executable one is the one of the transported field. -/
theorem f81Operations_one_eq : f81Operations.one = (1 : F81) := by
  apply f81EquivF81Z.injective
  calc
    f81EquivF81Z f81Operations.one = (1 : F81Z) := f81EquivF81Z_map_one
    _ = f81EquivF81Z (1 : F81) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_one f81EquivF81Z.ringEquiv).symm

/-- Executable addition is the transported field addition. -/
theorem f81Operations_add_eq (a b : F81) :
    f81Operations.add a b = a + b := by
  change f81Add a b = a + b
  apply f81EquivF81Z.injective
  calc
    f81EquivF81Z (f81Add a b) = f81EquivF81Z a + f81EquivF81Z b :=
      f81EquivF81Z_map_add a b
    _ = f81EquivF81Z (a + b) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_add f81EquivF81Z.ringEquiv a b).symm

/-- Executable negation is the transported field negation. -/
theorem f81Operations_neg_eq (a : F81) : f81Operations.neg a = -a := by
  change f81Neg a = -a
  apply f81EquivF81Z.injective
  calc
    f81EquivF81Z (f81Neg a) = -f81EquivF81Z a := f81EquivF81Z_map_neg a
    _ = f81EquivF81Z (-a) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_neg f81EquivF81Z.ringEquiv a).symm

/-- Executable multiplication is the transported field multiplication. -/
theorem f81Operations_mul_eq (a b : F81) :
    f81Operations.mul a b = a * b := by
  change f81Mul a b = a * b
  apply f81EquivF81Z.injective
  calc
    f81EquivF81Z (f81Mul a b) = f81EquivF81Z a * f81EquivF81Z b :=
      f81EquivF81Z_map_mul a b
    _ = f81EquivF81Z (a * b) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_mul f81EquivF81Z.ringEquiv a b).symm

/-- The transported field on `F81` has characteristic three. -/
instance f81CharP : CharP F81 3 :=
  f81EquivF81Z.ringEquiv.toRingHom.charP f81EquivF81Z.injective 3

/-- Exponentiation by the executable operation table agrees with standard
field exponentiation. -/
theorem ternaryPow_f81Operations_eq_pow (a : F81) :
    ∀ n : ℕ, ternaryPow f81Operations a n = a ^ n
  | 0 => f81Operations_one_eq
  | n + 1 => by
      rw [ternaryPow, f81Operations_mul_eq,
        ternaryPow_f81Operations_eq_pow]
      exact (pow_succ a n).symm

/-- The table inverse `a^79` is exactly the inverse in the transported field. -/
theorem f81Inv_eq_inv (a : F81) : f81Inv a = a⁻¹ := by
  unfold f81Inv
  rw [ternaryPow_f81Operations_eq_pow]
  apply f81EquivF81Z.injective
  calc
    f81EquivF81Z (a ^ 79) = (f81EquivF81Z a) ^ 79 :=
      f81EquivF81Z.ringEquiv.map_pow a 79
    _ = F81Z.pow (f81EquivF81Z a) 79 :=
      (F81Z.pow_eq_pow (f81EquivF81Z a) 79).symm
    _ = (f81EquivF81Z a)⁻¹ := rfl
    _ = f81EquivF81Z (a⁻¹) :=
      (map_inv₀ f81EquivF81Z.ringEquiv a).symm

/-! ## The executable prime-field table as an actual field

The same coordinate transport used above also gives the three-element
coefficient table its semantic field structure.  Exposing this small base
field lets the quadratic and cubic extension tables inherit symbolic ring
proofs instead of re-enumerating their algebraic laws.
-/

/-- The field structure on executable trits, transported from `ZMod 3`. -/
instance tritField : Field Trit := tritEquivF3Z.field

/-- The table zero is the zero of the transported prime field. -/
theorem f3Operations_zero_eq : f3Operations.zero = (0 : Trit) := by
  apply tritEquivF3Z.injective
  calc
    tritEquivF3Z f3Operations.zero = (0 : F3Z) := rfl
    _ = tritEquivF3Z (0 : Trit) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_zero tritEquivF3Z.ringEquiv).symm

/-- The table one is the one of the transported prime field. -/
theorem f3Operations_one_eq : f3Operations.one = (1 : Trit) := by
  apply tritEquivF3Z.injective
  calc
    tritEquivF3Z f3Operations.one = (1 : F3Z) := rfl
    _ = tritEquivF3Z (1 : Trit) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_one tritEquivF3Z.ringEquiv).symm

/-- Executable trit addition is transported field addition. -/
theorem f3Operations_add_eq (a b : Trit) :
    f3Operations.add a b = a + b := by
  change tritAdd a b = a + b
  apply tritEquivF3Z.injective
  calc
    tritEquivF3Z (tritAdd a b) = tritEquivF3Z a + tritEquivF3Z b :=
      tritEquivF3Z_map_add a b
    _ = tritEquivF3Z (a + b) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_add tritEquivF3Z.ringEquiv a b).symm

/-- Executable trit negation is transported field negation. -/
theorem f3Operations_neg_eq (a : Trit) : f3Operations.neg a = -a := by
  change tritNeg a = -a
  apply tritEquivF3Z.injective
  calc
    tritEquivF3Z (tritNeg a) = -tritEquivF3Z a := tritEquivF3Z_map_neg a
    _ = tritEquivF3Z (-a) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_neg tritEquivF3Z.ringEquiv a).symm

/-- Executable trit multiplication is transported field multiplication. -/
theorem f3Operations_mul_eq (a b : Trit) :
    f3Operations.mul a b = a * b := by
  change tritMul a b = a * b
  apply tritEquivF3Z.injective
  calc
    tritEquivF3Z (tritMul a b) = tritEquivF3Z a * tritEquivF3Z b :=
      tritEquivF3Z_map_mul a b
    _ = tritEquivF3Z (a * b) := by
      simpa only [Equiv.ringEquiv_apply] using
        (map_mul tritEquivF3Z.ringEquiv a b).symm

/-! The extension tables are written directly with `tritAdd`, `tritNeg`, and
`tritMul`, rather than through the record projections above.  The following
bridges expose the same semantic comparison in exactly that syntactic form,
so polynomial identities over `F9` and `F27` can be proved symbolically. -/

/-- The constructor used as the table zero is the transported field zero. -/
@[simp] theorem trit_zero_eq_zero : Trit.zero = (0 : Trit) :=
  f3Operations_zero_eq

/-- The constructor used as the table one is the transported field one. -/
@[simp] theorem trit_one_eq_one : Trit.one = (1 : Trit) :=
  f3Operations_one_eq

/-- Direct trit addition agrees with addition in the transported field. -/
@[simp] theorem tritAdd_eq_add (a b : Trit) : tritAdd a b = a + b :=
  f3Operations_add_eq a b

/-- Direct trit negation agrees with negation in the transported field. -/
@[simp] theorem tritNeg_eq_neg (a : Trit) : tritNeg a = -a :=
  f3Operations_neg_eq a

/-- Direct trit multiplication agrees with multiplication in the transported field. -/
@[simp] theorem tritMul_eq_mul (a b : Trit) : tritMul a b = a * b :=
  f3Operations_mul_eq a b

/-- The transported trit field has characteristic three. -/
instance tritCharP : CharP Trit 3 :=
  tritEquivF3Z.ringEquiv.toRingHom.charP tritEquivF3Z.injective 3

end MazurProof.RationalPointsN25QuotientWeilThree


