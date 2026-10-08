-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianDifferentSupport_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianDifferentSupport_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:19:06.209144+00:00
-- url     : https://prove2.me/theorems/2dc71779-bf1d-486d-851f-bc95dc5b353a
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianDifferentSupport source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianDifferentSupport

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianDifferentSupport
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerAwayDifferentParity_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerPID_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNumberField_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_ExceptionalPrincipalIdeal_p0
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Norm.Transitivity

set_option autoImplicit false




/-!
# Structural support of the N13 derivative

The two exceptional Gaussian factors are kept as literal algebraic
integers in the absolute maximal order:

* `A = 1 - i θ² - (1 + i) θ`,
* `Q = 2 - 3i`.

The Gaussian cubic relation gives the two short identities

`f'(θ) = 4 · i θ² (θ + 1) · A²`

and

`13 = (i - θ) · A³ · Q`.

All factors omitted from these displayed powers are exhibited as units.
Thus the different support and the ramification indices are read from
factorizations in the maximal order, rather than from a factor table or a
finite residue-field enumeration.
-/

open Algebra Module Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13GaussianDifferentSupport

noncomputable section

open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare

abbrev L := N13GaussianCubicField.L

local instance fieldL : Field L :=
  N13GaussianCubicField.cubicField

abbrev O := integralClosure ℤ L

local instance numberFieldL : NumberField L :=
  N13GaussianNumberField.numberFieldL

local instance dedekindO : IsDedekindDomain O :=
  integralClosure.isDedekindDomain ℤ ℚ L

local instance fractionRingOL : IsFractionRing O L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    ℤ ℚ L O

local instance intAlgebraO : Algebra ℤ O :=
  Ring.toIntAlgebra O

/-- The explicit absolute integral basis, transported across the
carrier-preserving equivalence with Mathlib's ring-of-integers wrapper. -/
def classNumberOrderToOIntLinearEquiv :
    N13GaussianClassNumberOne.O ≃ₗ[ℤ] O :=
  N13GlobalKummerPID.integralClosureEquivClassNumberOrder.symm.toAddEquiv.toIntLinearEquiv

/-- The same carrier-preserving equivalence, now recording compatibility
with the unique integer algebra structures. -/
def OToClassNumberOrderAlgEquiv :
    O ≃ₐ[ℤ] N13GaussianClassNumberOne.O :=
  AlgEquiv.ofRingEquiv
    (f := N13GlobalKummerPID.integralClosureEquivClassNumberOrder)
    (fun z => by simp)

def absoluteBasisO :
    Basis (Fin 2 × Fin 3) ℤ O :=
  N13GaussianNumberField.absoluteRingOfIntegersBasis.map
    classNumberOrderToOIntLinearEquiv

local instance freeO : Module.Free ℤ O :=
  Module.Free.of_basis absoluteBasisO

local instance finiteO : Module.Finite ℤ O :=
  Module.Finite.of_basis absoluteBasisO

/-- The Gaussian unit in the absolute maximal order. -/
def integralI : O :=
  ⟨gaussianI, gaussianI_integral⟩

@[simp] theorem coe_integralI :
    ((integralI : O) : L) = gaussianI :=
  rfl

@[simp] theorem integralI_sq :
    integralI ^ 2 = (-1 : O) := by
  apply Subtype.ext
  exact gaussianI_sq

/-- The factor of `2` defining its unique Gaussian prime. -/
def primeTwoInteger : O :=
  1 - integralI

/-- The ramification-three factor above `13`. -/
def primeAInteger : O :=
  1 - integralI * integralTheta ^ 2 -
    (1 + integralI) * integralTheta

/-- The residue-degree-three factor above `13`. -/
def primeQInteger : O :=
  2 - 3 * integralI

@[simp] theorem coe_primeTwoInteger :
    ((primeTwoInteger : O) : L) = 1 - gaussianI :=
  rfl

@[simp] theorem coe_primeAInteger :
    ((primeAInteger : O) : L) =
      1 - gaussianI * gaussianTheta ^ 2 -
        (1 + gaussianI) * gaussianTheta :=
  rfl

@[simp] theorem coe_primeQInteger :
    ((primeQInteger : O) : L) = 2 - 3 * gaussianI :=
  rfl

/-- The Gaussian unit, now as an actual unit of the maximal order. -/
def integralIUnit : Oˣ where
  val := integralI
  inv := -integralI
  val_inv := by
    rw [mul_neg, ← pow_two, integralI_sq]
    simp
  inv_val := by
    rw [neg_mul, ← pow_two, integralI_sq]
    simp

/-- The sextic generator is an integral unit. -/
def integralThetaUnit : Oˣ where
  val := integralTheta
  inv :=
    integralTheta ^ 2 +
      (2 - 2 * integralI) * integralTheta +
      (-1 - 2 * integralI)
  val_inv := by
    apply Subtype.ext
    exact gaussianTheta_mul_inverse
  inv_val := by
    rw [mul_comm]
    apply Subtype.ext
    exact gaussianTheta_mul_inverse

/-- The neighboring integral element `θ + 1` is also a unit. -/
def integralThetaAddOneUnit : Oˣ where
  val := integralTheta + 1
  inv :=
    -(integralTheta ^ 2 +
      (1 - 2 * integralI) * integralTheta - 2)
  val_inv := by
    apply Subtype.ext
    exact gaussianTheta_add_one_mul_inverse
  inv_val := by
    rw [mul_comm]
    apply Subtype.ext
    exact gaussianTheta_add_one_mul_inverse

theorem gaussianI_sub_theta_mul_inverse :
    (integralI - integralTheta) *
        (-integralTheta ^ 2 - 2 * integralTheta +
          integralI * integralTheta) = 1 := by
  apply Subtype.ext
  change
    (gaussianI - gaussianTheta) *
        (-gaussianTheta ^ 2 - 2 * gaussianTheta +
          gaussianI * gaussianTheta) = 1
  rw [← sub_eq_zero]
  calc
    (gaussianI - gaussianTheta) *
          (-gaussianTheta ^ 2 - 2 * gaussianTheta +
            gaussianI * gaussianTheta) - 1 =
        gaussianTheta ^ 3 + 2 * gaussianTheta ^ 2 -
          gaussianTheta - 1 -
          gaussianI *
            (2 * gaussianTheta * (gaussianTheta + 1)) := by
      ring_nf
      rw [gaussianI_sq]
      ring
    _ = 0 := gaussianTheta_gaussian_cubic

/-- The unit occurring in the factorization of the rational integer `13`. -/
def gaussianI_sub_theta_unit : Oˣ where
  val := integralI - integralTheta
  inv :=
    -integralTheta ^ 2 - 2 * integralTheta +
      integralI * integralTheta
  val_inv := gaussianI_sub_theta_mul_inverse
  inv_val := by
    rw [mul_comm]
    exact gaussianI_sub_theta_mul_inverse

/-- The unit multiplying `A²` in the derivative. -/
def differentUnit : Oˣ :=
  integralIUnit * integralThetaUnit ^ 2 *
    integralThetaAddOneUnit

@[simp] theorem differentUnit_val :
    (differentUnit : O) =
      integralI * integralTheta ^ 2 *
        (integralTheta + 1) := by
  rfl

/-- The Gaussian prime whose cube ramifies in the chosen cubic factor. -/
def gaussianPiInteger : O :=
  3 - 2 * integralI

/-- The unit quotient `A³ / (3-2i)`. -/
def primeACubeCofactor : O :=
  integralTheta *
    (-integralI * integralTheta - 1 - 2 * integralI)

theorem primeACubeCofactor_mul_inverse :
    primeACubeCofactor * (integralI * integralTheta + 1) = 1 := by
  apply Subtype.ext
  change
    (gaussianTheta *
        (-gaussianI * gaussianTheta - 1 - 2 * gaussianI)) *
      (gaussianI * gaussianTheta + 1) = 1
  have hi : gaussianI ^ 2 + 1 = 0 := by
    rw [gaussianI_sq]
    ring
  linear_combination
    gaussianTheta_gaussian_cubic +
      (-gaussianTheta ^ 3 - 2 * gaussianTheta ^ 2) * hi

/-- The quotient `A³ / (3-2i)` is a genuine integral unit. -/
def primeACubeCofactorUnit : Oˣ where
  val := primeACubeCofactor
  inv := integralI * integralTheta + 1
  val_inv := primeACubeCofactor_mul_inverse
  inv_val := by
    rw [mul_comm]
    exact primeACubeCofactor_mul_inverse

/-- Cubing the ramified carrier extracts the Gaussian prime `3-2i`. -/
theorem primeAInteger_cube :
    primeAInteger ^ 3 =
      gaussianPiInteger * primeACubeCofactor := by
  apply Subtype.ext
  change
    (1 - gaussianI * gaussianTheta ^ 2 -
        (1 + gaussianI) * gaussianTheta) ^ 3 =
      (3 - 2 * gaussianI) *
        (gaussianTheta *
          (-gaussianI * gaussianTheta - 1 - 2 * gaussianI))
  have hi : gaussianI ^ 2 + 1 = 0 := by
    rw [gaussianI_sq]
    ring
  rw [← sub_eq_zero]
  linear_combination
    (gaussianI * gaussianTheta ^ 3 +
        (1 + gaussianI) * gaussianTheta ^ 2 +
        (-3 + gaussianI) * gaussianTheta - 1) *
        gaussianTheta_gaussian_cubic +
      (-gaussianI * gaussianTheta ^ 6 -
        3 * gaussianI * gaussianTheta ^ 5 -
        3 * gaussianI * gaussianTheta ^ 4 -
        gaussianI * gaussianTheta ^ 3 -
        gaussianTheta ^ 5 + gaussianTheta ^ 4 +
        7 * gaussianTheta ^ 3 + 3 * gaussianTheta ^ 2 -
        4 * gaussianTheta) * hi

/-- Direct factorization of the sextic derivative at its integral root. -/
theorem differentInteger_eq :
    integralEval N13SexticIrreducible.fInt.derivative =
      4 * (differentUnit : O) * primeAInteger ^ 2 := by
  apply Subtype.ext
  rw [coe_integralEval]
  change
    eval₂ (algebraMap ℤ L) gaussianTheta
        N13SexticIrreducible.fInt.derivative =
      4 *
        (gaussianI * gaussianTheta ^ 2 *
          (gaussianTheta + 1)) *
        (1 - gaussianI * gaussianTheta ^ 2 -
          (1 + gaussianI) * gaussianTheta) ^ 2
  have hderivative :
      N13SexticIrreducible.fInt.derivative =
        6 * X ^ 5 + 20 * X ^ 4 + 24 * X ^ 3 +
          6 * X ^ 2 + 2 * X + 2 := by
    simp [N13SexticIrreducible.fInt]
    ring
  rw [hderivative]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_ofNat]
  rw [← sub_eq_zero]
  have hi : gaussianI ^ 2 + 1 = 0 := by
    rw [gaussianI_sq]
    ring
  linear_combination
    (4 * gaussianI * gaussianTheta ^ 4 +
        4 * gaussianI * gaussianTheta ^ 3 +
        4 * gaussianI * gaussianTheta ^ 2 +
        4 * gaussianI * gaussianTheta -
        2 * gaussianTheta ^ 2 - 2) *
        gaussianTheta_gaussian_cubic +
      (-4 * gaussianI * gaussianTheta ^ 7 -
        12 * gaussianI * gaussianTheta ^ 6 -
        12 * gaussianI * gaussianTheta ^ 5 -
        4 * gaussianI * gaussianTheta ^ 4 +
        8 * gaussianTheta ^ 5 + 24 * gaussianTheta ^ 4 +
        24 * gaussianTheta ^ 3 + 8 * gaussianTheta ^ 2) * hi

/-- The factor `1-i` squares to `2` times a unit. -/
theorem primeTwoInteger_sq :
    primeTwoInteger ^ 2 =
      2 * (-(integralIUnit : O)) := by
  simp only [primeTwoInteger]
  calc
    (1 - integralI) ^ 2 =
        1 - 2 * integralI + integralI ^ 2 := by ring
    _ = 2 * (-integralI) := by
      rw [integralI_sq]
      ring

/-- The exact factorization of `13` into its two Gaussian-cubic carriers. -/
theorem thirteen_eq :
    (13 : O) =
      (gaussianI_sub_theta_unit : O) *
        primeAInteger ^ 3 * primeQInteger := by
  apply Subtype.ext
  change
    (13 : L) =
      (gaussianI - gaussianTheta) *
        (1 - gaussianI * gaussianTheta ^ 2 -
          (1 + gaussianI) * gaussianTheta) ^ 3 *
        (2 - 3 * gaussianI)
  have hcube :
      (1 - gaussianI * gaussianTheta ^ 2 -
          (1 + gaussianI) * gaussianTheta) ^ 3 =
        (3 - 2 * gaussianI) *
          (gaussianTheta *
            (-gaussianI * gaussianTheta - 1 - 2 * gaussianI)) := by
    exact congrArg Subtype.val primeAInteger_cube
  rw [hcube]
  have hlinear :
      (gaussianI - gaussianTheta) *
          (3 - 2 * gaussianI) * (2 - 3 * gaussianI) =
        13 * (gaussianI * gaussianTheta + 1) := by
    have hi : gaussianI ^ 2 + 1 = 0 := by
      rw [gaussianI_sq]
      ring
    rw [← sub_eq_zero]
    linear_combination
      (6 * gaussianI - 13 - 6 * gaussianTheta) * hi
  rw [show
      (gaussianI - gaussianTheta) *
          ((3 - 2 * gaussianI) *
            (gaussianTheta *
              (-gaussianI * gaussianTheta - 1 - 2 * gaussianI))) *
          (2 - 3 * gaussianI) =
        ((gaussianI - gaussianTheta) *
          (3 - 2 * gaussianI) * (2 - 3 * gaussianI)) *
          (gaussianTheta *
            (-gaussianI * gaussianTheta - 1 - 2 * gaussianI)) by
      ring,
    hlinear]
  have hu :
      (gaussianTheta *
          (-gaussianI * gaussianTheta - 1 - 2 * gaussianI)) *
        (gaussianI * gaussianTheta + 1) = 1 :=
    congrArg Subtype.val primeACubeCofactor_mul_inverse
  calc
    (13 : L) =
        13 * 1 := by ring
    _ =
        13 *
          ((gaussianI * gaussianTheta + 1) *
            (gaussianTheta *
              (-gaussianI * gaussianTheta - 1 -
                2 * gaussianI))) := by
      rw [mul_comm] at hu
      rw [hu]
    _ = _ := by ring

/-- Principal ideals of the three displayed carriers. -/
def primeTwoIdeal : Ideal O :=
  Ideal.span ({primeTwoInteger} : Set O)

def primeAIdeal : Ideal O :=
  Ideal.span ({primeAInteger} : Set O)

def primeQIdeal : Ideal O :=
  Ideal.span ({primeQInteger} : Set O)

set_option maxHeartbeats 800000 in
theorem span_two_eq :
    Ideal.span ({(2 : O)} : Set O) = primeTwoIdeal ^ 2 := by
  have hnegI : IsUnit (-(integralIUnit : O)) :=
    (-integralIUnit).isUnit
  rw [primeTwoIdeal, Ideal.span_singleton_pow]
  calc
    Ideal.span ({(2 : O)} : Set O) =
        Ideal.span
          ({2 * (-(integralIUnit : O))} : Set O) :=
      (Ideal.span_singleton_mul_right_unit
        hnegI (2 : O)).symm
    _ = Ideal.span ({primeTwoInteger ^ 2} : Set O) :=
      congrArg (fun x : O => Ideal.span ({x} : Set O))
        primeTwoInteger_sq.symm

set_option maxHeartbeats 800000 in
theorem span_thirteen_eq :
    Ideal.span ({(13 : O)} : Set O) =
      primeAIdeal ^ 3 * primeQIdeal := by
  rw [primeAIdeal, primeQIdeal, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton]
  calc
    Ideal.span ({(13 : O)} : Set O) =
        Ideal.span
          ({(gaussianI_sub_theta_unit : O) *
            (primeAInteger ^ 3 * primeQInteger)} : Set O) := by
      apply congrArg (fun x : O => Ideal.span ({x} : Set O))
      rw [thirteen_eq]
      ring
    _ =
        Ideal.span
          ({primeAInteger ^ 3 * primeQInteger} : Set O) :=
      Ideal.span_singleton_mul_left_unit
        gaussianI_sub_theta_unit.isUnit _

set_option maxHeartbeats 800000 in
theorem span_differentInteger_eq :
    Ideal.span
        ({integralEval
          N13SexticIrreducible.fInt.derivative} : Set O) =
      primeTwoIdeal ^ 4 * primeAIdeal ^ 2 := by
  rw [differentInteger_eq]
  calc
    Ideal.span
          ({4 * (differentUnit : O) * primeAInteger ^ 2} :
            Set O) =
        Ideal.span ({4 * primeAInteger ^ 2} : Set O) := by
      convert
        Ideal.span_singleton_mul_left_unit
          differentUnit.isUnit (4 * primeAInteger ^ 2) using 1 <;>
        ring
    _ =
        Ideal.span ({(4 : O)} : Set O) *
          Ideal.span ({primeAInteger ^ 2} : Set O) :=
      (Ideal.span_singleton_mul_span_singleton _ _).symm
    _ =
        (Ideal.span ({(2 : O)} : Set O)) ^ 2 *
          primeAIdeal ^ 2 := by
      simp only [primeAIdeal, Ideal.span_singleton_pow]
      rw [show (4 : O) = (2 : O) ^ 2 by norm_num,
        ← Ideal.span_singleton_pow]
    _ = (primeTwoIdeal ^ 2) ^ 2 * primeAIdeal ^ 2 := by
      rw [span_two_eq]
    _ = primeTwoIdeal ^ 4 * primeAIdeal ^ 2 := by
      rw [← pow_mul]

/-! ## Norms and the ramified prime -/

abbrev GI := N13GaussianGlobalArithmetic.GI
abbrev K := N13GaussianCubicField.K

/-- In the absolute degree-six field, the Gaussian prime `3-2i` has norm
`13³`: its Gaussian norm is `13`, and the relative extension has degree
three. -/
theorem fieldNorm_gaussianPiInteger :
    Algebra.norm ℚ ((gaussianPiInteger : O) : L) =
      13 ^ 3 := by
  letI : Module.Free ℚ K :=
    Module.Free.of_basis
      N13GaussianFractionField.gaussianBasis
  letI : Module.Finite ℚ K :=
    Module.Finite.of_basis
      N13GaussianFractionField.gaussianBasis
  letI : Module.Free K L :=
    Module.Free.of_basis
      N13GaussianCubicField.powerBasis.basis
  letI : Module.Finite K L :=
    Module.Finite.of_basis
      N13GaussianCubicField.powerBasis.basis
  have hpi :
      ((gaussianPiInteger : O) : L) =
        algebraMap K L
          (algebraMap GI K
            N13GaussianGlobalArithmetic.pi) := by
    change
      3 - 2 * gaussianI =
        algebraMap K L
          (algebraMap GI K
            N13GaussianGlobalArithmetic.pi)
    simp only [N13GaussianGlobalArithmetic.pi,
      N13GaussianFieldEquiv.gaussianI,
      IsScalarTower.algebraMap_apply GI
        N13GaussianCubicField.K L,
      map_sub, map_mul, map_ofNat]
  rw [hpi, ← Algebra.norm_norm (R := ℚ) (S := K)]
  rw [Algebra.norm_algebraMap,
    N13GaussianNumberField.finrank_K_L,
    map_pow, N13GaussianFractionField.fieldNorm_pi]

theorem algebraNorm_gaussianPiInteger :
    Algebra.norm ℤ gaussianPiInteger = 13 ^ 3 := by
  let gpi : N13GaussianClassNumberOne.O :=
    OToClassNumberOrderAlgEquiv gaussianPiInteger
  have hfield :
      Algebra.norm ℚ
          ((gpi : N13GaussianClassNumberOne.O) : L) =
        13 ^ 3 := by
    have hcoe :
        ((gpi : N13GaussianClassNumberOne.O) : L) =
          ((gaussianPiInteger : O) : L) := by
      rfl
    rw [hcoe]
    exact fieldNorm_gaussianPiInteger
  have hnormStd :
      Algebra.norm ℤ gpi = 13 ^ 3 := by
    apply IsFractionRing.injective ℤ ℚ
    calc
      algebraMap ℤ ℚ (Algebra.norm ℤ gpi) =
          Algebra.norm ℚ
            ((gpi : N13GaussianClassNumberOne.O) : L) :=
        Algebra.coe_norm_int gpi
      _ = 13 ^ 3 := hfield
      _ = algebraMap ℤ ℚ (13 ^ 3 : ℤ) := by norm_num
  calc
    Algebra.norm ℤ gaussianPiInteger =
        Algebra.norm ℤ gpi :=
      (Algebra.norm_eq_of_algEquiv
        OToClassNumberOrderAlgEquiv
        gaussianPiInteger).symm
    _ = 13 ^ 3 := hnormStd

theorem absNorm_gaussianPiIdeal :
    Ideal.absNorm
        (Ideal.span ({gaussianPiInteger} : Set O)) =
      13 ^ 3 := by
  rw [Ideal.absNorm_span_singleton]
  change
    (Algebra.norm ℤ gaussianPiInteger).natAbs = 13 ^ 3
  rw [algebraNorm_gaussianPiInteger]
  norm_num

theorem primeAIdeal_pow_three :
    primeAIdeal ^ 3 =
      Ideal.span ({gaussianPiInteger} : Set O) := by
  rw [primeAIdeal, Ideal.span_singleton_pow,
    primeAInteger_cube]
  exact Ideal.span_singleton_mul_right_unit
    primeACubeCofactorUnit.isUnit gaussianPiInteger

/-- The ramified carrier has residue norm `13`. -/
theorem absNorm_primeAIdeal :
    Ideal.absNorm primeAIdeal = 13 := by
  apply Nat.pow_left_injective (by norm_num : 3 ≠ 0)
  change
    Ideal.absNorm primeAIdeal ^ 3 = 13 ^ 3
  rw [← map_pow, primeAIdeal_pow_three,
    absNorm_gaussianPiIdeal]

/-- The ramified carrier is prime because its absolute ideal norm is the
rational prime `13`. -/
theorem primeAIdeal_isPrime :
    primeAIdeal.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_primeAIdeal]
  exact Nat.irreducible_iff_prime.mpr
    (Nat.prime_iff.mp (by norm_num : Nat.Prime 13))

theorem primeAIdeal_ne_bot :
    primeAIdeal ≠ ⊥ := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_primeAIdeal, Ideal.absNorm_bot] at this
  norm_num at this

/-- The absolute integral basis has six elements. -/
theorem finrank_int_O :
    Module.finrank ℤ O = 6 := by
  rw [Module.finrank_eq_card_basis absoluteBasisO]
  norm_num

/-- The second carrier has norm `13³`, forced by the structural
factorization `(13) = PA³ PQ`. -/
theorem absNorm_primeQIdeal :
    Ideal.absNorm primeQIdeal = 13 ^ 3 := by
  have hnorm :=
    congrArg Ideal.absNorm span_thirteen_eq
  have hthirteen :
      Ideal.absNorm
          (Ideal.span ({(13 : O)} : Set O)) =
        13 ^ 6 := by
    simpa [finrank_int_O] using
      (Ideal.absNorm_span_natCast (S := O) 13)
  rw [map_mul, map_pow, absNorm_primeAIdeal,
    hthirteen] at hnorm
  norm_num at hnorm ⊢
  omega

/-- The two carriers above `13` are distinct already by their residue
degrees. -/
theorem primeAIdeal_ne_primeQIdeal :
    primeAIdeal ≠ primeQIdeal := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_primeAIdeal, absNorm_primeQIdeal] at this
  norm_num at this

/-! ## The residue-degree-three prime

Primality of `Q` is not inferred from its composite norm.  Instead we
descend to the Gaussian prime `(2-3i)`.  The relative cubic is irreducible
there: in the thirteen-element residue field, Frobenius and a quadratic
Bézout identity exclude roots. -/

def gaussianQInteger : GI :=
  2 - 3 * N13GaussianGlobalArithmetic.i

def gaussianQIdeal : Ideal GI :=
  Ideal.span ({gaussianQInteger} : Set GI)

@[simp] theorem gaussianQInteger_norm :
    Zsqrtd.norm gaussianQInteger = 13 := by
  norm_num [gaussianQInteger,
    N13GaussianGlobalArithmetic.i, Zsqrtd.norm]

theorem absNorm_gaussianQIdeal :
    Ideal.absNorm gaussianQIdeal = 13 := by
  rw [gaussianQIdeal, Ideal.absNorm_span_singleton,
    N13GaussianFractionField.algebraNorm_eq_gaussianNorm,
    gaussianQInteger_norm]
  norm_num

theorem gaussianQIdeal_isPrime :
    gaussianQIdeal.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_gaussianQIdeal]
  exact Nat.irreducible_iff_prime.mpr
    (Nat.prime_iff.mp (by norm_num : Nat.Prime 13))

theorem gaussianQIdeal_ne_bot :
    gaussianQIdeal ≠ ⊥ := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_gaussianQIdeal, Ideal.absNorm_bot] at this
  norm_num at this

abbrev GaussianQResidue :=
  GI ⧸ gaussianQIdeal

@[simp] theorem gaussianI_mod_gaussianQ :
    Ideal.Quotient.mk gaussianQIdeal
        N13GaussianGlobalArithmetic.i =
      (5 : GaussianQResidue) := by
  change
    Ideal.Quotient.mk gaussianQIdeal
        N13GaussianGlobalArithmetic.i =
      Ideal.Quotient.mk gaussianQIdeal (5 : GI)
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    gaussianQIdeal, Ideal.mem_span_singleton]
  refine ⟨-1 - N13GaussianGlobalArithmetic.i, ?_⟩
  ext <;>
    norm_num [gaussianQInteger,
      N13GaussianGlobalArithmetic.i]

@[simp] theorem thirteen_eq_zero_mod_gaussianQ :
    (13 : GaussianQResidue) = 0 := by
  change
    Ideal.Quotient.mk gaussianQIdeal (13 : GI) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (13 : GI) ∈ gaussianQIdeal
  rw [gaussianQIdeal, Ideal.mem_span_singleton]
  refine
    ⟨2 + 3 * N13GaussianGlobalArithmetic.i, ?_⟩
  ext <;>
    norm_num [gaussianQInteger,
      N13GaussianGlobalArithmetic.i]

def gaussianQResidueCubic :
    GaussianQResidue[X] :=
  X ^ 3 + 6 * X ^ 2 + 10 * X + 7

/-- The cubic left after reduction at `2-3i` is irreducible.  The proof
uses `x¹³=x`, polynomial reduction, and the degree-two Bézout identity;
it does not inspect the thirteen residue elements. -/
theorem gaussianQResidueCubic_irreducible :
    Irreducible gaussianQResidueCubic := by
  letI : gaussianQIdeal.IsMaximal :=
    gaussianQIdeal_isPrime.isMaximal gaussianQIdeal_ne_bot
  letI : Field GaussianQResidue :=
    Ideal.Quotient.field gaussianQIdeal
  letI : Finite GaussianQResidue :=
    (Ideal.absNorm_ne_zero_iff gaussianQIdeal).mp (by
      rw [absNorm_gaussianQIdeal]
      norm_num)
  letI : Fintype GaussianQResidue :=
    Fintype.ofFinite _
  have hcard :
      Fintype.card GaussianQResidue = 13 := by
    rw [← Nat.card_eq_fintype_card,
      ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply,
      absNorm_gaussianQIdeal]
  letI : CharP GaussianQResidue 13 :=
    (CharP.charP_iff_prime_eq_zero
      (by norm_num : Nat.Prime 13)).mpr
      thirteen_eq_zero_mod_gaussianQ
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc]
    have hdeg :
        gaussianQResidueCubic.natDegree = 3 := by
      unfold gaussianQResidueCubic
      compute_degree!
    rw [hdeg]
    norm_num
  intro x hx
  have hcubic :
      x ^ 3 + 6 * x ^ 2 + 10 * x + 7 = 0 := by
    simpa [gaussianQResidueCubic,
      Polynomial.IsRoot, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow] using hx
  have hfrob : x ^ 13 = x := by
    simpa only [hcard] using FiniteField.pow_card x
  have h13zero :
      (13 : GaussianQResidue) = 0 :=
    thirteen_eq_zero_mod_gaussianQ
  have h26zero :
      (26 : GaussianQResidue) = 0 := by
    calc
      (26 : GaussianQResidue) = 2 * 13 := by norm_num
      _ = 0 := by rw [h13zero, mul_zero]
  have h39zero :
      (39 : GaussianQResidue) = 0 := by
    calc
      (39 : GaussianQResidue) = 3 * 13 := by norm_num
      _ = 0 := by rw [h13zero, mul_zero]
  have h52zero :
      (52 : GaussianQResidue) = 0 := by
    calc
      (52 : GaussianQResidue) = 4 * 13 := by norm_num
      _ = 0 := by rw [h13zero, mul_zero]
  have h65zero :
      (65 : GaussianQResidue) = 0 := by
    calc
      (65 : GaussianQResidue) = 5 * 13 := by norm_num
      _ = 0 := by rw [h13zero, mul_zero]
  have h25neg :
      (25 : GaussianQResidue) = -1 := by
    calc
      (25 : GaussianQResidue) = 26 - 1 := by norm_num
      _ = -1 := by rw [h26zero, zero_sub]
  have hrem :
      -x ^ 2 + 2 * x + 5 = 0 := by
    have hid :
        x ^ 13 - x =
          (x ^ 10 - 6 * x ^ 9 + x ^ 7 -
              3 * x ^ 6 - 5 * x ^ 5 + x ^ 4 -
              x ^ 2 - x + 3) *
            (x ^ 3 + 6 * x ^ 2 + 10 * x + 7) +
          (-x ^ 2 + 2 * x + 5) := by
      ring_nf
      rw [h26zero, h25neg, h13zero, h65zero,
        h52zero, h39zero]
      ring
    rw [hfrob, sub_self, hcubic, mul_zero,
      zero_add] at hid
    exact hid.symm
  have hbezout :
      (3 - 3 * x) *
          (x ^ 3 + 6 * x ^ 2 + 10 * x + 7) +
        (-3 * x ^ 2 + 5 * x - 4) *
          (-x ^ 2 + 2 * x + 5) = 1 := by
    ring_nf
    rw [h26zero, h13zero]
    ring
  rw [hcubic, hrem, mul_zero, mul_zero,
    zero_add] at hbezout
  exact zero_ne_one hbezout

abbrev RelativeO :=
  integralClosure GI L

local instance dedekindRelativeO :
    IsDedekindDomain RelativeO :=
  integralClosure.isDedekindDomain GI K L

local instance torsionFreeGIL :
    Module.IsTorsionFree GI L :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hr | hx
    · left
      have hinj :
          Function.Injective (algebraMap GI L) := by
        rw [IsScalarTower.algebraMap_eq GI K L]
        exact
          (algebraMap K L).injective.comp
            (IsFractionRing.injective GI K)
      apply hinj
      simpa using hr
    · exact Or.inr hx

local instance torsionFreeRelativeO :
    Module.IsTorsionFree GI RelativeO :=
  Subalgebra.instIsTorsionFree (integralClosure GI L)

def relativeAlpha : RelativeO :=
  N13GaussianCubicField.relativeIntegralPowerBasis.gen

@[simp] theorem minpoly_relativeAlpha :
    minpoly GI relativeAlpha =
      N13GaussianGlobalArithmetic.h := by
  apply Polynomial.map_injective
    (f := algebraMap GI K)
    (FaithfulSMul.algebraMap_injective GI K)
  have halpha : IsIntegral GI relativeAlpha :=
    PowerBasis.isIntegral_gen
      N13GaussianCubicField.relativeIntegralPowerBasis
  calc
    (minpoly GI relativeAlpha).map
          (algebraMap GI K) =
        minpoly K
          (algebraMap RelativeO L relativeAlpha) :=
      (minpoly.isIntegrallyClosed_eq_field_fractions
        K L halpha).symm
    _ = minpoly K N13GaussianCubicField.alpha := by
      rw [show
        algebraMap RelativeO L relativeAlpha =
            N13GaussianCubicField.alpha by
          change
            ((N13GaussianCubicField.relativeIntegralPowerBasis.gen :
                RelativeO) : L) =
              N13GaussianCubicField.alpha
          exact
            N13GaussianCubicField.coe_relativeIntegralPowerBasis_gen]
    _ = N13GaussianCubicField.hK := by
      change
        minpoly K
            (AdjoinRoot.root N13GaussianCubicField.hK) =
          N13GaussianCubicField.hK
      exact AdjoinRoot.minpoly_powerBasis_gen_of_monic
        N13GaussianCubicField.hK_monic
    _ =
        N13GaussianGlobalArithmetic.h.map
          (algebraMap GI K) := rfl

theorem map_h_mod_gaussianQ :
    Polynomial.map
        (Ideal.Quotient.mk gaussianQIdeal)
        N13GaussianGlobalArithmetic.h =
      gaussianQResidueCubic := by
  rw [N13GaussianGlobalArithmetic.h_explicit]
  simp only [Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, map_add, map_mul, map_pow,
    map_sub, map_neg, map_one, map_ofNat,
    map_natCast, map_intCast,
    Polynomial.map_one, Polynomial.map_ofNat,
    Polynomial.map_natCast]
  rw [N13GaussianGlobalArithmetic.pi,
    gaussianI_mod_gaussianQ]
  simp only [map_sub, map_mul, map_ofNat,
    map_natCast, map_intCast,
    gaussianI_mod_gaussianQ]
  unfold gaussianQResidueCubic
  have h13 :
      (13 : GaussianQResidue[X]) = 0 := by
    change C (13 : GaussianQResidue) = 0
    rw [thirteen_eq_zero_mod_gaussianQ, map_zero]
  linear_combination
    (41 * X ^ 2 - 130 * X - 378) * h13

def relativeGaussianQIdeal : Ideal RelativeO :=
  gaussianQIdeal.map (algebraMap GI RelativeO)

theorem relativeGaussianQIdeal_irreducible :
    Irreducible relativeGaussianQIdeal := by
  unfold relativeGaussianQIdeal
  apply KummerDedekind.Ideal.irreducible_map_of_irreducible_minpoly
    (x := relativeAlpha)
    (gaussianQIdeal_isPrime.isMaximal
      gaussianQIdeal_ne_bot)
    gaussianQIdeal_ne_bot
  · rw [show
      conductor GI relativeAlpha = ⊤ by
        exact conductor_eq_top_of_powerBasis
          N13GaussianCubicField.relativeIntegralPowerBasis]
    simp
  · exact
      PowerBasis.isIntegral_gen
        N13GaussianCubicField.relativeIntegralPowerBasis
  · rw [minpoly_relativeAlpha, map_h_mod_gaussianQ]
    exact gaussianQResidueCubic_irreducible

theorem relativeGaussianQIdeal_isPrime :
    relativeGaussianQIdeal.IsPrime := by
  exact Ideal.isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      relativeGaussianQIdeal_irreducible)

/-- Forget whether integrality was first recorded over `ℤ[i]` or directly
over `ℤ`.  Both subtypes have the same elements of the ambient field. -/
def relativeToORingEquiv :
    RelativeO ≃+* O where
  toFun x :=
    ⟨x.1, isIntegral_trans x.1 x.2⟩
  invFun x :=
    ⟨x.1, x.2.tower_top⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem relativeGaussianQIdeal_eq_span :
    relativeGaussianQIdeal =
      Ideal.span
        ({algebraMap GI RelativeO gaussianQInteger} :
          Set RelativeO) := by
  rw [relativeGaussianQIdeal, gaussianQIdeal,
    Ideal.map_span, Set.image_singleton]

@[simp] theorem relativeToORingEquiv_gaussianQ :
    relativeToORingEquiv
        (algebraMap GI RelativeO gaussianQInteger) =
      primeQInteger := by
  apply Subtype.ext
  change
    algebraMap GI L gaussianQInteger =
      2 - 3 * gaussianI
  simp [gaussianQInteger,
    N13GaussianGlobalArithmetic.i,
    N13GaussianFieldEquiv.gaussianI,
    IsScalarTower.algebraMap_apply GI K L]
  simp only [map_sub, map_mul, map_ofNat]

theorem relativeGaussianQIdeal_map_eq :
    relativeGaussianQIdeal.map relativeToORingEquiv =
      primeQIdeal := by
  rw [relativeGaussianQIdeal_eq_span,
    primeQIdeal, Ideal.map_span, Set.image_singleton,
    relativeToORingEquiv_gaussianQ]

/-- The absolute carrier `Q=(2-3i)` is prime, by the structural
Kummer--Dedekind argument above. -/
theorem primeQIdeal_isPrime :
    primeQIdeal.IsPrime := by
  letI : relativeGaussianQIdeal.IsPrime :=
    relativeGaussianQIdeal_isPrime
  have h :
      (relativeGaussianQIdeal.map
        relativeToORingEquiv).IsPrime := by
    infer_instance
  rwa [relativeGaussianQIdeal_map_eq] at h

theorem primeQIdeal_ne_bot :
    primeQIdeal ≠ ⊥ := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_primeQIdeal, Ideal.absNorm_bot] at this
  norm_num at this

/-! ## The unique prime above two -/

def gaussianTwoInteger : GI :=
  1 - N13GaussianGlobalArithmetic.i

def gaussianTwoIdeal : Ideal GI :=
  Ideal.span ({gaussianTwoInteger} : Set GI)

@[simp] theorem gaussianTwoInteger_norm :
    Zsqrtd.norm gaussianTwoInteger = 2 := by
  norm_num [gaussianTwoInteger,
    N13GaussianGlobalArithmetic.i, Zsqrtd.norm]

theorem absNorm_gaussianTwoIdeal :
    Ideal.absNorm gaussianTwoIdeal = 2 := by
  rw [gaussianTwoIdeal, Ideal.absNorm_span_singleton,
    N13GaussianFractionField.algebraNorm_eq_gaussianNorm,
    gaussianTwoInteger_norm]
  norm_num

theorem gaussianTwoIdeal_isPrime :
    gaussianTwoIdeal.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [absNorm_gaussianTwoIdeal]
  exact Nat.irreducible_iff_prime.mpr
    (Nat.prime_iff.mp Nat.prime_two)

theorem gaussianTwoIdeal_ne_bot :
    gaussianTwoIdeal ≠ ⊥ := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_gaussianTwoIdeal, Ideal.absNorm_bot] at this
  norm_num at this

abbrev GaussianTwoResidue :=
  GI ⧸ gaussianTwoIdeal

@[simp] theorem gaussianI_mod_gaussianTwo :
    Ideal.Quotient.mk gaussianTwoIdeal
        N13GaussianGlobalArithmetic.i =
      (1 : GaussianTwoResidue) := by
  change
    Ideal.Quotient.mk gaussianTwoIdeal
        N13GaussianGlobalArithmetic.i =
      Ideal.Quotient.mk gaussianTwoIdeal (1 : GI)
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    gaussianTwoIdeal, Ideal.mem_span_singleton]
  refine ⟨-1, ?_⟩
  ext <;>
    norm_num [gaussianTwoInteger,
      N13GaussianGlobalArithmetic.i]

@[simp] theorem two_eq_zero_mod_gaussianTwo :
    (2 : GaussianTwoResidue) = 0 := by
  change
    Ideal.Quotient.mk gaussianTwoIdeal (2 : GI) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change (2 : GI) ∈ gaussianTwoIdeal
  rw [gaussianTwoIdeal, Ideal.mem_span_singleton]
  refine
    ⟨1 + N13GaussianGlobalArithmetic.i, ?_⟩
  ext <;>
    norm_num [gaussianTwoInteger,
      N13GaussianGlobalArithmetic.i]

def gaussianTwoResidueCubic :
    GaussianTwoResidue[X] :=
  X ^ 3 + X ^ 2 + 1

/-- Modulo `1-i`, Frobenius gives `x²=x`; hence the reduced cubic has
value `1` at every element. -/
theorem gaussianTwoResidueCubic_irreducible :
    Irreducible gaussianTwoResidueCubic := by
  letI : gaussianTwoIdeal.IsMaximal :=
    gaussianTwoIdeal_isPrime.isMaximal gaussianTwoIdeal_ne_bot
  letI : Field GaussianTwoResidue :=
    Ideal.Quotient.field gaussianTwoIdeal
  letI : Finite GaussianTwoResidue :=
    (Ideal.absNorm_ne_zero_iff gaussianTwoIdeal).mp (by
      rw [absNorm_gaussianTwoIdeal]
      norm_num)
  letI : Fintype GaussianTwoResidue :=
    Fintype.ofFinite _
  have hcard :
      Fintype.card GaussianTwoResidue = 2 := by
    rw [← Nat.card_eq_fintype_card,
      ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply,
      absNorm_gaussianTwoIdeal]
  letI : CharP GaussianTwoResidue 2 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr
      two_eq_zero_mod_gaussianTwo
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc]
    have hdeg :
        gaussianTwoResidueCubic.natDegree = 3 := by
      unfold gaussianTwoResidueCubic
      compute_degree!
    rw [hdeg]
    norm_num
  intro x hx
  have hcubic :
      x ^ 3 + x ^ 2 + 1 = 0 := by
    simpa [gaussianTwoResidueCubic,
      Polynomial.IsRoot, Polynomial.eval_add,
      Polynomial.eval_pow] using hx
  have hx2 : x ^ 2 = x := by
    simpa only [hcard] using FiniteField.pow_card x
  have hx3 : x ^ 3 = x := by
    calc
      x ^ 3 = x ^ 2 * x := by ring
      _ = x * x := by rw [hx2]
      _ = x ^ 2 := by ring
      _ = x := hx2
  have hxx : x + x = 0 := by
    calc
      x + x = 2 * x := by ring
      _ = 0 := by rw [two_eq_zero_mod_gaussianTwo,
        zero_mul]
  rw [hx3, hx2, hxx, zero_add] at hcubic
  exact one_ne_zero hcubic

theorem map_h_mod_gaussianTwo :
    Polynomial.map
        (Ideal.Quotient.mk gaussianTwoIdeal)
        N13GaussianGlobalArithmetic.h =
      gaussianTwoResidueCubic := by
  rw [N13GaussianGlobalArithmetic.h_explicit]
  simp only [Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, map_add, map_mul, map_pow,
    map_one, map_ofNat, Polynomial.map_one,
    Polynomial.map_ofNat]
  rw [N13GaussianGlobalArithmetic.pi,
    gaussianI_mod_gaussianTwo]
  simp only [map_sub, map_mul, map_ofNat,
    gaussianI_mod_gaussianTwo]
  simp only [Polynomial.C_1, one_pow, one_mul,
    mul_one]
  unfold gaussianTwoResidueCubic
  have htwo :
      (2 : GaussianTwoResidue[X]) = 0 := by
    change C (2 : GaussianTwoResidue) = 0
    rw [two_eq_zero_mod_gaussianTwo, map_zero]
  linear_combination
    (X ^ 2 + 52 * X + 162) * htwo

def relativeGaussianTwoIdeal : Ideal RelativeO :=
  gaussianTwoIdeal.map (algebraMap GI RelativeO)

theorem relativeGaussianTwoIdeal_irreducible :
    Irreducible relativeGaussianTwoIdeal := by
  unfold relativeGaussianTwoIdeal
  apply KummerDedekind.Ideal.irreducible_map_of_irreducible_minpoly
    (x := relativeAlpha)
    (gaussianTwoIdeal_isPrime.isMaximal
      gaussianTwoIdeal_ne_bot)
    gaussianTwoIdeal_ne_bot
  · rw [show
      conductor GI relativeAlpha = ⊤ by
        exact conductor_eq_top_of_powerBasis
          N13GaussianCubicField.relativeIntegralPowerBasis]
    simp
  · exact
      PowerBasis.isIntegral_gen
        N13GaussianCubicField.relativeIntegralPowerBasis
  · rw [minpoly_relativeAlpha, map_h_mod_gaussianTwo]
    exact gaussianTwoResidueCubic_irreducible

theorem relativeGaussianTwoIdeal_isPrime :
    relativeGaussianTwoIdeal.IsPrime := by
  exact Ideal.isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      relativeGaussianTwoIdeal_irreducible)

theorem relativeGaussianTwoIdeal_eq_span :
    relativeGaussianTwoIdeal =
      Ideal.span
        ({algebraMap GI RelativeO gaussianTwoInteger} :
          Set RelativeO) := by
  rw [relativeGaussianTwoIdeal, gaussianTwoIdeal,
    Ideal.map_span, Set.image_singleton]

@[simp] theorem relativeToORingEquiv_gaussianTwo :
    relativeToORingEquiv
        (algebraMap GI RelativeO gaussianTwoInteger) =
      primeTwoInteger := by
  apply Subtype.ext
  change
    algebraMap GI L gaussianTwoInteger =
      1 - gaussianI
  simp [gaussianTwoInteger,
    N13GaussianGlobalArithmetic.i,
    N13GaussianFieldEquiv.gaussianI,
    IsScalarTower.algebraMap_apply GI K L]

theorem relativeGaussianTwoIdeal_map_eq :
    relativeGaussianTwoIdeal.map relativeToORingEquiv =
      primeTwoIdeal := by
  rw [relativeGaussianTwoIdeal_eq_span,
    primeTwoIdeal, Ideal.map_span, Set.image_singleton,
    relativeToORingEquiv_gaussianTwo]

theorem primeTwoIdeal_isPrime :
    primeTwoIdeal.IsPrime := by
  letI : relativeGaussianTwoIdeal.IsPrime :=
    relativeGaussianTwoIdeal_isPrime
  have h :
      (relativeGaussianTwoIdeal.map
        relativeToORingEquiv).IsPrime := by
    infer_instance
  rwa [relativeGaussianTwoIdeal_map_eq] at h

/-- The unique prime above two has residue degree three. -/
theorem absNorm_primeTwoIdeal :
    Ideal.absNorm primeTwoIdeal = 2 ^ 3 := by
  have hnorm :=
    congrArg Ideal.absNorm span_two_eq
  have htwo :
      Ideal.absNorm
          (Ideal.span ({(2 : O)} : Set O)) =
        2 ^ 6 := by
    simpa [finrank_int_O] using
      (Ideal.absNorm_span_natCast (S := O) 2)
  rw [map_pow, htwo] at hnorm
  apply Nat.pow_left_injective (by norm_num : 2 ≠ 0)
  norm_num at hnorm ⊢
  omega

theorem primeTwoIdeal_ne_bot :
    primeTwoIdeal ≠ ⊥ := by
  intro h
  have := congrArg Ideal.absNorm h
  rw [absNorm_primeTwoIdeal, Ideal.absNorm_bot] at this
  norm_num at this

/-! ## Height-one carriers and support of the different -/

open IsDedekindDomain

def P2 : HeightOneSpectrum O :=
  ⟨primeTwoIdeal, primeTwoIdeal_isPrime,
    primeTwoIdeal_ne_bot⟩

def PA : HeightOneSpectrum O :=
  ⟨primeAIdeal, primeAIdeal_isPrime,
    primeAIdeal_ne_bot⟩

def PQ : HeightOneSpectrum O :=
  ⟨primeQIdeal, primeQIdeal_isPrime,
    primeQIdeal_ne_bot⟩

@[simp] theorem P2_asIdeal :
    P2.asIdeal = primeTwoIdeal :=
  rfl

@[simp] theorem PA_asIdeal :
    PA.asIdeal = primeAIdeal :=
  rfl

@[simp] theorem PQ_asIdeal :
    PQ.asIdeal = primeQIdeal :=
  rfl

theorem P2_ne_PA :
    P2 ≠ PA := by
  intro h
  have hideal := congrArg
    (fun P : HeightOneSpectrum O => P.asIdeal) h
  have hnorm := congrArg Ideal.absNorm hideal
  simpa [absNorm_primeTwoIdeal,
    absNorm_primeAIdeal] using hnorm

theorem PA_ne_PQ :
    PA ≠ PQ := by
  intro h
  apply primeAIdeal_ne_primeQIdeal
  exact congrArg
    (fun P : HeightOneSpectrum O => P.asIdeal) h

theorem P2_ne_PQ :
    P2 ≠ PQ := by
  intro h
  have hideal := congrArg
    (fun P : HeightOneSpectrum O => P.asIdeal) h
  have hnorm := congrArg Ideal.absNorm hideal
  simpa [absNorm_primeTwoIdeal,
    absNorm_primeQIdeal] using hnorm

/-- The derivative is supported at exactly the displayed primes above
two and at the ramified prime above thirteen. -/
theorem eq_P2_or_PA_of_different_mem
    (R : HeightOneSpectrum O)
    (hmem :
      integralEval
          N13SexticIrreducible.fInt.derivative ∈
        R.asIdeal) :
    R = P2 ∨ R = PA := by
  have hle :
      Ideal.span
          ({integralEval
            N13SexticIrreducible.fInt.derivative} :
            Set O) ≤ R.asIdeal := by
    rwa [Ideal.span_singleton_le_iff_mem]
  rw [span_differentInteger_eq] at hle
  rcases R.isPrime.mul_le.mp hle with htwo | hA
  · have htwo' : primeTwoIdeal ≤ R.asIdeal :=
      R.isPrime.le_of_pow_le htwo
    left
    apply HeightOneSpectrum.ext
    exact
      ((primeTwoIdeal_isPrime.isMaximal
        primeTwoIdeal_ne_bot).eq_of_le
          R.isPrime.ne_top htwo').symm
  · have hA' : primeAIdeal ≤ R.asIdeal :=
      R.isPrime.le_of_pow_le hA
    right
    apply HeightOneSpectrum.ext
    exact
      ((primeAIdeal_isPrime.isMaximal
        primeAIdeal_ne_bot).eq_of_le
          R.isPrime.ne_top hA').symm

theorem different_not_mem_PQ :
    integralEval
        N13SexticIrreducible.fInt.derivative ∉
      PQ.asIdeal := by
  intro h
  rcases eq_P2_or_PA_of_different_mem PQ h with hQ2 | hQA
  · exact P2_ne_PQ hQ2.symm
  · exact PA_ne_PQ hQA.symm

/-- Away from `P2` and `PA`, the already-proved étale parity theorem
applies uniformly. -/
theorem normalizedKummerInteger_count_even_away_P2_PA
    (D : N13LowDegreeKummerHom.LowRep)
    (R : HeightOneSpectrum O)
    (hR2 : R ≠ P2)
    (hRA : R ≠ PA) :
    Even
      (FractionalIdeal.count L R
        (FractionalIdeal.spanSingleton O⁰
          (((normalizedKummerInteger D : O) : L)))) := by
  apply
    N13GlobalKummerAwayDifferentParity.normalizedKummerInteger_count_even_of_not_mem_different
  intro hmem
  rcases eq_P2_or_PA_of_different_mem R hmem with h2 | hA
  · exact hR2 h2
  · exact hRA hA

theorem normalizedKummerInteger_count_even_PQ
    (D : N13LowDegreeKummerHom.LowRep) :
    Even
      (FractionalIdeal.count L PQ
        (FractionalIdeal.spanSingleton O⁰
          (((normalizedKummerInteger D : O) : L)))) :=
  N13GlobalKummerAwayDifferentParity.normalizedKummerInteger_count_even_of_not_mem_different
    D PQ different_not_mem_PQ

/-! ## Square norm and the two remaining parity bits -/

/-- Integral norms in the integral-closure presentation agree with the
field norm after embedding in `ℚ`. -/
theorem coe_algebraNorm_int (x : O) :
    (Algebra.norm ℤ x : ℚ) =
      Algebra.norm ℚ ((x : O) : L) := by
  let xstd : N13GaussianClassNumberOne.O :=
    OToClassNumberOrderAlgEquiv x
  have hcarrier :
      ((xstd : N13GaussianClassNumberOne.O) : L) =
        ((x : O) : L) := by
    rfl
  calc
    (Algebra.norm ℤ x : ℚ) =
        (Algebra.norm ℤ xstd : ℚ) := by
      rw [Algebra.norm_eq_of_algEquiv
        OToClassNumberOrderAlgEquiv x]
    _ =
        Algebra.norm ℚ
          ((xstd : N13GaussianClassNumberOne.O) : L) :=
      Algebra.coe_norm_int xstd
    _ = Algebra.norm ℚ ((x : O) : L) := by
      rw [hcarrier]

/-- A rational-square field norm gives even `p`-adic valuation of the
absolute norm of the principal ideal.  Rational denominators in the
square root are handled directly by `padicValRat`. -/
theorem even_padicValNat_absNorm_span_of_norm_sq
    (p : ℕ) [Fact (Nat.Prime p)]
    (x : O) (hx : x ≠ 0)
    (hsq : ∃ s : ℚ,
      Algebra.norm ℚ ((x : O) : L) = s ^ 2) :
    Even
      (padicValNat p
        (Ideal.absNorm
          (Ideal.span ({x} : Set O)))) := by
  obtain ⟨s, hs⟩ := hsq
  have hxL : ((x : O) : L) ≠ 0 := by
    exact
      (map_ne_zero_iff (algebraMap O L)
        (IsFractionRing.injective O L)).2 hx
  have hnorm0 :
      Algebra.norm ℚ ((x : O) : L) ≠ 0 := by
    exact
      (Algebra.norm_ne_zero_iff (R := ℚ) (S := L)).mpr hxL
  have hs0 : s ≠ 0 := by
    intro hs0
    apply hnorm0
    simpa [hs0] using hs
  have hRatEven :
      Even
        (padicValRat p
          (Algebra.norm ℚ ((x : O) : L))) := by
    refine ⟨padicValRat p s, ?_⟩
    rw [hs, padicValRat.pow s]
    ring
  have hValEq :
      (padicValNat p
          (Ideal.absNorm
            (Ideal.span ({x} : Set O))) : ℤ) =
        padicValRat p
          (Algebra.norm ℚ ((x : O) : L)) := by
    have h :=
      congrArg (padicValRat p) (coe_algebraNorm_int x)
    simpa [Ideal.absNorm_span_singleton,
      padicValInt] using h
  have hIntEven :
      Even
        ((padicValNat p
          (Ideal.absNorm
            (Ideal.span ({x} : Set O))) : ℤ)) := by
    rw [hValEq]
    exact hRatEven
  exact (Int.even_coe_nat _).mp hIntEven

/-- The normalized Kummer integer is already a unit times a square in the
maximal order.  The proof first leaves only the two primes supporting the
different, and then separates their two parity bits by the absolute ideal
norm at `2` and `13`. -/
theorem normalizedKummerInteger_eq_unit_mul_sq
    (D : N13LowDegreeKummerHom.LowRep) :
    ∃ ε : Oˣ, ∃ y : O,
      normalizedKummerInteger D = (ε : O) * y ^ 2 := by
  letI : IsPrincipalIdealRing O :=
    @N13GlobalKummerPID.isPrincipalIdealRing_of_ringEquiv
      O N13GaussianClassNumberOne.O
      inferInstance inferInstance
      N13GaussianClassNumberOne.isPrincipalIdealRingO
      N13GlobalKummerPID.integralClosureEquivClassNumberOrder
  let x : O := normalizedKummerInteger D
  have hx : x ≠ 0 := by
    simpa only [x] using
      N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero D
  have hAway :
      ∀ R : HeightOneSpectrum O,
        R ≠ P2 → R ≠ PA →
          Even
            (EvenPrincipalIdeal.principalCount
              (L := L) R x) := by
    intro R hR2 hRA
    simpa [EvenPrincipalIdeal.principalCount, x] using
      normalizedKummerInteger_count_even_away_P2_PA
        D R hR2 hRA
  obtain ⟨r, a, ε, y, hxy⟩ :=
    ExceptionalPrincipalIdeal.exists_unit_two_carriers_mul_sq_of_even_away
      (L := L) P2 PA P2_ne_PA
      primeTwoInteger primeAInteger x
      (by rfl) (by rfl) hx hAway
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    rw [hxy, hy0]
    simp
  let J : Ideal O := Ideal.span ({y} : Set O)
  have hJ : J ≠ ⊥ := by
    intro hJ0
    apply hy
    exact Ideal.span_singleton_eq_bot.mp hJ0
  have hfac :
      Ideal.span ({x} : Set O) =
        P2.asIdeal ^ r.val *
          PA.asIdeal ^ a.val * J ^ 2 := by
    calc
      Ideal.span ({x} : Set O) =
          Ideal.span
            ({(ε : O) * primeTwoInteger ^ r.val *
              primeAInteger ^ a.val * y ^ 2} : Set O) :=
        congrArg
          (fun z : O => Ideal.span ({z} : Set O)) hxy
      _ =
          Ideal.span ({(ε : O)} : Set O) *
            Ideal.span
              ({primeTwoInteger ^ r.val} : Set O) *
            Ideal.span
              ({primeAInteger ^ a.val} : Set O) *
            Ideal.span ({y ^ 2} : Set O) := by
        rw [Ideal.span_singleton_mul_span_singleton,
          Ideal.span_singleton_mul_span_singleton,
          Ideal.span_singleton_mul_span_singleton]
      _ =
          P2.asIdeal ^ r.val *
            PA.asIdeal ^ a.val * J ^ 2 := by
        rw [Ideal.span_singleton_eq_top.mpr ε.isUnit,
          ← Ideal.one_eq_top, one_mul,
          ← Ideal.span_singleton_pow,
          ← Ideal.span_singleton_pow,
          ← Ideal.span_singleton_pow]
        rfl
  have hNJ : Ideal.absNorm J ≠ 0 := by
    intro hzero
    exact hJ (Ideal.absNorm_eq_zero_iff.mp hzero)
  have hAbs :
      Ideal.absNorm (Ideal.span ({x} : Set O)) =
        (2 ^ 3) ^ r.val * 13 ^ a.val *
          (Ideal.absNorm J) ^ 2 := by
    calc
      Ideal.absNorm (Ideal.span ({x} : Set O)) =
          Ideal.absNorm
            (P2.asIdeal ^ r.val *
              PA.asIdeal ^ a.val * J ^ 2) :=
        congrArg Ideal.absNorm hfac
      _ =
          (2 ^ 3) ^ r.val * 13 ^ a.val *
            (Ideal.absNorm J) ^ 2 := by
        simp only [map_mul, map_pow, P2_asIdeal, PA_asIdeal,
          absNorm_primeTwoIdeal, absNorm_primeAIdeal]
  letI primeTwoFact : Fact (Nat.Prime 2) :=
    ⟨by norm_num⟩
  have hValTwo :
      padicValNat 2
          (Ideal.absNorm (Ideal.span ({x} : Set O))) =
        3 * r.val +
          2 * padicValNat 2 (Ideal.absNorm J) := by
    have h2 : (2 : ℕ) ≠ 0 := by norm_num
    have h13 : (13 : ℕ) ≠ 0 := by norm_num
    rw [hAbs]
    rw [padicValNat.mul
      (mul_ne_zero
        (pow_ne_zero _ (pow_ne_zero 3 h2))
        (pow_ne_zero _ h13))
      (pow_ne_zero _ hNJ)]
    rw [padicValNat.mul
      (pow_ne_zero _ (pow_ne_zero 3 h2))
      (pow_ne_zero _ h13)]
    rw [padicValNat.pow (2 ^ 3) r.val,
      padicValNat.prime_pow,
      padicValNat.pow 13 a.val,
      padicValNat.eq_zero_of_not_dvd
        (p := 2) (n := 13) (by norm_num),
      padicValNat.pow (Ideal.absNorm J) 2]
    ring
  have hTotalEvenTwo :
      Even
        (padicValNat 2
          (Ideal.absNorm
            (Ideal.span ({x} : Set O)))) := by
    apply even_padicValNat_absNorm_span_of_norm_sq
      2 x hx
    change
      ∃ s : ℚ,
        Algebra.norm ℚ
            (((normalizedKummerInteger D : O) : L)) =
          s ^ 2
    exact normalizedKummerInteger_norm_isSquare D
  have hrEven : Even (3 * r.val) := by
    rcases hTotalEvenTwo with ⟨k, hk⟩
    refine
      ⟨k - padicValNat 2 (Ideal.absNorm J), ?_⟩
    rw [hValTwo] at hk
    omega
  have hr0 : r.val = 0 := by
    rcases hrEven with ⟨k, hk⟩
    have hrlt := r.val_lt
    omega
  letI primeThirteenFact : Fact (Nat.Prime 13) :=
    ⟨by norm_num⟩
  have hValThirteen :
      padicValNat 13
          (Ideal.absNorm (Ideal.span ({x} : Set O))) =
        a.val +
          2 * padicValNat 13 (Ideal.absNorm J) := by
    have h2 : (2 : ℕ) ≠ 0 := by norm_num
    have h13 : (13 : ℕ) ≠ 0 := by norm_num
    rw [hAbs]
    rw [padicValNat.mul
      (mul_ne_zero
        (pow_ne_zero _ (pow_ne_zero 3 h2))
        (pow_ne_zero _ h13))
      (pow_ne_zero _ hNJ)]
    rw [padicValNat.mul
      (pow_ne_zero _ (pow_ne_zero 3 h2))
      (pow_ne_zero _ h13)]
    rw [padicValNat.pow (2 ^ 3) r.val,
      padicValNat.pow 2 3,
      padicValNat.eq_zero_of_not_dvd
        (p := 13) (n := 2) (by norm_num),
      padicValNat.pow 13 a.val,
      padicValNat_self,
      padicValNat.pow (Ideal.absNorm J) 2]
    ring
  have hTotalEvenThirteen :
      Even
        (padicValNat 13
          (Ideal.absNorm
            (Ideal.span ({x} : Set O)))) := by
    apply even_padicValNat_absNorm_span_of_norm_sq
      13 x hx
    change
      ∃ s : ℚ,
        Algebra.norm ℚ
            (((normalizedKummerInteger D : O) : L)) =
          s ^ 2
    exact normalizedKummerInteger_norm_isSquare D
  have haEven : Even a.val := by
    rcases hTotalEvenThirteen with ⟨k, hk⟩
    refine
      ⟨k - padicValNat 13 (Ideal.absNorm J), ?_⟩
    rw [hValThirteen] at hk
    omega
  have ha0 : a.val = 0 := by
    rcases haEven with ⟨k, hk⟩
    have halt := a.val_lt
    omega
  refine ⟨ε, y, ?_⟩
  simpa only [x, hr0, ha0, pow_zero, mul_one] using hxy

/-- Every height-one count of the normalized Kummer principal ideal is
even.  This is the valuation form of
`normalizedKummerInteger_eq_unit_mul_sq`. -/
theorem normalizedKummerInteger_principalCount_even
    (D : N13LowDegreeKummerHom.LowRep)
    (R : HeightOneSpectrum O) :
    Even
      (EvenPrincipalIdeal.principalCount
        (L := L) R (normalizedKummerInteger D)) := by
  obtain ⟨ε, y, hxy⟩ :=
    normalizedKummerInteger_eq_unit_mul_sq D
  have hx :
      normalizedKummerInteger D ≠ 0 :=
    N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero D
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    rw [hxy, hy0]
    simp
  have hcount :
      EvenPrincipalIdeal.principalCount
          (L := L) R (normalizedKummerInteger D) =
        2 * EvenPrincipalIdeal.principalCount
          (L := L) R y := by
    calc
      EvenPrincipalIdeal.principalCount
            (L := L) R (normalizedKummerInteger D) =
          EvenPrincipalIdeal.principalCount
            (L := L) R ((ε : O) * y ^ 2) :=
        congrArg
          (EvenPrincipalIdeal.principalCount
            (L := L) R) hxy
      _ =
          EvenPrincipalIdeal.principalCount
              (L := L) R (ε : O) +
            EvenPrincipalIdeal.principalCount
              (L := L) R (y ^ 2) :=
        ExceptionalPrincipalIdeal.principalCount_mul
          ε.ne_zero (pow_ne_zero 2 hy) R
      _ =
          2 * EvenPrincipalIdeal.principalCount
            (L := L) R y := by
        rw [ExceptionalPrincipalIdeal.principalCount_unit,
          ExceptionalPrincipalIdeal.principalCount_pow]
        ring
  refine
    ⟨EvenPrincipalIdeal.principalCount
      (L := L) R y, ?_⟩
  rw [hcount]
  ring

theorem normalizedKummerInteger_count_even
    (D : N13LowDegreeKummerHom.LowRep)
    (R : HeightOneSpectrum O) :
    Even
      (FractionalIdeal.count L R
        (FractionalIdeal.spanSingleton O⁰
          (((normalizedKummerInteger D : O) : L)))) := by
  simpa [EvenPrincipalIdeal.principalCount] using
    normalizedKummerInteger_principalCount_even D R

/-- In particular, the two primes above `13` have the same parity (in
fact, each count is even). -/
theorem normalizedKummerInteger_principalCount_sub_even_PA_PQ
    (D : N13LowDegreeKummerHom.LowRep) :
    Even
      (EvenPrincipalIdeal.principalCount
          (L := L) PA (normalizedKummerInteger D) -
        EvenPrincipalIdeal.principalCount
          (L := L) PQ (normalizedKummerInteger D)) := by
  rcases
      normalizedKummerInteger_principalCount_even D PA with
    ⟨m, hm⟩
  rcases
      normalizedKummerInteger_principalCount_even D PQ with
    ⟨n, hn⟩
  refine ⟨m - n, ?_⟩
  omega

end

end MazurProof.N13GaussianDifferentSupport


