-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FullNormPairGaussian_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FullNormPairGaussian_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:22:02.505997+00:00
-- url     : https://prove2.me/theorems/0d413b62-34c3-4dad-80dd-0fb5468d1070
-- title:
--   FLT.Assumptions.MazurProof.N13FullNormPairGaussian source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FullNormPairGaussian

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FullNormPairGaussian
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FullNormPair_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFieldEquiv_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNumberField_p0

set_option autoImplicit false




/-!
# The N13 full norm-pair sign is gauge-trivial

The N13 sextic field is a cubic extension of the Gaussian field, so it
contains a unit `i` with

`i² = -1`,  `Norm(i) = 1`.

Consequently the square/norm gauge at `i`, multiplied by the scalar/cubic
gauge at `-1`, is exactly the sign pair `(1,-1)`.  Thus the distinguished
sign class in the full norm-pair target is already trivial for N13.

This is a field-structure argument.  It uses neither divisor enumeration
nor a finite square-class certificate.
-/

namespace MazurProof.N13FullNormPairGaussian

noncomputable section

open N13GaussianGlobalArithmetic

abbrev Ls : Type :=
  N13GaussianFieldEquiv.Ls

abbrev Lg : Type :=
  N13GaussianFieldEquiv.Lg

abbrev K : Type :=
  N13GaussianFieldEquiv.K

abbrev GI : Type :=
  N13GaussianGlobalArithmetic.GI

local instance fieldLs : Field Ls :=
  N13SexticIrreducible.sexticAlgebraField

local instance fieldLg : Field Lg :=
  N13GaussianCubicField.cubicField

/-- The Gaussian unit transported into the original sextic presentation. -/
def sexticI : Ls :=
  N13GaussianFieldEquiv.sexticEquivGaussian.symm
    N13GaussianFieldEquiv.gaussianI

@[simp] theorem sexticEquivGaussian_sexticI :
    N13GaussianFieldEquiv.sexticEquivGaussian sexticI =
      N13GaussianFieldEquiv.gaussianI := by
  simp [sexticI]

@[simp] theorem sexticI_sq :
    sexticI ^ 2 = -1 := by
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  simp

/-- The absolute norm of `i` is one: the relative norm through the cubic
Gaussian extension is `i³ = -i`, whose Gaussian norm is one. -/
theorem norm_gaussianI :
    Algebra.norm ℚ N13GaussianFieldEquiv.gaussianI = 1 := by
  letI : Module.Free ℚ K :=
    Module.Free.of_basis
      N13GaussianFractionField.gaussianBasis
  letI : Module.Finite ℚ K :=
    Module.Finite.of_basis
      N13GaussianFractionField.gaussianBasis
  letI : Module.Free K Lg :=
    Module.Free.of_basis
      N13GaussianCubicField.powerBasis.basis
  letI : Module.Finite K Lg :=
    Module.Finite.of_basis
      N13GaussianCubicField.powerBasis.basis
  rw [N13GaussianFieldEquiv.gaussianI,
    ← Algebra.norm_norm (R := ℚ) (S := K),
    Algebra.norm_algebraMap,
    N13GaussianNumberField.finrank_K_L]
  have hi3 :
      (algebraMap GI K N13GaussianGlobalArithmetic.i) ^ 3 =
        -(algebraMap GI K N13GaussianGlobalArithmetic.i) := by
    calc
      (algebraMap GI K N13GaussianGlobalArithmetic.i) ^ 3 =
          (algebraMap GI K N13GaussianGlobalArithmetic.i) ^ 2 *
            algebraMap GI K N13GaussianGlobalArithmetic.i := by
              ring
      _ = algebraMap GI K
            (N13GaussianGlobalArithmetic.i ^ 2) *
            algebraMap GI K N13GaussianGlobalArithmetic.i := by
              rw [map_pow]
      _ = -(algebraMap GI K
          N13GaussianGlobalArithmetic.i) := by
              rw [N13GaussianGlobalArithmetic.i_sq,
                map_neg, map_one]
              ring
  rw [hi3, ← map_neg,
    N13GaussianFractionField.fieldNorm_algebraMap]
  norm_num [N13GaussianGlobalArithmetic.i, Zsqrtd.norm]

@[simp] theorem norm_sexticI :
    Algebra.norm ℚ sexticI = 1 := by
  calc
    Algebra.norm ℚ sexticI =
        Algebra.norm ℚ
          (N13GaussianFieldEquiv.sexticEquivGaussian
            sexticI) :=
      (Algebra.norm_eq_of_algEquiv
        N13GaussianFieldEquiv.sexticEquivGaussian
        sexticI).symm
    _ = Algebra.norm ℚ
        N13GaussianFieldEquiv.gaussianI := by
      rw [sexticEquivGaussian_sexticI]
    _ = 1 := norm_gaussianI

/-- The transported Gaussian element as a sextic-field unit. -/
def sexticIUnit : Lsˣ :=
  Units.mk0 sexticI (by
    intro h
    have hi := sexticI_sq
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hi
    norm_num at hi)

@[simp] theorem sexticIUnit_sq :
    sexticIUnit ^ 2 = -1 := by
  apply Units.ext
  exact sexticI_sq

@[simp] theorem normUnits_sexticIUnit :
    N13FullNormPair.normUnits sexticIUnit = 1 := by
  apply Units.ext
  exact norm_sexticI

/-- The sign pair is the product of the Gaussian square/norm gauge and
the `-1` scalar/cubic gauge. -/
theorem signPair_eq_chi_mul_iota :
    EvenSexticNormPair.signPair
        N13FullNormPair.normUnits (-1)
        N13FullNormPair.minusOne_sq =
      EvenSexticNormPair.chi
          N13FullNormPair.normUnits sexticIUnit *
        EvenSexticNormPair.iota
          N13FullNormPair.normUnits
          N13FullNormPair.scalarUnits
          N13FullNormPair.normUnits_scalarUnits (-1) := by
  apply Subtype.ext
  apply Prod.ext
  · change
      (1 : Lsˣ) =
        sexticIUnit ^ 2 *
          N13FullNormPair.scalarUnits (-1)
    rw [sexticIUnit_sq]
    apply Units.ext
    norm_num [N13FullNormPair.scalarUnits,
      FakeSquareClass.scalarUnitsMap]
  · change
      (-1 : ℚˣ) =
        N13FullNormPair.normUnits sexticIUnit *
          (-1 : ℚˣ) ^ 3
    rw [normUnits_sexticIUnit, one_mul]
    norm_num

/-- N13 has no residual sign class in the full norm-pair quotient. -/
@[simp] theorem signClass_eq_one :
    N13FullNormPair.signClass = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [signPair_eq_chi_mul_iota]
  apply Subgroup.mul_mem_sup
  · exact ⟨sexticIUnit, rfl⟩
  · exact ⟨(-1 : ℚˣ), rfl⟩

/-- For N13, forgetting the norm root loses no information: the only
possible kernel classes were `1` and `signClass`, and these coincide. -/
theorem forget_injective :
    Function.Injective N13FullNormPair.forget := by
  intro x y hxy
  have hker :
      N13FullNormPair.forget (x / y) = 1 := by
    rw [map_div, hxy]
    simp
  rcases
      (N13FullNormPair.forget_eq_one_iff (x / y)).mp hker with
    hone | hsign
  · exact div_eq_one.mp hone
  · exact div_eq_one.mp
      (hsign.trans signClass_eq_one)

end

end MazurProof.N13FullNormPairGaussian


