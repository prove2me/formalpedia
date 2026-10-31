-- Prove2me | Definitions.Def_HuangN13_VerticalGraphStatementCore
-- name    : HuangN13_VerticalGraphStatementCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:17:18.22939+00:00
-- url     : https://prove2.me/theorems/033d8dc1-84d5-4209-b766-66eddfce7104
-- title:
--   Exact original statement data for restrict_twoChartLine_of_reduce_c_eq_one, restrict_twoChartLine_of_reduce_c_eq_zero, exists_specialDivisor…
-- statement:
--   Exactly the original definitions (and the lemmas their bodies need) that the statements of the listed N13 nodes refer to; no new mathematics.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Theorems.Thm_MazurProof_N13InfinityLineSpecialRestriction_map_pointIdeal
import Theorems.Thm_MazurProof_N13IntegralCurveProperties_infinity_tClass_mem_nonZeroDivisors
import Theorems.Thm_MazurProof_N13IntegralFractionalHull_functionField_isFractionRing
import Theorems.Thm_MazurProof_N13IntegralInfinityGraphTwoChart_xClassHom_on_overlap
import Theorems.Thm_MazurProof_N13IntegralInfinityPointSpread_pointIdeal_isUnit
import Theorems.Thm_MazurProof_N13IntegralInfinityVerticalGraphJacobian_verticalIdeal_isUnit
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_infinityEquation_of_affineEquation
import Theorems.Thm_MazurProof_N13SpecialDivisorCharts_map_infinityPointIdeal
import Theorems.Thm_MazurProof_N13SpecialDivisorCharts_overlap_unitPointIdeal

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinityCurve_relation :
    N13IntegralInfinityChart.infinityCurvePoly.eval₂
        infinityCoeffMap infinityVImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.infinityEquation_of_affineEquation
      xAffineOverlap tAffineOverlap yAffineOverlap
      xAffineOverlap_mul_tAffineOverlap
      affineOverlap_coordinate_relation
  simp only [N13IntegralInfinityChart.infinityCurvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, infinityCoeffMap_hBase,
    infinityCoeffMap_rhsBase]
  exact sub_eq_zero.mpr h
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restriction of the infinity coordinate ring to the ordinary affine
principal open. -/
def infinityToAffineOverlap :
    InfinityCurve →+* AffineOverlap :=
  AdjoinRoot.lift
    infinityCoeffMap infinityVImage infinityCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_of (p : Base) :
    infinityToAffineOverlap
        (AdjoinRoot.of
          N13IntegralInfinityChart.infinityCurvePoly p) =
      infinityCoeffMap p := by
  exact AdjoinRoot.lift_of infinityCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_tClass :
    infinityToAffineOverlap N13IntegralInfinityChart.tClass =
      tAffineOverlap := by
  simp [infinityToAffineOverlap,
    N13IntegralInfinityChart.tClass, infinityCoeffMap]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToAffineOverlap_vClass :
    infinityToAffineOverlap N13IntegralInfinityChart.vClass =
      infinityVImage := by
  exact AdjoinRoot.lift_root infinityCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinity_tClass_mapsToUnit :
    IsUnit
      (infinityToAffineOverlap
        N13IntegralInfinityChart.tClass) := by
  rw [infinityToAffineOverlap_tClass]
  exact tAffineOverlap_isUnit
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The reverse restriction from the infinity principal open to the affine
principal open. -/
def infinityOverlapToAffineOverlap :
    InfinityOverlap →+* AffineOverlap :=
  IsLocalization.Away.lift
    N13IntegralInfinityChart.tClass
    infinity_tClass_mapsToUnit
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityOverlapToAffineOverlap_algebraMap
    (z : InfinityCurve) :
    infinityOverlapToAffineOverlap
        (algebraMap InfinityCurve InfinityOverlap z) =
      infinityToAffineOverlap z := by
  exact
    IsLocalization.Away.lift_eq
      N13IntegralInfinityChart.tClass
      infinity_tClass_mapsToUnit z
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityOverlapToAffineOverlap_tOverlap :
    infinityOverlapToAffineOverlap tOverlap = tAffineOverlap := by
  rw [tOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_tClass]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The reverse overlap map sends `t⁻¹` back to `x`. -/
@[simp] theorem infinityOverlapToAffineOverlap_xOverlap :
    infinityOverlapToAffineOverlap xOverlap = xAffineOverlap := by
  have hinv :
      tAffineOverlap *
          infinityOverlapToAffineOverlap xOverlap = 1 := by
    calc
      tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap =
          infinityOverlapToAffineOverlap tOverlap *
            infinityOverlapToAffineOverlap xOverlap := by
              rw [infinityOverlapToAffineOverlap_tOverlap]
      _ =
          infinityOverlapToAffineOverlap
            (tOverlap * xOverlap) := by
              rw [map_mul]
      _ = 1 := by rw [tOverlap_mul_xOverlap, map_one]
  calc
    infinityOverlapToAffineOverlap xOverlap =
        1 * infinityOverlapToAffineOverlap xOverlap := by simp
    _ =
        (xAffineOverlap * tAffineOverlap) *
          infinityOverlapToAffineOverlap xOverlap := by
            rw [xAffineOverlap_mul_tAffineOverlap]
    _ =
        xAffineOverlap *
          (tAffineOverlap *
            infinityOverlapToAffineOverlap xOverlap) := by
              rw [mul_assoc]
    _ = xAffineOverlap := by rw [hinv, mul_one]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The forward overlap map sends `x⁻¹` back to `t`. -/
@[simp] theorem affineOverlapToInfinityOverlap_tAffineOverlap :
    affineOverlapToInfinityOverlap tAffineOverlap = tOverlap := by
  have hinv :
      xOverlap *
          affineOverlapToInfinityOverlap tAffineOverlap = 1 := by
    calc
      xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap =
          affineOverlapToInfinityOverlap xAffineOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap := by
              rw [affineOverlapToInfinityOverlap_xAffineOverlap]
      _ =
          affineOverlapToInfinityOverlap
            (xAffineOverlap * tAffineOverlap) := by
              rw [map_mul]
      _ = 1 := by
            rw [xAffineOverlap_mul_tAffineOverlap, map_one]
  calc
    affineOverlapToInfinityOverlap tAffineOverlap =
        1 * affineOverlapToInfinityOverlap tAffineOverlap := by simp
    _ =
        (tOverlap * xOverlap) *
          affineOverlapToInfinityOverlap tAffineOverlap := by
            rw [tOverlap_mul_xOverlap]
    _ =
        tOverlap *
          (xOverlap *
            affineOverlapToInfinityOverlap tAffineOverlap) := by
              rw [mul_assoc]
    _ = tOverlap := by rw [hinv, mul_one]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityOverlapToAffineOverlap_vOverlap :
    infinityOverlapToAffineOverlap vOverlap =
      tAffineOverlap ^ 3 * yAffineOverlap := by
  rw [vOverlap,
    infinityOverlapToAffineOverlap_algebraMap,
    infinityToAffineOverlap_vClass]
  rfl
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] private theorem xCube_cancel
    (z : AffineOverlap) :
    xAffineOverlap ^ 3 * (tAffineOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    xAffineOverlap_mul_tAffineOverlap, one_pow, one_mul]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] private theorem tCube_cancel
    (z : InfinityOverlap) :
    tOverlap ^ 3 * (xOverlap ^ 3 * z) = z := by
  rw [← mul_assoc, ← mul_pow,
    tOverlap_mul_xOverlap, one_pow, one_mul]
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The reverse ordinary overlap map is a left inverse of the forward map. -/
theorem infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap :
    infinityOverlapToAffineOverlap.comp
        affineOverlapToInfinityOverlap =
      RingHom.id AffineOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers xClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        infinityOverlapToAffineOverlap
            (affineOverlapToInfinityOverlap xAffineOverlap) =
          xAffineOverlap
      simp
  · change
      infinityOverlapToAffineOverlap
          (affineOverlapToInfinityOverlap yAffineOverlap) =
        yAffineOverlap
    simp
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The forward ordinary overlap map is a left inverse of the reverse map. -/
theorem affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap :
    affineOverlapToInfinityOverlap.comp
        infinityOverlapToAffineOverlap =
      RingHom.id InfinityOverlap := by
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers N13IntegralInfinityChart.tClass)
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp [RingHom.comp_apply, affineCoeffMap,
        coefficientToInfinityOverlap, infinityCoeffMap,
        coefficientToAffineOverlap]
    · change
        affineOverlapToInfinityOverlap
            (infinityOverlapToAffineOverlap tOverlap) =
          tOverlap
      simp
  · change
      affineOverlapToInfinityOverlap
          (infinityOverlapToAffineOverlap vOverlap) =
        vOverlap
    simp
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The ordinary principal opens of the affine and infinity charts agree. -/
noncomputable def overlapEquiv :
    AffineOverlap ≃+* InfinityOverlap where
  toEquiv :=
    { toFun := affineOverlapToInfinityOverlap
      invFun := infinityOverlapToAffineOverlap
      left_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            infinityOverlapToAffineOverlap_comp_affineOverlapToInfinityOverlap z
      right_inv := fun z => by
        simpa using
          DFunLike.congr_fun
            affineOverlapToInfinityOverlap_comp_infinityOverlapToAffineOverlap z }
  map_mul' := affineOverlapToInfinityOverlap.map_mul
  map_add' := affineOverlapToInfinityOverlap.map_add
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
instance infinityOverlap_isDomain : IsDomain InfinityOverlap :=
  N13OrdinaryCurveOverlap.overlapEquiv.symm.toMulEquiv.isDomain
    AffineOverlap
end
end MazurProof.N13IntegralCurveProperties
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinity_powers_le_nonZeroDivisors :
    Submonoid.powers N13IntegralInfinityChart.tClass ≤
      nonZeroDivisors InfinityCurve :=
  Submonoid.powers_le.mpr
    infinity_tClass_mem_nonZeroDivisors
end
end MazurProof.N13IntegralCurveProperties
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem infinity_to_overlap_injective :
    Function.Injective
      (algebraMap InfinityCurve InfinityOverlap) :=
  IsLocalization.injective InfinityOverlap
    infinity_powers_le_nonZeroDivisors
end
end MazurProof.N13IntegralCurveProperties
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open CategoryTheory
open Polynomial
open Set Topology
namespace MazurProof.N13IntegralCurveProperties
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
instance infinityCurve_isDomain : IsDomain InfinityCurve :=
  infinity_to_overlap_injective.isDomain
    (algebraMap InfinityCurve InfinityOverlap)
end
end MazurProof.N13IntegralCurveProperties
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13IntegralInfinityReduction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem reduce_integralBaseClass (p : IntegralBase) :
    reduceCoordinate (integralBaseClass p) =
      specialBaseClass (reducePoly p) := by
  exact AdjoinRoot.map_of
    reducePoly
    N13IntegralInfinityChart.infinityCurvePoly
    N13SpecialInfinityChart.curvePoly
    special_curve_dvd p
end
end MazurProof.N13IntegralInfinityReduction
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TraceGluing
noncomputable section
variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
/-- A generic-power certificate and a congruence-one trace certificate
force a fractional ideal to be a unit. -/
theorem isUnit_of_genericPower_and_modUniformizerTrace
    (M : FractionalIdeal A⁰ K)
    {f : A}
    (hpow :
      ∃ n : ℕ,
        algebraMap A K (f ^ n) ∈ M * M⁻¹)
    (hmod :
      ∃ a : A,
        algebraMap A K (1 - f * a) ∈ M * M⁻¹) :
    IsUnit M := by
  obtain ⟨n, hn⟩ := hpow
  obtain ⟨a, ha⟩ := hmod
  let Q : FractionalIdeal A⁰ K := M * M⁻¹
  change algebraMap A K (f ^ n) ∈ Q at hn
  change algebraMap A K (1 - f * a) ∈ Q at ha
  let z : A := f * a
  let s : A := ∑ i ∈ Finset.range n, z ^ i
  have hzpow : algebraMap A K (z ^ n) ∈ Q := by
    have h := Q.val.smul_mem (a ^ n) hn
    simpa [z, Algebra.smul_def, mul_pow, mul_comm] using h
  have hgeom : s * (1 - z) = 1 - z ^ n := by
    dsimp [s]
    rw [mul_comm]
    simpa using (Commute.one_right z).mul_neg_geom_sum₂ n
  have htail : algebraMap A K (1 - z ^ n) ∈ Q := by
    have ha' : algebraMap A K (1 - z) ∈ Q := by
      simpa [z] using ha
    have hscaled := Q.val.smul_mem s ha'
    have hmapped :
        algebraMap A K (s * (1 - z)) ∈ Q.val := by
      simpa only [Algebra.smul_def, map_mul] using hscaled
    rw [hgeom] at hmapped
    exact FractionalIdeal.mem_coe.mp hmapped
  have hone : (1 : K) ∈ Q := by
    have h := Q.val.add_mem htail hzpow
    simpa using h
  have hQ_le_one :
      Q ≤ (1 : FractionalIdeal A⁰ K) := by
    change M * M⁻¹ ≤ (1 : FractionalIdeal A⁰ K)
    simpa only [FractionalIdeal.inv_eq] using
      (FractionalIdeal.mul_one_div_le_one (I := M))
  have hQ : Q = 1 :=
    le_antisymm hQ_le_one
      ((FractionalIdeal.one_le).mpr hone)
  apply (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
  simpa [Q] using hQ
end
end MazurProof.N13TraceGluing
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
/-- A fraction field of a localization is also a fraction field of the
original domain. -/
theorem fractionRing_of_localization_fractionRing
    [IsFractionRing B K] :
    IsFractionRing A K := by
  let N := nonZeroDivisors B
  have hloc :
      IsLocalization
          (N.comap (algebraMap A B))
          K :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      M N K (fun x hx => by
        change x ∈ nonZeroDivisors B
        rw [mem_nonZeroDivisors_iff_ne_zero]
        exact hx.ne_zero)
  have hsub :
      N.comap (algebraMap A B) =
        nonZeroDivisors A := by
    ext a
    change
      algebraMap A B a ∈ nonZeroDivisors B ↔
        a ∈ nonZeroDivisors A
    simp only [mem_nonZeroDivisors_iff_ne_zero]
    simpa only [map_zero] using
      ((IsLocalization.injective B
          (submonoid_le_nonZeroDivisors (A := A) (B := B) M)).ne_iff
        (x := a) (y := 0))
  rw [hsub] at hloc
  exact hloc
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- The induced endomorphism of the common fraction field is the identity. -/
theorem fractionFieldMap_eq_id :
    IsLocalization.map
        K (algebraMap A B)
        (nonZeroDivisors_le_comap (A := A) (B := B) M) =
      RingHom.id K := by
  apply IsLocalization.ringHom_ext A⁰
  apply DFunLike.ext _ _
  intro a
  change
    IsLocalization.map
        K (algebraMap A B)
        (nonZeroDivisors_le_comap (A := A) (B := B) M)
        (algebraMap A K a) =
      algebraMap A K a
  rw [IsLocalization.map_eq]
  exact (IsScalarTower.algebraMap_apply A B K a).symm
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- Every section of a fractional ideal maps into its localization. -/
theorem mem_extendFractional_of_mem
    {I : FractionalIdeal A⁰ K} {x : K}
    (hx : x ∈ I) :
    x ∈ extendFractional (A := A) (B := B) (K := K) M I := by
  change
    x ∈ FractionalIdeal.extended
      K (nonZeroDivisors_le_comap (A := A) (B := B) M) I
  rw [FractionalIdeal.mem_extended_iff]
  apply Submodule.subset_span
  refine ⟨x, hx, ?_⟩
  rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
  rfl
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- Extension of the multiplier inverse is contained in the inverse of
the extended fractional ideal. -/
theorem extendFractional_inv_le
    {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    extendFractional (A := A) (B := B) (K := K) M I⁻¹ ≤
      (extendFractional (A := A) (B := B) (K := K) M I)⁻¹ := by
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B
      (submonoid_le_nonZeroDivisors (A := A) (B := B) M)
  have hExtended :
      extendFractional (A := A) (B := B) (K := K) M I ≠ 0 :=
    FractionalIdeal.extended_ne_zero
      K (nonZeroDivisors_le_comap (A := A) (B := B) M)
        hAB hI (by simp)
  intro z hz
  change
    z ∈ FractionalIdeal.extended
      K (nonZeroDivisors_le_comap (A := A) (B := B) M) I⁻¹ at hz
  rw [FractionalIdeal.mem_extended_iff] at hz
  refine Submodule.span_induction
    (p := fun z _ =>
      z ∈
        (extendFractional (A := A) (B := B) (K := K) M I)⁻¹)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨y, hy, rfl⟩
    rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
    rw [FractionalIdeal.mem_inv_iff hExtended]
    intro x hx
    change
      x ∈ FractionalIdeal.extended
        K (nonZeroDivisors_le_comap (A := A) (B := B) M) I at hx
    rw [FractionalIdeal.mem_extended_iff] at hx
    refine Submodule.span_induction
      (p := fun x _ =>
        y * x ∈ (1 : FractionalIdeal B⁰ K))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, rfl⟩
      rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
      obtain ⟨r, hr⟩ :=
        (FractionalIdeal.mem_one_iff A⁰).mp
          ((FractionalIdeal.mem_inv_iff hI).mp hy a ha)
      apply (FractionalIdeal.mem_one_iff B⁰).mpr
      refine ⟨algebraMap A B r, ?_⟩
      rw [← IsScalarTower.algebraMap_apply A B K]
      exact hr
    · simp
    · intro a b _ _ ha hb
      rw [mul_add]
      exact
        ((1 : FractionalIdeal B⁰ K) :
          Submodule B K).add_mem ha hb
    · intro a b _ hb
      have hsmul :=
        ((1 : FractionalIdeal B⁰ K) :
          Submodule B K).smul_mem a hb
      simpa [Algebra.smul_def, mul_assoc,
        mul_left_comm, mul_comm] using hsmul
  · exact FractionalIdeal.zero_mem _
  · intro a b _ _ ha hb
    exact
      ((((extendFractional (A := A) (B := B) (K := K) M I)⁻¹ :
          FractionalIdeal B⁰ K)) :
        Submodule B K).add_mem ha hb
  · intro a b _ hb
    exact
      ((((extendFractional (A := A) (B := B) (K := K) M I)⁻¹ :
          FractionalIdeal B⁰ K)) :
        Submodule B K).smul_mem a hb
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- Finite generation clears one common localization denominator and gives
the reverse inclusion for multiplier inverses. -/
theorem inv_extendFractional_le
    {I : FractionalIdeal A⁰ K}
    (hI : I ≠ 0)
    (hfg : I.coeToSubmodule.FG) :
    (extendFractional (A := A) (B := B) (K := K) M I)⁻¹ ≤
      extendFractional (A := A) (B := B) (K := K) M I⁻¹ := by
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B
      (submonoid_le_nonZeroDivisors (A := A) (B := B) M)
  have hExtended :
      extendFractional (A := A) (B := B) (K := K) M I ≠ 0 :=
    FractionalIdeal.extended_ne_zero
      K (nonZeroDivisors_le_comap (A := A) (B := B) M)
        hAB hI (by simp)
  obtain ⟨n, g, hspan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hfg
  intro z hz
  have hgI (i : Fin n) : g i ∈ I := by
    change g i ∈ I.coeToSubmodule
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hzg (i : Fin n) :
      z * g i ∈ (1 : FractionalIdeal B⁰ K) := by
    exact
      (FractionalIdeal.mem_inv_iff hExtended).mp hz
        (g i)
        (mem_extendFractional_of_mem
          (A := A) (B := B) (K := K) M (hgI i))
  choose b hb using fun i =>
    (FractionalIdeal.mem_one_iff B⁰).mp (hzg i)
  obtain ⟨s, hs⟩ :=
    IsLocalization.exist_integer_multiples_of_finite M b
  choose a ha using fun i => hs i
  have hszInv :
      (s : A) • z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI]
    intro x hx
    change x ∈ I.coeToSubmodule at hx
    rw [← hspan] at hx
    refine Submodule.span_induction
      (p := fun x _ =>
        ((s : A) • z) * x ∈
          (1 : FractionalIdeal A⁰ K))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      apply (FractionalIdeal.mem_one_iff A⁰).mpr
      refine ⟨a i, ?_⟩
      calc
        algebraMap A K (a i) =
            algebraMap B K (algebraMap A B (a i)) := by
              rw [IsScalarTower.algebraMap_apply A B K]
        _ = algebraMap B K ((s : A) • b i) := by rw [ha i]
        _ = (s : A) • algebraMap B K (b i) := by
              simp only [Algebra.smul_def]
              rw [map_mul,
                IsScalarTower.algebraMap_apply A B K]
        _ = (s : A) • (z * g i) := by rw [hb i]
        _ = ((s : A) • z) * g i := by
              simp [Algebra.smul_def, mul_assoc]
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact
        ((1 : FractionalIdeal A⁰ K) :
          Submodule A K).add_mem hx hy
    · intro r x _ hx
      have hrx :=
        ((1 : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem r hx
      simpa [Algebra.smul_def, mul_assoc,
        mul_left_comm, mul_comm] using hrx
  have hszExtended :
      (s : A) • z ∈
        extendFractional (A := A) (B := B) (K := K) M I⁻¹ := by
    change
      (s : A) • z ∈
        FractionalIdeal.extended
          K (nonZeroDivisors_le_comap (A := A) (B := B) M) I⁻¹
    rw [FractionalIdeal.mem_extended_iff]
    apply Submodule.subset_span
    refine ⟨(s : A) • z, hszInv, ?_⟩
    rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M]
    rfl
  exact
    (IsLocalization.smul_mem_iff
      (R := A) (R' := B)
      (N' :=
        (extendFractional (A := A) (B := B) (K := K) M I⁻¹ :
          Submodule B K))
      (s := s)).mp hszExtended
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- Extension through a localization commutes with multiplier inverse for
every nonzero finitely generated fractional ideal. -/
theorem extendFractional_inv
    {I : FractionalIdeal A⁰ K}
    (hI : I ≠ 0)
    (hfg : I.coeToSubmodule.FG) :
    extendFractional (A := A) (B := B) (K := K) M I⁻¹ =
      (extendFractional (A := A) (B := B) (K := K) M I)⁻¹ :=
  le_antisymm
    (extendFractional_inv_le (A := A) (B := B) (K := K) M hI)
    (inv_extendFractional_le
      (A := A) (B := B) (K := K) M hI hfg)
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
/-- If a finitely generated fractional ideal becomes invertible after
localization, one element of the localization submonoid lies in `I I⁻¹`. -/
theorem exists_submonoid_mem_mul_inv
    (I : FractionalIdeal A⁰ K)
    (hfg : I.coeToSubmodule.FG)
    (hlocal :
      IsUnit
        (extendFractional (A := A) (B := B) (K := K) M I)) :
    ∃ s : M, algebraMap A K (s : A) ∈ I * I⁻¹ := by
  have hExtended :
      extendFractional (A := A) (B := B) (K := K) M I ≠ 0 :=
    hlocal.ne_zero
  have hAB : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B
      (submonoid_le_nonZeroDivisors (A := A) (B := B) M)
  have hI : I ≠ 0 := by
    intro hzero
    apply hExtended
    rw [hzero]
    exact map_zero
      (extendFractional (A := A) (B := B) (K := K) M)
  have hExtMul :
      extendFractional (A := A) (B := B) (K := K) M (I * I⁻¹) =
        1 := by
    rw [map_mul,
      extendFractional_inv
        (A := A) (B := B) (K := K) M hI hfg]
    exact
      (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hlocal
  have hone :
      (1 : K) ∈
        extendFractional (A := A) (B := B) (K := K) M (I * I⁻¹) := by
    rw [hExtMul]
    simp
  change
    (1 : K) ∈
      FractionalIdeal.extended
        K (nonZeroDivisors_le_comap (A := A) (B := B) M)
          (I * I⁻¹) at hone
  rw [FractionalIdeal.mem_extended_iff] at hone
  rw [fractionFieldMap_eq_id (A := A) (B := B) (K := K) M] at hone
  have hone' :
      (1 : K) ∈
        Submodule.span B (I * I⁻¹ : Set K) := by
    simpa using hone
  obtain ⟨s, hs⟩ :=
    multiple_mem_span_of_mem_localization_span
      M B (I * I⁻¹ : Set K) (1 : K) hone'
  refine ⟨s, ?_⟩
  change
    s • (1 : K) ∈
      Submodule.span A
        ((((I * I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K)) : Set K) at hs
  rw [Submodule.span_eq] at hs
  change
    algebraMap A K (s : A) ∈
      ((I * I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K)
  simpa only [Submonoid.smul_def, Algebra.smul_def, mul_one] using hs
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13LocalizationIdealPatch
noncomputable section
variable {A B K : Type*}
variable [CommRing A] [IsDomain A]
variable [CommRing B] [IsDomain B]
variable [Field K]
variable [Algebra A B] [Algebra A K] [Algebra B K]
variable [IsScalarTower A B K]
variable (M : Submonoid A)
variable [IsLocalization M B]
include B M
variable [IsFractionRing A K] [IsFractionRing B K]
omit M in
/-- An ideal that is invertible after localizing at powers of `f` is
already invertible when `f` is a unit modulo that ideal. -/
theorem ideal_isUnit_of_localized_isUnit
    (f : A)
    [IsLocalization (Submonoid.powers f) B]
    (I : Ideal A)
    (hfg : I.FG)
    (hmod : ∃ a : A, 1 - f * a ∈ I)
    (hlocal :
      IsUnit
        (extendFractional
          (A := A) (B := B) (K := K)
          (Submonoid.powers f)
          (I : FractionalIdeal A⁰ K))) :
    IsUnit (I : FractionalIdeal A⁰ K) := by
  let IF : FractionalIdeal A⁰ K :=
    (I : FractionalIdeal A⁰ K)
  have hfgF : IF.coeToSubmodule.FG := by
    change
      ((I : FractionalIdeal A⁰ K) :
        Submodule A K).FG
    rw [FractionalIdeal.coeIdeal_fg A⁰
      (IsFractionRing.injective A K)]
    exact hfg
  obtain ⟨s, hs⟩ :=
    exists_submonoid_mem_mul_inv
      (A := A) (B := B) (K := K)
      (Submonoid.powers f) IF hfgF hlocal
  obtain ⟨n, hn⟩ := s.2
  have hpow :
      ∃ n : ℕ,
        algebraMap A K (f ^ n) ∈ IF * IF⁻¹ := by
    refine ⟨n, ?_⟩
    simpa only [hn] using hs
  obtain ⟨a, ha⟩ := hmod
  have hmod' :
      ∃ a : A,
        algebraMap A K (1 - f * a) ∈ IF * IF⁻¹ := by
    refine ⟨a, ?_⟩
    exact
      FractionalIdeal.coe_ideal_le_self_mul_inv K I
        (FractionalIdeal.mem_coeIdeal_of_mem A⁰ ha)
  exact
    N13TraceGluing.isUnit_of_genericPower_and_modUniformizerTrace
      IF hpow hmod'
end
end MazurProof.N13LocalizationIdealPatch
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
/-- The proper two-chart point line supported at positive infinity. -/
def infinityPlusLine : TwoChartLine :=
  N13IntegralInfinityPointSpread.pointLine infinityPlusPoint
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
/-- The proper two-chart point line supported at negative infinity. -/
def infinityMinusLine : TwoChartLine :=
  N13IntegralInfinityPointSpread.pointLine infinityMinusPoint
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Both infinity point lines are trivial on the affine chart.  The branch
distinction is retained entirely by their infinity-chart point ideals. -/
@[simp] theorem infinityPlusLine_affineIdeal :
    infinityPlusLine.affineIdeal = ⊤ := by
  simp [infinityPlusLine,
    N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.affinePointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    N13IntegralInfinityPointSpread.affineU,
    infinityPlusPoint]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp)
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartLineTensor
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The negative infinity point line is likewise trivial on the affine
chart, although its infinity-chart ideal differs from the positive line. -/
@[simp] theorem infinityMinusLine_affineIdeal :
    infinityMinusLine.affineIdeal = ⊤ := by
  simp [infinityMinusLine,
    N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.affinePointIdeal,
    GeneralizedGraphIdealCore.graphIdeal,
    N13IntegralInfinityPointSpread.affineU,
    infinityMinusPoint]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp)
end
end MazurProof.N13TwoChartLineTensor
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
/-- Compatible chart pairs are equal once their two chart ideals agree.

The overlap field is a proposition, so proof irrelevance removes it after
the affine and infinity ideals have been identified. -/
@[ext] theorem ChartPair.ext
    {L M : ChartPair}
    (haffine : L.affineIdeal = M.affineIdeal)
    (hinfinity : L.infinityIdeal = M.infinityIdeal) :
    L = M := by
  cases L
  cases M
  simp_all
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Chartwise restriction carries tensor products of proper lines to products
of their reduced affine ideals. -/
@[simp] theorem restrict_tensor_affineIdeal
    (L M : Line) :
    (restrict (N13TwoChartLineTensor.tensor L M)).affineIdeal =
      (restrict L).affineIdeal * (restrict M).affineIdeal := by
  exact Ideal.map_mul _ _ _
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13TwoChartSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Chartwise restriction carries tensor products of proper lines to products
of their reduced infinity ideals. -/
@[simp] theorem restrict_tensor_infinityIdeal
    (L M : Line) :
    (restrict (N13TwoChartLineTensor.tensor L M)).infinityIdeal =
      (restrict L).infinityIdeal * (restrict M).infinityIdeal := by
  exact Ideal.map_mul _ _ _
end
end MazurProof.N13TwoChartSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialDivisorCharts
noncomputable section
@[simp] theorem ofDivisor_mk (P Q : CurvePoint) :
    ofDivisor s(P, Q) =
      tensor (point P) (point Q) :=
  rfl
end
end MazurProof.N13SpecialDivisorCharts
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- A monic polynomial of degree two is determined by its two lower
coefficients. -/
theorem monic_quadratic_eq
    (u : R₂[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2) :
    u = X ^ 2 + C (u.coeff 1) * X + C (u.coeff 0) := by
  have hc₂ : u.coeff 2 = 1 := by
    calc
      u.coeff 2 = u.coeff u.natDegree :=
        congrArg u.coeff hdeg.symm
      _ = 1 := hu.coeff_natDegree
  have hdegree : u.degree ≤ 2 := by
    rw [degree_eq_natDegree hu.ne_zero, hdeg]
    norm_num
  calc
    u =
        C (u.coeff 2) * X ^ 2 +
          C (u.coeff 1) * X +
          C (u.coeff 0) :=
      u.eq_quadratic_of_degree_le_two hdegree
    _ = X ^ 2 + C (u.coeff 1) * X + C (u.coeff 0) := by
      rw [hc₂, C_1]
      ring
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- A monic quadratic reflects to a polynomial with constant coefficient
one and an explicit remaining multiple of `X`. -/
theorem reflect_two_eq_one_add_X_mul
    (u : R₂[X])
    (hu : u.Monic)
    (hdeg : u.natDegree = 2) :
    u.reflect 2 =
      1 + X * (C (u.coeff 1) + C (u.coeff 0) * X) := by
  have hshape := monic_quadratic_eq u hu hdeg
  have hX2 :
      ((X : R₂[X]) ^ 2).reflect 2 = 1 := by
    simpa using
      (reflect_monomial 2 2 (R := R₂))
  have hCX :
      (C (u.coeff 1) * X : R₂[X]).reflect 2 =
        C (u.coeff 1) * X := by
    simpa using
      (reflect_C_mul_X_pow
        (R := R₂) 2 1 (c := u.coeff 1))
  calc
    u.reflect 2 =
        (X ^ 2 + C (u.coeff 1) * X +
          C (u.coeff 0)).reflect 2 :=
      congrArg (fun p : R₂[X] => p.reflect 2) hshape
    _ =
        (X ^ 2).reflect 2 +
          (C (u.coeff 1) * X).reflect 2 +
          (C (u.coeff 0)).reflect 2 := by
            rw [reflect_add, reflect_add]
    _ = 1 + X * (C (u.coeff 1) + C (u.coeff 0) * X) := by
      rw [hX2, hCX, reflect_C]
      ring
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem affineToInfinityOverlap_algebraMap_R₂
    (r : R₂) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (algebraMap R₂ AffineCurve r) =
      algebraMap R₂ InfinityOverlap r := by
  change
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom (C r)) =
      _
  rw [N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    N13OrdinaryCurveOverlap.affineCoeffMap_C]
  unfold N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
  change
    (algebraMap InfinityCurve InfinityOverlap)
        (algebraMap R₂ InfinityCurve r) =
      algebraMap R₂ InfinityOverlap r
  exact IsScalarTower.algebraMap_apply R₂ InfinityCurve InfinityOverlap r
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityOverlap_algebraMap_R₂
    (r : R₂) :
    (algebraMap InfinityCurve InfinityOverlap)
        (algebraMap R₂ InfinityCurve r) =
      algebraMap R₂ InfinityOverlap r := by
  exact IsScalarTower.algebraMap_apply R₂ InfinityCurve InfinityOverlap r
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityGraphSaturation
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The named coefficient map is the ordinary scalar map into the
infinity overlap. -/
@[simp] theorem coefficientToInfinityOverlap_eq_algebraMap_R₂
    (r : R₂) :
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap r =
      algebraMap R₂ InfinityOverlap r := by
  unfold N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
  change
    (algebraMap InfinityCurve InfinityOverlap)
        (algebraMap R₂ InfinityCurve r) =
      algebraMap R₂ InfinityOverlap r
  exact infinityOverlap_algebraMap_R₂ r
end
end MazurProof.N13IntegralInfinityGraphSaturation
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Weighted reflection of the reciprocal generator on the overlap. -/
theorem affineReciprocal_on_overlap
    (u : R₂[X])
    (huDegree : u.natDegree ≤ 2) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineReciprocal u) =
      N13OrdinaryCurveOverlap.xOverlap ^ 2 *
        (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityReduction.integralBaseClass u) := by
  change
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13GeneralizedMumfordIntegral.xClassHom (u.reflect 2)) =
      N13OrdinaryCurveOverlap.xOverlap ^ 2 *
        (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityGraphJacobian.xClassHom u)
  rw [
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    N13IntegralInfinityGraphTwoChart.reflect_on_overlap
      2 u huDegree,
    N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap]
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The vertical quadratic generator changes by the unit `x⁶` on the
ordinary overlap. -/
theorem affineVerticalEquation_on_overlap
    (E : VerticalGraph)
    (hmDegree : E.m.natDegree = 2) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineVerticalEquation E) =
      N13OrdinaryCurveOverlap.xOverlap ^ 6 *
        (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityVerticalGraphJacobian.U E) := by
  have hmShape :=
    N13IntegralInfinityGraphSaturation.monic_quadratic_eq
      E.m E.m_monic hmDegree
  have hU :
      (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityVerticalGraphJacobian.U E) =
        N13OrdinaryCurveOverlap.vOverlap ^ 2 +
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
              (E.m.coeff 1) *
            N13OrdinaryCurveOverlap.vOverlap +
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            (E.m.coeff 0) := by
    rw [N13IntegralInfinityVerticalGraphJacobian.U, hmShape]
    simp [N13IntegralInfinityGraphJacobian.yClass,
      N13IntegralInfinityPointSpread.yClass,
      N13OrdinaryCurveOverlap.vOverlap,
      N13IntegralInfinityGraphSaturation.coefficientToInfinityOverlap_eq_algebraMap_R₂]
  rw [affineVerticalEquation]
  simp only [map_add, map_mul, map_pow,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClassHom,
    N13OrdinaryCurveOverlap.affineYImage,
    N13OrdinaryCurveOverlap.affineCoeffMap_C,
    N13OrdinaryCurveOverlap.affineCoeffMap_X]
  rw [hU]
  change
    (N13OrdinaryCurveOverlap.xOverlap ^ 3 *
          N13OrdinaryCurveOverlap.vOverlap) ^ 2 +
        (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
              (E.m.coeff 1) *
            N13OrdinaryCurveOverlap.xOverlap ^ 3) *
          (N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap) +
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            (E.m.coeff 0) *
          N13OrdinaryCurveOverlap.xOverlap ^ 6 =
      N13OrdinaryCurveOverlap.xOverlap ^ 6 *
        (N13OrdinaryCurveOverlap.vOverlap ^ 2 +
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
              (E.m.coeff 1) *
            N13OrdinaryCurveOverlap.vOverlap +
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap
            (E.m.coeff 0))
  ring
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The vertical linear generator changes by the unit `x³` on the
ordinary overlap. -/
theorem affineLinearEquation_on_overlap
    (E : VerticalGraph) :
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineLinearEquation E) =
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
        (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityVerticalGraphJacobian.G E) := by
  have hG :
      (algebraMap InfinityCurve InfinityOverlap)
          (N13IntegralInfinityVerticalGraphJacobian.G E) =
        N13OrdinaryCurveOverlap.tOverlap -
          (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.a +
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.c *
              N13OrdinaryCurveOverlap.vOverlap) := by
    simp [N13IntegralInfinityVerticalGraphJacobian.G,
      N13IntegralInfinityVerticalGraphJacobian.L,
      N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.s,
      N13IntegralInfinityChart.tClass,
      N13IntegralInfinityGraphJacobian.yClass,
      N13IntegralInfinityPointSpread.yClass,
      N13OrdinaryCurveOverlap.tOverlap,
      N13OrdinaryCurveOverlap.vOverlap,
      N13IntegralInfinityGraphSaturation.coefficientToInfinityOverlap_eq_algebraMap_R₂]
  rw [affineLinearEquation]
  simp only [map_sub, map_mul, map_pow,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_xClass,
    N13OrdinaryCurveOverlap.affineToInfinityOverlap_generalized_yClass,
    N13OrdinaryCurveOverlap.affineYImage,
    N13IntegralInfinityGraphSaturation.affineToInfinityOverlap_algebraMap_R₂,
    hG]
  change
    N13OrdinaryCurveOverlap.xOverlap ^ 2 -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.a *
            N13OrdinaryCurveOverlap.xOverlap ^ 3 -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.c *
          (N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap) =
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
        (N13OrdinaryCurveOverlap.tOverlap -
          (N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.a +
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap E.c *
              N13OrdinaryCurveOverlap.vOverlap))
  have htx :=
    N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  have hxt :
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
          N13OrdinaryCurveOverlap.tOverlap =
        N13OrdinaryCurveOverlap.xOverlap ^ 2 := by
    calc
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.tOverlap =
          N13OrdinaryCurveOverlap.xOverlap ^ 2 *
            (N13OrdinaryCurveOverlap.tOverlap *
              N13OrdinaryCurveOverlap.xOverlap) := by ring
      _ = N13OrdinaryCurveOverlap.xOverlap ^ 2 := by rw [htx, mul_one]
  linear_combination -hxt
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The three-generated affine closure and the vertical graph ideal agree
after restricting to the ordinary overlap. -/
theorem ideals_agree_on_overlap
    (u : R₂[X])
    (E : VerticalGraph)
    (huDegree : u.natDegree ≤ 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal) :
    Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (affineIdeal u E) =
      Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        E.ideal := by
  let f :=
    N13OrdinaryCurveOverlap.affineToInfinityOverlap
  let g : InfinityCurve →+* InfinityOverlap :=
    algebraMap InfinityCurve InfinityOverlap
  let J : Ideal InfinityOverlap :=
    Ideal.map g E.ideal
  have huJ :
      g (N13IntegralInfinityReduction.integralBaseClass u) ∈ J :=
    Ideal.mem_map_of_mem g huMem
  have hmJ :
      g (N13IntegralInfinityVerticalGraphJacobian.U E) ∈ J := by
    apply Ideal.mem_map_of_mem g
    rw [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal]
    exact Ideal.subset_span (by
      left
      rfl)
  have hGJ :
      g (N13IntegralInfinityVerticalGraphJacobian.G E) ∈ J := by
    apply Ideal.mem_map_of_mem g
    rw [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal]
    exact Ideal.subset_span (by
      right
      rfl)
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · change f (affineReciprocal u) ∈ J
      rw [affineReciprocal_on_overlap u huDegree]
      exact Ideal.mul_mem_left J _ huJ
    · change f (affineVerticalEquation E) ∈ J
      rw [affineVerticalEquation_on_overlap E hmDegree]
      exact Ideal.mul_mem_left J _ hmJ
    · change f (affineLinearEquation E) ∈ J
      rw [affineLinearEquation_on_overlap E]
      exact Ideal.mul_mem_left J _ hGJ
  · rw [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.ideal,
      Ideal.map_span, Set.image_pair]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hgen :
          f (affineVerticalEquation E) ∈
            Ideal.map f (affineIdeal u E) :=
        Ideal.mem_map_of_mem f
          (Ideal.subset_span (by
            right
            left
            rfl))
      rw [affineVerticalEquation_on_overlap E hmDegree] at hgen
      exact
        (Ideal.unit_mul_mem_iff_mem
          (Ideal.map f (affineIdeal u E))
          (N13OrdinaryCurveOverlap.xOverlap_isUnit.pow 6)).mp
          (by
            simpa [N13IntegralInfinityVerticalGraphJacobian.U] using hgen)
    · have hgen :
          f (affineLinearEquation E) ∈
            Ideal.map f (affineIdeal u E) :=
        Ideal.mem_map_of_mem f
          (Ideal.subset_span (by
            right
            right
            rfl))
      rw [affineLinearEquation_on_overlap E] at hgen
      exact
        (Ideal.unit_mul_mem_iff_mem
          (Ideal.map f (affineIdeal u E))
          (N13OrdinaryCurveOverlap.xOverlap_isUnit.pow 3)).mp
          (by
            simpa [N13IntegralInfinityVerticalGraphJacobian.G,
              N13IntegralInfinityVerticalGraphJacobian.L] using hgen)
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The reflected reciprocal generator makes `x` a unit modulo the affine
vertical closure. -/
theorem affineIdeal_xUnitMod
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2) :
    N13IntegralInfinityGraphSaturation.XUnitMod
      (affineIdeal u E) := by
  let q : AffineCurve :=
    -N13GeneralizedMumfordIntegral.xClassHom
      (C (u.coeff 1) + C (u.coeff 0) * X)
  refine ⟨q, ?_⟩
  have hgen :
      affineReciprocal u ∈ affineIdeal u E :=
    Ideal.subset_span (by
      left
      rfl)
  rw [affineReciprocal,
    N13IntegralInfinityGraphSaturation.reflect_two_eq_one_add_X_mul
      u hu huDegree] at hgen
  convert hgen using 1
  simp only [q, N13OrdinaryCurveOverlap.xClass,
    N13GeneralizedMumfordIntegral.xClassHom_apply,
    map_add, map_mul, map_one]
  ring
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The three-generated affine closure is finitely generated. -/
theorem affineIdeal_fg
    (u : R₂[X])
    (E : VerticalGraph) :
    (affineIdeal u E).FG := by
  refine
    ⟨{affineReciprocal u,
        affineVerticalEquation E,
        affineLinearEquation E}, ?_⟩
  simp [affineIdeal]
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- A vertical infinity graph plus its redundant monic reciprocal equation
has an invertible affine two-chart closure. -/
theorem affineIdeal_isUnit
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal) :
    IsUnit
      (affineIdeal u E :
        N13IntegralGraphJacobian.IntegralFractionalIdeal) := by
  let K := FractionRing InfinityOverlap
  letI : Algebra AffineCurve InfinityOverlap :=
    N13OrdinaryCurveOverlap.affineToInfinityOverlap.toAlgebra
  letI : IsLocalization
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
      InfinityOverlap := by
    let e :
        N13OrdinaryCurveOverlap.AffineOverlap ≃ₐ[AffineCurve]
          InfinityOverlap :=
      { N13OrdinaryCurveOverlap.overlapEquiv with
        commutes' := fun z =>
          N13OrdinaryCurveOverlap.affineOverlapToInfinityOverlap_algebraMap z }
    exact
      IsLocalization.isLocalization_of_algEquiv
        (Submonoid.powers N13OrdinaryCurveOverlap.xClass) e
  letI : IsFractionRing AffineCurve K :=
    N13LocalizationIdealPatch.fractionRing_of_localization_fractionRing
      (A := AffineCurve) (B := InfinityOverlap) (K := K)
      (Submonoid.powers N13OrdinaryCurveOverlap.xClass)
  letI : IsFractionRing InfinityCurve K :=
    N13LocalizationIdealPatch.fractionRing_of_localization_fractionRing
      (A := InfinityCurve) (B := InfinityOverlap) (K := K)
      (Submonoid.powers N13IntegralInfinityChart.tClass)
  have hInfinityK :
      IsUnit
        (E.ideal : FractionalIdeal InfinityCurve⁰ K) := by
    let e :=
      FractionalIdeal.canonicalEquiv
        InfinityCurve⁰
        N13IntegralInfinityVerticalGraphJacobian.FunctionField K
    have hmap :=
      (N13IntegralInfinityVerticalGraphJacobian.verticalIdeal_isUnit E).map
        e.toRingHom
    change
      IsUnit
        (e
          (E.ideal :
            FractionalIdeal InfinityCurve⁰
              N13IntegralInfinityVerticalGraphJacobian.FunctionField)) at hmap
    rw [FractionalIdeal.canonicalEquiv_coeIdeal] at hmap
    exact hmap
  have hInfinityOverlap :
      IsUnit
        (Ideal.map
            (algebraMap InfinityCurve InfinityOverlap)
            E.ideal :
          FractionalIdeal InfinityOverlap⁰ K) := by
    have hmap :=
      hInfinityK.map
        (N13LocalizationIdealPatch.extendFractional
          (A := InfinityCurve) (B := InfinityOverlap) (K := K)
          (Submonoid.powers N13IntegralInfinityChart.tClass))
    rw [N13LocalizationIdealPatch.extendFractional,
      FractionalIdeal.extendedHom'_apply,
      FractionalIdeal.extended_coeIdeal_eq_map] at hmap
    exact hmap
  have hAffineOverlap :
      IsUnit
        (Ideal.map
            N13OrdinaryCurveOverlap.affineToInfinityOverlap
            (affineIdeal u E) :
          FractionalIdeal InfinityOverlap⁰ K) := by
    rw [ideals_agree_on_overlap
      u E huDegree.le hmDegree huMem]
    exact hInfinityOverlap
  have hAffineK :
      IsUnit
        (affineIdeal u E :
          FractionalIdeal AffineCurve⁰ K) := by
    apply
      N13LocalizationIdealPatch.ideal_isUnit_of_localized_isUnit
        (A := AffineCurve) (B := InfinityOverlap) (K := K)
        N13OrdinaryCurveOverlap.xClass
        (affineIdeal u E)
        (affineIdeal_fg u E)
    · obtain ⟨q, hq⟩ :=
        affineIdeal_xUnitMod u E hu huDegree
      exact ⟨q, by simpa [mul_comm] using hq⟩
    · rw [N13LocalizationIdealPatch.extendFractional,
        FractionalIdeal.extendedHom'_apply,
        FractionalIdeal.extended_coeIdeal_eq_map]
      exact hAffineOverlap
  letI : Algebra
      N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.RationalRing :=
    N13IntegralFractionalHull.integralToRational.toAlgebra
  letI : IsFractionRing
      N13IntegralFractionalHull.IntegralRing
      N13IntegralFractionalHull.FunctionField :=
    N13IntegralFractionalHull.functionField_isFractionRing
  let e :=
    FractionalIdeal.canonicalEquiv
      AffineCurve⁰ K AffineFunctionField
  have hmap := hAffineK.map e.toRingHom
  change
    IsUnit
      (e
        (affineIdeal u E :
          FractionalIdeal AffineCurve⁰ K)) at hmap
  rw [FractionalIdeal.canonicalEquiv_coeIdeal] at hmap
  exact hmap
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityVerticalGraphTwoChart
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Package a recovered vertical infinity graph and its weighted affine
closure as an actual invertible line on the two ordinary integral charts.
The reciprocal equation `u` is redundant on the overlap, but it is what
removes affine support at `x = 0` and hence makes the affine closure
invertible on the whole chart. -/
def twoChartLine
    (u : R₂[X])
    (E : VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal) :
    N13IntegralInfinityPointSpread.TwoChartLine where
  affineIdeal := affineIdeal u E
  infinityIdeal := E.ideal
  affine_isUnit :=
    affineIdeal_isUnit u E hu huDegree hmDegree huMem
  infinity_isUnit :=
    N13IntegralInfinityVerticalGraphJacobian.verticalIdeal_isUnit E
  overlap_eq :=
    ideals_agree_on_overlap u E huDegree.le hmDegree huMem
end
end MazurProof.N13IntegralInfinityVerticalGraphTwoChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialNonconstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- Translating a vertical factorization through the involution `v=t+a`
gives the horizontal semigraph equation on the infinity chart. -/
theorem translated_curve_eq
    (m w : K[X])
    (a : K)
    (hcurve :
      N13SpecialConstantInfinityVerticalGraph.verticalCurve
          (C a + X) =
        m * w) :
    (X + C a) ^ 2 +
          N13SpecialInfinityChart.hPoly * (X + C a) -
          N13SpecialInfinityChart.rhsPoly =
      translate a m * translate a w := by
  have h :=
    congrArg (fun p : K[X] => p.comp (X + C a)) hcurve
  simp only [N13SpecialConstantInfinityVerticalGraph.verticalCurve,
    pow_comp, add_comp, mul_comp, sub_comp, X_comp] at h
  rw [comp_assoc, translateLinear_comp_translateLinear, comp_X,
    comp_assoc, translateLinear_comp_translateLinear, comp_X] at h
  simpa [translate] using h
end
end MazurProof.N13SpecialNonconstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialNonconstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- The translated vertical equations form monic horizontal graph data.
This is the bridge to the completed-root divisor machinery. -/
def horizontalGraph
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hcurve :
      N13SpecialConstantInfinityVerticalGraph.verticalCurve
          (C a + X) =
        m * w) :
    N13SpecialInfinityGraphDivisor.SemiMumford where
  u := translate a m
  v := X + C a
  w := translate a w
  u_monic := hm.comp_X_add_C a
  curve_eq := translated_curve_eq m w a hcurve
end
end MazurProof.N13SpecialNonconstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13SpecialNonconstantInfinityVerticalGraph
noncomputable section
attribute [local instance] MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialNonconstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT
/-- Translation preserves the degree of a monic quadratic. -/
theorem horizontalGraph_u_natDegree
    (m w : K[X])
    (a : K)
    (hm : m.Monic)
    (hdeg : m.natDegree = 2)
    (hcurve :
      N13SpecialConstantInfinityVerticalGraph.verticalCurve
          (C a + X) =
        m * w) :
    (horizontalGraph m w a hm hcurve).u.natDegree = 2 := by
  change (m.comp (X + C a)).natDegree = 2
  rw [Polynomial.natDegree_comp, natDegree_X_add_C, hdeg]
end
end MazurProof.N13SpecialNonconstantInfinityVerticalGraph
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- Coefficient reduction sends the integral vertical substitution equation
to the corresponding equation on the special infinity chart. -/
theorem reduce_verticalCurve
    (s : R₂[X]) :
    N13IntegralInfinityReduction.reducePoly
        (N13IntegralInfinityVerticalGraphJacobian.verticalCurve s) =
      N13SpecialConstantInfinityVerticalGraph.verticalCurve
        (N13IntegralInfinityReduction.reducePoly s) := by
  rw [N13IntegralInfinityVerticalGraphJacobian.verticalCurve,
    N13SpecialConstantInfinityVerticalGraph.verticalCurve]
  change
    (X ^ 2 +
          N13IntegralInfinityChart.hBase.comp s * X -
        N13IntegralInfinityChart.rhsBase.comp s).map
          N13IntegralInfinityReduction.reduceBase =
      _
  simp only [Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_comp]
  rw [show
        N13IntegralInfinityChart.hBase.map
            N13IntegralInfinityReduction.reduceBase =
          N13SpecialInfinityChart.hPoly from
        N13IntegralInfinityReduction.reduce_hBase,
      show
        N13IntegralInfinityChart.rhsBase.map
            N13IntegralInfinityReduction.reduceBase =
          N13SpecialInfinityChart.rhsPoly from
        N13IntegralInfinityReduction.reduce_rhsBase]
  rfl
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialConstantInfinityVerticalGraph.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- When the slope `c` reduces to one, the reduced substitution is
`t=ā+v`, giving the nonconstant special vertical factorization. -/
theorem reduced_curve_eq_of_reduce_c_eq_one
    (E : VerticalGraph)
    (hc :
      N13IntegralInfinityReduction.reduceBase E.c = 1) :
    N13SpecialConstantInfinityVerticalGraph.verticalCurve
          (C (N13IntegralInfinityReduction.reduceBase E.a) + X) =
      N13IntegralInfinityReduction.reducePoly E.m *
        N13IntegralInfinityReduction.reducePoly E.w := by
  have h :=
    congrArg N13IntegralInfinityReduction.reducePoly E.curve_eq
  rw [reduce_verticalCurve] at h
  simpa [N13IntegralInfinityVerticalGraphJacobian.VerticalGraph.s,
    N13IntegralInfinityReduction.reducePoly, hc] using h
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The reduced vertical quadratic remains monic. -/
theorem reduced_m_monic
    (E : VerticalGraph) :
    (N13IntegralInfinityReduction.reducePoly E.m).Monic :=
  E.m_monic.map N13IntegralInfinityReduction.reduceBase
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- A monic integral quadratic keeps degree two after reduction. -/
theorem reduced_m_natDegree
    (E : VerticalGraph)
    (hmDegree : E.m.natDegree = 2) :
    (N13IntegralInfinityReduction.reducePoly E.m).natDegree = 2 := by
  rw [N13IntegralInfinityReduction.reducePoly_apply,
    E.m_monic.natDegree_map, hmDegree]
end
end MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13InfinityLineSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The explicit special sheet-zero point at infinity. -/
def specialInfinityPlusPoint : CurvePoint :=
  Sum.inr
    ⟨0, by
      norm_num [N13GoodModelTwo.InfinityChartEquation]⟩
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine ideal of the restricted positive-infinity line is the unit
ideal, as is the affine ideal of its canonical special point pair. -/
theorem restrict_infinityPlusLine_affineIdeal :
    (N13TwoChartSpecialRestriction.restrict
      N13TwoChartLineTensor.infinityPlusLine).affineIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityPlusPoint).affineIdeal := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        N13TwoChartLineTensor.infinityPlusLine.affineIdeal =
      ⊤
  rw [
    N13TwoChartLineTensor.infinityPlusLine_affineIdeal,
    Ideal.map_top]
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13InfinityLineSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The infinity ideal of the restricted positive-infinity line is exactly
the canonical ideal of the special sheet-zero point. -/
theorem restrict_infinityPlusLine_infinityIdeal :
    (N13TwoChartSpecialRestriction.restrict
      N13TwoChartLineTensor.infinityPlusLine).infinityIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityPlusPoint).infinityIdeal := by
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.pointIdeal
          N13TwoChartLineTensor.infinityPlusPoint) =
      N13SpecialDivisorCharts.infinityPointIdeal 0 0
  simpa [N13TwoChartLineTensor.infinityPlusPoint] using
    map_pointIdeal N13TwoChartLineTensor.infinityPlusPoint
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13InfinityLineSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The explicit special sheet-one point at infinity. -/
def specialInfinityMinusPoint : CurvePoint :=
  Sum.inr
    ⟨1, by
      exact
        (N13GoodModelTwo.infinityChartEquation_zero_iff_fixed
          (K := N13GoodModelTwo.F2) 1).2 (by norm_num)⟩
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine ideal of the restricted negative-infinity line is also the
unit ideal. -/
theorem restrict_infinityMinusLine_affineIdeal :
    (N13TwoChartSpecialRestriction.restrict
      N13TwoChartLineTensor.infinityMinusLine).affineIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityMinusPoint).affineIdeal := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        N13TwoChartLineTensor.infinityMinusLine.affineIdeal =
      ⊤
  rw [
    N13TwoChartLineTensor.infinityMinusLine_affineIdeal,
    Ideal.map_top]
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13InfinityLineSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13InfinityLineSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The negative-infinity line remembers its sheet: its ordinate `-1`
reduces to `1` in characteristic two. -/
theorem restrict_infinityMinusLine_infinityIdeal :
    (N13TwoChartSpecialRestriction.restrict
      N13TwoChartLineTensor.infinityMinusLine).infinityIdeal =
      (N13SpecialDivisorCharts.point
        specialInfinityMinusPoint).infinityIdeal := by
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.pointIdeal
          N13TwoChartLineTensor.infinityMinusPoint) =
      N13SpecialDivisorCharts.infinityPointIdeal 0 1
  simpa [N13TwoChartLineTensor.infinityMinusPoint,
    N13IntegralInfinityReduction.reduceBase,
    N13GeneralizedMumfordReduction.reduceBase] using
    map_pointIdeal N13TwoChartLineTensor.infinityMinusPoint
end
end MazurProof.N13InfinityLineSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13EscapingPointSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13EscapingPointSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The reduced affine-chart ideal of an escaping point line is the unit
ideal because its horizontal generator `1-t₀x` reduces to `1`. -/
theorem restrict_nonintegralPointLine_affineIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13IntegralInfinityPointSpread.nonintegralPointLine
        x y hx hxy)).affineIdeal =
      (N13SpecialDivisorCharts.point
        (N13ProperCurveReduction.reduceNonintegralAffine
          x y hx hxy)).affineIdeal := by
  let P : N13IntegralInfinityPointSpread.IntegralInfinityPoint :=
    N13ProperCurveReduction.nonintegralInfinityLift x y hx hxy
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.affinePointIdeal P) =
      ⊤
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (N13IntegralInfinityPointSpread.affineU P)
          (N13IntegralInfinityPointSpread.affineV P)) =
      ⊤
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal]
  have ht :
      N13GeneralizedMumfordReduction.reduceBase P.1.1 = 0 := by
    exact
      N13IntegralInfinityPointSpread.nonintegralLift_t_residue_eq_zero
        x y hx hxy
  have hu :
      N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityPointSpread.affineU P) = 1 := by
    simp [N13IntegralInfinityPointSpread.affineU,
      N13GeneralizedMumfordReduction.reducePoly_apply, ht]
  rw [hu, Ideal.eq_top_iff_one]
  exact
    N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
      1
      (N13GeneralizedMumfordReduction.reducePoly
        (N13IntegralInfinityPointSpread.affineV P))
end
end MazurProof.N13EscapingPointSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13EscapingPointSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13EscapingPointSpecialRestriction.instFactPrimeOfNatNat_fLT
/-- The reduced infinity-chart ideal is exactly the canonical ideal of the
properly reduced point at infinity. -/
theorem restrict_nonintegralPointLine_infinityIdeal
    (x y : Q₂)
    (hx : x.valuation < 0)
    (hxy : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13IntegralInfinityPointSpread.nonintegralPointLine
        x y hx hxy)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        (N13ProperCurveReduction.reduceNonintegralAffine
          x y hx hxy)).infinityIdeal := by
  let P : N13IntegralInfinityPointSpread.IntegralInfinityPoint :=
    N13ProperCurveReduction.nonintegralInfinityLift x y hx hxy
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13IntegralInfinityPointSpread.pointIdeal P) =
      N13SpecialDivisorCharts.infinityPointIdeal
        0
        (N13IntegralInfinityReduction.reduceBase P.1.2)
  rw [N13InfinityLineSpecialRestriction.map_pointIdeal]
  congr 2
  exact
    N13IntegralInfinityPointSpread.nonintegralLift_t_residue_eq_zero
      x y hx hxy
end
end MazurProof.N13EscapingPointSpecialRestriction
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
/-- The two-adic coefficient ring of the integral point graph. -/
abbrev R₂ : Type :=
  N13GeneralizedMumfordReduction.R₂
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT
/-- The literal linear graph ideal of the reduced affine point. -/
def reducedPointIdeal (P : IntegralPoint) : Ideal SpecialRing :=
  N13GoodCoordinateRingTwo.mumfordIdeal
    (X - C (PadicInt.toZMod P.1.1))
    (C (PadicInt.toZMod P.1.2))
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT
/-- Reduction of the integral affine point ideal is exactly the linear
Mumford graph of the coefficientwise reduced point.

This is an equality of ideals after base change, rather than only a
containment or a comparison of quotient cardinalities. -/
theorem map_pointIdeal_eq_reducedPointIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralAffinePointSpread.pointIdeal P) =
      reducedPointIdeal P := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂)
          (N13IntegralAffinePointSpread.pointU P)
          (N13IntegralAffinePointSpread.pointV P)) =
      reducedPointIdeal P
  rw [N13GeneralizedMumfordReduction.map_mumfordIdeal]
  simp [reducedPointIdeal,
    N13IntegralAffinePointSpread.pointU,
    N13IntegralAffinePointSpread.pointV,
    N13GeneralizedMumfordReduction.reducePoly_apply,
    N13GeneralizedMumfordReduction.reduceBase]
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped Sym2
namespace MazurProof.N13IntegralAffinePointSpecialClass
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The affine component of the proper integral point line has the same exact
special graph as the stored integral point.

The contracted infinity ideal supplies proper gluing but does not alter this
affine reduction equality. -/
theorem map_integralPointTwoChartLine_affineIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P).affineIdeal =
      reducedPointIdeal P := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralAffinePointSpread.pointIdeal P) =
      reducedPointIdeal P
  exact map_pointIdeal_eq_reducedPointIdeal P
end
end MazurProof.N13IntegralAffinePointSpecialClass
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- An ideal containing `1-t a` is already saturated with respect to powers
of `t`.

Indeed, if `tⁿz` belongs to the ideal, multiplication by `aⁿ` recovers `z`
modulo the ideal because `(ta)ⁿ=1` there. -/
theorem under_map_eq_of_one_sub_t_mul_mem
    (J : Ideal InfinityCurve)
    (a : InfinityCurve)
    (hunit :
      1 - N13IntegralInfinityChart.tClass * a ∈ J) :
    (Ideal.map
      (algebraMap InfinityCurve InfinityOverlap) J).under
        InfinityCurve =
      J := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap InfinityCurve InfinityOverlap z ∈
        Ideal.map (algebraMap InfinityCurve InfinityOverlap) J at hz
    obtain ⟨m, hm, hmz⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Submonoid.powers N13IntegralInfinityChart.tClass)
        InfinityOverlap J z).mp hz
    obtain ⟨n, hn⟩ :=
      (Submonoid.mem_powers_iff
        m N13IntegralInfinityChart.tClass).mp hm
    rw [← hn] at hmz
    have hpow_all :
        ∀ k : ℕ,
          1 - (N13IntegralInfinityChart.tClass * a) ^ k ∈ J := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          have hmul :=
            Ideal.mul_mem_left J
              ((N13IntegralInfinityChart.tClass * a) ^ k)
              hunit
          have hadd := Ideal.add_mem J ih hmul
          convert hadd using 1
          ring
    have hpow :=
      hpow_all n
    have hmultiple :=
      Ideal.mul_mem_left J (a ^ n) hmz
    have hcorrection :=
      Ideal.mul_mem_left J z hpow
    have hadd := Ideal.add_mem J hmultiple hcorrection
    convert hadd using 1
    ring
  · exact Ideal.le_comap_map
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Weighted infinity-chart ideal of an integral affine point. -/
def weightedInfinityIdeal (P : IntegralPoint) : Ideal InfinityCurve :=
  Ideal.span
    {1 -
        N13IntegralInfinityReduction.integralBaseClass (C P.1.1) *
          N13IntegralInfinityChart.tClass,
      N13IntegralInfinityChart.vClass -
        N13IntegralInfinityReduction.integralBaseClass (C P.1.2) *
          N13IntegralInfinityChart.tClass ^ 3}
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
/-- Multiplying two generators by units does not change the ideal they
generate. -/
private theorem span_pair_unit_mul
    {A : Type*} [CommRing A]
    (u v : Aˣ) (a b : A) :
    Ideal.span ({(u : A) * a, (v : A) * b} : Set A) =
      Ideal.span ({a, b} : Set A) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      have hmem :
          ((u⁻¹ : Aˣ) : A) * ((u : A) * a) ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.mul_mem_left _ _
          (Ideal.subset_span (by simp))
      simpa [mul_assoc] using hmem
    · rw [hz]
      have hmem :
          ((v⁻¹ : Aˣ) : A) * ((v : A) * b) ∈
            Ideal.span ({(u : A) * a, (v : A) * b} : Set A) :=
        Ideal.mul_mem_left _ _
          (Ideal.subset_span (by simp))
      simpa [mul_assoc] using hmem
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The weighted infinity ideal and the affine point ideal have the same
extension to the ordinary overlap. -/
theorem map_weightedInfinityIdeal (P : IntegralPoint) :
    Ideal.map
        (algebraMap InfinityCurve InfinityOverlap)
        (weightedInfinityIdeal P) =
      Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap
        (N13IntegralAffinePointSpread.pointIdeal P) := by
  simp [weightedInfinityIdeal,
    N13IntegralAffinePointSpread.pointIdeal,
    N13IntegralAffinePointSpread.integralSemiGraph,
    N13IntegralAffinePointSpread.pointU,
    N13IntegralAffinePointSpread.pointV,
    N13GeneralizedMumfordIntegral.mumfordIdeal,
    N13GeneralizedMumfordIntegral.ySubClass,
    Ideal.map_span, Set.image_pair,
    N13IntegralInfinityReduction.integralBaseClass,
    N13GeneralizedMumfordIntegral.xClass,
    N13GeneralizedMumfordIntegral.mk,
    N13OrdinaryCurveOverlap.affineYImage,
    N13OrdinaryCurveOverlap.affineCoeffMap,
    N13OrdinaryCurveOverlap.coefficientToInfinityOverlap]
  change
    Ideal.span
        {1 -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
              N13OrdinaryCurveOverlap.tOverlap,
          N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
              N13OrdinaryCurveOverlap.tOverlap ^ 3} =
      Ideal.span
        {N13OrdinaryCurveOverlap.xOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1,
          N13OrdinaryCurveOverlap.xOverlap ^ 3 *
              N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2}
  let ux : InfinityOverlapˣ :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit
  have hux :
      (ux : InfinityOverlap) =
        N13OrdinaryCurveOverlap.xOverlap :=
    N13OrdinaryCurveOverlap.xOverlap_isUnit.unit_spec
  have hfirst :
      N13OrdinaryCurveOverlap.xOverlap -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 =
        (ux : InfinityOverlap) *
          (1 -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
              N13OrdinaryCurveOverlap.tOverlap) := by
    rw [hux]
    linear_combination
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
        N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  have hsecond :
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 =
        ((ux ^ 3 : InfinityOverlapˣ) : InfinityOverlap) *
          (N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
              N13OrdinaryCurveOverlap.tOverlap ^ 3) := by
    change
      N13OrdinaryCurveOverlap.xOverlap ^ 3 *
            N13OrdinaryCurveOverlap.vOverlap -
          N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 =
        (ux : InfinityOverlap) ^ 3 *
          (N13OrdinaryCurveOverlap.vOverlap -
            N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
              N13OrdinaryCurveOverlap.tOverlap ^ 3)
    rw [hux]
    linear_combination
      N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
        (N13OrdinaryCurveOverlap.xOverlap ^ 2 *
        N13OrdinaryCurveOverlap.tOverlap ^ 2 +
        N13OrdinaryCurveOverlap.xOverlap *
          N13OrdinaryCurveOverlap.tOverlap +
        1) *
        N13OrdinaryCurveOverlap.tOverlap_mul_xOverlap
  rw [hfirst, hsecond]
  exact
    (span_pair_unit_mul
      ux (ux ^ 3)
      (1 -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.1 *
          N13OrdinaryCurveOverlap.tOverlap)
      (N13OrdinaryCurveOverlap.vOverlap -
        N13OrdinaryCurveOverlap.coefficientToInfinityOverlap P.1.2 *
          N13OrdinaryCurveOverlap.tOverlap ^ 3)).symm
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The horizontal weighted equation explicitly makes `t` invertible modulo
the weighted ideal. -/
theorem one_sub_t_mul_mem_weightedInfinityIdeal
    (P : IntegralPoint) :
    1 -
        N13IntegralInfinityChart.tClass *
          N13IntegralInfinityReduction.integralBaseClass (C P.1.1) ∈
      weightedInfinityIdeal P := by
  have hgen :
      1 -
          N13IntegralInfinityReduction.integralBaseClass (C P.1.1) *
            N13IntegralInfinityChart.tClass ∈
        weightedInfinityIdeal P :=
    Ideal.subset_span (by simp)
  simpa [mul_comm] using hgen
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- The weighted point ideal has no additional component supported at
`t=0`; extending to the overlap and contracting returns it unchanged. -/
theorem under_map_weightedInfinityIdeal
    (P : IntegralPoint) :
    (Ideal.map
      (algebraMap InfinityCurve InfinityOverlap)
      (weightedInfinityIdeal P)).under InfinityCurve =
        weightedInfinityIdeal P :=
  under_map_eq_of_one_sub_t_mul_mem
    (weightedInfinityIdeal P)
    (N13IntegralInfinityReduction.integralBaseClass (C P.1.1))
    (one_sub_t_mul_mem_weightedInfinityIdeal P)
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- The abstract contracted infinity closure of a finite affine point is
exactly its explicit weighted infinity ideal. -/
theorem infinityClosure_pointIdeal
    (P : IntegralPoint) :
    N13FiniteAffineTwoChart.infinityClosure
        (N13IntegralAffinePointSpread.pointIdeal P) =
      weightedInfinityIdeal P := by
  rw [N13FiniteAffineTwoChart.infinityClosure,
    ← map_weightedInfinityIdeal P]
  exact under_map_weightedInfinityIdeal P
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Reduction of the integral weighted ideal is exactly the weighted ideal
with reduced coordinates. -/
theorem map_weightedInfinityIdeal_reduce
    (P : IntegralPoint) :
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (weightedInfinityIdeal P) =
      reducedWeightedInfinityIdeal P := by
  simp [weightedInfinityIdeal, reducedWeightedInfinityIdeal,
    Ideal.map_span, Set.image_pair,
    N13IntegralInfinityReduction.reduce_integralBaseClass,
    N13IntegralInfinityReduction.reducePoly,
    N13IntegralInfinityReduction.reduceBase,
    N13IntegralInfinityReduction.specialBaseClass]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteAffinePointInfinityClosure.instFactPrimeOfNatNat_fLT
/-- At the unit horizontal coordinate, the weighted point equations
`(1-t, v-bt³)` generate the same ideal as the ordinary point equations
`(t-1, v-b)`. -/
theorem reducedWeightedUnit_eq_infinityPointIdeal
    (b : N13GoodModelTwo.F2) :
    Ideal.span
        {1 - N13SpecialInfinityChart.tClass,
          N13SpecialInfinityChart.vClass -
            N13IntegralInfinityReduction.specialBaseClass (C b) *
              N13SpecialInfinityChart.tClass ^ 3} =
      N13SpecialDivisorCharts.infinityPointIdeal 1 b := by
  let t := N13SpecialInfinityChart.tClass
  let v := N13SpecialInfinityChart.vClass
  let c :=
    N13IntegralInfinityReduction.specialBaseClass (C b)
  let I : Ideal N13IntegralInfinityReduction.SpecialRing :=
    Ideal.span {1 - t, v - c * t ^ 3}
  let J : Ideal N13IntegralInfinityReduction.SpecialRing :=
    Ideal.span {t - 1, v - c}
  change I = J
  have honeI : 1 - t ∈ I :=
    Ideal.subset_span (by simp)
  have hvI : v - c * t ^ 3 ∈ I :=
    Ideal.subset_span (by simp)
  have htJ : t - 1 ∈ J :=
    Ideal.subset_span (by simp)
  have hvJ : v - c ∈ J :=
    Ideal.subset_span (by simp)
  have htI : t - 1 ∈ I := by
    have hmem := Ideal.mul_mem_left I (-1) honeI
    convert hmem using 1
    ring
  have honeJ : 1 - t ∈ J := by
    have hmem := Ideal.mul_mem_left J (-1) htJ
    convert hmem using 1
    ring
  have ht3I : t ^ 3 - 1 ∈ I := by
    have hmem :=
      Ideal.mul_mem_left I (t ^ 2 + t + 1) htI
    convert hmem using 1
    ring
  have hone3J : 1 - t ^ 3 ∈ J := by
    have hmem :=
      Ideal.mul_mem_left J (t ^ 2 + t + 1) honeJ
    convert hmem using 1
    ring
  have hvPlainI : v - c ∈ I := by
    have h₁ := hvI
    have h₂ := Ideal.mul_mem_left I c ht3I
    have hmem := Ideal.add_mem I h₁ h₂
    convert hmem using 1
    ring
  have hvWeightedJ : v - c * t ^ 3 ∈ J := by
    have h₁ := hvJ
    have h₂ := Ideal.mul_mem_left J c hone3J
    have hmem := Ideal.add_mem J h₁ h₂
    convert hmem using 1
    ring
  have hIJ : I = J := by
    apply le_antisymm
    · exact Ideal.span_le.mpr (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact honeJ
        · exact hvWeightedJ)
    · exact Ideal.span_le.mpr (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact htI
        · exact hvPlainI)
  rw [hIJ]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteAffinePointInfinityClosure.instFactPrimeOfNatNat_fLT
/-- If the affine horizontal coordinate reduces to zero, the weighted
infinity ideal reduces to the unit ideal, as the point is absent from that
chart. -/
theorem reducedWeightedInfinityIdeal_eq_top
    (P : IntegralPoint)
    (ha :
      N13GeneralizedMumfordReduction.reduceBase P.1.1 = 0) :
    reducedWeightedInfinityIdeal P = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hgen :
      1 -
          N13IntegralInfinityReduction.specialBaseClass
              (C (N13GeneralizedMumfordReduction.reduceBase P.1.1)) *
            N13SpecialInfinityChart.tClass ∈
        reducedWeightedInfinityIdeal P :=
    Ideal.subset_span (by simp)
  simpa [ha, N13IntegralInfinityReduction.specialBaseClass] using hgen
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralInfinityReduction.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteAffinePointInfinityClosure.instFactPrimeOfNatNat_fLT
/-- The infinity component of an integral affine point line reduces exactly
to the canonical infinity-chart ideal of its reduced special point. -/
theorem map_infinityClosure_pointIdeal
    (P : IntegralPoint) :
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.infinityClosure
          (N13IntegralAffinePointSpread.pointIdeal P)) =
      (N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P)).infinityIdeal := by
  rw [infinityClosure_pointIdeal, map_weightedInfinityIdeal_reduce]
  let a :=
    N13GeneralizedMumfordReduction.reduceBase P.1.1
  let b :=
    N13GeneralizedMumfordReduction.reduceBase P.1.2
  have ha : a = 0 ∨ a = 1 :=
    N13GoodModelTwo.fixedTwo_eq_zero_or_one
      a (ZMod.pow_card a)
  rcases ha with ha | ha
  · rw [reducedWeightedInfinityIdeal_eq_top P ha]
    have ha0 :
        PadicInt.toZMod P.1.1 = 0 := by
      exact ha
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineZeroPoint, ha0]
  · have hweighted :
        reducedWeightedInfinityIdeal P =
          N13SpecialDivisorCharts.infinityPointIdeal 1 b := by
      simpa [reducedWeightedInfinityIdeal, a, b, ha,
        N13IntegralInfinityReduction.specialBaseClass] using
        reducedWeightedUnit_eq_infinityPointIdeal b
    rw [hweighted]
    have hb :
        b = PadicInt.toZMod P.1.2 := by
      rfl
    rw [hb]
    have ha1 :
        PadicInt.toZMod P.1.1 = 1 := by
      exact ha
    have ha0 :
        PadicInt.toZMod P.1.1 ≠ 0 := by
      rw [ha1]
      norm_num
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineOnePoint, ha0]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
attribute [local instance] MazurProof.N13IntegralAffinePointSpecialClass.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13FiniteAffinePointInfinityClosure.instFactPrimeOfNatNat_fLT
/-- The affine component of the integral point line reduces to the canonical
affine ideal of the same reduced point. -/
theorem restrict_integralPointTwoChartLine_affineIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).affineIdeal =
      (N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P)).affineIdeal := by
  change
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.integralPointTwoChartLine P).affineIdeal =
      _
  rw [
    N13IntegralAffinePointSpecialClass.map_integralPointTwoChartLine_affineIdeal]
  let a :=
    N13GeneralizedMumfordReduction.reduceBase P.1.1
  have ha : a = 0 ∨ a = 1 :=
    N13GoodModelTwo.fixedTwo_eq_zero_or_one
      a (ZMod.pow_card a)
  rcases ha with ha | ha
  · have ha0 :
        PadicInt.toZMod P.1.1 = 0 := by
      exact ha
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13IntegralAffinePointSpecialClass.reducedPointIdeal,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineZeroPoint,
      N13SpecialDivisorCharts.affinePointIdeal, ha0]
  · have ha1 :
        PadicInt.toZMod P.1.1 = 1 := by
      exact ha
    have ha0 :
        PadicInt.toZMod P.1.1 ≠ 0 := by
      rw [ha1]
      norm_num
    simp [N13IntegralAffinePointSpecialClass.reducedPoint,
      N13IntegralAffinePointSpecialClass.reducedPointIdeal,
      N13SpecialDivisorCharts.point,
      N13SpecialDivisorCharts.affineOnePoint,
      N13SpecialDivisorCharts.affinePointIdeal, ha0]
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FiniteAffinePointInfinityClosure
noncomputable section
/-- The infinity component of the integral point line reduces to the
canonical infinity ideal of the same reduced point. -/
theorem restrict_integralPointTwoChartLine_infinityIdeal
    (P : IntegralPoint) :
    (N13TwoChartSpecialRestriction.restrict
      (N13FiniteAffineTwoChart.integralPointTwoChartLine P)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        (N13IntegralAffinePointSpecialClass.reducedPoint P)).infinityIdeal := by
  change
    Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate
        (N13FiniteAffineTwoChart.infinityClosure
          (N13IntegralAffinePointSpread.pointIdeal P)) =
      _
  exact map_infinityClosure_pointIdeal P
end
end MazurProof.N13FiniteAffinePointInfinityClosure
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Restriction of the valuation-independent point line on the ordinary
affine chart is the canonical ideal of its properly reduced point. -/
theorem restrict_pointLine_affineIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x y hcurve)).affineIdeal =
      (N13SpecialDivisorCharts.point
        (reducedPoint x y hcurve)).affineIdeal := by
  rw [N13QuadraticTwoChartSpread.pointLine, reducedPoint]
  split
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_integralPointTwoChartLine_affineIdeal _
  · exact
      N13EscapingPointSpecialRestriction.restrict_nonintegralPointLine_affineIdeal
        x y _ hcurve
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
open scoped Sym2
namespace MazurProof.N13SplitQuadraticSpecialRestriction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
/-- Restriction of the same point line on the infinity chart is the canonical
ideal of the same properly reduced point. -/
theorem restrict_pointLine_infinityIdeal
    (x y : Q₂)
    (hcurve : N13GoodModelTwo.AffineEquation x y) :
    (N13TwoChartSpecialRestriction.restrict
      (N13QuadraticTwoChartSpread.pointLine x y hcurve)).infinityIdeal =
      (N13SpecialDivisorCharts.point
        (reducedPoint x y hcurve)).infinityIdeal := by
  rw [N13QuadraticTwoChartSpread.pointLine, reducedPoint]
  split
  · exact
      N13FiniteAffinePointInfinityClosure.restrict_integralPointTwoChartLine_infinityIdeal _
  · exact
      N13EscapingPointSpecialRestriction.restrict_nonintegralPointLine_infinityIdeal
        x y _ hcurve
end
end MazurProof.N13SplitQuadraticSpecialRestriction
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13.TwoChartTensorCompatibility
noncomputable section
open N13TwoChartPicardRealization
/-- Both special charts, not merely the affine chart, respect tensor. -/
theorem restrict_tensor (L M : Line) :
    N13TwoChartSpecialRestriction.restrict
        (N13TwoChartLineTensor.tensor L M) =
      N13SpecialDivisorCharts.tensor
        (N13TwoChartSpecialRestriction.restrict L)
        (N13TwoChartSpecialRestriction.restrict M) := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal L M
  · exact N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal L M
end
end MazurProof.N13.TwoChartTensorCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
abbrev SpecialPoint := N13SymmetricSquareTwo.CurvePoint
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
def pointPairData (L M : Line) (p q : SpecialPoint)
    (hL : N13TwoChartSpecialRestriction.restrict L = N13SpecialDivisorCharts.point p)
    (hM : N13TwoChartSpecialRestriction.restrict M = N13SpecialDivisorCharts.point q)
    (k : ℤ) : Data where
  charts := N13TwoChartLineTensor.tensor L M
  infinityOrder := k
  specialDivisor := s(p, q)
  special_affine := by
    rw [restrict_tensor, hL, hM, N13SpecialDivisorCharts.ofDivisor_mk]
  special_infinity := by
    rw [restrict_tensor, hL, hM, N13SpecialDivisorCharts.ofDivisor_mk]
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
def infinityLine (positive : Bool) : Line :=
  if positive then N13TwoChartLineTensor.infinityPlusLine
  else N13TwoChartLineTensor.infinityMinusLine
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
def infinityPoint (positive : Bool) : SpecialPoint :=
  if positive then N13InfinityLineSpecialRestriction.specialInfinityPlusPoint
  else N13InfinityLineSpecialRestriction.specialInfinityMinusPoint
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
theorem restrict_infinityLine (b : Bool) :
    N13TwoChartSpecialRestriction.restrict (infinityLine b) =
      N13SpecialDivisorCharts.point (infinityPoint b) := by
  cases b
  · exact N13TwoChartSpecialRestriction.ChartPair.ext
      N13InfinityLineSpecialRestriction.restrict_infinityMinusLine_affineIdeal
      N13InfinityLineSpecialRestriction.restrict_infinityMinusLine_infinityIdeal
  · exact N13TwoChartSpecialRestriction.ChartPair.ext
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_affineIdeal
      N13InfinityLineSpecialRestriction.restrict_infinityPlusLine_infinityIdeal
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
theorem restrict_affinePointLine (x y : Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) :
    N13TwoChartSpecialRestriction.restrict (N13QuadraticTwoChartSpread.pointLine x y h) =
      N13SpecialDivisorCharts.point (N13SplitQuadraticSpecialRestriction.reducedPoint x y h) :=
  N13TwoChartSpecialRestriction.ChartPair.ext
    (N13SplitQuadraticSpecialRestriction.restrict_pointLine_affineIdeal x y h)
    (N13SplitQuadraticSpecialRestriction.restrict_pointLine_infinityIdeal x y h)
end
end MazurProof.N13EffectiveGraphData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13EffectiveGraphData
noncomputable section
open Polynomial
open scoped Sym2
open N13TwoChartPicardRealization N13EffectiveInfinityRepair
open N13.TwoChartTensorCompatibility
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
/-- Choose which infinity section really occurs in the degree-two divisor.
The negative section gives mark -2 and the positive section gives mark -1. -/
def anchoredPointData (x y : Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) (positive : Bool) : Data :=
  pointPairData (N13QuadraticTwoChartSpread.pointLine x y h) (infinityLine positive)
    (N13SplitQuadraticSpecialRestriction.reducedPoint x y h) (infinityPoint positive)
    (restrict_affinePointLine x y h) (restrict_infinityLine positive)
    (if positive then -1 else -2)
end
end MazurProof.N13EffectiveGraphData
end
end


