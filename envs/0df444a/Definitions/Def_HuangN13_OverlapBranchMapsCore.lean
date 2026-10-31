-- Prove2me | Definitions.Def_HuangN13_OverlapBranchMapsCore
-- name    : HuangN13_OverlapBranchMapsCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:19:47.543592+00:00
-- url     : https://prove2.me/theorems/9e97b14e-d18d-46da-9696-ab6d3d1cdb1a
-- title:
--   The two actual ordinary-overlap branch maps
-- statement:
--   The original ordinary-overlap maps into the positive and negative Laurent branches, with exactly the formal-curve and Laurent-evaluation map-construction prerequisites needed by their types and values.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source-owner ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Theorems.Thm_MazurProof_N13FormalInfinityChart_infinityCurve_relation

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityChart
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem includePowerRing_hPower :
    includePowerRing hPower =
      N13FormalLineBundleCech.hInfinity (R := R₂) := by
  simp [includePowerRing, hPower,
    N13FormalLineBundleCech.hInfinity,
    N13FormalLineBundleCech.tPow]
end
end MazurProof.N13FormalInfinityChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityChart
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem includePowerRing_rhsPower :
    includePowerRing rhsPower =
      N13FormalLineBundleCech.rhsInfinity (R := R₂) := by
  simp [includePowerRing, rhsPower,
    N13FormalLineBundleCech.rhsInfinity,
    N13FormalLineBundleCech.tPow]
end
end MazurProof.N13FormalInfinityChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityChart
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restriction from the complete formal chart to its punctured overlap. -/
def infinityToFormalCurve :
    InfinityCurve →+* FormalCurve :=
  AdjoinRoot.lift infinityCoeffMap
    N13FormalCurveOverlap.vClass infinityCurve_relation
end
end MazurProof.N13FormalInfinityChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityChart
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToFormalCurve_of
    (f : Power) :
    infinityToFormalCurve
        (algebraMap Power InfinityCurve f) =
      algebraMap Laurent FormalCurve
        (includePowerRing f) := by
  exact AdjoinRoot.lift_of infinityCurve_relation
end
end MazurProof.N13FormalInfinityChart
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The zero branch restricted to the punctured formal chart. -/
def branchZeroLaurent : Laurent :=
  N13FormalInfinityChart.includePowerRing branchZero
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The one branch restricted to the punctured formal chart. -/
def branchOneLaurent : Laurent :=
  N13FormalInfinityChart.includePowerRing branchOne
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZeroLaurent_relation :
    branchZeroLaurent ^ 2 +
        N13FormalLineBundleCech.hInfinity *
          branchZeroLaurent -
      N13FormalLineBundleCech.rhsInfinity = 0 := by
  have h := congrArg
    N13FormalInfinityChart.includePowerRing branchZero_relation
  simp only [map_sub, map_add, map_pow, map_mul, map_zero] at h
  simpa [branchZeroLaurent] using h
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchOneLaurent_relation :
    branchOneLaurent ^ 2 +
        N13FormalLineBundleCech.hInfinity *
          branchOneLaurent -
      N13FormalLineBundleCech.rhsInfinity = 0 := by
  have h := congrArg
    N13FormalInfinityChart.includePowerRing
      (show branchOne ^ 2 +
          N13FormalInfinityChart.hPower * branchOne -
        N13FormalInfinityChart.rhsPower = 0 by
        simpa [N13FormalInfinityChart.infinityCurvePoly] using
          branchOne_isRoot)
  simp only [map_sub, map_add, map_pow, map_mul, map_zero] at h
  simpa [branchOneLaurent] using h
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem eval₂_branchZeroLaurent :
    N13FormalCurveOverlap.formalCurvePoly.eval₂
        (RingHom.id Laurent) branchZeroLaurent = 0 := by
  simpa [N13FormalCurveOverlap.formalCurvePoly] using
    branchZeroLaurent_relation
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem eval₂_branchOneLaurent :
    N13FormalCurveOverlap.formalCurvePoly.eval₂
        (RingHom.id Laurent) branchOneLaurent = 0 := by
  simpa [N13FormalCurveOverlap.formalCurvePoly] using
    branchOneLaurent_relation
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
def evalBranchZeroLaurent : FormalCurve →+* Laurent :=
  AdjoinRoot.lift (RingHom.id Laurent) branchZeroLaurent
    eval₂_branchZeroLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
def evalBranchOneLaurent : FormalCurve →+* Laurent :=
  AdjoinRoot.lift (RingHom.id Laurent) branchOneLaurent
    eval₂_branchOneLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalOverlapSplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
def formalBranchEval : FormalCurve →+* Laurent × Laurent :=
  evalBranchZeroLaurent.prod evalBranchOneLaurent
end
end MazurProof.N13FormalOverlapSplit
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restrict an ordinary infinity-chart function to the punctured formal
overlap. -/
def infinityToFormalCurve :
    OrdinaryInfinityCurve →+* FormalCurve :=
  N13FormalInfinityChart.infinityToFormalCurve.comp
    N13IntegralInfinityChart.toFormalInfinity
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem infinityToFormalCurve_tClass :
    infinityToFormalCurve N13IntegralInfinityChart.tClass =
      algebraMap Laurent FormalCurve
        (N13FormalCurveOverlap.tPow 1) := by
  rw [infinityToFormalCurve, RingHom.comp_apply,
    N13IntegralInfinityChart.toFormalInfinity_tClass,
    N13FormalInfinityChart.infinityToFormalCurve_of,
    N13FormalInfinityChart.includePowerRing_X]
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
private theorem infinity_tClass_isUnit :
    IsUnit
      (infinityToFormalCurve
        N13IntegralInfinityChart.tClass) := by
  rw [infinityToFormalCurve_tClass]
  exact
    (tPowUnit 1).isUnit.map
      (algebraMap Laurent FormalCurve)
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OrdinaryCompletionCompatibility
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Completion of the ordinary principal open to the punctured formal
overlap. -/
def ordinaryToFormalCurve :
    OrdinaryOverlap →+* FormalCurve :=
  IsLocalization.Away.lift
    N13IntegralInfinityChart.tClass
    infinity_tClass_isUnit
end
end MazurProof.N13OrdinaryCompletionCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def overlapBranches : O →+* L × L :=
  N13TwoAdicAffineRestrictionCompatibility.laurentPairMap.comp
    (N13FormalOverlapSplit.formalBranchEval.comp
      N13OrdinaryCompletionCompatibility.ordinaryToFormalCurve)
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def positiveOverlap : O →+* L := (RingHom.fst L L).comp overlapBranches
end
end MazurProof.N13OverlapBranchCompatibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13OverlapBranchCompatibility
noncomputable section
open scoped nonZeroDivisors LaurentSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def negativeOverlap : O →+* L := (RingHom.snd L L).comp overlapBranches
end
end MazurProof.N13OverlapBranchCompatibility
end
end


