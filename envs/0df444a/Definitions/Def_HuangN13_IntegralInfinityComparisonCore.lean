-- Prove2me | Definitions.Def_HuangN13_IntegralInfinityComparisonCore
-- name    : HuangN13_IntegralInfinityComparisonCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:05:42.567804+00:00
-- url     : https://prove2.me/theorems/f117047c-0d8c-42cf-bafa-bd3274f6fbc5
-- title:
--   Ordinary two-chart lines and their two actual infinity expansions
-- statement:
--   The original ordinary two-chart line type and the two actual integral/rational infinity expansion homomorphisms, including only their map-construction prerequisites.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13FormalInfinityBranches_infinityCurvePoly_derivative_mod_x_isUnit
import Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_infinityOverlap_coordinate_relation
import Theorems.Thm_MazurProof_N13OrdinaryOverlapCore_affineEquation_of_infinityEquation

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13OrdinaryCurveOverlap
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem affineCurve_relation :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).eval₂
        affineCoeffMap affineYImage = 0 := by
  have h :=
    N13OrdinaryOverlapCore.affineEquation_of_infinityEquation
      tOverlap xOverlap vOverlap
      tOverlap_mul_xOverlap infinityOverlap_coordinate_relation
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    eval₂_sub, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_mul, affineCoeffMap_hPoly,
    affineCoeffMap_rhsPoly]
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
/-- Restriction of the affine coordinate ring to the ordinary infinity
principal open. -/
def affineToInfinityOverlap :
    AffineCurve →+* InfinityOverlap :=
  AdjoinRoot.lift affineCoeffMap affineYImage affineCurve_relation
end
end MazurProof.N13OrdinaryCurveOverlap
end
end

section
section
set_option autoImplicit false
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralInfinityPointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralFractionalHull.integralRationalAlgebra MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Concrete two-chart presentation of an invertible line on the ordinary
integral N13 model. -/
structure TwoChartLine where
  affineIdeal : Ideal N13IntegralGraphJacobian.IntegralRing
  infinityIdeal : Ideal InfinityCurve
  affine_isUnit :
    IsUnit
      (affineIdeal :
        N13IntegralGraphJacobian.IntegralFractionalIdeal)
  infinity_isUnit :
    IsUnit (infinityIdeal : InfinityFractionalIdeal)
  overlap_eq :
    Ideal.map
        N13OrdinaryCurveOverlap.affineToInfinityOverlap affineIdeal =
      Ideal.map
        (algebraMap InfinityCurve
          N13OrdinaryCurveOverlap.InfinityOverlap)
        infinityIdeal
end
end MazurProof.N13IntegralInfinityPointSpread
end
end
end

section
section
set_option autoImplicit false
open scoped nonZeroDivisors
namespace MazurProof.N13TwoChartPicardRealization
noncomputable section
/-- Proper line data on the ordinary affine and infinity charts. -/
abbrev Line : Type :=
  N13IntegralInfinityPointSpread.TwoChartLine
end
end MazurProof.N13TwoChartPicardRealization
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13FormalInfinityBranches.instIsAdicCompletePowerXIdeal
/-- The simple special-fibre root `v = 0` has an X-adic lift. -/
theorem exists_branch_zero :
    ∃ r : Power,
      N13FormalInfinityChart.infinityCurvePoly.IsRoot r ∧
        r ∈ xIdeal := by
  obtain ⟨r, hr, hr0⟩ :=
    HenselianRing.is_henselian
      N13FormalInfinityChart.infinityCurvePoly
      N13FormalInfinityChart.infinityCurvePoly_monic
      0 infinityCurvePoly_eval_zero_mem
      infinityCurvePoly_derivative_mod_x_isUnit
  refine ⟨r, hr, ?_⟩
  simpa using hr0
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The Hensel branch reducing to `v = 0`. -/
def branchZero : Power :=
  Classical.choose exists_branch_zero
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_isRoot :
    N13FormalInfinityChart.infinityCurvePoly.IsRoot branchZero :=
  (Classical.choose_spec exists_branch_zero).1
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchZero_relation :
    branchZero ^ 2 +
        N13FormalInfinityChart.hPower * branchZero -
      N13FormalInfinityChart.rhsPower = 0 := by
  simpa [N13FormalInfinityChart.infinityCurvePoly] using
    branchZero_isRoot
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The conjugate Hensel branch, reducing to `v = 1` modulo `(2, X)`. -/
def branchOne : Power :=
  -N13FormalInfinityChart.hPower - branchZero
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinityBranches
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem branchOne_isRoot :
    N13FormalInfinityChart.infinityCurvePoly.IsRoot branchOne := by
  have hsame :
      branchOne ^ 2 +
          N13FormalInfinityChart.hPower * branchOne -
        N13FormalInfinityChart.rhsPower =
        branchZero ^ 2 +
          N13FormalInfinityChart.hPower * branchZero -
        N13FormalInfinityChart.rhsPower := by
    unfold branchOne
    ring
  simpa [N13FormalInfinityChart.infinityCurvePoly, hsame] using
    branchZero_relation
end
end MazurProof.N13FormalInfinityBranches
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem eval₂_branchZero :
    N13FormalInfinityChart.infinityCurvePoly.eval₂
        (RingHom.id Power) branchZero = 0 := by
  simpa using branchZero_isRoot
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
theorem eval₂_branchOne :
    N13FormalInfinityChart.infinityCurvePoly.eval₂
        (RingHom.id Power) branchOne = 0 := by
  simpa using branchOne_isRoot
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Evaluation on the branch reducing to `v = 0`. -/
def evalBranchZero : InfinityCurve →+* Power :=
  AdjoinRoot.lift (RingHom.id Power) branchZero
    eval₂_branchZero
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13FormalInfinitySplit
noncomputable section
open N13FormalInfinityBranches
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Evaluation on the branch reducing to `v = 1`. -/
def evalBranchOne : InfinityCurve →+* Power :=
  AdjoinRoot.lift (RingHom.id Power) branchOne
    eval₂_branchOne
end
end MazurProof.N13FormalInfinitySplit
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
def positiveIntegralExpansion : B →+* P :=
  N13FormalInfinitySplit.evalBranchZero.comp N13IntegralInfinityChart.toFormalInfinity
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
def negativeIntegralExpansion : B →+* P :=
  N13FormalInfinitySplit.evalBranchOne.comp N13IntegralInfinityChart.toFormalInfinity
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def positiveExpansion : B →+* QP :=
  N13TwoAdicInfinityCompatibility.powerMap.comp positiveIntegralExpansion
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13InfinityChartMarking
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
def negativeExpansion : B →+* QP :=
  N13TwoAdicInfinityCompatibility.powerMap.comp negativeIntegralExpansion
end
end MazurProof.N13InfinityChartMarking
end
end
end
end
end
end
end
end


