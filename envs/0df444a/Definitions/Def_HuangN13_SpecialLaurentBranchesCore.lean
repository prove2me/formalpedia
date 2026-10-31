-- Prove2me | Definitions.Def_HuangN13_SpecialLaurentBranchesCore
-- name    : HuangN13_SpecialLaurentBranchesCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:05:39.762093+00:00
-- url     : https://prove2.me/theorems/7c52822a-bf91-44c7-84cd-e88e7bcd2c8b
-- title:
--   The two Laurent branches of the N13 good characteristic-two model
-- statement:
--   The original plus and minus maps from the good characteristic-two coordinate ring to its Laurent-series field, together with exactly their construction prerequisites.
-- source:
--   Xiang Huang, Apache-2.0. Original source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13SpecialLaurentBranches.lean; exact original prerequisites, source-owner ranges and hashes are recorded alongside the payload. Original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13FormalInfinityBranches_infinityCurvePoly_derivative_mod_x_isUnit

set_option autoImplicit false

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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def r₀ : P := powerReduce N13FormalInfinityBranches.branchZero
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def r₁ : P := powerReduce N13FormalInfinityBranches.branchOne
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₀_relation : r₀ ^ 2 + h * r₀ - rhs = 0 := by
  have he := congrArg powerReduce N13FormalInfinityBranches.branchZero_relation
  simp only [map_sub, map_add, map_pow, map_mul, map_zero, reduce_h, reduce_rhs] at he
  exact he
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₁_eq : r₁ = -h - r₀ := by
  simp [r₁, N13FormalInfinityBranches.branchOne, reduce_h, r₀]
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₁_relation : r₁ ^ 2 + h * r₁ - rhs = 0 := by
  rw [r₁_eq]
  linear_combination r₀_relation
end
end MazurProof.N13SpecialInfinityBranchJets
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
private theorem base_X : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem root_relation (r : P)
    (hr : r ^ 2 + N13SpecialInfinityBranchJets.h * r - N13SpecialInfinityBranchJets.rhs = 0) :
    N13GoodCoordinateRingTwo.curvePoly.eval₂ base (t⁻¹ ^ 3 * includeSeries r) = 0 := by
  have hl := congrArg includeSeries hr
  simp only [map_sub, map_add, map_mul, map_pow, map_zero] at hl
  have hh : includeSeries N13SpecialInfinityBranchJets.h = 1 + t ^ 2 + t ^ 3 := by
    simp [N13SpecialInfinityBranchJets.h, includeSeries, N13LaurentPolynomialOrder.parameter]
  have hrhs : includeSeries N13SpecialInfinityBranchJets.rhs = t + t ^ 2 := by
    simp [N13SpecialInfinityBranchJets.rhs, includeSeries, N13LaurentPolynomialOrder.parameter]
  rw [hh, hrhs] at hl
  have he : (t⁻¹ ^ 3 * includeSeries r) ^ 2 +
      (t⁻¹ ^ 3 + t⁻¹ + 1) * (t⁻¹ ^ 3 * includeSeries r) - (t⁻¹ ^ 5 + t⁻¹ ^ 4) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 t_ne_zero)
    calc
      t ^ 6 * ((t⁻¹ ^ 3 * includeSeries r) ^ 2 +
          (t⁻¹ ^ 3 + t⁻¹ + 1) * (t⁻¹ ^ 3 * includeSeries r) - (t⁻¹ ^ 5 + t⁻¹ ^ 4)) =
        (includeSeries r) ^ 2 + (1 + t ^ 2 + t ^ 3) * includeSeries r - (t + t ^ 2) := by
          field_simp [t_ne_zero]
          try ring
      _ = t ^ 6 * 0 := by rw [hl, mul_zero]
  simp only [N13GoodCoordinateRingTwo.curvePoly, N13GoodCoordinateRingTwo.hPoly,
    N13GoodCoordinateRingTwo.rhsPoly, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_one, map_add, map_pow, map_one, base_X]
  linear_combination he
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
def plus : R →+* L := AdjoinRoot.lift base
  (t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀)
  (root_relation _ N13SpecialInfinityBranchJets.r₀_relation)
end
end MazurProof.N13SpecialLaurentBranches
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
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
def minus : R →+* L := AdjoinRoot.lift base
  (t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₁)
  (root_relation _ N13SpecialInfinityBranchJets.r₁_relation)
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end


