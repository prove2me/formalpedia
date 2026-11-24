-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:48.994326+00:00
-- url     : https://prove2.me/theorems/fd95309c-df12-4587-a9fc-5dd14cbf5975
-- title:
--   PChart Hess Compare
-- statement:
--   Definitions and structural lemmas for PChart Hess Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
namespace ChartHessianComparison
section Gram
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}
def gramHess (u : F) (d : Fin e → F) : Matrix (Fin e) (Fin e) ℂ :=
  Matrix.of fun i j => (⟪u, u⟫_ℂ * ⟪d j, d i⟫_ℂ - ⟪u, d i⟫_ℂ * ⟪d j, u⟫_ℂ) / (2 * ⟪u, u⟫_ℂ ^ 2)
end Gram
section Chart
variable {e : ℕ} (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
def chartLin : (Fin e → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin (e + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (B *ᵥ (Fin.cons 0 y : Fin (e + 1) → ℂ))
      map_add' := fun y z => by
        have h : (Fin.cons 0 (y + z) : Fin (e + 1) → ℂ) = Fin.cons 0 y + Fin.cons 0 z := by
          funext k; refine Fin.cases ?_ (fun k => ?_) k <;> simp
        rw [h, mulVec_add, WithLp.toLp_add]
      map_smul' := fun a y => by
        have h : (Fin.cons 0 (a • y) : Fin (e + 1) → ℂ) = a • Fin.cons 0 y := by
          funext k; refine Fin.cases ?_ (fun k => ?_) k <;> simp
        rw [h, mulVec_smul, WithLp.toLp_smul]
        rfl }
def chartConst : EuclideanSpace ℂ (Fin (e + 1)) :=
  WithLp.toLp 2 (B *ᵥ (Fin.cons 1 0 : Fin (e + 1) → ℂ))
def hessForm (y x : Fin e → ℂ) : ℝ :=
  ‖chartLin B (star x) - (⟪chartConst B + chartLin B y, chartLin B (star x)⟫_ℂ /
      ⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ) • (chartConst B + chartLin B y)‖ ^ 2 /
    (2 * ‖chartConst B + chartLin B y‖ ^ 2)
end Chart
end ChartHessianComparison
end
end GroundTheory.Heights₂.Heights


