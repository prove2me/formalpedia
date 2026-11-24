-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyIntegrable
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyIntegrable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:42.656147+00:00
-- url     : https://prove2.me/theorems/764727d9-ce64-4973-a861-979e7b182d3b
-- title:
--   Statements Chart Energy Integrable
-- statement:
--   Definitions and structural lemmas for Statements Chart Energy Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartEnergyIntegrable.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergy
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
def ChartEnergyIntegrable.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → ∀ k : ℕ,
    Integrable (fun y : Fin e → ℂ => (hermChartPot M y - hermChartPot N y) *
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y)
example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) ≠ 1 :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one, fun h => by
    have h1 := congrFun (congrFun h 0) 0
    simp at h1⟩
end
end GroundTheory.Heights₂.Heights


