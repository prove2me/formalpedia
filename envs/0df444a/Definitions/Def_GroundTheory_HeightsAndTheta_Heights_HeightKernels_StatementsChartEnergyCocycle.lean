-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyCocycle
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyCocycle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:41.128388+00:00
-- url     : https://prove2.me/theorems/9451e5e1-4e5a-4a15-bf00-59d0f7f23cff
-- title:
--   Statements Chart Energy Cocycle
-- statement:
--   Definitions and structural lemmas for Statements Chart Energy Cocycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartEnergyCocycle.lean

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
def ChartEnergyCocycle.Statement : Prop :=
  ∀ (e : ℕ) (M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → P.PosDef →
    ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M P k =
      ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M N k + ∑ k ∈ Finset.range (e + 1), chartMixedEnergy N P k
example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(1 : ℂ), 9] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) ≠
      (Matrix.diagonal ![(1 : ℂ), 9] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num,
    Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one, fun h => by
    have h1 := congrFun (congrFun h 0) 0
    norm_num at h1⟩
end
end GroundTheory.Heights₂.Heights


