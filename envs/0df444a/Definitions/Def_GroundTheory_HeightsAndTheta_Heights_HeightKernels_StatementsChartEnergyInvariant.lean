-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:06.91067+00:00
-- url     : https://prove2.me/theorems/cb48ef4e-f17f-4f90-8aa3-4cd3ce8b3109
-- title:
--   Statements Chart Energy Invariant
-- statement:
--   Definitions and structural lemmas for Statements Chart Energy Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartEnergyInvariant.lean

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
def ChartEnergyLinearInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M N C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef → C.det ≠ 0 → ∀ k : ℕ,
    chartMixedEnergy (Cᴴ * M * C) (Cᴴ * N * C) k = chartMixedEnergy M N k
example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (!![0, 1; 1, 0] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).det ≠ 0 :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one, by
    simp [Matrix.det_fin_two]⟩
end
end GroundTheory.Heights₂.Heights


