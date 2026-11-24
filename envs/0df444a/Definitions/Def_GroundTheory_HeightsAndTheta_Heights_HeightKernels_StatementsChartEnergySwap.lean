-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:02.692168+00:00
-- url     : https://prove2.me/theorems/99fe73b6-7777-4c9c-8c11-596eaab7a4fe
-- title:
--   Statements Chart Energy Swap
-- statement:
--   Definitions and structural lemmas for Statements Chart Energy Swap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartEnergySwap.lean

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
def swapFirstTwo (e : ℕ) : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
  (Equiv.swap (0 : Fin (e + 1 + 1)) 1).permMatrix ℂ
def ChartEnergySwapInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ), M.PosDef → N.PosDef → ∀ k : ℕ,
    chartMixedEnergy ((swapFirstTwo e)ᴴ * M * swapFirstTwo e) ((swapFirstTwo e)ᴴ * N * swapFirstTwo e) k =
      chartMixedEnergy M N k
example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (0 + 1 + 1)) (Fin (0 + 1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (0 + 1 + 1)) (Fin (0 + 1 + 1)) ℂ).PosDef :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one⟩
example (w : ℂ) : swapFirstTwo 0 *ᵥ ![1, w] = ![w, 1] := by
  ext i
  fin_cases i <;> simp [swapFirstTwo, PEquiv.toMatrix_toPEquiv_mulVec]
example (e : ℕ) : swapFirstTwo e 0 1 = 1 := by
  simp [swapFirstTwo, PEquiv.toMatrix_apply]
end
end GroundTheory.Heights₂.Heights


