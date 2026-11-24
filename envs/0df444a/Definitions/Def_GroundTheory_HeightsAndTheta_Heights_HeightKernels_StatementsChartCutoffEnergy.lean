-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:14.181678+00:00
-- url     : https://prove2.me/theorems/c7b27852-cda0-4990-946f-800b1714345e
-- title:
--   Statements Chart Cutoff Energy
-- statement:
--   Definitions and structural lemmas for Statements Chart Cutoff Energy, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartCutoffEnergy.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
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
def chartCutoff {D : ℕ} (k : ℕ) (y : Fin D → ℂ) : ℝ :=
  Real.smoothTransition (2 - (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2)
def ChartCutoffEnergy.Statement : Prop :=
  ∀ (n : ℕ) (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ), (∀ i, (T i).PosDef) →
    ∃ K : ℝ, ∀ k : ℕ,
      ∫ y : Fin (n + 1) → ℂ,
        ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ K
example (D k : ℕ) : chartCutoff k (0 : Fin D → ℂ) = 1 := by
  simp only [chartCutoff, Pi.zero_apply, norm_zero]
  exact Real.smoothTransition.one_of_one_le (by norm_num)
example : chartCutoff 0 (fun _ : Fin 1 => (2 : ℂ)) = 0 := by
  simp only [chartCutoff, Finset.univ_unique, Finset.sum_singleton, Complex.norm_ofNat]
  exact Real.smoothTransition.zero_of_nonpos (by norm_num)
example : ∀ i : Fin 1, ((fun _ => Matrix.diagonal ![(1 : ℂ), 4, 1]) i :
    Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef :=
  fun _ => Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num
end
end GroundTheory.Heights₂.Heights


