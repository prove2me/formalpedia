-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:48.700676+00:00
-- url     : https://prove2.me/theorems/dda1640e-5b36-4b28-a08f-6c6f9c18978b
-- title:
--   Statements Chart Energy Symm
-- statement:
--   Definitions and structural lemmas for Statements Chart Energy Symm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartEnergySymm.lean

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
def ChartEnergySymm.Statement : Prop :=
  ∀ (e : ℕ) (A B C D : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (T : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (p : Fin e), A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ j, (T j).PosDef) →
    ∫ y : Fin e → ℂ, (hermChartPot A y - hermChartPot B y) *
        (maDensity (fun j => hermChartPot (Function.update T p C j)) y -
          maDensity (fun j => hermChartPot (Function.update T p D j)) y) =
      ∫ y : Fin e → ℂ, (hermChartPot C y - hermChartPot D y) *
        (maDensity (fun j => hermChartPot (Function.update T p A j)) y -
          maDensity (fun j => hermChartPot (Function.update T p B j)) y)
example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(1 : ℂ), 9] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (∀ j : Fin 1, ((fun _ => (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ)) j).PosDef) :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one,
    Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, fun _ => Matrix.PosDef.one⟩
example : ∀ j : Fin 2, ((![Matrix.diagonal ![(4 : ℂ), 1, 1], Matrix.diagonal ![(1 : ℂ), 1, 9]] :
    Fin 2 → Matrix (Fin (2 + 1)) (Fin (2 + 1)) ℂ) j).PosDef := by
  intro j
  fin_cases j
  · exact Matrix.posDef_diagonal_iff.mpr fun i => by fin_cases i <;> norm_num
  · exact Matrix.posDef_diagonal_iff.mpr fun i => by fin_cases i <;> norm_num
end
end GroundTheory.Heights₂.Heights


