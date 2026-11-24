-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSymm
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSymm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:41.447765+00:00
-- url     : https://prove2.me/theorems/9fc6f98c-e05a-4874-b5ae-5abbabd02991
-- title:
--   Statements Chart Ibp Symm
-- statement:
--   Definitions and structural lemmas for Statements Chart Ibp Symm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartIbpSymm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
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
def ChartIbpSymm.Statement : Prop :=
  ∀ (n : ℕ) (A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
    A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ i, (T i).PosDef) →
    ∫ y : Fin (n + 1) → ℂ, (hermChartPot A y - hermChartPot B y) *
        maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
          fun i => hermChartPot (T i)) y =
      ∫ y : Fin (n + 1) → ℂ, (hermChartPot C y - hermChartPot D y) *
        maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
          fun i => hermChartPot (T i)) y
example : (Matrix.diagonal ![(4 : ℂ), 1, 1] : Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef ∧
    (Matrix.diagonal ![(1 : ℂ), 1, 9] : Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef ∧
    (∀ i : Fin 1, ((fun _ => Matrix.diagonal ![(1 : ℂ), 4, 1]) i :
      Matrix (Fin (1 + 1 + 1)) (Fin (1 + 1 + 1)) ℂ).PosDef) :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one,
    Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num,
    fun _ => Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num⟩
end
end GroundTheory.Heights₂.Heights


