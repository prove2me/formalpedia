-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:33.145062+00:00
-- url     : https://prove2.me/theorems/37f204fd-023d-4e06-9964-6fc27e93f519
-- title:
--   Statements Chart Hess Compare
-- statement:
--   Definitions and structural lemmas for Statements Chart Hess Compare, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartHessCompare.lean

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder
noncomputable section
def ChartHessCompare.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef →
    ∃ C : ℝ, ∀ y : Fin e → ℂ, (cxHessian (hermChartPot M) y).PosDef ∧
      ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef
example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef ∧
    (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef :=
  ⟨Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num, Matrix.PosDef.one⟩
end
end GroundTheory.Heights₂.Heights


