-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:15.181255+00:00
-- url     : https://prove2.me/theorems/33e8ea65-006a-4d1f-b19a-56d6d9f4c70e
-- title:
--   Statements Chart Density Integrable
-- statement:
--   Definitions and structural lemmas for Statements Chart Density Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartDensityIntegrable.lean

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
def ChartDensityIntegrable.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    Integrable (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y)
example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num
example : (!![(2 : ℂ), 1; 1, 2] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef := by
  have h : (!![(2 : ℂ), 1; 1, 2] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) =
      (!![(1 : ℂ), 1; 0, 0])ᴴ * !![(1 : ℂ), 1; 0, 0] + 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  rw [h]
  exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self _) Matrix.PosDef.one
end
end GroundTheory.Heights₂.Heights


