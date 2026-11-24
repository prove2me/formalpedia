-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:41.105706+00:00
-- url     : https://prove2.me/theorems/a10b4ff8-eb96-43c7-98d3-90495875ff7a
-- title:
--   Statements Chart Mass
-- statement:
--   Definitions and structural lemmas for Statements Chart Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsChartMass.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
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
def hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (y : Fin e → ℂ) : ℝ :=
  Real.log (Real.sqrt (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ
    (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re)
def chartMass {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : ℝ :=
  ∫ y : Fin e → ℂ, maDensity (fun _ : Fin e => hermChartPot M) y
def ChartMassInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    chartMass M = chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num
example (e : ℕ) : (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ).PosDef := Matrix.PosDef.one
example (e : ℕ) (y : Fin e → ℂ) :
    hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y =
      Real.log (Real.sqrt (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)).re) := by
  simp [hermChartPot]
end
end GroundTheory.Heights₂.Heights


