-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartGram
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartGram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:06.739796+00:00
-- url     : https://prove2.me/theorems/40f619c6-9548-405f-931d-541827e2ab1c
-- title:
--   Statements Chart Gram
-- statement:
--   Definitions and structural lemmas for Statements Chart Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartGram.lean

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (maDensity)
def gramVol {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) : ℝ :=
  let w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  (Matrix.det (Matrix.of fun a b => ∑ i, star (w a i) * w b i)).re
def ChartGramMA.Statement : Prop :=
  ∀ (e n : ℕ) (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ),
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ v y') → v y ≠ 0 →
      maDensity (fun _ y' => Real.log ‖WithLp.toLp 2 (v y')‖) y =
        (e.factorial : ℝ) / Real.pi ^ e * gramVol v y / ‖WithLp.toLp 2 (v y)‖ ^ (2 * (e + 1))
end GroundTheory.Heights₂.Heights


