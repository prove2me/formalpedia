-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:55.166937+00:00
-- url     : https://prove2.me/theorems/f36318c3-9c53-4ad5-9420-d537565a456c
-- title:
--   PLead Block Gauss Tail
-- statement:
--   Definitions and structural lemmas for PLead Block Gauss Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
namespace LeadBlockGaussTail
def halfGauss : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-(‖z‖ ^ 2 / 2)))
def entryConst : ℝ := 4 * (2 * halfGauss.toReal + Real.pi)
def ballInd (ρ : ℝ) (z : ℂ) : ℝ≥0∞ := {z : ℂ | |ρ| * ‖z‖ < 1}.indicator 1 z
def entryFn (r : ℝ) {n : ℕ} (c0 s j : Fin n) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ (if j = s then 1 else 0)) *
    ballInd (if j = c0 then r else 0) z
end LeadBlockGaussTail
end
end GroundTheory.Heights₂.Heights


