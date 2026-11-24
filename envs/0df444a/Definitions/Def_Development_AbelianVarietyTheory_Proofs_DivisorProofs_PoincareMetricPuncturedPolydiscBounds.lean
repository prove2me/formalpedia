-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:24.312781+00:00
-- url     : https://prove2.me/theorems/3262d4ac-be42-4039-9b9a-c6f235bde42a
-- title:
--   Poincare Metric Punctured Polydisc Bounds
-- statement:
--   Definitions and structural lemmas for Poincare Metric Punctured Polydisc Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PoincareMetricPuncturedPolydiscBounds.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
namespace GlobalTheory.PoincareBounds
def pdiag {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) : ℝ :=
  if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * tlog (z k) ^ 2)) else 1 / 2
end GlobalTheory.PoincareBounds
end


