-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ApproxStep
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ApproxStep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:15.043808+00:00
-- url     : https://prove2.me/theorems/4ec5e5ba-96e5-442c-b441-94708fa8a537
-- title:
--   Approx Step
-- statement:
--   Definitions and structural lemmas for Approx Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ApproxStep.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.FixedPointApproximation
noncomputable def approx {B : Type} [CommRing B] (q : B) (σ : B →+* B) (w : B) : ℕ → B
  | 0 => 0
  | n + 1 => -w + q * σ (approx q σ w n)
end GlobalTheory.FixedPointApproximation


