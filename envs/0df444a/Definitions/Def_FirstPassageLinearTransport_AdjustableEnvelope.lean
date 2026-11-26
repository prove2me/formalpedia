-- Prove2me | Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
-- name    : FirstPassageLinearTransport_AdjustableEnvelope
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:01:28.26581+00:00
-- url     : https://prove2.me/theorems/cd796eba-9985-5b79-95a3-0b6d6930d041
-- title:
--   Adjustable Envelope
-- statement:
--   Definitions and structural lemmas for Adjustable Envelope, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
def adjustableBarrierHeight (lambda t : ℝ) (M : ℕ) : ℝ :=
  lambda * t * M / logTwoThree
end
end FirstPassageLinearTransport


