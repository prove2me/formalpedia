-- Prove2me | Definitions.Def_FirstPassageLinearTransport_AdjustableEntropyRate
-- name    : FirstPassageLinearTransport_AdjustableEntropyRate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:10:48.010119+00:00
-- url     : https://prove2.me/theorems/8143fe8d-7713-5546-9e65-4497b8672e3d
-- title:
--   Adjustable Entropy Rate
-- statement:
--   Definitions and structural lemmas for Adjustable Entropy Rate, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEntropyRate.lean

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
def adjustableEntropyRate (lambda t : ℝ) : ℝ :=
  binaryBarrierRate (adjustableBarrierDisplacement lambda t)
end
end FirstPassageLinearTransport


