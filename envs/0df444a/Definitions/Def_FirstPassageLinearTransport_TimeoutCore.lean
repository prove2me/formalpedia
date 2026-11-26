-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutCore
-- name    : FirstPassageLinearTransport_TimeoutCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:15:01.356329+00:00
-- url     : https://prove2.me/theorems/5377f0a2-b817-59d6-b740-5bb8d8d0bb81
-- title:
--   Timeout Core
-- statement:
--   Definitions and structural lemmas for Timeout Core, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Topology
noncomputable def timeoutTargetRank (K₀ : ℝ) (L m : ℕ) : ℕ :=
  ⌊movingLowRatio K₀ L * (m : ℝ)⌋₊
def LowStageTimeout (K₀ : ℝ) (L m x : ℕ) : Prop :=
  ∀ j : Fin (m + 1), 2 ^ timeoutTargetRank K₀ L m < orbit j x
end FirstPassageLinearTransport


