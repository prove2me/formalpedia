-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
-- name    : FirstPassageLinearTransport_TimeSupportTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:00:35.333534+00:00
-- url     : https://prove2.me/theorems/55b42859-cc7f-53be-8e0f-a4fe37ed52c9
-- title:
--   Time Support Transport
-- statement:
--   Definitions and structural lemmas for Time Support Transport, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeSupportTransport.lean

import Definitions.Def_FirstPassageLinearTransport_LossTransport
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
noncomputable def lossFilteredTransportedSourcesAtTimes
    (M Y : ℕ) (times B : Finset ℕ) (D : ℚ) : Finset ℕ := by
  classical
  exact times.biUnion fun h =>
    B.biUnion fun y => lossFilteredTaggedFiber M Y h y D
end
end FirstPassageLinearTransport


