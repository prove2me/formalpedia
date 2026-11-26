-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Transport
-- name    : FirstPassageLinearTransport_Transport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:59:34.927801+00:00
-- url     : https://prove2.me/theorems/24fc5fb5-fcaf-5690-bb4b-9fa62b368f31
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Transport.lean

import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable def transportedSources (M Y H : ℕ) (B : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range H).biUnion fun t =>
    B.biUnion fun y => taggedFiber M Y (t + 1) y
end FirstPassageLinearTransport


