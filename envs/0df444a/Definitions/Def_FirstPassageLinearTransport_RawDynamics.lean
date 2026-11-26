-- Prove2me | Definitions.Def_FirstPassageLinearTransport_RawDynamics
-- name    : FirstPassageLinearTransport_RawDynamics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:03:06.594704+00:00
-- url     : https://prove2.me/theorems/15c5587e-2417-5603-ad4b-c14187e14c0e
-- title:
--   Raw Dynamics
-- statement:
--   Definitions and structural lemmas for Raw Dynamics, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean

import Definitions.Def_FirstPassageLinearTransport_Basic
set_option autoImplicit true
namespace FirstPassageLinearTransport
def rawCollatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1
def rawOrbit (j n : ℕ) : ℕ := (rawCollatz^[j]) n
def rawTime (n k : ℕ) : ℕ := k + oddCount n k
end FirstPassageLinearTransport


