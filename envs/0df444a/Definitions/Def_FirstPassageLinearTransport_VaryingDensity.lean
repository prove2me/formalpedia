-- Prove2me | Definitions.Def_FirstPassageLinearTransport_VaryingDensity
-- name    : FirstPassageLinearTransport_VaryingDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:05:42.792423+00:00
-- url     : https://prove2.me/theorems/3fb0280a-a9ac-5234-bfc0-1f2c06ee9635
-- title:
--   Varying Density
-- statement:
--   Definitions and structural lemmas for Varying Density, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/VaryingDensity.lean

import Definitions.Def_FirstPassageLinearTransport_Density
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
def assembleDyadic (S : ℕ → Set ℕ) : Set ℕ :=
  {n | n ∈ S (Nat.log 2 n)}
def shellExceptionalRatio (S : Set ℕ) (M : ℕ) : ℝ :=
  ((shellBad S M).card : ℝ) / (2 : ℝ) ^ M
end
end FirstPassageLinearTransport


