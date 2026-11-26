-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
-- name    : FirstPassageLinearTransport_TimeoutEndpointProfile
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:21:48.066228+00:00
-- url     : https://prove2.me/theorems/906940aa-0117-5f62-af76-00ab5ed31539
-- title:
--   Timeout Endpoint Profile
-- statement:
--   Definitions and structural lemmas for Timeout Endpoint Profile, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointProfile.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointParameters
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
noncomputable def timeoutStrengthenedFailureEnvelope
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (M L S : ℕ) (R : ℝ) : Finset ℕ :=
  timeoutSeparatedFailureEnvelope P K₀ M L S ∪
    shellMultiplicativeHit M (R / 4)
def timeoutEndpointGood
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    (A : ℕ → ℝ) (M : ℕ) : Set ℕ :=
  let L := movingTerminalRank A M
  let S := shrinkingSwitchRank P.Cswitch M
  {n | n ∉ timeoutSeparatedFailureEnvelope P.run.toTimeoutHigh P.K₀ M L S}
def timeoutStrengthenedEndpointGood
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    (A : ℕ → ℝ) (R : ℕ → ℝ) (M : ℕ) : Set ℕ :=
  let L := movingTerminalRank A M
  let S := shrinkingSwitchRank P.Cswitch M
  {n | n ∉ timeoutStrengthenedFailureEnvelope
    P.run.toTimeoutHigh P.K₀ M L S (R M)}
end
end FirstPassageLinearTransport


