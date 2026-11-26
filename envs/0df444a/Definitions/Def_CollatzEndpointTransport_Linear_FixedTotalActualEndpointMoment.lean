-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
-- name    : CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:57:13.628174+00:00
-- url     : https://prove2.me/theorems/ca337956-186e-5575-97c3-80d9e8bb590c
-- title:
--   Fixed Total Actual Endpoint Moment
-- statement:
--   Definitions and structural lemmas for Fixed Total Actual Endpoint Moment, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalActualEndpointMoment.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
def actualLevelEndpointSet (M s : ℕ) : Finset ℕ :=
  (sourceOddLevel M s).image sourceEndpoint
def actualLevelFiberCard (M s y : ℕ) : ℕ :=
  (mapFiber (sourceOddLevel M s) sourceEndpoint y).card
def actualLevelCriticalContribution (M s : ℕ) : ℝ :=
  Real.sqrt (3 ^ s) *
      (∑ y ∈ actualLevelEndpointSet M s,
        (actualLevelFiberCard M s y : ℝ) *
          Real.sqrt (actualLevelFiberCard M s y)) /
    Real.sqrt (sourceOddLevel M s).card
def actualCriticalEndpointInformation (M : ℕ) : ℝ :=
  Real.sqrt 3 / (2 ^ M : ℝ) *
    ∑ s ∈ Finset.range (M + 1),
      actualLevelCriticalContribution M s
end
end FixedTotal
end CollatzEndpointTransport


