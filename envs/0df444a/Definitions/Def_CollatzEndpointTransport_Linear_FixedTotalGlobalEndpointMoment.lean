-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
-- name    : CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:54:15.310504+00:00
-- url     : https://prove2.me/theorems/d55b671b-5ad3-5f42-ad76-7253d71448d1
-- title:
--   Fixed Total Global Endpoint Moment
-- statement:
--   Definitions and structural lemmas for Fixed Total Global Endpoint Moment, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalGlobalEndpointMoment.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
local instance globalCompositionDecidableEq (N : ℕ) :
    DecidableEq (Composition N) :=
  Classical.decEq _
def levelCohortSet (M s : ℕ) (u : Fin M) :
    Finset (Composition (M - (u : ℕ))) :=
  fixedSet (M - (u : ℕ)) s
def levelSourceCard (M s : ℕ) : ℕ :=
  ∑ u : Fin M, (levelCohortSet M s u).card
def levelEndpointSet (M s : ℕ) : Finset ℕ :=
  mixedTargetSet (Finset.univ : Finset (Fin M))
    (levelCohortSet M s) (fun u => cohortEndpoint u)
def levelEndpointFiberCard (M s : ℕ) (y : ℕ) : ℕ :=
  mixedFiberCard (Finset.univ : Finset (Fin M))
    (levelCohortSet M s) (fun u => cohortEndpoint u) y
def levelCriticalNumerator (M s : ℕ) : ℝ :=
  Real.sqrt (3 ^ s) *
    ∑ y ∈ levelEndpointSet M s,
      (levelEndpointFiberCard M s y : ℝ) *
        Real.sqrt (levelEndpointFiberCard M s y)
def levelCriticalContribution (M s : ℕ) : ℝ :=
  levelCriticalNumerator M s / Real.sqrt (levelSourceCard M s)
def criticalEndpointInformation (M : ℕ) : ℝ :=
  Real.sqrt 3 / (2 ^ M : ℝ) *
    (1 + ∑ s ∈ Finset.Icc 1 M, levelCriticalContribution M s)
end
end FixedTotal
end CollatzEndpointTransport


