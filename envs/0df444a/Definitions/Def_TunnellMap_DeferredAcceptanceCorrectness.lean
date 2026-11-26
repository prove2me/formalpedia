-- Prove2me | Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
-- name    : TunnellMap_DeferredAcceptanceCorrectness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:09:18.823747+00:00
-- url     : https://prove2.me/theorems/2d316e66-9493-4717-a0ff-1000583c3c21
-- title:
--   Deferred Acceptance Correctness
-- statement:
--   Definitions and structural lemmas for Deferred Acceptance Correctness, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace DAState
variable (I : GloballyRanked K S T)
def Occupied (st : I.DAState) (t : T) : Prop :=
  ∃ s, st.held t = some s
structure Valid (st : I.DAState) : Prop where
  queue_nodup : st.queue.Nodup
  queued_iff_unassigned : ∀ s, s ∈ st.queue ↔ st.assigned s = none
  held_iff_assigned : ∀ s t, st.held t = some s ↔ st.assigned s = some t
  tried_occupied : ∀ s t,
    t ∈ (I.preferenceList s).take (st.cursor s) → st.Occupied I t
end DAState
end GloballyRanked
end TunnellMap


