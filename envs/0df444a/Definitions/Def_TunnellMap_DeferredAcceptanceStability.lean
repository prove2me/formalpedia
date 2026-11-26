-- Prove2me | Definitions.Def_TunnellMap_DeferredAcceptanceStability
-- name    : TunnellMap_DeferredAcceptanceStability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:32:07.629936+00:00
-- url     : https://prove2.me/theorems/1f7de10b-16f4-5750-9880-a0463f7a9dd3
-- title:
--   Deferred Acceptance Stability
-- statement:
--   Definitions and structural lemmas for Deferred Acceptance Stability, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace DAState
variable (I : GloballyRanked K S T)
structure ProposalValid (st : I.DAState) : Prop where
  assigned_tried : ∀ s t, st.assigned s = some t →
    t ∈ (I.preferenceList s).take (st.cursor s)
  held_dominates : ∀ s t,
    t ∈ (I.preferenceList s).take (st.cursor s) →
      ∃ holder, st.held t = some holder ∧
        I.rank holder t ≤ I.rank s t
end DAState
end GloballyRanked
end TunnellMap


