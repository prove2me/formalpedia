-- Prove2me | Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
-- name    : TunnellMap_DeferredAcceptanceAccounting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:57:52.29029+00:00
-- url     : https://prove2.me/theorems/d1e059a1-6a91-5d2b-b7d2-fe1aaa69cc7d
-- title:
--   Deferred Acceptance Accounting
-- statement:
--   Definitions and structural lemmas for Deferred Acceptance Accounting, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace DAState
variable (I : GloballyRanked K S T)
def AssignedLast (st : I.DAState) : Prop :=
  ∀ s t, st.assigned s = some t →
    0 < st.cursor s ∧
      (I.preferenceList s)[st.cursor s - 1]? = some t
def cursorTotal (st : I.DAState) : ℕ :=
  ∑ s : S, st.cursor s
noncomputable def proposalSteps (st : I.DAState) : ℕ :=
  st.remaining I - (st.run I).remaining I
def auxiliaryRecordSlots (st : I.DAState) : ℕ :=
  2 * Fintype.card S + Fintype.card T + st.queue.length
end DAState
end GloballyRanked
end TunnellMap


