-- Prove2me | Definitions.Def_TunnellMap_DeferredAcceptance
-- name    : TunnellMap_DeferredAcceptance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:02:44.341331+00:00
-- url     : https://prove2.me/theorems/a937f9ee-5491-5cff-abc2-f98e1fe43244
-- title:
--   Deferred Acceptance
-- statement:
--   Definitions and structural lemmas for Deferred Acceptance, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K]
def DeferredAcceptanceCertificate (I : GloballyRanked K S T) (M : S ≃ T) : Prop :=
  ∀ s t, I.rank s t < I.rank s (M s) →
    I.rank (M.symm t) t < I.rank s t
section Finite
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
def proposalTargets (I : GloballyRanked K S T) (M : S ≃ T) (s : S) : Finset T :=
  insert (M s) (I.preferredTargets M s)
end Finite
end GloballyRanked
end TunnellMap


