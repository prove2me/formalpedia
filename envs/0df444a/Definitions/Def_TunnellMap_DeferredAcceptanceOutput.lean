-- Prove2me | Definitions.Def_TunnellMap_DeferredAcceptanceOutput
-- name    : TunnellMap_DeferredAcceptanceOutput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:26:52.82582+00:00
-- url     : https://prove2.me/theorems/0ced6e9c-a4bb-4d5a-a8e5-04b1dd0a96a5
-- title:
--   Deferred Acceptance Output
-- statement:
--   Definitions and structural lemmas for Deferred Acceptance Output, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceOutput.lean

import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_valid
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_run_queue_nil
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_run

set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
namespace DAState
variable (I : GloballyRanked K S T)
theorem exists_assigned_of_queue_nil (st : I.DAState) (hv : st.Valid I)
    (hqueue : st.queue = []) (s : S) : ∃ t, st.assigned s = some t := by
  cases hassigned : st.assigned s with
  | none =>
      have hsMem := (hv.queued_iff_unassigned s).mpr hassigned
      rw [hqueue] at hsMem
      contradiction
  | some t => exact ⟨t, rfl⟩
noncomputable def assignedTarget (st : I.DAState) (hv : st.Valid I)
    (hqueue : st.queue = []) (s : S) : T :=
  Classical.choose (exists_assigned_of_queue_nil I st hv hqueue s)
theorem assignedTarget_spec (st : I.DAState) (hv : st.Valid I)
    (hqueue : st.queue = []) (s : S) :
    st.assigned s = some (assignedTarget I st hv hqueue s) :=
  Classical.choose_spec (exists_assigned_of_queue_nil I st hv hqueue s)
theorem assignedTarget_injective (st : I.DAState) (hv : st.Valid I)
    (hqueue : st.queue = []) :
    Function.Injective (assignedTarget I st hv hqueue) := by
  intro s₁ s₂ ht
  have hheld₁ := (hv.held_iff_assigned s₁
    (assignedTarget I st hv hqueue s₁)).mpr
      (assignedTarget_spec I st hv hqueue s₁)
  have hheld₂ := (hv.held_iff_assigned s₂
    (assignedTarget I st hv hqueue s₂)).mpr
      (assignedTarget_spec I st hv hqueue s₂)
  rw [ht] at hheld₁
  exact Option.some.inj (hheld₁.symm.trans hheld₂)
noncomputable def matchingOfTerminal
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = []) : S ≃ T :=
  Equiv.ofBijective (assignedTarget I st hv hqueue)
    ((Fintype.bijective_iff_injective_and_card
      (assignedTarget I st hv hqueue)).2
        ⟨assignedTarget_injective I st hv hqueue, hcard⟩)
noncomputable def deferredAcceptanceMatching
    (hcard : Fintype.card S = Fintype.card T)
    (sourceOrder : List S) (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) : S ≃ T := by
  let st₀ := initial I sourceOrder
  let hv₀ : st₀.Valid I := initial_valid I sourceOrder hnodup hcomplete
  let st := st₀.run I
  let hv : st.Valid I := valid_run I st₀ hv₀
  let hqueue : st.queue = [] := run_queue_nil I hcard st₀ hv₀
  exact matchingOfTerminal I hcard st hv hqueue
end DAState
end GloballyRanked
end TunnellMap


