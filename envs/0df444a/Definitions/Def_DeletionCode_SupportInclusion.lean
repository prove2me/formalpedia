-- Prove2me | Definitions.Def_DeletionCode_SupportInclusion
-- name    : DeletionCode_SupportInclusion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:08:25.769176+00:00
-- url     : https://prove2.me/theorems/d577f3c8-886e-4b6e-87c6-d219acbfac7f
-- title:
--   Support Inclusion
-- statement:
--   Definitions and structural lemmas for Support Inclusion, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportInclusion.lean

import Definitions.Def_DeletionCode_ComponentBounds
set_option autoImplicit true
namespace DeletionCode.SupportInclusion
open SignedSupport SupportComponents RuleSetGraph
def CoordinateSupportIncluded {L : ℕ} (Q S : Finset (Gram L → ℤ)) : Prop :=
  ∀ g, (∃ w ∈ Q, w g ≠ 0) → ∃ w ∈ S, w g ≠ 0
theorem edge_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) {u v : Vertex L}
    (he : RuleSetEdge Q u v) : RuleSetEdge S u v := by
  obtain ⟨w, hw, g, hg, hu, hv⟩ := he
  obtain ⟨z, hz, hzg⟩ := hsub g ⟨w, hw, hg⟩
  exact ⟨z, hz, g, hzg, hu, hv⟩
theorem incident_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) {v : Vertex L}
    (hv : Incident Q v) : Incident S v := by
  obtain ⟨u, hu | hu⟩ := hv
  · exact ⟨u, Or.inl (edge_mono hsub hu)⟩
  · exact ⟨u, Or.inr (edge_mono hsub hu)⟩
theorem connected_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) {u v : Vertex L}
    (hc : RuleSetConnected Q u v) : RuleSetConnected S u v := by
  induction hc with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (edge_mono hsub hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
def supportComponentMap {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) :
    RuleSetComponents Q → RuleSetComponents S :=
  Quotient.map (fun v => ⟨v.val, incident_mono hsub v.property⟩)
    (fun _ _ hc => connected_mono hsub hc)
noncomputable instance hitComponentsFintype {L : ℕ} (S : Finset (Gram L → ℤ))
    (P : RuleSetComponents S → Prop) : Fintype {C : RuleSetComponents S // P C} :=
  Fintype.ofFinite _
end DeletionCode.SupportInclusion


