-- Prove2me | Definitions.Def_DeletionCode_ComponentBounds
-- name    : DeletionCode_ComponentBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:07:50.150726+00:00
-- url     : https://prove2.me/theorems/89b0c096-df47-406d-9470-7541259b44bf
-- title:
--   Component Bounds
-- statement:
--   Definitions and structural lemmas for Component Bounds, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentBounds.lean

import Definitions.Def_DeletionCode_RuleSetGraph
import Mathlib.Data.Fintype.Sum
set_option autoImplicit true
namespace DeletionCode.ComponentBounds
open SignedSupport SupportComponents RuleSetGraph
noncomputable instance incidentVerticesFintype {L : ℕ} (Q : Finset (Gram L → ℤ)) :
    Fintype (RuleSetVertex Q) := by
  classical
  unfold RuleSetVertex
  infer_instance
noncomputable instance componentsFintype {L : ℕ} (Q : Finset (Gram L → ℤ)) :
    Fintype (RuleSetComponents Q) := by
  classical
  exact Fintype.ofFinite (Quotient (ruleSetSetoid Q))
theorem edge_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)} (h : Q ⊆ S)
    {u v : Vertex L} (he : RuleSetEdge Q u v) : RuleSetEdge S u v := by
  obtain ⟨w, hw, g, hg, hu, hv⟩ := he
  exact ⟨w, h hw, g, hg, hu, hv⟩
theorem incident_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)} (h : Q ⊆ S)
    {v : Vertex L} (hv : Incident Q v) : Incident S v := by
  obtain ⟨u, hu | hu⟩ := hv
  · exact ⟨u, Or.inl (edge_mono h hu)⟩
  · exact ⟨u, Or.inr (edge_mono h hu)⟩
theorem connected_mono {L : ℕ} {Q S : Finset (Gram L → ℤ)} (h : Q ⊆ S)
    {u v : Vertex L} (hc : RuleSetConnected Q u v) : RuleSetConnected S u v := by
  induction hc with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (edge_mono h hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
def componentMap {L : ℕ} {Q S : Finset (Gram L → ℤ)} (h : Q ⊆ S) :
    RuleSetComponents Q → RuleSetComponents S :=
  Quotient.map (fun v => ⟨v.val, incident_mono h v.property⟩)
    (fun _ _ hc => connected_mono h hc)
def unionComponentMap {L : ℕ} (Q S : Finset (Gram L → ℤ)) :
    RuleSetComponents Q ⊕ RuleSetComponents S → RuleSetComponents (Q ∪ S) :=
  Sum.elim (componentMap Finset.subset_union_left) (componentMap Finset.subset_union_right)
end DeletionCode.ComponentBounds


