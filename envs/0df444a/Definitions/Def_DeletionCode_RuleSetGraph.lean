-- Prove2me | Definitions.Def_DeletionCode_RuleSetGraph
-- name    : DeletionCode_RuleSetGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:07:18.942157+00:00
-- url     : https://prove2.me/theorems/e1726487-c866-48dc-8c34-710f1129f7a8
-- title:
--   Rule Set Graph
-- statement:
--   Definitions and structural lemmas for Rule Set Graph, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleSetGraph.lean

import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.SetTheory.Cardinal.Finite
import Theorems.Thm_DeletionCode_SignedSupport_rule_support_iff
import Theorems.Thm_DeletionCode_SignedSupport_signed_graph_connected_iff
import Theorems.Thm_DeletionCode_SignedSupport_supported_iff_signed_incident

set_option autoImplicit true
namespace DeletionCode.RuleSetGraph
open Windows HeaderRecovery GeneratingModel RootSelection
open SignedSupport RuleReconstruction SupportComponents
def RuleSetEdge {L : ℕ} (Q : Finset (Gram L → ℤ)) (u v : Vertex L) : Prop :=
  ∃ rule ∈ Q, ∃ g, rule g ≠ 0 ∧ u = gramPrefix g ∧ v = gramSuffix g
def Incident {L : ℕ} (Q : Finset (Gram L → ℤ)) (v : Vertex L) : Prop :=
  ∃ w, RuleSetEdge Q v w ∨ RuleSetEdge Q w v
def RuleSetVertex {L : ℕ} (Q : Finset (Gram L → ℤ)) :=
  {v : Vertex L // Incident Q v}
def RuleSetConnected {L : ℕ} (Q : Finset (Gram L → ℤ)) : Vertex L → Vertex L → Prop :=
  Relation.EqvGen (RuleSetEdge Q)
def ruleSetSetoid {L : ℕ} (Q : Finset (Gram L → ℤ)) : Setoid (RuleSetVertex Q) where
  r := fun u v => RuleSetConnected Q u.val v.val
  iseqv := ⟨fun v => Relation.EqvGen.refl v.val,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩
abbrev RuleSetComponents {L : ℕ} (Q : Finset (Gram L → ℤ)) :=
  Quotient (ruleSetSetoid Q)
noncomputable def componentCount {L : ℕ} (Q : Finset (Gram L → ℤ)) : ℕ :=
  Nat.card (RuleSetComponents Q)
theorem rank_bubbles_eq_group {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val) (r : Fin R) :
    ruleBubbles E.family r.val = groupBubbles group r := by
  ext b
  simp only [ruleBubbles, groupBubbles, Finset.mem_filter, Finset.mem_univ, true_and]
  change E.rank b = r.val ↔ group b = r
  rw [hrank b]
  constructor
  · exact Fin.ext
  · exact congrArg (fun z : Fin R => z.val)
theorem rulesOfFamily_edge_iff {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i))
    (u v : Vertex (windowLength k)) :
    RuleSetEdge (rulesOfFamily E group) u v ↔
      signedSupportEdge E.family (windowLength k) u v := by
  classical
  constructor
  · rintro ⟨rule, hrule, g, hg, hu, hv⟩
    change rule ∈ Finset.univ.image
      (fun r => ruleSpectrum E.family (windowLength k) (groupBubbles group r)) at hrule
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hrule
    refine ⟨r.val, g, ?_, hu, hv⟩
    simpa only [rank_bubbles_eq_group E group hrank r] using hg
  · rintro ⟨i, g, hg, hu, hv⟩
    obtain ⟨b, hb, _⟩ :=
      (rule_support_iff E.family (windowLength k) H
        (ruleBubbles E.family i) (hdis i) g).mp hg
    have hbi : E.rank b = i := (Finset.mem_filter.mp hb).2
    have hri : (group b).val = i := (hrank b).symm.trans hbi
    have hsets : ruleBubbles E.family i = groupBubbles group (group b) := by
      rw [← hri]
      exact rank_bubbles_eq_group E group hrank (group b)
    refine ⟨ruleSpectrum E.family (windowLength k) (groupBubbles group (group b)),
      ?_, g, ?_, hu, hv⟩
    · exact Finset.mem_image.mpr ⟨group b, Finset.mem_univ _, rfl⟩
    · simpa only [hsets] using hg
theorem rulesOfFamily_edge_eq {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    RuleSetEdge (rulesOfFamily E group) = signedSupportEdge E.family (windowLength k) := by
  funext u v
  exact propext (rulesOfFamily_edge_iff E group hrank H hdis u v)
theorem incident_iff_supported {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i))
    (v : Vertex (windowLength k)) :
    Incident (rulesOfFamily E group) v ↔
      ∃ b, HasVertex E.family (windowLength k) b v := by
  unfold Incident
  rw [rulesOfFamily_edge_eq E group hrank H hdis]
  exact (supported_iff_signed_incident E.family (windowLength k) H hdis v).symm
def incidentVertexEquiv {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    RuleSetVertex (rulesOfFamily E group) ≃ SupportedVertex E.family (windowLength k) where
  toFun v := ⟨v.val, (incident_iff_supported E group hrank H hdis v.val).mp v.property⟩
  invFun v := ⟨v.val, (incident_iff_supported E group hrank H hdis v.val).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem rulesOfFamily_connected_iff {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i))
    (u v : Vertex (windowLength k)) :
    RuleSetConnected (rulesOfFamily E group) u v ↔
      GraphConnected E.family (windowLength k) u v := by
  unfold RuleSetConnected
  rw [rulesOfFamily_edge_eq E group hrank H hdis]
  exact signed_graph_connected_iff E.family (windowLength k) H hdis u v
noncomputable def ruleSetComponentMap {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    RuleSetComponents (rulesOfFamily E group) → GraphComponents E.family (windowLength k) :=
  Quotient.map (incidentVertexEquiv E group hrank H hdis) (fun a b hab =>
    (rulesOfFamily_connected_iff E group hrank H hdis a.val b.val).mp hab)
theorem ruleSetComponentMap_injective {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    Function.Injective (ruleSetComponentMap E group hrank H hdis) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro a b hab
  apply Quotient.sound
  apply (rulesOfFamily_connected_iff E group hrank H hdis a.val b.val).mpr
  exact Quotient.exact hab
theorem ruleSetComponentMap_surjective {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    Function.Surjective (ruleSetComponentMap E group hrank H hdis) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  refine ⟨Quotient.mk (ruleSetSetoid (rulesOfFamily E group))
    ((incidentVertexEquiv E group hrank H hdis).symm v), ?_⟩
  apply Quotient.sound
  exact Relation.EqvGen.refl v.val
noncomputable def ruleSetComponentEquiv {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    RuleSetComponents (rulesOfFamily E group) ≃ GraphComponents E.family (windowLength k) :=
  Equiv.ofBijective (ruleSetComponentMap E group hrank H hdis)
    ⟨ruleSetComponentMap_injective E group hrank H hdis,
      ruleSetComponentMap_surjective E group hrank H hdis⟩
end DeletionCode.RuleSetGraph


