-- Prove2me | Definitions.Def_OAIW2LM004
-- name    : OAIW2LM004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T03:05:52.657037+00:00
-- url     : https://prove2.me/theorems/cb3a8461-a8ca-4c05-a382-4187221733be
-- title:
--   Definitions bundle OAIW2LM004 of the split of OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LoopMatching.fullEndpoint`, carved from OpenAI's openai/math development (OpenAI, *the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)*, OpenAI Math Release, October 2026, result family not identified here; see lean/formalization.yaml, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 1 definition and 11 theorems. The definitions and types are `OAI.MatchingEntropy.LooplessGraph.glueMatching`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, lean/OAI/Combinatorics, in whole or in part: [`PerfectMatching_Contraction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/Contraction.lean).
--
--   **Imports.** It imports the published bundle `Def_SingletonLoopMatching`; the bundles `OAIW2LM002` and `OAIW2LM003` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.BinaryMatching.Algorithm.R_partition_bracket` and `OAI.LoopMatching.fullEndpoint`.
-- source:
--   OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint), OpenAI Math Release, October 2026, https://github.com/openai/math (result family not identified here; see lean/formalization.yaml; paper: https://github.com/openai/math; Apache License 2.0); definitions carved from lean/OAI/Computability, lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_SingletonLoopMatching
import Definitions.Def_OAIW2LM002
import Definitions.Def_OAIW2LM003

section
-- module Solutions.OAIW2_LoopMatching.PerfectMatching_Contraction
attribute [-instance] _root_.OAI.MatchingEntropy.LooplessGraph.remainingEdgeDecidable _root_.OAI.MatchingEntropy.LooplessGraph.remainingVertexDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Contraction of tight odd cuts and gluing of perfect matchings and their laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph


omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem onSide_incident_some (G : LooplessGraph V E) (S : Finset V)
    (v : {v // v ∈ S}) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Incident (some v) e ↔ G.Incident v.val e.val := by
  have hf : ∀ (w : V),
      (if h : w ∈ S then some (⟨w,h⟩ : {v // v ∈ S}) else none) = some v ↔ w=v.val := by
    intro w
    by_cases hw : w ∈ S
    · simp only [hw, ↓reduceDIte, Option.some.injEq]
      exact Subtype.ext_iff
    · simp only [hw, ↓reduceDIte]
      constructor
      · intro h
        cases h
      · intro he
        exact (hw (he.symm ▸ v.property)).elim
  change ((if h : G.left e.val ∈ S then some ⟨G.left e.val,h⟩ else none) = some v ∨
    (if h : G.right e.val ∈ S then some ⟨G.right e.val,h⟩ else none) = some v) ↔ _
  rw [hf, hf]
  rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem onSide_incident_none (G : LooplessGraph V E) (S : Finset V)
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    (G.onSide S).Incident none e ↔ G.Crosses S e.val := by
  simp only [Incident, onSide, Crosses]
  by_cases hl : G.left e.val ∈ S <;> by_cases hr : G.right e.val ∈ S <;>
    simp [hl, hr]
  exact (e.property.elim hl hr).elim

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem eq_boundaryEdge (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : {e // G.left e ∈ S ∨ G.right e ∈ S}}
    (he : e ∈ M.val) (hc : G.Crosses S e.val) : e = G.boundaryEdge S M :=
  (Classical.choose_spec (M.property none)).2 e ⟨he, (G.onSide_incident_none S e).mpr hc⟩

omit [Fintype V] [Fintype E] in
theorem mem_liftedEdges (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    e.val ∈ G.liftedEdges S M ↔ e ∈ M.val := by
  simp only [liftedEdges, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    have he' : a = e := Subtype.ext he
    simpa only [he'] using ha
  · intro he
    exact ⟨e, he, rfl⟩

omit [Fintype V] [Fintype E] in
theorem liftedEdges_keep (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : E} (he : e ∈ G.liftedEdges S M) :
    G.left e ∈ S ∨ G.right e ∈ S := by
  rcases Finset.mem_image.mp he with ⟨a, _, rfl⟩
  exact a.property

omit [Fintype V] [Fintype E] in
theorem lifted_cross_eq_boundary (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : E} (he : e ∈ G.liftedEdges S M)
    (hc : G.Crosses S e) : e = (G.boundaryEdge S M).val := by
  let e' : {e // G.left e ∈ S ∨ G.right e ∈ S} := ⟨e, G.liftedEdges_keep S M he⟩
  exact congrArg Subtype.val (G.eq_boundaryEdge S M ((G.mem_liftedEdges S M e').mp he) hc)

omit [Fintype V] [Fintype E] in
theorem boundary_mem_lifted (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : (G.boundaryEdge S M).val ∈ G.liftedEdges S M :=
  (G.mem_liftedEdges S M _).mpr (G.boundaryEdge_mem S M)

omit [Fintype E] in
/-- A compatible pair only duplicates its common boundary edge. -/
theorem lifted_other_subset (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    {e : E} (he : e ∈ G.liftedEdges Sᶜ M₂)
    (hkeep : G.left e ∈ S ∨ G.right e ∈ S) : e ∈ G.liftedEdges S M₁ := by
  have hc := G.crosses_of_kept_both S e hkeep (G.liftedEdges_keep Sᶜ M₂ he)
  have hcb : G.Crosses Sᶜ e := (G.crosses_compl S e).mpr hc
  rw [G.lifted_cross_eq_boundary Sᶜ M₂ he hcb, ← heq]
  exact G.boundary_mem_lifted S M₁

omit [Fintype E] in
/-- Gluing compatible perfect matchings preserves each retained edge choice. -/
theorem mem_glued_left (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    (e : {e // G.left e ∈ S ∨ G.right e ∈ S}) :
    e.val ∈ G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂ ↔ e ∈ M₁.val := by
  simp only [Finset.mem_union]
  constructor
  · rintro (h | h)
    · exact (G.mem_liftedEdges S M₁ e).mp h
    · exact (G.mem_liftedEdges S M₁ e).mp (G.lifted_other_subset S M₁ M₂ heq h e.property)
  · intro h
    exact Or.inl ((G.mem_liftedEdges S M₁ e).mpr h)

omit [Fintype E] in
theorem mem_glued_right (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val)
    (e : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ}) :
    e.val ∈ G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂ ↔ e ∈ M₂.val := by
  simp only [Finset.mem_union]
  constructor
  · rintro (h | h)
    · have hc := G.crosses_of_kept_both S e.val (G.liftedEdges_keep S M₁ h) e.property
      have he := (G.lifted_cross_eq_boundary S M₁ h hc).trans heq
      apply (G.mem_liftedEdges Sᶜ M₂ e).mp
      rw [he]
      exact G.boundary_mem_lifted Sᶜ M₂
    · exact (G.mem_liftedEdges Sᶜ M₂ e).mp h
  · intro h
    exact Or.inr ((G.mem_liftedEdges Sᶜ M₂ e).mpr h)

omit [Fintype E] in
theorem glued_perfect (G : LooplessGraph V E) (S : Finset V)
    (M₁ : (G.onSide S).Matching) (M₂ : (G.onSide Sᶜ).Matching)
    (heq : (G.boundaryEdge S M₁).val = (G.boundaryEdge Sᶜ M₂).val) :
    G.IsPerfectMatching (G.liftedEdges S M₁ ∪ G.liftedEdges Sᶜ M₂) := by
  intro v
  by_cases hv : v ∈ S
  · obtain ⟨e, ⟨he, hev⟩, hu⟩ := M₁.property (some ⟨v,hv⟩)
    have hev' := (G.onSide_incident_some S ⟨v,hv⟩ e).mp hev
    refine ⟨e.val, ⟨(G.mem_glued_left S M₁ M₂ heq e).mpr he, hev'⟩, ?_⟩
    rintro f ⟨hf, hfv⟩
    have hk : G.left f ∈ S ∨ G.right f ∈ S := by
      rcases hfv with h | h
      · exact Or.inl (h.symm ▸ hv)
      · exact Or.inr (h.symm ▸ hv)
    let f' : {e // G.left e ∈ S ∨ G.right e ∈ S} := ⟨f,hk⟩
    have hf' : f' ∈ M₁.val := (G.mem_glued_left S M₁ M₂ heq f').mp hf
    exact congrArg Subtype.val (hu f' ⟨hf', (G.onSide_incident_some S ⟨v,hv⟩ f').mpr hfv⟩)
  · have hv' := Finset.mem_compl.mpr hv
    obtain ⟨e, ⟨he, hev⟩, hu⟩ := M₂.property (some ⟨v,hv'⟩)
    have hev' := (G.onSide_incident_some Sᶜ ⟨v,hv'⟩ e).mp hev
    refine ⟨e.val, ⟨(G.mem_glued_right S M₁ M₂ heq e).mpr he, hev'⟩, ?_⟩
    rintro f ⟨hf, hfv⟩
    have hk : G.left f ∈ Sᶜ ∨ G.right f ∈ Sᶜ := by
      rcases hfv with h | h
      · exact Or.inl (h.symm ▸ hv')
      · exact Or.inr (h.symm ▸ hv')
    let f' : {e // G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ} := ⟨f,hk⟩
    have hf' : f' ∈ M₂.val := (G.mem_glued_right S M₁ M₂ heq f').mp hf
    exact congrArg Subtype.val (hu f' ⟨hf', (G.onSide_incident_some Sᶜ ⟨v,hv'⟩ f').mpr hfv⟩)

def glueMatching (G : LooplessGraph V E) (S : Finset V)
    (z : {z : (G.onSide S).Matching × (G.onSide Sᶜ).Matching //
      (G.boundaryEdge S z.1).val = (G.boundaryEdge Sᶜ z.2).val}) : G.Matching :=
  ⟨G.liftedEdges S z.val.1 ∪ G.liftedEdges Sᶜ z.val.2,
    G.glued_perfect S z.val.1 z.val.2 z.property⟩

end LooplessGraph

end MatchingEntropy

end

end OAI
end


