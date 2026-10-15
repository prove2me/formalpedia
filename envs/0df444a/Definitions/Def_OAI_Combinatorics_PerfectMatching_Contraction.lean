-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
-- name    : OAI_Combinatorics_PerfectMatching_Contraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:50:52.36097+00:00
-- url     : https://prove2.me/theorems/9aa6e131-7cb6-43e7-9515-62fb2ba5c308
-- title:
--   Contracting one side of a cut and gluing perfect matchings along a common boundary edge
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$, each edge $e$ having endpoints $\ell(e)\neq r(e)$, and let $S\subseteq V$. A perfect matching is a set of edges covering every vertex exactly once.
--
--   1. *The side graph $G_S$.* This is $G$ with $V\setminus S$ contracted to one new vertex $\ast$. Its vertex set is $S\sqcup\{\ast\}$ and its edges are the edges of $G$ with at least one endpoint in $S$, each keeping its identity. An endpoint in $S$ is kept and an endpoint outside $S$ is replaced by $\ast$. Edges with both endpoints outside $S$ are discarded, so $G_S$ is again loopless. A vertex $v\in S$ is incident to $e$ in $G_S$ if and only if it is incident to $e$ in $G$, and $\ast$ is incident to $e$ if and only if $e$ crosses $S$ (has exactly one endpoint in $S$).
--   2. *Boundary edge.* For a perfect matching $M$ of $G_S$, the boundary edge $\beta_S(M)$ is the unique edge of $M$ at the contracted vertex $\ast$. It is an edge of $G$ crossing $S$.
--   3. *Lifted edges.* $L_S(M)\subseteq E$ is the set of edges of $M$ regarded as edges of $G$. Every lifted edge has an endpoint in $S$, $\beta_S(M)\in L_S(M)$, and $\beta_S(M)$ is the only edge of $L_S(M)$ crossing $S$.
--   4. *Gluing.* Let $M_1$ be a perfect matching of $G_S$ and $M_2$ a perfect matching of $G_{V\setminus S}$ with the same boundary edge, $\beta_S(M_1)=\beta_{V\setminus S}(M_2)$ in $E$. Then
--   $$
--   L_S(M_1)\cup L_{V\setminus S}(M_2)
--   $$
--   is a perfect matching of $G$. Its edges with an endpoint in $S$ are exactly those of $M_1$, and its edges with an endpoint in $V\setminus S$ are exactly those of $M_2$. The resulting gluing map sends compatible pairs $(M_1,M_2)$ to perfect matchings of $G$.
--   5. *Side map and lifted vertex sets.* $\sigma_S:V\to S\sqcup\{\ast\}$ sends $v\in S$ to itself and every other vertex to $\ast$. For $T\subseteq S\sqcup\{\ast\}$, the lifted vertex set is the preimage $\sigma_S^{-1}(T)\subseteq V$.
--
--   This is the contraction step of Edmonds' perfect matching polytope theorem. A tight odd cut splits the problem into the two smaller graphs $G_S$ and $G_{V\setminus S}$, and perfect matchings of $G$ are recovered by gluing matchings of the two sides that agree on the edge used across the cut. Lifting vertex sets transports vertex sets, and hence cuts, of a contracted graph back to $G$.
--
--   **Formalization Note** The side graph is `onSide G S`, with vertex type `Option {v // v ∈ S}` (`none` is the contracted vertex) and edge type `{e // G.left e ∈ S ∨ G.right e ∈ S}`. The boundary edge `boundaryEdge` is selected with `Classical.choose` from the unique-existence clause of the perfect matching property. The remaining names are `liftedEdges`, `glued_perfect`, `glueMatching`, `sideMap` and `liftVertices`, and the module also proves the auxiliary incidence and membership lemmas listed with it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Contraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Contraction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

/-- Contraction of the complement of S to a new vertex. Edges retain identities;
only edges with both endpoints outside S are discarded. -/
def onSide (G : LooplessGraph V E) (S : Finset V) :
    LooplessGraph (Option {v // v ∈ S}) {e // G.left e ∈ S ∨ G.right e ∈ S} where
  left e := if h : G.left e.val ∈ S then some ⟨G.left e.val, h⟩ else none
  right e := if h : G.right e.val ∈ S then some ⟨G.right e.val, h⟩ else none
  loopless e := by
    dsimp
    split_ifs with hl hr
    · intro he
      have hv := Option.some.inj he
      exact G.loopless e.val (congrArg Subtype.val hv)
    · simp
    · simp
    · rename_i hr
      exact (e.property.elim hl hr).elim

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

def boundaryEdge (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) :
    {e // G.left e ∈ S ∨ G.right e ∈ S} := Classical.choose (M.property none)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem boundaryEdge_mem (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) : G.boundaryEdge S M ∈ M.val :=
  (Classical.choose_spec (M.property none)).1.1

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem eq_boundaryEdge (G : LooplessGraph V E) (S : Finset V)
    (M : (G.onSide S).Matching) {e : {e // G.left e ∈ S ∨ G.right e ∈ S}}
    (he : e ∈ M.val) (hc : G.Crosses S e.val) : e = G.boundaryEdge S M :=
  (Classical.choose_spec (M.property none)).2 e ⟨he, (G.onSide_incident_none S e).mpr hc⟩

def liftedEdges (G : LooplessGraph V E) (S : Finset V) (M : (G.onSide S).Matching) : Finset E :=
  M.val.image Subtype.val

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

omit [Fintype E] [DecidableEq E] in
theorem crosses_of_kept_both (G : LooplessGraph V E) (S : Finset V) (e : E)
    (h₁ : G.left e ∈ S ∨ G.right e ∈ S)
    (h₂ : G.left e ∈ Sᶜ ∨ G.right e ∈ Sᶜ) : G.Crosses S e := by
  simp only [Finset.mem_compl] at h₂
  unfold Crosses
  tauto

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

def sideMap (S : Finset V) (v : V) : Option {v // v ∈ S} :=
  if h : v ∈ S then some ⟨v,h⟩ else none

def liftVertices (S : Finset V) (T : Finset (Option {v // v ∈ S})) : Finset V :=
  Finset.univ.filter (fun v => sideMap S v ∈ T)

@[simp] theorem mem_liftVertices (S : Finset V)
    (T : Finset (Option {v // v ∈ S})) (v : V) :
    v ∈ liftVertices S T ↔ sideMap S v ∈ T := by simp [liftVertices]

omit [Fintype V] in
@[simp] theorem sideMap_some (S : Finset V) (v : {v // v ∈ S}) :
    sideMap S v.val = some v := by
  simp [sideMap, v.property]

end LooplessGraph

end MatchingEntropy

end

end OAI


