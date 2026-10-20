-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction
-- name    : OAI_Combinatorics_MatchingEntropy_EdgeReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:36:49.508538+00:00
-- url     : https://prove2.me/theorems/ddfcac06-b696-4e19-ac76-c3f663f040d8
-- title:
--   Deleting the endpoints of an edge: perfect matchings through a forced edge
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e\in E$ has two endpoints $\ell(e)\neq r(e)$ in $V$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; write $\mathcal M(G)$ for the finite set of perfect matchings and $\mathbf 1_M\in\mathbb{R}^E$ for the indicator vector of $M$ ($\mathbf 1_M(e)=1$ if $e\in M$ and $0$ otherwise). The *perfect matching polytope* is $P(G)=\operatorname{conv}\{\mathbf 1_M:\ M\in\mathcal M(G)\}\subseteq\mathbb{R}^E$; it is empty when $G$ has no perfect matching.
--
--   For a finite set $I$, $\Delta(I)=\{w\in\mathbb{R}^I:\ w_i\ge0\text{ for all }i,\ \sum_{i\in I}w_i=1\}$ is the probability simplex, and for $p\in\mathbb{R}^{\mathcal M(G)}$ the edge-marginal (mean) vector is $\operatorname{mean}_G(p)_e=\sum_{M\in\mathcal M(G)}p_M\,\mathbf 1_M(e)$.
--
--   Fix an edge $e_0$ with endpoints $u_0=\ell(e_0)$ and $w_0=r(e_0)$. A vertex is *remaining* if it is not an endpoint of $e_0$, and an edge is *remaining* if both of its endpoints are remaining. The graph $G-\{u_0,w_0\}$ has vertex set $V'=V\setminus\{u_0,w_0\}$, edge set $E'$ consisting of the remaining edges, and the same endpoint maps; it is again a loopless multigraph.
--
--   1. *Incidence.* A remaining edge differs from $e_0$; an endpoint of a remaining edge is a remaining vertex; and a vertex is incident to an edge in $G-\{u_0,w_0\}$ if and only if it is in $G$.
--   2. *Edges of a matching.* Two edges of a perfect matching that share a vertex are equal. Consequently, if $M\in\mathcal M(G)$ contains $e_0$, every other edge of $M$ is remaining.
--   3. *Adding and removing the forced edge.* For $N\in\mathcal M(G-\{u_0,w_0\})$ the set $N\cup\{e_0\}$ is a perfect matching of $G$, and an edge $e$ belongs to it if and only if $e=e_0$, or $e$ is remaining and $e\in N$. Conversely, for $M\in\mathcal M(G)$ with $e_0\in M$, the set $M\cap E'$ is a perfect matching of $G-\{u_0,w_0\}$. These maps are mutually inverse, giving a bijection
--   $$
--   \mathcal M\big(G-\{u_0,w_0\}\big)\ \cong\ \{M\in\mathcal M(G):\ e_0\in M\},\qquad N\mapsto N\cup\{e_0\},
--   $$
--   and a perfect matching $M$ of $G$ has the form $N\cup\{e_0\}$ if and only if $e_0\in M$.
--   4. *Laws with marginal one.* If $p\in\Delta(\mathcal M(G))$ and $\operatorname{mean}_G(p)_{e_0}=1$, then $p_M=0$ for every perfect matching $M$ with $e_0\notin M$.
--   5. *Forced zeros.* If $x\in P(G)$ and $x_{e_0}=1$, then $x_e=0$ for every edge $e\neq e_0$ that is not remaining, that is, for every other edge sharing an endpoint with $e_0$.
--
--   An edge whose marginal equals $1$ is used by every perfect matching charged by a law with those marginals. The bijection then reduces questions about such laws, and about points of the polytope with $x_{e_0}=1$, to the smaller graph $G-\{u_0,w_0\}$.
--
--   **Formalization Note** The predicates are `RemainingVertex` and `RemainingEdge` (with decidability instances), and the reduced graph is `deleteEndpoints G e₀`, whose vertex and edge types are the corresponding subtypes. The maps are `addForced` and `removeForced`, packaged as the equivalence `forcedMatchingEquiv`; the remaining facts are `remainingEdge_ne`, `remaining_of_incident`, `deleteEndpoints_incident`, `matching_common_vertex`, `matching_remaining`, `mem_addForced`, `mem_addForced_remaining`, `mem_removeForced`, `range_addForced`, `law_support_of_mean_one` and `forced_coordinate_zero`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/EdgeReduction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/EdgeReduction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

namespace LooplessGraph
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def RemainingVertex (G : LooplessGraph V E) (e₀ : E) (v : V) : Prop :=
  ¬G.Incident v e₀

instance remainingVertexDecidable (G : LooplessGraph V E) (e₀ : E) (v : V) :
    Decidable (G.RemainingVertex e₀ v) := inferInstanceAs (Decidable (¬G.Incident v e₀))

def RemainingEdge (G : LooplessGraph V E) (e₀ e : E) : Prop :=
  G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)

instance remainingEdgeDecidable (G : LooplessGraph V E) (e₀ e : E) :
    Decidable (G.RemainingEdge e₀ e) := inferInstanceAs
      (Decidable (G.RemainingVertex e₀ (G.left e) ∧ G.RemainingVertex e₀ (G.right e)))

def deleteEndpoints (G : LooplessGraph V E) (e₀ : E) :
    LooplessGraph {v // G.RemainingVertex e₀ v} {e // G.RemainingEdge e₀ e} where
  left e := ⟨G.left e.val, e.property.1⟩
  right e := ⟨G.right e.val, e.property.2⟩
  loopless e he := G.loopless e.val (congrArg Subtype.val he)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remainingEdge_ne (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) : e ≠ e₀ := by
  rintro rfl
  exact he.1 (Or.inl rfl)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem remaining_of_incident (G : LooplessGraph V E) (e₀ : E)
    {e : E} (he : G.RemainingEdge e₀ e) {v : V} (hv : G.Incident v e) :
    G.RemainingVertex e₀ v := by
  rcases hv with h | h
  · exact h ▸ he.1
  · exact h ▸ he.2

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] theorem deleteEndpoints_incident (G : LooplessGraph V E) (e₀ : E)
    (v : {v // G.RemainingVertex e₀ v}) (e : {e // G.RemainingEdge e₀ e}) :
    (G.deleteEndpoints e₀).Incident v e ↔ G.Incident v.val e.val := by
  simp only [Incident, deleteEndpoints, Subtype.ext_iff]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem matching_common_vertex (G : LooplessGraph V E) (M : G.Matching)
    {e f : E} (he : e ∈ M.val) (hf : f ∈ M.val) {v : V}
    (hve : G.Incident v e) (hvf : G.Incident v f) : e=f := by
  obtain ⟨g, _, hg⟩ := M.property v
  exact (hg e ⟨he,hve⟩).trans (hg f ⟨hf,hvf⟩).symm

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in

theorem matching_remaining (G : LooplessGraph V E) (e₀ : E) (M : G.Matching)
    (h₀ : e₀ ∈ M.val) {e : E} (he : e ∈ M.val) (hne : e ≠ e₀) :
    G.RemainingEdge e₀ e := by
  constructor
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inl rfl) hv)
  · intro hv
    exact hne (G.matching_common_vertex M he h₀ (Or.inr rfl) hv)

def addForced (G : LooplessGraph V E) (e₀ : E) (N : (G.deleteEndpoints e₀).Matching) :
    G.Matching := by
  refine ⟨insert e₀ (N.val.image Subtype.val), ?_⟩
  intro v
  by_cases hv : G.Incident v e₀
  · refine ⟨e₀, ⟨by simp, hv⟩, ?_⟩
    rintro f ⟨hf,hfv⟩
    rcases Finset.mem_insert.mp hf with h | h
    · exact h
    · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp h
      exact False.elim (G.remaining_of_incident e₀ g.property hfv hv)
  · let v' : {v // G.RemainingVertex e₀ v} := ⟨v,hv⟩
    obtain ⟨f,⟨hf,hfv⟩, hu⟩ := N.property v'
    refine ⟨f.val, ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f,hf,rfl⟩),
      (G.deleteEndpoints_incident e₀ v' f).mp hfv⟩, ?_⟩
    rintro g ⟨hg,hgv⟩
    rcases Finset.mem_insert.mp hg with h | h
    · exact False.elim (hv (h ▸ hgv))
    · obtain ⟨g',hg',rfl⟩ := Finset.mem_image.mp h
      exact congrArg Subtype.val (hu g' ⟨hg', (G.deleteEndpoints_incident e₀ v' g').mpr hgv⟩)

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : E) :
    e ∈ (G.addForced e₀ N).val ↔ e=e₀ ∨ ∃ h : G.RemainingEdge e₀ e, ⟨e,h⟩ ∈ N.val := by
  simp only [addForced, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨f,hf,rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨f.property,hf⟩
  · rintro (h | ⟨h,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨e,h⟩,he,rfl⟩

omit [Fintype V] [Fintype E] in
@[simp] theorem mem_addForced_remaining (G : LooplessGraph V E) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) (e : {e // G.RemainingEdge e₀ e}) :
    e.val ∈ (G.addForced e₀ N).val ↔ e ∈ N.val := by
  rw [mem_addForced]
  simp only [G.remainingEdge_ne e₀ e.property, false_or]
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨e.property,h⟩⟩

def removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) : (G.deleteEndpoints e₀).Matching := by
  refine ⟨M.val.val.subtype (G.RemainingEdge e₀), ?_⟩
  intro v
  obtain ⟨e,⟨he,hev⟩,hu⟩ := M.val.property v.val
  have hne : e ≠ e₀ := by rintro rfl; exact v.property hev
  have hrem := G.matching_remaining e₀ M.val M.property he hne
  refine ⟨⟨e,hrem⟩, ⟨by simpa using he,
    (G.deleteEndpoints_incident e₀ v ⟨e,hrem⟩).mpr hev⟩, ?_⟩
  rintro f ⟨hf,hfv⟩
  apply Subtype.ext
  exact hu f.val ⟨by simpa using hf, (G.deleteEndpoints_incident e₀ v f).mp hfv⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem mem_removeForced (G : LooplessGraph V E) (e₀ : E)
    (M : {M : G.Matching // e₀ ∈ M.val}) (e : {e // G.RemainingEdge e₀ e}) :
    e ∈ (G.removeForced e₀ M).val ↔ e.val ∈ M.val.val := by
  simp [removeForced]

def forcedMatchingEquiv (G : LooplessGraph V E) (e₀ : E) :
    (G.deleteEndpoints e₀).Matching ≃ {M : G.Matching // e₀ ∈ M.val} where
  toFun N := ⟨G.addForced e₀ N, (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)⟩
  invFun M := G.removeForced e₀ M
  left_inv N := by
    apply Subtype.ext
    ext e
    exact (G.mem_removeForced e₀ _ e).trans (G.mem_addForced_remaining e₀ N e)
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    ext e
    rw [mem_addForced]
    constructor
    · rintro (rfl | ⟨h,he⟩)
      · exact M.property
      · exact (G.mem_removeForced e₀ M ⟨e,h⟩).mp he
    · intro he
      by_cases h : e=e₀
      · exact Or.inl h
      · exact Or.inr ⟨G.matching_remaining e₀ M.val M.property he h,
          (G.mem_removeForced e₀ M _).mpr he⟩

omit [Fintype V] [Fintype E] in
@[simp] theorem range_addForced (G : LooplessGraph V E) (e₀ : E) (M : G.Matching) :
    M ∈ Set.range (G.addForced e₀) ↔ e₀ ∈ M.val := by
  constructor
  · rintro ⟨N,rfl⟩
    exact (G.mem_addForced e₀ N e₀).mpr (Or.inl rfl)
  · intro h
    refine ⟨G.removeForced e₀ ⟨M,h⟩, ?_⟩
    exact congrArg Subtype.val ((G.forcedMatchingEquiv e₀).apply_symm_apply ⟨M,h⟩)

omit [Fintype V] [DecidableEq V] in
theorem law_support_of_mean_one (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) {e₀ : E} (he : G.mean p e₀=1)
    (M : G.Matching) (hM : e₀ ∉ M.val) : p M=0 := by
  have hz : ∑ N, p N*(1-G.indicator N e₀)=0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2]
    change 1-G.mean p e₀=0
    rw [he, sub_self]
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun N (_ : N ∈ Finset.univ) =>
      mul_nonneg (hp.1 N) (sub_nonneg.mpr (G.indicator_le_one N e₀)))).mp hz M (by simp)
  simpa [indicator,hM] using hh

omit [Fintype V] [DecidableEq V] in

theorem forced_coordinate_zero (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) {e : E}
    (hneq : e ≠ e₀) (hrem : ¬G.RemainingEdge e₀ e) : x e=0 := by
  obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
  rw [← congrFun hp.2 e]
  apply Finset.sum_eq_zero
  intro M _
  by_cases hM : e₀ ∈ M.val
  · have hh : e ∉ M.val := fun hh => hrem (G.matching_remaining e₀ M hM hh hneq)
    simp [indicator,hh]
  · rw [G.law_support_of_mean_one hp.1 (by rw [hp.2,he]) M hM,zero_mul]

end LooplessGraph

namespace LooplessGraph
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
end LooplessGraph

end MatchingEntropyBounds

end

end OAI


