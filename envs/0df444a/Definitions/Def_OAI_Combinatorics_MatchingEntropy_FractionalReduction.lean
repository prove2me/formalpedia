-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_FractionalReduction
-- name    : OAI_Combinatorics_MatchingEntropy_FractionalReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:41:17.200451+00:00
-- url     : https://prove2.me/theorems/d4c3a342-bb17-457e-a364-07ca30401037
-- title:
--   The fractional subgraph of a point of the perfect matching polytope
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e\in E$ has two endpoints $\ell(e)\neq r(e)$ in $V$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* of $G$ is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; write $\mathcal M(G)$ for the finite set of perfect matchings and $\mathbf 1_M\in\mathbb{R}^E$ for the indicator vector of $M$ ($\mathbf 1_M(e)=1$ if $e\in M$ and $0$ otherwise). The *perfect matching polytope* is $P(G)=\operatorname{conv}\{\mathbf 1_M:\ M\in\mathcal M(G)\}\subseteq\mathbb{R}^E$; it is empty when $G$ has no perfect matching.
--
--   Let $x\in\mathbb{R}^E$. An edge $e$ is *fractional* if $0<x_e<1$; let $E_f(x)$ be the set of fractional edges. A vertex is *fractional* if it is incident to some fractional edge; let $V_f(x)$ be the set of fractional vertices.
--
--   1. *Fractional subgraph.* $G_f(x)$ is the loopless multigraph with vertex set $V_f(x)$, edge set $E_f(x)$ and the endpoints inherited from $G$ (the endpoints of a fractional edge are fractional vertices). Incidence in $G_f(x)$ coincides with incidence in $G$.
--   2. *Restriction and affine extension.* Let $x_f\in\mathbb{R}^{E_f(x)}$ be the restriction of $x$ to the fractional edges, and let $\Phi_x:\mathbb{R}^{E_f(x)}\to\mathbb{R}^E$ be the affine map
--   $$
--   (\Phi_x z)_e=\begin{cases}z_e,& e\in E_f(x),\\ x_e,& e\notin E_f(x),\end{cases}
--   $$
--   whose linear part extends a vector by zero outside $E_f(x)$. Then $(\Phi_x z)_e=z_e$ on fractional edges, $(\Phi_x z)_e=x_e$ on the other edges, and $\Phi_x(x_f)=x$.
--   3. *The integral part of a polytope point.* Suppose $x\in P(G)$. Then:
--      - every non-fractional coordinate satisfies $x_e=0$ or $x_e=1$;
--      - if $x_{e_0}=1$ and an edge $e\neq e_0$ shares a vertex with $e_0$, then $x_e=0$;
--      - no fractional vertex is incident to an edge $e$ with $x_e=1$;
--      - every vertex is incident to some edge $e$ with $x_e>0$;
--      - every non-fractional vertex is incident to exactly one edge $e$ with $x_e=1$.
--   4. *Lifting matchings.* If $x\in P(G)$ and $N$ is a perfect matching of $G_f(x)$, then
--   $$
--   N\cup\{e\in E:\ x_e=1\}
--   $$
--   is a perfect matching of $G$. An edge belongs to it if and only if it is a fractional edge in $N$ or satisfies $x_e=1$; in particular a fractional edge belongs to it if and only if it belongs to $N$.
--
--   A point of the polytope thus splits into an integral part, the edges with $x_e=1$, which form a perfect matching of the non-fractional vertices, and a fractional part living on $G_f(x)$. Perfect matchings of the fractional subgraph extend to perfect matchings of $G$ by adding the integral part, and $\Phi_x$ embeds edge vectors of $G_f(x)$ into $\mathbb{R}^E$ while freezing the integral coordinates; these are the tools for reducing questions about $x$ to its fractional subgraph.
--
--   **Formalization Note** The definitions are `FractionalVertex`, `fractionalGraph`, `fractionalMean` (the restriction $x_f$), `fractionalExtension` (the affine map $\Phi_x$) and `fractionalAdd` (the lift, which takes the proof of $x\in P(G)$ as an argument); decidability of the fractional predicates is classical. The lemmas are `fractionalExtension_apply_fractional`, `fractionalExtension_apply_fixed`, `fractionalExtension_mean`, `fractional_incident`, `fixed_or_zero`, `incident_forced_zero`, `fractional_no_forced`, `positive_incident`, `fixed_at_vertex`, `mem_fractionalAdd` and `mem_fractionalAdd_fractional`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/FractionalReduction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/FractionalReduction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_MinimalFace

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def FractionalVertex (G : LooplessGraph V E) (x : E → ℝ) (v : V) : Prop :=
  ∃ e, IsFractional x e ∧ G.Incident v e

instance fractionalVertexDecidable (G : LooplessGraph V E) (x : E → ℝ) :
    DecidablePred (FractionalVertex G x) := Classical.decPred _
instance fractionalEdgeDecidable (x : E → ℝ) : DecidablePred (IsFractional x) := Classical.decPred _

def fractionalGraph (G : LooplessGraph V E) (x : E → ℝ) :
    LooplessGraph {v // FractionalVertex G x v} {e // IsFractional x e} where
  left e := ⟨G.left e.val, e.val, e.property, Or.inl rfl⟩
  right e := ⟨G.right e.val, e.val, e.property, Or.inr rfl⟩
  loopless e h := G.loopless e.val (congrArg Subtype.val h)

def fractionalMean (x : E → ℝ) (e : {e // IsFractional x e}) : ℝ := x e.val

def fractionalExtension (x : E → ℝ) : ({e // IsFractional x e} → ℝ) →ᵃ[ℝ] (E → ℝ) where
  toFun z e := if h : IsFractional x e then z ⟨e,h⟩ else x e
  linear := {
    toFun := fun u e => if h : IsFractional x e then u ⟨e,h⟩ else 0
    map_add' := by intro u v; ext e; by_cases h : IsFractional x e <;> simp [h]
    map_smul' := by intro a u; ext e; by_cases h : IsFractional x e <;> simp [h] }
  map_vadd' := by intro z u; ext e; by_cases h : IsFractional x e <;> simp [h]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fractionalExtension_apply_fractional (x : E → ℝ)
    (z : {e // IsFractional x e} → ℝ) (e : {e // IsFractional x e}) :
    fractionalExtension x z e.val = z e := by simp [fractionalExtension, e.property]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fractionalExtension_apply_fixed (x : E → ℝ)
    (z : {e // IsFractional x e} → ℝ) {e : E} (he : ¬IsFractional x e) :
    fractionalExtension x z e = x e := by simp [fractionalExtension, he]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem fractionalExtension_mean (x : E → ℝ) :
    fractionalExtension x (fractionalMean x) = x := by
  ext e
  by_cases he : IsFractional x e <;> simp [fractionalExtension, fractionalMean, he]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem fractional_incident (G : LooplessGraph V E) (x : E → ℝ)
    (v : {v // FractionalVertex G x v}) (e : {e // IsFractional x e}) :
    (fractionalGraph G x).Incident v e ↔ G.Incident v.val e.val := by
  simp only [LooplessGraph.Incident, fractionalGraph, Subtype.ext_iff]

omit [Fintype V] [DecidableEq V] in
theorem fixed_or_zero (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {e : E} (he : ¬IsFractional x e) : x e = 0 ∨ x e = 1 := by
  have h := G.coordinate_mem_Icc hx e
  dsimp [IsFractional] at he
  by_cases hz : x e = 0
  · exact Or.inl hz
  · exact Or.inr (le_antisymm h.2 (not_lt.mp (fun hh => he ⟨lt_of_le_of_ne h.1 (Ne.symm hz), hh⟩)))

omit [Fintype V] [DecidableEq V] in
theorem incident_forced_zero (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {v : V} {e₀ e : E} (h₀ : x e₀ = 1) (hv₀ : G.Incident v e₀)
    (hv : G.Incident v e) (hne : e ≠ e₀) : x e = 0 := by
  apply G.forced_coordinate_zero hx e₀ h₀ hne
  intro hr
  rcases hv with h | h
  · exact hr.1 (h ▸ hv₀)
  · exact hr.2 (h ▸ hv₀)

omit [Fintype V] [DecidableEq V] in
theorem fractional_no_forced (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {v : V} (hv : FractionalVertex G x v) {e : E} (he : x e = 1) : ¬G.Incident v e := by
  intro hi
  obtain ⟨f, hf, hif⟩ := hv
  have hne : f ≠ e := by intro h; subst f; exact (ne_of_lt hf.2) he
  have hz := incident_forced_zero G hx he hi hif hne
  exact (ne_of_gt hf.1) hz

omit [Fintype V] in
theorem positive_incident (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) (v : V) :
    ∃ e, G.Incident v e ∧ 0 < x e := by
  by_contra! hn
  have hc := G.polytope_subset_constraintPolytope hx
  have hz : G.degree x v = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    by_cases hi : G.Incident v e
    · simp [hi, le_antisymm (hn e hi) (hc.1 e)]
    · simp [hi]
  rw [hc.2.1 v] at hz
  norm_num at hz

omit [Fintype V] in
theorem fixed_at_vertex (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    {v : V} (hv : ¬FractionalVertex G x v) : ∃! e, x e = 1 ∧ G.Incident v e := by
  obtain ⟨e, hi, he⟩ := positive_incident G hx v
  have hnot : ¬IsFractional x e := fun h => hv ⟨e, h, hi⟩
  have hone : x e = 1 := (fixed_or_zero G hx hnot).resolve_left (ne_of_gt he)
  refine ⟨e, ⟨hone, hi⟩, ?_⟩
  intro f hf
  by_contra hn
  have hz := incident_forced_zero G hx hone hi hf.2 hn
  linarith [hf.1]

def fractionalAdd (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : (fractionalGraph G x).Matching) : G.Matching := by
  classical
  let N := M.val.map (Function.Embedding.subtype (IsFractional x)) ∪
    Finset.univ.filter (fun e => x e = 1)
  have hmem (e : E) : e ∈ N ↔
      (∃ he : IsFractional x e, (⟨e,he⟩ : {e // IsFractional x e}) ∈ M.val) ∨ x e = 1 := by
    simp only [N, Finset.mem_union, Finset.mem_map, Function.Embedding.coe_subtype,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨f, hf, rfl⟩ | h)
      · exact Or.inl ⟨f.property, hf⟩
      · exact Or.inr h
    · rintro (⟨he, hm⟩ | h)
      · exact Or.inl ⟨⟨e,he⟩, hm, rfl⟩
      · exact Or.inr h
  refine ⟨N, ?_⟩
  intro v
  by_cases hv : FractionalVertex G x v
  · obtain ⟨e, ⟨he, hi⟩, hu⟩ := M.property ⟨v,hv⟩
    refine ⟨e.val, ⟨(hmem e.val).mpr (Or.inl ⟨e.property,he⟩),
      (fractional_incident G x _ _).mp hi⟩, ?_⟩
    intro f hf
    rcases (hmem f).mp hf.1 with ⟨hfrac, hm⟩ | hone
    · exact congrArg Subtype.val (hu ⟨f,hfrac⟩ ⟨hm, (fractional_incident G x _ _).mpr hf.2⟩)
    · exact (fractional_no_forced G hx hv hone hf.2).elim
  · obtain ⟨e, he, hu⟩ := fixed_at_vertex G hx hv
    refine ⟨e, ⟨(hmem e).mpr (Or.inr he.1), he.2⟩, ?_⟩
    intro f hf
    rcases (hmem f).mp hf.1 with ⟨hfrac, _⟩ | hone
    · exact (hv ⟨f,hfrac,hf.2⟩).elim
    · exact hu f ⟨hone,hf.2⟩

omit [Fintype V] in
theorem mem_fractionalAdd (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope)
    (M : (fractionalGraph G x).Matching) (e : E) :
    e ∈ (fractionalAdd G hx M).val ↔
      (∃ he : IsFractional x e, (⟨e,he⟩ : {e // IsFractional x e}) ∈ M.val) ∨ x e = 1 := by
  classical
  simp only [fractionalAdd, Finset.mem_union, Finset.mem_map, Function.Embedding.coe_subtype,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨f,hf,rfl⟩ | h)
    · exact Or.inl ⟨f.property,hf⟩
    · exact Or.inr h
  · rintro (⟨he,hm⟩ | h)
    · exact Or.inl ⟨⟨e,he⟩,hm,rfl⟩
    · exact Or.inr h

omit [Fintype V] in
@[simp] theorem mem_fractionalAdd_fractional (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (M : (fractionalGraph G x).Matching) (e : {e // IsFractional x e}) :
    e.val ∈ (fractionalAdd G hx M).val ↔ e ∈ M.val := by
  rw [mem_fractionalAdd]
  simp only [exists_prop, Subtype.coe_eta]
  constructor
  · rintro (⟨_, hm⟩ | h)
    · exact hm
    · exact ((ne_of_lt e.property.2) h).elim
  · intro h
    exact Or.inl ⟨e.property,h⟩

section AffineFaces
variable {A : Type uA} {B : Type uB} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]

end AffineFaces

section FaceMaps
variable {W : Type uW} {D : Type uD} [Fintype W] [Fintype D] [DecidableEq W] [DecidableEq D]

end FaceMaps

end MatchingEntropyBounds.Refined

end

end OAI


