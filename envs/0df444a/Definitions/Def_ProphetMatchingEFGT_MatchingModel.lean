-- Prove2me | Definitions.Def_ProphetMatchingEFGT_MatchingModel
-- name    : ProphetMatchingEFGT_MatchingModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:49:58.385834+00:00
-- url     : https://prove2.me/theorems/c2012205-4255-4d08-a1df-664bded634a1
-- title:
--   §3 — matchings of a finite graph, the maximum matching weight and the fractional matching polytope $\mathcal F_M$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, not necessarily bipartite (§3, p. 9).
--
--   1. A set $M\subseteq E$ is a **matching** if $e_1\cap e_2=\emptyset$ for any two distinct $e_1,e_2\in M$; $\mathcal M$ is the family of matchings.
--   2. For weights $w\in\mathbb R^E$, $w(M)=\sum_{e\in M}w_e$ and the **maximum matching weight** is
--   $$w(\mathrm{OPT}(w))=\max_{M\in\mathcal M}w(M).$$
--   3. The **fractional matching polytope** (p. 10) is
--   $$\mathcal F_M=\Big\{y\in\mathbb R^E:\ \sum_{u}y_{(uv)}\le1\ \ \forall v\in V,\ \ y_e\ge0\ \ \forall e\in E\Big\}.$$
--
--   These are the feasible sets and the benchmark of the matching prophet inequality, and the polytope in which the marginals of every OCRS of §5 live.
--
--   **Formalization Note** $G$ is a Mathlib `SimpleGraph` (no loops, at most one edge $(uv)$ between two vertices); edges are the elements of `G.edgeSet`. The maximum is a finite maximum over the nonempty set of matchings ($\emptyset$ is a matching), so it is never a junk supremum; it is $\ge 0$.
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §3 pp. 9–10 (definition of 𝓜, FM on p. 10); OPT p. 8

import Mathlib

open MeasureTheory

namespace ProphetMatchingEFGT

/-! # Graph matching (§3, pp. 9–10, Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2)

A finite simple graph `G` on `V` (not necessarily bipartite), its edges as a finite type, matchings,
the weight of a matching, the maximum matching weight, and the fractional matching polytope `FM`.

**Formalization Note.** `G` is a Mathlib `SimpleGraph`: no loops and at most one edge `(uv)` between
two vertices, as the paper's notation `(uv)` presumes. Edges are the elements of `G.edgeSet`, as a
subtype of `Sym2 V`. The maximum matching weight is a finite maximum (`Finset.sup'`) over the
nonempty finite set of matchings (`∅` is a matching), never a real supremum. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `G`, as a finite type. -/
abbrev Edge (G : SimpleGraph V) : Type _ := G.edgeSet

/-- A set of edges is a matching when distinct edges share no vertex (`e₁ ∩ e₂ = ∅`, p. 9). -/
def IsMatching (G : SimpleGraph V) (M : Finset (Edge G)) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : V, v ∈ (e : Sym2 V) → v ∉ (f : Sym2 V)

/-- The family `𝓜` of all matchings of `G` (p. 9). -/
def matchingFamily (G : SimpleGraph V) : Set (Finset (Edge G)) :=
  {M | IsMatching G M}

open Classical in
/-- The finite set of all matchings of `G`. -/
noncomputable def matchings (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset (Edge G)) :=
  Finset.univ.filter (IsMatching G)

/-- `w(M) = Σ_{e ∈ M} w_e`. -/
def weightOf {G : SimpleGraph V} (w : Edge G → ℝ) (M : Finset (Edge G)) : ℝ :=
  ∑ e ∈ M, w e

omit [DecidableEq V] in
theorem matchings_nonempty (G : SimpleGraph V) [DecidableRel G.Adj] : (matchings G).Nonempty :=
  ⟨∅, by simp [matchings, IsMatching]⟩

/-- `w(OPT(w)) = max_{M ∈ 𝓜} w(M)`, the weight of a maximum-weight matching (p. 8, p. 9). -/
noncomputable def optWeight (G : SimpleGraph V) [DecidableRel G.Adj] (w : Edge G → ℝ) : ℝ :=
  (matchings G).sup' (matchings_nonempty G) (weightOf w)

open Classical in
/-- The fractional matching polytope `FM = {y | ∀ v, Σ_u y_{(uv)} ≤ 1, ∀ e, y_e ≥ 0}` (p. 10). -/
def InFM (G : SimpleGraph V) [DecidableRel G.Adj] (y : Edge G → ℝ) : Prop :=
  (∀ e, 0 ≤ y e) ∧ ∀ v : V, ∑ e ∈ Finset.univ.filter (fun e : Edge G => v ∈ (e : Sym2 V)), y e ≤ 1

end ProphetMatchingEFGT


