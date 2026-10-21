-- Prove2me | Definitions.Def_RegMatroidXC_Main_Sums
-- name    : RegMatroidXC_Main_Sums
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:31.068999+00:00
-- url     : https://prove2.me/theorems/9753d9c6-1a92-494a-b89e-f86c8568f231
-- title:
--   1-, 2- and 3-sums of binary matroids, star decompositions, decomposition trees and bad nodes (pp. 2–3, 7, 10, 17)
-- statement:
--   Let $M, M_1, M_2$ be matroids on subsets of a common ambient set, with ground sets $E, E_1, E_2$.
--
--   1. **Cycle sum** (p. 3, after Seymour): $M = M_1 \Delta M_2$ if $E = E_1 \Delta E_2$ and the cycles of $M$ are exactly the subsets of $E$ of the form $C_1 \Delta C_2$ with $C_i$ a cycle of $M_i$.
--   2. **1-sum** $M = M_1 \oplus_1 M_2$: $M_1, M_2$ binary, $M = M_1 \Delta M_2$, $E_1 \cap E_2 = \emptyset$ and $E_1, E_2 \neq \emptyset$.
--   3. **2-sum** $M = M_1 \oplus_2 M_2$: $M_1, M_2$ binary, $M = M_1 \Delta M_2$, $E_1 \cap E_2 = \{a\}$ where $a$ is neither a loop nor a coloop of $M_1$ or of $M_2$, and $|E_1|, |E_2| \ge 3$.
--   4. **3-sum** $M = M_1 \oplus_3 M_2$: $M_1, M_2$ binary, $M = M_1 \Delta M_2$, and $T = E_1 \cap E_2$ has three elements, is a circuit (a *triangle*) of both $M_1$ and $M_2$, contains no cocircuit of $M_1$ or of $M_2$, and $|E_1|, |E_2| \ge 7$.
--   5. **Star decomposition** $M \overset{\star}{=} M_0 \oplus_3 M_1 \oplus_3 \cdots \oplus_3 M_k$ (Lemma 4 (iii), p. 2; §4.4, p. 7): $M_0, \dots, M_k$ have finite ground sets, $M_1, \dots, M_k$ are mutually disjoint, every pair $(M_0, M_i)$ satisfies the 3-sum conditions with triangle $T_i = E(M_0) \cap E(M_i)$,
--   $$E(M) = \Big(E(M_0) \cup \bigcup_{i=1}^k E(M_i)\Big) \setminus \bigcup_{i=1}^k T_i,$$
--   and the cycles of $M$ are exactly the sets $C_0 \Delta C_1 \Delta \cdots \Delta C_k$ contained in $E(M)$, with $C_i$ a cycle of $M_i$.
--   6. **Vertex-star condition** (Section 6, p. 10, via Proposition 27, p. 17): if $M_0$ is not graphic, then $M_0 = M^*(G)$ for a connected finite multigraph $G$ and every triangle $T_i$ is the set $\delta(v_i)$ of edges at some node $v_i$ of $G$ (a node of degree 3, as $|T_i| = 3$).
--   7. **Decomposition tree** (Theorem 6, p. 3; p. 17): a finite tree $T$ with a binary matroid $M_v$ (finite ground set) at each node $v$, such that every edge $vw$ of $T$ satisfies the 3-sum conditions for $(M_v, M_w)$, labels of distinct non-adjacent nodes are disjoint, $E(M)$ is the set of elements lying in exactly one $E(M_v)$, and the cycles of $M$ are exactly the sets $\Delta_v C_v$ (the elements lying in an odd number of the $C_v$) contained in $E(M)$, with $C_v$ a cycle of $M_v$. This is "the matroid obtained by performing all the 3-sums corresponding to the edges of $T$, in arbitrary order".
--   8. **No bad nodes** (Appendix C, p. 17): for a tree $T$ labelled by matroids $M_v$, a node $v$ whose label is cographic and not graphic, $M_v = M^*(G_v)$, is *bad* if some triangle $T_{uv} = E(M_v) \cap E(M_u)$ of a 3-sum at $v$ is a cut of $G_v$ not of the form $\delta(w)$ for a degree-3 node $w$ of $G_v$. The tree has no bad nodes if every node $v$ whose label is not graphic has a finite multigraph $G_v$ with $M_v = M^*(G_v)$ in which every $T_{uv}$ is the set $\delta(w)$ of edges at some node $w$ (a node of degree 3, since $T_{uv}$ is a 3-element circuit of $M_v$).
--
--   These notions carry Seymour's decomposition of regular matroids, which the proof of the main theorem uses through Lemmas 3–5 and Theorem 6.
--
--   **Formalization Note** All matroids share one ambient type, so the parts of a sum may contain elements (the triangle elements) outside $E(M)$. A matroid is called 3-connected when it is neither a 1-sum nor a 2-sum (p. 3). The vertex-star condition is the assumption the paper makes at the start of Section 6 and justifies by Proposition 27; it is stated as a separate predicate so that Lemma 4 and Lemma 5 use literally the same clause.
-- source:
--   Aprile & Fiorini, Regular Matroids Have Polynomial Extension Complexity, arXiv:1909.08539v2, p. 3 (Section 2.1, t-sums), p. 2 (Lemma 4 (iii)), p. 7 (Section 4.4), p. 10 (Section 6), p. 17 (decomposition tree, Proposition 27)

import Mathlib
import Definitions.Def_RegMatroidXC_Main_Matroids

namespace RegMatroidXC.Main

/-- `M = M₁ Δ M₂` (p. 3, following Seymour): `E(M) = E(M₁) Δ E(M₂)` and the cycles of `M` are
exactly the subsets of `E(M)` of the form `C₁ Δ C₂` with `Cᵢ` a cycle of `Mᵢ`. -/
def IsCycleSum {α : Type} (M M₁ M₂ : Matroid α) : Prop :=
  M.E = symmDiff M₁.E M₂.E ∧
    ∀ C : Set α, IsCycle M C ↔
      ∃ C₁ C₂ : Set α, IsCycle M₁ C₁ ∧ IsCycle M₂ C₂ ∧ C = symmDiff C₁ C₂ ∧ C ⊆ M.E

/-- **1-sum** `M = M₁ ⊕₁ M₂` (p. 3): `M₁, M₂` binary, `M = M₁ Δ M₂`, `E₁` and `E₂` disjoint and
both nonempty. -/
def IsOneSum {α : Type} (M M₁ M₂ : Matroid α) : Prop :=
  IsBinary M₁ ∧ IsBinary M₂ ∧ IsCycleSum M M₁ M₂ ∧
    Disjoint M₁.E M₂.E ∧ M₁.E.Nonempty ∧ M₂.E.Nonempty

/-- **2-sum** `M = M₁ ⊕₂ M₂` (p. 3): `M₁, M₂` binary, `M = M₁ Δ M₂`, `E₁` and `E₂` share exactly
one element `a`, which is neither a loop nor a coloop of `M₁` or of `M₂`, and `|E₁|, |E₂| ≥ 3`. -/
def IsTwoSum {α : Type} (M M₁ M₂ : Matroid α) : Prop :=
  IsBinary M₁ ∧ IsBinary M₂ ∧ IsCycleSum M M₁ M₂ ∧
    ∃ a : α, M₁.E ∩ M₂.E = {a} ∧ ¬ M₁.IsLoop a ∧ ¬ M₁.IsColoop a ∧
      ¬ M₂.IsLoop a ∧ ¬ M₂.IsColoop a ∧ 3 ≤ M₁.E.ncard ∧ 3 ≤ M₂.E.ncard

/-- The side conditions of a **3-sum** of the binary matroids `M₁, M₂` (p. 3): `M₁, M₂` are binary,
`T := E₁ ∩ E₂` has exactly three elements, `T` is a circuit (a *triangle*) of `M₁` and of `M₂`, `T`
contains no cocircuit of `M₁` or of `M₂`, and `|E₁|, |E₂| ≥ 7`. -/
def IsThreeSumPair {α : Type} (M₁ M₂ : Matroid α) : Prop :=
  IsBinary M₁ ∧ IsBinary M₂ ∧ (M₁.E ∩ M₂.E).ncard = 3 ∧
    M₁.IsCircuit (M₁.E ∩ M₂.E) ∧ M₂.IsCircuit (M₁.E ∩ M₂.E) ∧
    (∀ D ⊆ M₁.E ∩ M₂.E, ¬ M₁.IsCocircuit D) ∧ (∀ D ⊆ M₁.E ∩ M₂.E, ¬ M₂.IsCocircuit D) ∧
    7 ≤ M₁.E.ncard ∧ 7 ≤ M₂.E.ncard

/-- **3-sum** `M = M₁ ⊕₃ M₂` (p. 3): the side conditions of `IsThreeSumPair` and `M = M₁ Δ M₂`. -/
def IsThreeSum {α : Type} (M M₁ M₂ : Matroid α) : Prop :=
  IsThreeSumPair M₁ M₂ ∧ IsCycleSum M M₁ M₂

/-- **Star decomposition** `M ⋆= M₀ ⊕₃ M₁ ⊕₃ ⋯ ⊕₃ M_k` (Lemma 4 (iii), p. 2; §4.4, p. 7): `M` is
obtained from `M₀` by simultaneously performing a 3-sum with each `Mᵢ`, `i ∈ [k]`.
* `M₀` and the `Mᵢ` have finite ground sets, and `M₁, …, M_k` are mutually disjoint;
* each pair `(M₀, Mᵢ)` satisfies the 3-sum conditions, with triangle `Tᵢ := E(M₀) ∩ E(Mᵢ)`;
* `E(M) = (E(M₀) ∪ ⋃ᵢ E(Mᵢ)) \ ⋃ᵢ Tᵢ`;
* the cycles of `M` are exactly the sets `C₀ Δ (C₁ ∪ ⋯ ∪ C_k)` (= `C₀ Δ C₁ Δ ⋯ Δ C_k`, the `Cᵢ`,
  `i ≥ 1`, being disjoint) contained in `E(M)`, with `C₀` a cycle of `M₀` and `Cᵢ` a cycle
  of `Mᵢ`. -/
def IsStarDecomposition {α : Type} {k : ℕ} (M M₀ : Matroid α) (Ms : Fin k → Matroid α) : Prop :=
  M₀.E.Finite ∧ (∀ i, (Ms i).E.Finite) ∧
    Pairwise (fun i j => Disjoint (Ms i).E (Ms j).E) ∧
    (∀ i, IsThreeSumPair M₀ (Ms i)) ∧
    M.E = (M₀.E ∪ ⋃ i, (Ms i).E) \ ⋃ i, (M₀.E ∩ (Ms i).E) ∧
    ∀ C : Set α, IsCycle M C ↔
      ∃ (C₀ : Set α) (Cs : Fin k → Set α), IsCycle M₀ C₀ ∧ (∀ i, IsCycle (Ms i) (Cs i)) ∧
        C = symmDiff C₀ (⋃ i, Cs i) ∧ C ⊆ M.E

/-- **Clause (iv)** of the star decomposition used by Lemma 5's cographic case (Section 6, p. 10,
via Proposition 27, p. 17): if `M₀` is not graphic, then `M₀ = M*(G)` for a connected finite
multigraph `G` (vertex set `V`, edge `e` from `tail e` to `head e`) and every triangle
`Tᵢ = E(M₀) ∩ E(Mᵢ)` is the star `δ(vᵢ)` of a node `vᵢ` of `G` (the set of edges with an end at
`vᵢ`; since `|Tᵢ| = 3`, `vᵢ` has degree 3). -/
def TrianglesAreVertexStars {α : Type} {k : ℕ} (M₀ : Matroid α) (Ms : Fin k → Matroid α) : Prop :=
  ¬ IsGraphic M₀ →
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (tail head : α → V),
      IsCycleMatroidOf M₀✶ V tail head ∧
      (SimpleGraph.fromRel (fun u v : V => ∃ e ∈ M₀.E, tail e = u ∧ head e = v)).Connected ∧
      ∀ i, ∃ v : V, M₀.E ∩ (Ms i).E = {e | e ∈ M₀.E ∧ (tail e = v ∨ head e = v)}

open Classical in
/-- **Decomposition tree** (Theorem 6, p. 3; p. 17): `M` is the matroid obtained by performing the
3-sums `M_v ⊕₃ M_w` for all edges `vw` of the tree `T` (in arbitrary order).
* every label `M_v` is binary with a finite ground set;
* for every edge `vw` of `T`, `(M_v, M_w)` satisfies the 3-sum conditions (triangle
  `E(M_v) ∩ E(M_w)`), and labels of distinct non-adjacent nodes are disjoint;
* `E(M)` is the set of elements lying in exactly one `E(M_v)`;
* the cycles of `M` are exactly the sets `Δ_v C_v` (elements in an odd number of the `C_v`)
  contained in `E(M)`, with `C_v` a cycle of `M_v`. -/
def IsDecompositionTree {α ι : Type} [Fintype ι] (M : Matroid α) (T : SimpleGraph ι)
    (Ms : ι → Matroid α) : Prop :=
  (∀ v, IsBinary (Ms v) ∧ (Ms v).E.Finite) ∧
    (∀ v w, T.Adj v w → IsThreeSumPair (Ms v) (Ms w)) ∧
    (∀ v w, v ≠ w → ¬ T.Adj v w → Disjoint (Ms v).E (Ms w).E) ∧
    M.E = {e | (Finset.univ.filter (fun v => e ∈ (Ms v).E)).card = 1} ∧
    ∀ C : Set α, IsCycle M C ↔
      ∃ Cs : ι → Set α, (∀ v, IsCycle (Ms v) (Cs v)) ∧
        C = {e | Odd (Finset.univ.filter (fun v => e ∈ Cs v)).card} ∧ C ⊆ M.E

/-- **No bad nodes** (Appendix C, p. 17), for a tree `T` whose nodes are labelled by the matroids
`Ms v`: a node `v` whose label is cographic and not graphic, `M_v = M*(G_v)`, is *bad* if `G_v`
contains a cut `T_uv` involved in some 3-sum (`u` a neighbour of `v`, `T_uv = E(M_v) ∩ E(M_u)`) that is
not of the form `δ(w)` for a degree-3 node `w` of `G_v`. Here: every node `v` whose label is not
graphic has a finite multigraph `G_v` (vertex set `V`, edge `e` from `tail e` to `head e`) with
`M_v✶ = M(G_v)` in which every `T_uv` is the star `δ(w)` of some node `w` (the edges with an end at
`w`; since `|T_uv| = 3` and `T_uv` is a circuit of `M_v`, `w` has degree 3). -/
def HasNoBadNodes {α ι : Type} (T : SimpleGraph ι) (Ms : ι → Matroid α) : Prop :=
  ∀ v, ¬ IsGraphic (Ms v) →
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (tail head : α → V),
      IsCycleMatroidOf (Ms v)✶ V tail head ∧
      ∀ u, T.Adj v u → ∃ w : V,
        (Ms v).E ∩ (Ms u).E = {e | e ∈ (Ms v).E ∧ (tail e = w ∨ head e = w)}

end RegMatroidXC.Main


