-- Prove2me | Definitions.Def_MinKCutII_Main_TreePacking
-- name    : MinKCutII_Main_TreePacking
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:38:53.945951+00:00
-- url     : https://prove2.me/theorems/59604827-554e-4f85-b9bf-a3c1a5481d4c
-- title:
--   Spanning trees of a multigraph, δ_T(S) and p-respecting, k-cut tree packings (Lemma 43, conditions (1)–(2))
-- statement:
--   A **spanning tree** of $G=(V,E,c)$ is a set $T\subseteq E$ of non-loop records, no two with the same ends, whose ends form a tree on all of $V$. For $S\subseteq V$, $\delta_T(S)$ is the set of tree edges with exactly one end in $S$; $T$ **$p$-respects** the cut $S$ when $|\delta_T(S)|\le p$.
--
--   For $k\ge 2$ and $\eta>0$, a **$k$-cut packing** is a pair of nonnegative tree weights $(y_T)$, supported on spanning trees of $G$, and nonnegative edge slacks $(z_e)$, with $\tau=\sum_T y_T$, satisfying conditions (1) and (2) of Lemma 43:
--   $$\sum_{T\ni e}y_T\le c(e)+z_e\quad(e\in E),\qquad (k-1)\,\tau\ \ge\ \frac{(1-\eta)\,\lambda_k(G)}{2}+z(E),$$
--   with $\lambda_k(G)$ finite. When $T$ is drawn with probability $y_T/\tau$, $\Pr[|\delta_T(S)|\le p]=\big(\sum_{T:|\delta_T(S)|\le p}y_T\big)/\tau$.
--
--   **Formalization Note.** Weights are indexed by all edge sets `Finset E` (a finite type) and vanish off spanning trees, so the family is finitely supported. The probability is written as the ratio `respectMass G y S p / packTotal y` rather than through a measure.
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 6, §2 (Respecting a tree); p. 31, Lemma 43, (1) and (2)

import Mathlib
import Definitions.Def_MinKCutII_Main_KCut

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-!
# Spanning trees of a multigraph, respecting, and k-cut tree packings (Lemma 43 (1)–(2))

Vaughn, *Faster Minimum k-Cut II*, arXiv:2609.27797 (version of November 1, 2026, sha256
b01b5a6f…), §2 p. 6 (respecting a tree), §4.2 p. 31 (Lemma 43, conditions (1) and (2)).

* A spanning tree of `G` is a set `T` of edge records of `G`, no loop, no two records with the same
  ends, whose ends form a tree on all of `V` (Mathlib `SimpleGraph.IsTree`). Tree weights `y_T` are
  indexed by all edge sets `T : Finset E` (a finite type) and must vanish off spanning trees, so
  every family is finitely supported.
* `treeDelta G T S = δ_T(S)`: the tree edges with exactly one end in `S`; `T` `p`-respects the cut
  `S` when `|δ_T(S)| ≤ p` (p. 6).
* `IsKCutPacking G k η y z` (conditions (1) and (2) of Lemma 43): `y ≥ 0` supported on spanning
  trees of `G`, `z ≥ 0` edge slacks, `τ = Σ_T y_T`, (1) `Σ_{T ∋ e} y_T ≤ c(e) + z_e` for every edge
  record `e`, and (2) `(k − 1) τ ≥ (1 − η) λ_k(G)/2 + z(E)` with `λ_k(G)` finite (Lemma 43 assumes
  `2 ≤ k ≤ n`, where `λ_k` is a real number; the predicate requires `λ_k(G) = L` for a real `L`).
* `respectMass G y S p = Σ_{T : |δ_T(S)| ≤ p} y_T`; when `T` is drawn with probability `y_T/τ`,
  `Pr[|δ_T(S)| ≤ p] = respectMass G y S p / τ`.
-/

/-- `T` is (the edge set of) a spanning tree of `G`. -/
def IsSpanningTreeOf {V E : Type*} (G : CapGraph V E) (T : Finset E) : Prop :=
  (∀ e ∈ T, ¬ (G.ends e).IsDiag) ∧ Set.InjOn G.ends (T : Set E) ∧
    (SimpleGraph.fromEdgeSet (G.ends '' (T : Set E))).IsTree

open Classical in
/-- `δ_T(S)`: the edges of `T` with exactly one end in `S`. -/
noncomputable def treeDelta {V E : Type*} [Fintype E] (G : CapGraph V E) (T : Finset E)
    (S : Finset V) : Finset E :=
  T.filter (fun e => e ∈ G.delta S)

/-- `τ = Σ_T y_T`. -/
noncomputable def packTotal {E : Type*} [Fintype E] (y : Finset E → ℝ) : ℝ :=
  ∑ T, y T

open Classical in
/-- Conditions (1) and (2) of Lemma 43 for tree weights `y` and edge slacks `z`. -/
def IsKCutPacking {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : CapGraph V E)
    (k : ℕ) (η : ℝ) (y : Finset E → ℝ) (z : E → ℝ) : Prop :=
  (∀ T, 0 ≤ y T) ∧ (∀ T, 0 < y T → IsSpanningTreeOf G T) ∧ (∀ e, 0 ≤ z e) ∧
    (∀ e, ∑ T ∈ Finset.univ.filter (fun T : Finset E => e ∈ T), y T ≤ G.u e + z e) ∧
    ∃ L : ℝ, lam G k = (L : WithTop ℝ) ∧
      (1 - η) * L / 2 + ∑ e, z e ≤ ((k : ℝ) - 1) * packTotal y

open Classical in
/-- `Σ_{T : |δ_T(S)| ≤ p} y_T`, the `y`-mass of the trees that `p`-respect `S`. -/
noncomputable def respectMass {V E : Type*} [Fintype E] (G : CapGraph V E)
    (y : Finset E → ℝ) (S : Finset V) (p : ℕ) : ℝ :=
  ∑ T ∈ Finset.univ.filter (fun T : Finset E => (treeDelta G T S).card ≤ p), y T

end MinKCutII.Main


