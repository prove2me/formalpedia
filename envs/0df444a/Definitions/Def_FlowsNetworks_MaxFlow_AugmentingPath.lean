-- Prove2me | Definitions.Def_FlowsNetworks_MaxFlow_AugmentingPath
-- name    : FlowsNetworks_MaxFlow_AugmentingPath
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:01.654524+00:00
-- url     : https://prove2.me/theorems/87516119-2702-4d80-86cd-b7443598bc10
-- title:
--   Flow augmenting paths, and the source set $X$ and sink set $\bar Y$ of a flow
-- statement:
--   Let $[N; \mathcal A]$ be a network with capacity function $c$, and let $f$ be a function on the arcs (in use, a flow).
--
--   1. A **step** from $x$ to $y$ is admissible with respect to $f$ if either $(x, y)$ is an arc with $f(x, y) < c(x, y)$ (a forward arc), or $(y, x)$ is an arc with $f(y, x) > 0$ (a reverse arc).
--   2. A **flow augmenting path** from $a$ to $b$ with respect to $f$ is a sequence of distinct nodes $a = x_0, x_1, \dots, x_n = b$ in which every step from $x_i$ to $x_{i+1}$ is admissible: $f < c$ on the forward arcs of the path and $f > 0$ on its reverse arcs (Chapter I, pp. 5 and 22).
--   3. The **source set** $X$ of $f$ (the set defined in the proof of Theorem 5.1, restated on pp. 22 and 24) is the smallest set of nodes such that
--      - (a) $s \in X$;
--      - (b) if $x \in X$ and $f(x, y) < c(x, y)$, then $y \in X$; if $x \in X$ and $f(y, x) > 0$, then $y \in X$.
--   4. The **sink set** $\bar Y$ of $f$ (p. 24) is the smallest set of nodes such that
--      - (a′) $t \in \bar Y$;
--      - (b′) if $y \in \bar Y$ and $f(x, y) < c(x, y)$, then $x \in \bar Y$; if $y \in \bar Y$ and $f(y, x) > 0$, then $x \in \bar Y$.
--
--   For a maximal flow $f$ the source set $X$ determines the minimal cut $(X, \bar X)$ singled out in the proof of the max flow min cut theorem, and $\bar Y$ is the sink side of the mirror-image minimal cut $(Y, \bar Y)$; Theorems 5.5 and 5.6 are about these two sets.
--
--   **Formalization Note** A path is a map $x : \{0, \dots, n\} \to N$ that is injective (distinct nodes); for each consecutive pair, the book's "selection" of a forward or reverse arc is the disjunction in the admissible step. In rules (b) and (b′) the inequality $f(x, y) < c(x, y)$ is only meaningful for an arc, so membership of the arc is part of the rule. "Smallest set" is the intersection of all node sets satisfying (a), (b) (respectively (a′), (b′)); both sets are therefore defined for every $f$ without any choice.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, p. 5 (§1, path, forward and reverse arcs), p. 22 (§5, flow augmenting path; the set X of the proof of Theorem 5.1), p. 24 (§5, rules (a′), (b′) for Ȳ)

import Mathlib
import Definitions.Def_FlowsNetworks_MaxFlow_Network

namespace FlowsNetworks.MaxFlow

variable {N : Type} [Fintype N] [DecidableEq N]

/-- One admissible step from `x` to `y` with respect to the flow `f` (§5, p. 22): either `(x, y)`
is an arc with `f(x, y) < c(x, y)` (a forward arc that is unsaturated), or `(y, x)` is an arc with
`f(y, x) > 0` (a reverse arc carrying positive flow). -/
def AugStep (G : Network N) (f : N → N → ℝ) (x y : N) : Prop :=
  ((x, y) ∈ G.arcs ∧ f x y < G.cap x y) ∨ ((y, x) ∈ G.arcs ∧ 0 < f y x)

/-- A flow augmenting path from `a` to `b` with respect to `f` (§1 p. 5, §5 p. 22): a sequence of
distinct nodes `a = x₀, x₁, …, xₙ = b` such that for each `i` either `(xᵢ, xᵢ₊₁)` is an arc with
`f < c` (forward arc) or `(xᵢ₊₁, xᵢ)` is an arc with `f > 0` (reverse arc). -/
def IsFlowAugmentingPath (G : Network N) (f : N → N → ℝ) (a b : N) {n : ℕ}
    (x : Fin (n + 1) → N) : Prop :=
  Function.Injective x ∧ x 0 = a ∧ x (Fin.last n) = b ∧
    ∀ i : Fin n, AugStep G f (x i.castSucc) (x i.succ)

/-- There is a flow augmenting path from `a` to `b` with respect to `f`. -/
def HasFlowAugmentingPath (G : Network N) (f : N → N → ℝ) (a b : N) : Prop :=
  ∃ (n : ℕ) (x : Fin (n + 1) → N), IsFlowAugmentingPath G f a b x

/-- The source set `X` of the proof of Theorem 5.1, as restated on pp. 22 and 24: the least set of
nodes such that (a) `s ∈ X`; (b) if `x ∈ X` and `f(x, y) < c(x, y)` then `y ∈ X`, and if `x ∈ X` and
`f(y, x) > 0` then `y ∈ X`. It is the intersection of all node sets satisfying (a) and (b). -/
noncomputable def sourceSet (G : Network N) (f : N → N → ℝ) (s : N) : Finset N := by
  classical
  exact Finset.univ.filter (fun x => ∀ Z : Finset N, s ∈ Z →
    (∀ u w, u ∈ Z → AugStep G f u w → w ∈ Z) → x ∈ Z)

/-- The sink set `Ȳ` of p. 24: the least set of nodes such that (a′) `t ∈ Ȳ`; (b′) if `y ∈ Ȳ` and
`f(x, y) < c(x, y)` then `x ∈ Ȳ`, and if `y ∈ Ȳ` and `f(y, x) > 0` then `x ∈ Ȳ`. It is the
intersection of all node sets satisfying (a′) and (b′). -/
noncomputable def sinkSet (G : Network N) (f : N → N → ℝ) (t : N) : Finset N := by
  classical
  exact Finset.univ.filter (fun x => ∀ Z : Finset N, t ∈ Z →
    (∀ u w, w ∈ Z → AugStep G f u w → u ∈ Z) → x ∈ Z)

end FlowsNetworks.MaxFlow


