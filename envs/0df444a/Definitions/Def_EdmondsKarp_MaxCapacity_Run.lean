-- Prove2me | Definitions.Def_EdmondsKarp_MaxCapacity_Run
-- name    : EdmondsKarp_MaxCapacity_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:17:36.096667+00:00
-- url     : https://prove2.me/theorems/88c116d5-11aa-41cc-9e7b-1298b12c3c01
-- title:
--   Maximum-augmentation runs of the labeling method; cut quantities $c(X,\bar X)$, $f(X,\bar X)$, $f(\bar X,X)$ and the arc bound $M$
-- statement:
--   Let $N$ be a network and $f$ a flow in $N$. An augmenting path $P$ relative to $f$ **gives the maximum possible augmentation** if its augmentation $\varepsilon(P)$ is at least $\varepsilon(Q)$ for every augmenting path $Q$ relative to $f$.
--
--   A **run of $K$ steps of the labeling method with maximum augmentations** is a sequence of functions $f^0, f^1, \dots, f^K$ and node sequences $P^0, \dots, P^{K-1}$ such that $f^0$ is a flow in $N$ and, for every $k < K$, $P^k$ is an augmenting path relative to $f^k$ giving the maximum possible augmentation and $f^{k+1}$ is obtained from $f^k$ by augmentation along $P^k$.
--
--   For a set $X$ of nodes with complement $\bar X$, put
--   $$c(X,\bar X) = \sum_{\substack{u\in X,\ v\in \bar X\ (u,v)\in A}} c(u,v),\qquad f(X,\bar X) = \sum_{\substack{u\in X,\ v\in \bar X\ (u,v)\in A}} f(u,v),\qquad f(\bar X,X) = \sum_{\substack{u\in \bar X,\ v\in X\ (u,v)\in A}} f(u,v).$$
--   Finally, a natural number $M$ **bounds the crossing arcs** of $N$ if, for every partition of the nodes into $X$ and $\bar X$ with $s \in X$ and $t \in \bar X$, the number of arcs of $N$ with one end in $X$ and the other in $\bar X$ is at most $M$.
--
--   These objects set up the second refinement of the labeling method (§1.3) and its complexity analysis.
--
--   **Formalization Note** The arcs counted in the crossing-arc bound are the arcs of $N$, i.e. those of $A$ together with the return arc $(t,s)$, which crosses every such partition; this is the literal reading of p. 253 ("the number of arcs with one end in $X$ and the other in $\bar X$"). A run is a pair of sequences indexed by `ℕ`; only indices `≤ K` for flows and `< K` for paths are constrained.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 253, §1.3 (the refinement, the hypothesis on M); p. 254, proof of Theorem 2 (c(X, X̄), f(X, X̄), f(X̄, X)); p. 250, §1.1 (the labeling method)

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation

namespace EdmondsKarp.MaxCapacity

variable {V : Type} [Fintype V] [DecidableEq V]

/-- An augmenting path giving the maximum possible augmentation relative to `f` (§1.3, p. 253): an
augmenting path `P` whose `ε` is at least the `ε` of every augmenting path relative to `f`. -/
def IsMaxAugPath (N : Network V) (f : V → V → ℝ) (P : List V) : Prop :=
  IsAugPath N f P ∧ ∀ Q : List V, IsAugPath N f Q → pathEps N f Q ≤ pathEps N f P

/-- `K` steps of the labeling method with maximum augmentations (pp. 250, 253): `f 0` is a flow in
`N` and, for every `k < K`, `P k` is an augmenting path giving the maximum possible augmentation
relative to `f k`, and `f (k+1)` is obtained from `f k` by augmentation along `P k`. -/
def IsMaxAugRun (N : Network V) (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) : Prop :=
  IsFlow N (f 0) ∧
    ∀ k < K, IsMaxAugPath N (f k) (P k) ∧ f (k + 1) = augment N (f k) (P k)

/-- The number of arcs of `N` (the arcs of `A` together with the return arc `(t, s)`) with one end in
`X` and the other end outside `X` (§1.3, p. 253). -/
def crossArcCount (N : Network V) (X : Finset V) : ℕ :=
  (N.arcs.filter (fun p => (p.1 ∈ X ∧ p.2 ∉ X) ∨ (p.1 ∉ X ∧ p.2 ∈ X))).card

/-- The hypothesis on `M` of §1.3, p. 253: for any partition of the nodes into `X` and `X̄` with
`s ∈ X` and `t ∈ X̄`, the number of arcs of `N` with one end in `X` and the other in `X̄` is at
most `M`. -/
def CrossArcsBounded (N : Network V) (M : ℕ) : Prop :=
  ∀ X : Finset V, N.s ∈ X → N.t ∉ X → crossArcCount N X ≤ M

/-- `c(X, X̄) = Σ_{u ∈ X, v ∈ X̄, (u, v) ∈ A} c(u, v)` (proof of Theorem 2, p. 254). -/
def cutCap (N : Network V) (X : Finset V) : ℝ :=
  ∑ p ∈ N.A.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X), N.c p.1 p.2

/-- `f(X, X̄) = Σ_{u ∈ X, v ∈ X̄, (u, v) ∈ A} f(u, v)` (proof of Theorem 2, p. 254). -/
def cutFlowOut (N : Network V) (f : V → V → ℝ) (X : Finset V) : ℝ :=
  ∑ p ∈ N.A.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X), f p.1 p.2

/-- `f(X̄, X) = Σ_{u ∈ X̄, v ∈ X, (u, v) ∈ A} f(u, v)` (proof of Theorem 2, p. 254). -/
def cutFlowIn (N : Network V) (f : V → V → ℝ) (X : Finset V) : ℝ :=
  ∑ p ∈ N.A.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X), f p.1 p.2

end EdmondsKarp.MaxCapacity


