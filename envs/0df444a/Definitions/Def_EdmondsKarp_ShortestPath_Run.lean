-- Prove2me | Definitions.Def_EdmondsKarp_ShortestPath_Run
-- name    : EdmondsKarp_ShortestPath_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:10:29.01697+00:00
-- url     : https://prove2.me/theorems/f42bc532-e69e-4dd4-a2ff-094355e0ddcc
-- title:
--   Residual distances $\delta^k$ and runs of the labeling method with fewest-arc augmentations
-- statement:
--   Let $f$ be a flow in a network $N$ and $N^f$ its residual network. The **distance** $\delta(u,v)$ from a node $u$ to a node $v$ in $N^f$ is the minimum length (number of arcs) of a directed path from $u$ to $v$ in $N^f$, or $\infty$ if there is no such path. In particular $\delta(u,u) = 0$.
--
--   An augmenting path $P$ relative to $f$ has **fewest arcs** if no augmenting path relative to $f$ has fewer arcs, i.e. $P$ is a shortest directed path from $s$ to $t$ in $N^f$.
--
--   A **run of the labeling method with fewest-arc augmentations** of length $K$ is a sequence of functions $f^0, f^1, \dots, f^K$ and node sequences $P^0, \dots, P^{K-1}$ such that $f^0$ is a flow in $N$ and, for every $k < K$, $P^k$ is an augmenting path having fewest arcs relative to $f^k$ and $f^{k+1}$ is obtained from $f^k$ by augmentation along $P^k$. We write $N^k = N^{f^k}$ and $\delta^k(u,v)$ for the distance from $u$ to $v$ in $N^k$.
--
--   Runs are the objects on which Theorem 1 and all its lemmas are stated: $K$ is the number of augmentations performed.
--
--   **Formalization Note** Distances take values in `ℕ∞`, so the infimum over an empty set of paths is `⊤`, which is the paper's $\infty$. The run is encoded by sequences indexed by `ℕ`; only the indices $0,\dots,K$ of `f` and $0,\dots,K-1$ of `P` are constrained. The initial flow is arbitrary (the paper's labeling method starts "with, say, the zero flow", and its analysis considers "any sequence of flows" of this form).
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 250 (labeling method) and p. 251, §1.2 (length, distance, the sequence F, N^k, δ^k)

import Mathlib
import Definitions.Def_EdmondsKarp_ShortestPath_Network
import Definitions.Def_EdmondsKarp_ShortestPath_Augmentation

namespace EdmondsKarp.ShortestPath

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The distance `δ(u, v)` from `u` to `v` in `N^f` (p. 251): the minimum length (number of arcs) of a
directed path from `u` to `v` in `N^f`, or `∞` (`⊤`) if there is none. -/
noncomputable def resDist (N : Network V) (f : V → V → ℝ) (u v : V) : ℕ∞ :=
  ⨅ (P : List V) (_ : IsDirPath N f u v P), ((pathArcs P).length : ℕ∞)

/-- An augmenting path having fewest arcs relative to `f` (Theorem 1, p. 251). -/
def IsShortestAugPath (N : Network V) (f : V → V → ℝ) (P : List V) : Prop :=
  IsAugPath N f P ∧ ∀ Q : List V, IsAugPath N f Q → (pathArcs P).length ≤ (pathArcs Q).length

/-- `K` steps of the labeling method with fewest-arc augmentations (pp. 250–251): `f 0` is a flow in
`N` and, for every `k < K`, `P k` is an augmenting path having fewest arcs relative to `f k` and
`f (k+1)` is obtained from `f k` by augmentation along `P k`. -/
def IsShortestRun (N : Network V) (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) : Prop :=
  IsFlow N (f 0) ∧
    ∀ k < K, IsShortestAugPath N (f k) (P k) ∧ f (k + 1) = augment N (f k) (P k)

end EdmondsKarp.ShortestPath


