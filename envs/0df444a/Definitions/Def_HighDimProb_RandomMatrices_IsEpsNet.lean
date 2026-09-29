-- Prove2me | Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet
-- name    : HighDimProb_RandomMatrices_IsEpsNet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:18:56.197353+00:00
-- url     : https://prove2.me/theorems/f3c40033-98af-4742-b6cb-61d2a9f17be7
-- title:
--   The $\varepsilon$-net predicate on a metric space
-- statement:
--   This is **Definition 4.2.1** (ε-net): the basic covering relation this chapter's ε-net
--   argument is built on.
--
--   Let $(T, d)$ be a metric space, $K \subseteq T$, and $\varepsilon > 0$. A subset
--   $N \subseteq K$ is an **ε-net** of $K$ if every point of $K$ is within distance
--   $\varepsilon$ of some point of $N$:
--
--   $$
--   \forall x \in K,\ \exists x' \in N : d(x, x') \le \varepsilon.
--   $$
--
--   Equivalently, $N$ is an ε-net of $K$ exactly when the closed balls of radius $\varepsilon$
--   centered at the points of $N$ cover $K$.
--
--   **Formalization Note** Stated for a general `PseudoMetricSpace`, since the mission applies
--   it both to Euclidean spheres/balls (Corollary 4.2.13, Exercise 4.4.3) and to the Hamming
--   cube (used internally, though not exposed, in Theorem 4.3.5's proof). The book's own
--   definition requires `N ⊆ K`, which is encoded as the first conjunct.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Definition 4.2.1, p. 81 (PDF p. 89)

import Mathlib

namespace HighDimProb.RandomMatrices

/-- **Definition 4.2.1** (ε-net), Vershynin, *High-Dimensional Probability* (2018), p. 81.

Let `(T, d)` be a metric space, `K ⊆ T`, `ε > 0`. A subset `N ⊆ K` is an `ε`-net of `K` if
every point of `K` is within distance `ε` of some point of `N`. -/
def IsEpsNet {T : Type*} [PseudoMetricSpace T] (K : Set T) (N : Set T) (ε : ℝ) : Prop :=
  N ⊆ K ∧ ∀ x ∈ K, ∃ y ∈ N, dist x y ≤ ε

end HighDimProb.RandomMatrices


