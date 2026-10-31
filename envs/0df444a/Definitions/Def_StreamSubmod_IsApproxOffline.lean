-- Prove2me | Definitions.Def_StreamSubmod_IsApproxOffline
-- name    : StreamSubmod_IsApproxOffline
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:13.848967+00:00
-- url     : https://prove2.me/theorems/c9fd32b6-3e6c-49a4-b63f-e0a308ff3c0f
-- title:
--   An $\alpha$-approximation offline algorithm
-- statement:
--   Let $f$ be a set function on $V$ and let $k$ be a natural number. An $\alpha$-approximation offline algorithm OfflineAlg for $f$ and $k$ takes a ground set $U\subseteq V$ and returns a feasible solution $S_o\subseteq U$ with $|S_o|\le k$, such that
--
--   $$
--   \mathbb E[f(S_o)]\ \ge\ \alpha\cdot f(A)\qquad\text{for every } A\subseteq U \text{ with } |A|\le k.
--   $$
--
--   This is the only property of the post-processing step that the analysis of StreamProcess uses, so any offline algorithm or heuristic with this guarantee can be plugged in.
--
--   **Formalization Note** The randomness is a finite seed type $\Omega$ with a probability vector $\mu$, and `Off ω U` is the output on $U$ with seed $\omega$. The algorithm is deterministic when `Off ω U` does not depend on $\omega$. Outputs are subsets of a finite set, so every randomized algorithm has this form, and calls on different ground sets may use independent coordinates of the seed.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Theorem 1, p.14; Algorithm 1, line 6, p.7; proof of Lemma 6, p.9

import Mathlib

namespace StreamSubmod

/-- `Off` is an `α`-approximation offline algorithm for maximizing `f` subject to the cardinality
constraint `k`, on every ground set `U ⊆ V` (Alaluf, Ene, Feldman, Nguyen & Suh,
arXiv:1911.12959v3, Theorem 1, p.14; Algorithm 1, line 6, p.7; proof of Lemma 6, p.9: "Since `S_o`
is produced by the algorithm OfflineAlg whose approximation ratio is `α` and `A_i` is one possible
output for this algorithm, this implies `E[f(S_o)] ≥ α · f(A_i)`").

**Formalization Note.** The randomness of the algorithm is a finite seed type `Ω` with the
probability vector `μ`, and `Off ω U` is its output on the ground set `U` with seed `ω`; a
deterministic algorithm is one for which `Off ω U` does not depend on `ω`. Every output is a
feasible solution: a subset of `U` with at most `k` elements. Since the outputs range over the
finite type `Finset E`, every randomized algorithm has this form (take for `ω` a choice of output
for every `U`), and calls on different `U` may use independent coordinates of `ω`. -/
structure IsApproxOffline {E Ω : Type} [Fintype Ω] (f : Finset E → ℝ) (k : ℕ) (α : ℝ)
    (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E) : Prop where
  /-- `μ` is non-negative. -/
  prob_nonneg : ∀ ω, 0 ≤ μ ω
  /-- `μ` has total mass one. -/
  prob_sum : ∑ ω, μ ω = 1
  /-- The output is a subset of the ground set. -/
  subset : ∀ ω U, Off ω U ⊆ U
  /-- The output has at most `k` elements. -/
  card_le : ∀ ω U, (Off ω U).card ≤ k
  /-- The expected output value is at least `α` times the value of every feasible solution. -/
  approx : ∀ U A, A ⊆ U → A.card ≤ k → α * f A ≤ ∑ ω, μ ω * f (Off ω U)

end StreamSubmod


