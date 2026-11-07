-- Prove2me | Definitions.Def_FairKMeans_WeightedKMeans
-- name    : FairKMeans_WeightedKMeans
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:54.260804+00:00
-- url     : https://prove2.me/theorems/c58b4c68-ba19-48ac-bfa8-5d6e22dfa7f3
-- title:
--   Weighted $k$-means cost, optimum, and $\rho$-approximate oracles
-- statement:
--   For a weighted point set $Q=(q_1,\dots,q_N)$ in $\mathbb R^d$ with weights $w(q)$ and a nonempty center family $S$,
--
--   $$\mathrm{Cost}(Q,S)=\sum_{q\in Q} w(q)\,\mathrm{dist}^2(q,S),\qquad \mathrm{dist}^2(q,S)=\min_{s\in S}\|q-s\|^2 .$$
--
--   The weighted $k$-means optimum is $\min_{|S'|\le k}\mathrm{Cost}(Q,S')$. A **$\rho$-approximate weighted $k$-means algorithm** ($\rho\ge 1$) outputs, on every weighted point set with nonnegative weights, at most $k$ centers whose cost is at most $\rho$ times this optimum.
--
--   Algorithm 1 calls such an algorithm once, on the weighted centroids of its fragment clusters.
--
--   **Formalization Note** The algorithm is an oracle function from $(k,Q,w)$ to a center family, and "$\rho$-approximate for this $k$" is its specification. Outputs are required to be nonempty; this excludes only the empty family, whose cost is $+\infty$ in the paper. The optimum is a real infimum over families with $1\le|S'|\le k$.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Section 4, Cost(Q, S), p.18 (PDF p.20), and 'Weighted k-means', p.20 (PDF p.22)

import Mathlib
import Definitions.Def_FairKMeans_Model

namespace FairKMeans

/-!
# Weighted k-means and ρ-approximate k-means oracles

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…), Section 4: the cost
`Cost(Q, S) = ∑_q w(q) dist²(q, S)`, p.18 (PDF 20), and "Weighted k-means", p.20 (PDF 22).

**Formalization Note.** A weighted point set is a family `Q : Fin q → E d` with weights
`w : Fin q → ℝ`. `dist²(z, S)` is `⨅ j, ‖z − S j‖²`, the minimum over the finite family `S`;
it is used only for nonempty `S` (for `s = 0` the real infimum is Lean's junk `0`; the paper's
cost of the empty set is `+∞`, never optimal). The optimum `min_{|S'| ≤ k} Cost(Q, S')` is a
real `sInf` over center families with `1 ≤ s ≤ k`; it is bounded below by `0` for nonnegative
weights. A k-means oracle is any function from `(k, Q, w)` to a center family; "ρ-approximate"
is its specification. Its outputs are nonempty, which excludes only the infinite-cost empty set.
-/

variable {d : ℕ}

/-- `Cost(Q, S) = ∑_q w(q) · dist²(q, S)` (p.18). Meaningful for `1 ≤ s`. -/
noncomputable def kmCost {q s : ℕ} (Q : Fin q → E d) (w : Fin q → ℝ) (S : Fin s → E d) : ℝ :=
  ∑ i, w i * ⨅ j, ‖Q i - S j‖ ^ 2

/-- The weighted k-means optimum `min_{|S'| ≤ k} Cost(Q, S')` (p.20), over nonempty families of
at most `k` centers. -/
noncomputable def kmOpt {q : ℕ} (Q : Fin q → E d) (w : Fin q → ℝ) (k : ℕ) : ℝ :=
  sInf {c : ℝ | ∃ s, 1 ≤ s ∧ s ≤ k ∧ ∃ S : Fin s → E d, kmCost Q w S = c}

/-- A weighted k-means oracle: given `k` and a weighted point set, it returns a center family. -/
abbrev KMOracle (d : ℕ) : Type :=
  (k q : ℕ) → (Fin q → E d) → (Fin q → ℝ) → Σ s : ℕ, (Fin s → E d)

/-- A ρ-approximate weighted k-means algorithm for this `k` (p.20, PDF 22): on every weighted
point set with nonnegative weights it outputs at most `k` (and at least one) centers whose cost
is at most `ρ` times the optimum. -/
def IsRhoApprox (ρ : ℝ) (k : ℕ) (KM : KMOracle d) : Prop :=
  ∀ (q : ℕ) (Q : Fin q → E d) (w : Fin q → ℝ), (∀ i, 0 ≤ w i) →
    1 ≤ (KM k q Q w).1 ∧ (KM k q Q w).1 ≤ k ∧ kmCost Q w (KM k q Q w).2 ≤ ρ * kmOpt Q w k

end FairKMeans


