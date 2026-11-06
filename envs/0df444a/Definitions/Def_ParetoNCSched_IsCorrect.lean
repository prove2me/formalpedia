-- Prove2me | Definitions.Def_ParetoNCSched_IsCorrect
-- name    : ParetoNCSched_IsCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:28.395314+00:00
-- url     : https://prove2.me/theorems/a2937feb-9081-4f70-bedf-4a1c634958ca
-- title:
--   Correct predicted order: $p_{\sigma(1)}\le\dots\le p_{\sigma(n)}$
-- statement:
--   A predicted order is a permutation $\sigma$ of the $n$ jobs; it is *correct* for the sizes $p$ if
--   $$p_{\sigma(1)}\le p_{\sigma(2)}\le\cdots\le p_{\sigma(n)}.$$
--   Ties are allowed, so several orders may be correct for the same sizes.
--
--   **Formalization Note** Positions are 0-based: $\sigma(k)$ is the job at position $k\in\{0,\dots,n-1\}$, and correctness is monotonicity of $k\mapsto p_{\sigma(k)}$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7; Appendix A, Model, p.15

import Mathlib

namespace ParetoNCSched

/-- **Correct predicted order.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Section 2, p.7, and Appendix A, Model, p.15: the prediction
is a permutation σ of the jobs, "correct if p_σ(1) ≤ ⋯ ≤ p_σ(n)".

**Formalization Note.** Positions are 0-based: `σ k` is the job at position `k` of the predicted
order, so correctness is monotonicity of `k ↦ p (σ k)`. Ties are allowed, so a correct order need
not be unique. -/
def IsCorrect {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  Monotone (p ∘ σ)

end ParetoNCSched


