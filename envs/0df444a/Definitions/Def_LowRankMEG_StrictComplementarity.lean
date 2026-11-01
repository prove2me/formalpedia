-- Prove2me | Definitions.Def_LowRankMEG_StrictComplementarity
-- name    : LowRankMEG_StrictComplementarity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:24.812035+00:00
-- url     : https://prove2.me/theorems/195affd3-dbe9-4f97-896c-4d04afa6c84e
-- title:
--   Assumption 1 (strict complementarity)
-- statement:
--   An optimal solution $X^*$ of rank $r^*$ satisfies **strict complementarity** with parameter $\delta>0$ if
--   $$
--   \lambda_{n-r^*}(\nabla f(X^*))-\lambda_n(\nabla f(X^*))\ge\delta.
--   $$
--   It is an eigengap at the bottom of the spectrum of the gradient at the optimum, and it is the assumption on which the low-rank analysis rests.
--
--   **Formalization Note** The positivity of $\delta$ is part of the definition. $n-r^*$ is natural-number subtraction, exact because every statement assumes $r^*<n$.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Assumption 1, p.3

import Mathlib
import Definitions.Def_LowRankMEG_lam

namespace LowRankMEG

/-- **Assumption 1 (strict complementarity)**: with `r* = rank(X*)`,
`λ_{n−r*}(∇f(X*)) − λ_n(∇f(X*)) ≥ δ`, with parameter `δ > 0`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Assumption 1, p.3.

**Formalization Note.** `n - Xs.rank` is natural-number subtraction. Every statement using this
definition assumes `Xs.rank < n`, so it is exact and the index lies in `1, …, n`. -/
def StrictComplementarity {n : ℕ} (grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
    (Xs : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ lam (grad Xs) (n - Xs.rank) - lam (grad Xs) n

end LowRankMEG


