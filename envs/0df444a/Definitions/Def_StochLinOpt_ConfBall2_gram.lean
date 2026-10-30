-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_gram
-- name    : StochLinOpt_ConfBall2_gram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:47:08.012374+00:00
-- url     : https://prove2.me/theorems/6e578bea-66b4-4cd6-8ae3-f4faf8e362d6
-- title:
--   Precision matrix $A_t$
-- statement:
--   Given a barycentric spanner $b_1,\dots,b_n$ and decisions $x_1,x_2,\dots\in\mathbb R^n$, the **precision matrix** at round $t\ge1$ is
--
--   $$A_t=\sum_{i=1}^n b_ib_i^\top+\sum_{1\le\tau<t}x_\tau x_\tau^\top .$$
--
--   Thus $A_1=\sum_i b_ib_i^\top$ and $A_{t+1}=A_t+x_tx_t^\top$, which is the update of Algorithm 3.1. If the spanner spans $\mathbb R^n$, every $A_t$ is positive definite.
--
--   **Formalization Note** Rounds are numbered from $1$; the decision sequence is indexed by $\mathbb N$ and its entry at index $0$ is never read.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, §3.1, p. 4 (definition of A_t); Algorithm 3.1, p. 4

import Mathlib
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The precision matrix `A_t`** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, §3.1, p. 4:
"At = Σ_{i=1}^n bib†i + Σ_{τ<t} xτx†τ where b1, . . . , bn is the barycentric spanner";
Algorithm 3.1: "A1 = Σ_{i=1}^n bib†i", "At+1 = At + xtx†t").

`gram b x t = ∑ i, b i b iᵀ + ∑_{1 ≤ τ < t} x τ x τᵀ`.

**Formalization Note** Rounds are 1-based: `x : ℕ → (Fin n → ℝ)` and only `x τ` with `τ ≥ 1` is
read, so `gram b x 1 = ∑ i, b i b iᵀ` (the algorithm's `A_1`) and
`gram b x (t+1) = gram b x t + x t x tᵀ` for `t ≥ 1`. `Matrix.vecMulVec u u` is `u uᵀ`. -/
def gram {n : ℕ} (b : Fin n → Fin n → ℝ) (x : ℕ → Fin n → ℝ) (t : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, Matrix.vecMulVec (b i) (b i) + ∑ τ ∈ Finset.Ico 1 t, Matrix.vecMulVec (x τ) (x τ)

end StochLinOpt.ConfBall2


