-- Prove2me | Definitions.Def_OnlineSaddlePoint_Supplement_onePointEstimate
-- name    : OnlineSaddlePoint_Supplement_onePointEstimate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:51:47.95436+00:00
-- url     : https://prove2.me/theorems/6438b49d-7f8f-54ea-8626-9bca2b6a1238
-- title:
--   One-point estimate $\hat A=\frac{A_{i'j'}}{x_{i'}y_{j'}}e_{i'}e_{j'}^\top$
-- statement:
--   Let $A$ be a real $d_1\times d_2$ matrix, $x\in\mathbb R^{d_1}$, $y\in\mathbb R^{d_2}$, and let $(i',j')$ be a pair of actions. The **one-point estimate** of $A$ from the entry $(i',j')$ is the $d_1\times d_2$ matrix $\hat A$ with
--
--   $$
--   \hat A_{i,j}=\begin{cases}\dfrac{A_{i',j'}}{x_{i'}\,y_{j'}}, & (i,j)=(i',j'),\\[4pt] 0, & \text{otherwise.}\end{cases}
--   $$
--
--   With bandit feedback the players observe only the entry $A_{i'j'}$ of the action pair they sampled; $\hat A$ is the importance-weighted estimate of the whole matrix built from that single entry.
--
--   **Formalization Note** The printed "$\hat A_{i,j}=0$ for all $i,j$ such that $i\ne i'$ and $j\ne j'$" is read as $(i,j)\ne(i',j')$, as the proof on p.20 shows ($\hat A$ is a multiple of the matrix $B_{i',j'}$ that is zero except in entry $(i',j')$).
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Theorem 4, p.19 (proof p.20)

import Mathlib

namespace OnlineSaddlePoint.Supplement

/-- **One-point estimate `Â` of a payoff matrix.** Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3,
Theorem 4, p.19: "Sample `i′ ∼ x`, `j′ ∼ y`. Let `Â` be the `d₁ × d₂` matrix with `Â_{i,j} = 0` for
all `i, j` such that `i ≠ i′` and `j ≠ j′` and `Â_{i′,j′} = A_{i′,j′}/(x_{i′} y_{j′})`."
`onePointEstimate A x y i' j'` is the matrix `Â` obtained when the sampled pair is `(i′, j′)`.

**Formalization Note.** The printed "`i ≠ i′` and `j ≠ j′`" is read as `(i, j) ≠ (i′, j′)`: the proof
on p.20 writes `Â = (A_{i′,j′}/(x_{i′}y_{j′})) B_{i′,j′}` with `B_{i,j}` "the matrix with all zeros
except in entry `(i, j)`", so every entry other than `(i′, j′)` is `0`. With the literal reading the
entries in row `i′` and column `j′` would be left unspecified. Points are in
`PiLp 1 (fun _ : Fin d => ℝ)`. -/
noncomputable def onePointEstimate {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ)
    (x : PiLp 1 (fun _ : Fin d₁ => ℝ)) (y : PiLp 1 (fun _ : Fin d₂ => ℝ)) (i' : Fin d₁)
    (j' : Fin d₂) : Matrix (Fin d₁) (Fin d₂) ℝ :=
  fun i j => if i = i' ∧ j = j' then A i' j' / (x i' * y j') else 0

end OnlineSaddlePoint.Supplement


