-- Prove2me | Definitions.Def_MarkovSA_winSum
-- name    : MarkovSA_winSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:17.691735+00:00
-- url     : https://prove2.me/theorems/190d8f6e-8a61-4f5d-82c2-7ab9f021b955
-- title:
--   Window sums $\alpha_{i,j-1}=\sum_{l=i}^{j-1}\alpha_l$
-- statement:
--   The paper writes $\alpha_{i,j}=\sum_{k=i}^{j}\alpha_k$. The mission's window sum is
--
--   $$
--   \mathrm{winSum}(\alpha,i,j)=\sum_{l=i}^{j-1}\alpha_l=\alpha_{i,j-1},
--   $$
--
--   so the window $\alpha_{k-t_k,k-1}$ of Condition A.1 is $\mathrm{winSum}(\alpha,k-t_k,k)$, and it is the empty sum when $t_k=0$.
--
--   **Formalization Note** Summing over $[i,j)$ avoids the natural-number subtraction $j-1$.
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Appendix A, p.24

import Mathlib

namespace MarkovSA

/-- The window sum `α_{i, j−1} = Σ_{l=i}^{j−1} α_l` (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, p.24, "we use `α_{i,j}` for `Σ_{k=i}^j α_k`").

**Formalization Note.** `winSum α i j` is the paper's `α_{i,j−1}` (sum over `[i, j)`), so the window
`α_{k−t_k, k−1}` is `winSum α (k - t k) k`; it avoids the natural-number subtraction `k − 1` and is the
empty sum when `t_k = 0`, as in the paper. -/
def winSum (α : ℕ → ℝ) (i j : ℕ) : ℝ := ∑ l ∈ Finset.Ico i j, α l

end MarkovSA


