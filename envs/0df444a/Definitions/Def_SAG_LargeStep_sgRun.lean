-- Prove2me | Definitions.Def_SAG_LargeStep_sgRun
-- name    : SAG_LargeStep_sgRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:12.278397+00:00
-- url     : https://prove2.me/theorems/f2ebe175-6702-4ce6-9d35-ceef02ad0863
-- title:
--   Stochastic gradient iterates x̃ʲ = x̃ʲ⁻¹ − γ_j f′_{i_j}(x̃ʲ⁻¹) and the steps γ_j = 1/(2L + μj/2) (§A.3)
-- statement:
--   Given a start $\tilde x^0\in\mathbb R^p$, step sizes $\gamma_1,\gamma_2,\dots$ and indices $i_1,\dots,i_K\in\{1,\dots,n\}$, the **stochastic gradient iterates** are
--   $$\tilde x^j=\tilde x^{j-1}-\gamma_j\,f'_{i_j}(\tilde x^{j-1}),\qquad j=1,\dots,K .$$
--   The paper's step sizes for the warm start are
--   $$\gamma_j=\frac{1}{2L+\frac\mu2 j}.$$
--
--   These iterates are used to initialize SAG in Proposition 2.
--
--   **Formalization Note** `sgIterate f' γ x0 js j` is $\tilde x^j$ for `js : Fin K → Fin n`; step $j$ uses `js (j-1)` (0-based indexing). For $j>K$ the iterate stays at $\tilde x^K$; no statement uses that range. `sgStepSize L μ j` is $\gamma_j$.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 14, §A.3 (recursion); p. 15 (choice of γ_k)

import Mathlib

namespace SAG.LargeStep

/-- The stochastic gradient step sizes of §A.3 (p. 15): `γ_j = 1/(2L + (μ/2) j)`. -/
noncomputable def sgStepSize (L μ : ℝ) (j : ℕ) : ℝ :=
  1 / (2 * L + μ / 2 * (j : ℝ))

/-- The stochastic gradient iterates of §A.3 (p. 14), `x̃ʲ = x̃ʲ⁻¹ − γ_j f'_{i_j}(x̃ʲ⁻¹)`, from
`x̃⁰ = x0`, for the index sequence `js = (i_1, …, i_K)` (0-based: step `j` uses `js (j − 1)`) and
an arbitrary step-size sequence `γ`. Iterate `j ≤ K` uses the first `j` indices; past `K` the
iterate is frozen (never used in a statement). -/
noncomputable def sgIterate {p n K : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (γ : ℕ → ℝ)
    (x0 : EuclideanSpace ℝ (Fin p)) (js : Fin K → Fin n) : ℕ → EuclideanSpace ℝ (Fin p)
  | 0 => x0
  | j + 1 =>
    if h : j < K then
      sgIterate f' γ x0 js j - γ (j + 1) • f' (js ⟨j, h⟩) (sgIterate f' γ x0 js j)
    else sgIterate f' γ x0 js j

end SAG.LargeStep


