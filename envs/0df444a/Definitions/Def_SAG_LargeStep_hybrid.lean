-- Prove2me | Definitions.Def_SAG_LargeStep_hybrid
-- name    : SAG_LargeStep_hybrid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:05.616323+00:00
-- url     : https://prove2.me/theorems/2ede5708-f405-4b88-a616-c8a735264f40
-- title:
--   The run of Proposition 2: one SG pass, average of its iterates, table reset to 0, then SAG with α = 1/(2nμ)
-- statement:
--   Proposition 2 is about the following run, described on p. 6 after the proposition and in §A.6 Step 3. Let $k\ge n$ and let $i_1,\dots,i_k$ be indices in $\{1,\dots,n\}$.
--
--   1. **Stochastic gradient phase.** Starting from $\tilde x^0=x^0$, compute $\tilde x^1,\dots,\tilde x^{n-1}$ by $\tilde x^j=\tilde x^{j-1}-\gamma_j f'_{i_j}(\tilde x^{j-1})$ with $\gamma_j=1/(2L+\frac\mu2 j)$.
--   2. **Initialization of SAG.** Set
--   $$x^n=\frac1n\sum_{j=0}^{n-1}\tilde x^j,\qquad y^n_1=\dots=y^n_n=0 .$$
--   3. **SAG phase.** Apply the SAG iterations with step size $\alpha=\frac1{2n\mu}$ from $(y^n,x^n)$, with the indices $i_{n+1},\dots,i_k$.
--
--   The value is the final SAG iterate $x^k$.
--
--   The paper says: "We state this result for $k\ge n$ because we assume that the first $n$ iterations of the algorithm use an SG method and that we initialize the subsequent SAG iterations with the average of the iterates [...] Note that this bound is obtained when initializing all $y_i$ to zero after the SG phase."
--
--   **Formalization Note** `hybrid f' L μ x0 js` takes `js : Fin k → Fin n`. The SG phase uses `js 0, …, js (n-2)`, the index `js (n-1)` (iteration $n$, whose gradient the paper does not use) is drawn but not used, and SAG uses `js n, …, js (k-1)`. Under the uniform law on `Fin k → Fin n`, an unused coordinate does not change any expectation.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 6 (Proposition 2 and the paragraph after it); p. 30, §A.6 Step 3

import Mathlib
import Definitions.Def_SAG_LargeStep_sagRun
import Definitions.Def_SAG_LargeStep_sgRun

namespace SAG.LargeStep

/-- The run that Proposition 2 is about (p. 6, paragraph after Proposition 2; §A.6 Step 3,
p. 30), for an index sequence `js : Fin k → Fin n` with `k ≥ n`:
1. stochastic gradient from `x̃⁰ = x0` with steps `γ_j = 1/(2L + μj/2)`, producing
   `x̃⁰, …, x̃ⁿ⁻¹` (it uses the indices `js 0, …, js (n − 2)`);
2. `xⁿ = (1/n) ∑_{j=0}^{n−1} x̃ʲ`, and the gradient table is reset to `yⁿ = 0`;
3. SAG iterations with step size `α = 1/(2nμ)` from `(0, xⁿ)`, using the indices
   `js n, …, js (k − 1)` (`k − n` iterations).
The index `js (n − 1)` is drawn and not used. The value is the final iterate `xᵏ`. -/
noncomputable def hybrid {p n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L μ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin p)) (js : Fin k → Fin n) : EuclideanSpace ℝ (Fin p) :=
  (runFrom f' (1 / (2 * (n : ℝ) * μ))
    (fun _ => 0,
      (1 / (n : ℝ)) • ∑ j ∈ Finset.range n, sgIterate f' (sgStepSize L μ) x0 js j)
    ((List.ofFn js).drop n)).2

end SAG.LargeStep


