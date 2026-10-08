-- Prove2me | Definitions.Def_ErlangA_Diffusion_InfinitesimalMoments
-- name    : ErlangA_Diffusion_InfinitesimalMoments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:01:54.696259+00:00
-- url     : https://prove2.me/theorems/0b7098af-3410-4ac4-b714-ffe4da301149
-- title:
--   Infinitesimal expectation $\mu_N(x)$ and variance $\sigma_N^2(x)$ of the scaled Erlang-A queue
-- statement:
--   Let $N \ge 1$ agents serve at rate $\mu$, let callers arrive at rate $\lambda_N$ and abandon at patience rate $\theta_N$. In Appendix C of Garnett, Mandelbaum and Reiman (2002), the **infinitesimal expectation** and **infinitesimal variance** of the scaled queue-length process $q_N = (Q_N - N)/\sqrt N$ at the point $x \in \mathbb R$ are
--   $$
--   \mu_N(x) = \begin{cases} -\dfrac{\lfloor N + \sqrt N x\rfloor \mu}{\sqrt N} + \dfrac{\lambda_N}{\sqrt N}, & x \le 0,\\[2mm] -\dfrac{N\mu + \lfloor \sqrt N x\rfloor \theta_N}{\sqrt N} + \dfrac{\lambda_N}{\sqrt N}, & x > 0,\end{cases}
--   \qquad
--   \sigma_N^2(x) = \begin{cases} \dfrac{\lfloor N + \sqrt N x\rfloor \mu}{N} + \dfrac{\lambda_N}{N}, & x \le 0,\\[2mm] \dfrac{N\mu + \lfloor \sqrt N x\rfloor \theta_N}{N} + \dfrac{\lambda_N}{N}, & x > 0,\end{cases}
--   $$
--   where $\lfloor\cdot\rfloor$ is the integer part.
--
--   At a lattice state $x = (k - N)/\sqrt N$ of $q_N$, $\mu_N(x)$ is the drift of $q_N$ (arrival rate minus departure rate, scaled by $1/\sqrt N$) and $\sigma_N^2(x)$ is the sum of the jump rates scaled by $(1/\sqrt N)^2$. These are the quantities whose convergence is checked through Stone's criteria in the proof of Theorem 2*.
--
--   **Formalization Note** The formulas are transcribed exactly as displayed, with $\lfloor\cdot\rfloor$ = `Int.floor`, for every real $x$ and every $N$ (at $N = 0$ the values are Lean's defaults and play no role in the limits).
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 224, App. C, proof of Theorem 2*, Part 1, display of μ_N(x) and σ_N²(x)

import Mathlib

namespace ErlangA.Diffusion

/-!
Garnett, Mandelbaum & Reiman (2002), Appendix C, proof of Theorem 2*, Part 1 (p. 224): the
infinitesimal expectation `μ_N(x)` and variance `σ_N²(x)` of the scaled process `q_N`, exactly
as displayed, with `⌊·⌋` the integer part (`Int.floor`).
-/

/-- Infinitesimal expectation (p. 224):
`μ_N(x) = −⌊N + √N x⌋ μ/√N + λ_N/√N` for `x ≤ 0` and
`μ_N(x) = −(Nμ + ⌊√N x⌋ θ_N)/√N + λ_N/√N` for `x > 0`. -/
noncomputable def infMean (lam thetaN : ℕ → ℝ) (μ : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 0 then
    -((⌊(N : ℝ) + Real.sqrt N * x⌋ : ℝ) * μ) / Real.sqrt N + lam N / Real.sqrt N
  else
    -((N : ℝ) * μ + (⌊Real.sqrt N * x⌋ : ℝ) * thetaN N) / Real.sqrt N + lam N / Real.sqrt N

/-- Infinitesimal variance (p. 224):
`σ_N²(x) = ⌊N + √N x⌋ μ/N + λ_N/N` for `x ≤ 0` and
`σ_N²(x) = (Nμ + ⌊√N x⌋ θ_N)/N + λ_N/N` for `x > 0`. -/
noncomputable def infVar (lam thetaN : ℕ → ℝ) (μ : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 0 then
    (⌊(N : ℝ) + Real.sqrt N * x⌋ : ℝ) * μ / N + lam N / N
  else
    ((N : ℝ) * μ + (⌊Real.sqrt N * x⌋ : ℝ) * thetaN N) / N + lam N / N

end ErlangA.Diffusion


