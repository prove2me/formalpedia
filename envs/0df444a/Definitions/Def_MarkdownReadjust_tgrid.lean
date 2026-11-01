-- Prove2me | Definitions.Def_MarkdownReadjust_tgrid
-- name    : MarkdownReadjust_tgrid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:52.941494+00:00
-- url     : https://prove2.me/theorems/39a9ceb6-ca59-475f-bcef-11389304f2e9
-- title:
--   Update times $t_n=T[1-(x_0+1)^{-n/(N+2)}]$ of (14)
-- statement:
--   For $N\ge1$ price updates, the update times are
--
--   $$
--   t_n=T\big[1-(x_0+1)^{-\frac{n}{N+2}}\big],\qquad n=1,\dots,N,
--   $$
--
--   with $t_0=0$ and $t_{N+1}=T$. With $\theta=(x_0+1)^{-1/(N+2)}$ this reads $t_n=T(1-\theta^n)$, so updates become more frequent towards the end of the horizon. The module also defines $\theta$.
--
--   **Formalization Note** The formula gives $t_0=0$; for $n\ge N+1$ the value is $T$ (only $n=N+1$ is used). The exponent is a real number.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), §7.1, eq. (14), p.18; t₀ = 0 (p.9), t_{N+1} = T (p.19); θ (p.ec11)

import Mathlib

namespace MarkdownReadjust

/-- `θ = (x₀ + 1)^{−1/(N+2)}` (Chen–Jasin, SSRN 3740871, Appendix B, p.ec11). -/
noncomputable def theta (x N : ℕ) : ℝ :=
  ((x : ℝ) + 1) ^ (-(1 : ℝ) / ((N : ℝ) + 2))

/-- The price update times of (14) (Chen–Jasin, SSRN 3740871, §7.1, p.18):
`tₙ = T[1 − (x₀+1)^{−n/(N+2)}]` for `n = 1, …, N`, with `t₀ = 0` (p.9) and `t_{N+1} = T`
(p.19), for the problem with inventory `x` and horizon `τ`.

**Formalization Note.** The formula at `n = 0` gives `t₀ = 0`; for every `n ≥ N + 1` the value
is `τ` (only `n = N + 1` is used). The exponent is the real number `−n/(N+2)`. -/
noncomputable def tgrid (x : ℕ) (τ : ℝ) (N n : ℕ) : ℝ :=
  if n ≤ N then τ * (1 - ((x : ℝ) + 1) ^ (-(n : ℝ) / ((N : ℝ) + 2))) else τ

end MarkdownReadjust


