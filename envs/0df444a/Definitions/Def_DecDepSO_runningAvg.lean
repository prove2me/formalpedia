-- Prove2me | Definitions.Def_DecDepSO_runningAvg
-- name    : DecDepSO_runningAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:46.411423+00:00
-- url     : https://prove2.me/theorems/17da399e-f989-4471-974a-e9145b91e7f8
-- title:
--   The running average $\hat x_0=x_0$, $\hat x_t=(1-c_t)\hat x_{t-1}+c_t x_t$
-- statement:
--   Given weights $(c_t)_{t\ge1}$ and points $x_0,x_1,\dots$ (random, i.e. functions of the outcome $\omega$), the **running average** is defined recursively by
--   $$
--   \hat x_0:=x_0,\qquad \hat x_t:=(1-c_t)\,\hat x_{t-1}+c_t\,x_t\quad(t\ge1),
--   $$
--   pointwise in $\omega$. Appendix A uses the weights $c_t=\hat\delta_t=\delta_t(c_1+c_2)/(1+c_2\delta_t)$; Theorem 7.3 uses the constant weight $c_t=\hat\alpha\eta/2$.
--
--   When every $c_t\in[0,1]$, $\hat x_t$ is a convex combination of $x_0,\dots,x_t$.
--
--   **Formalization Note** The weight $c_0$ is not used. The definition assumes nothing about the weights.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Appendix A, p.47 (definition of x̂t); Theorem 7.3, p.27

import Mathlib

namespace DecDepSO

/-- **The running average `x̂_t` of a sequence of random points.**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, Appendix A, p.47: "x̂0 := x0 and x̂t := (1 − δ̂t)x̂t−1 + δ̂txt ∀t ≥ 1"; and
Theorem 7.3, p.27: "the average iterate is defined recursively by x̂t = (1 − α̂η/2)x̂t−1 + (α̂η/2)xt".

`runningAvg c x` is defined by `x̂_0 = x_0` and `x̂_{t+1} = (1 − c_{t+1}) x̂_t + c_{t+1} x_{t+1}`,
pointwise in the outcome `ω`. Theorem 7.3 uses the constant weight `c_t = α̂η/2`; Lemma A.2 the
weights `c_t = δ̂_t`.

**Formalization Note.** The weight `c_0` is never used. No range of the weights is assumed in the
definition; the theorems that use it have weights in `[0, 1)`, so `x̂_t` is a convex combination of
`x_0, …, x_t`. -/
noncomputable def runningAvg {Ω E : Type*} [AddCommGroup E] [Module ℝ E] (c : ℕ → ℝ)
    (x : ℕ → Ω → E) : ℕ → Ω → E
  | 0 => x 0
  | t + 1 => fun ω => (1 - c (t + 1)) • runningAvg c x t ω + c (t + 1) • x (t + 1) ω

end DecDepSO


