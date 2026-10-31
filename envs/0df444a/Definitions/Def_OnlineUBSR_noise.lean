-- Prove2me | Definitions.Def_OnlineUBSR_noise
-- name    : OnlineUBSR_noise
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:54.819866+00:00
-- url     : https://prove2.me/theorems/cdc9671e-b518-41b1-87a6-b2471cc27705
-- title:
--   The noise $\varepsilon_n=\hat g(t_n)-g(t_n)$
-- statement:
--   Given iterates $(t_n)_{n\ge0}$ and samples $(\xi_n)_{n\ge1}$, the noise at step $n\ge0$ is
--
--   $$
--   \varepsilon_n=\ell(\xi_{n+1}-t_n)-\lambda-g(t_n),
--   $$
--
--   the error of the sample estimate $\hat g(t_n)=\ell(\xi_{n+1}-t_n)-\lambda$ of $g(t_n)$. With it the recursion reads $t_{n+1}=\Gamma\big(t_n+a_{n+1}(g(t_n)+\varepsilon_n)\big)$, and Assumption 4 bounds its conditional second moment.
--
--   **Formalization Note** Assumption 4 writes $\varepsilon_n=\hat g(t_n)-g(t_n)$ without naming the sample; the proof's display (26) fixes it as the fresh sample $\xi_{n+1}$, the only reading under which $\varepsilon_n$ is centred given the past. The definition takes the iterate sequence as an argument; the theorems apply it to `OnlineUBSR.iterate`.
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, Assumption 4, p.5; eq. (26), p.18

import Mathlib
import Definitions.Def_OnlineUBSR_gFun

open MeasureTheory

namespace OnlineUBSR

/-- **The noise `ε_n = ĝ(t_n) − g(t_n)` of the recursion.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Assumption 4, p.5: "Let εn = ĝ(tn) −
g(tn)", with "ĝ(t) = ℓ(ξn − t) − λ" from §4, (5), p.4.

`noise μ ℓ lam X t ξ n ω = ℓ(ξ_{n+1}(ω) − t_n(ω)) − lam − g(t_n(ω))`, for a sequence of iterates
`t : ℕ → Ω → ℝ` (in the theorems, `t = iterate …`).

**Formalization Note.** The page does not say which sample `ĝ` uses in `ε_n`. The proof's (26),
p.18, `t_n = Γ(t_{n−1} + a_n(g(t_{n−1}) + ε_{n−1}))`, fixes it: `ε_{n−1}` uses the sample `ξ_n`
that forms `t_n`, so `ε_n` uses the fresh sample `ξ_{n+1}`. This is the only reading under which
`ε_n` is centred given the past. `g` is `OnlineUBSR.gFun`. -/
noncomputable def noise {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ℓ : ℝ → ℝ) (lam : ℝ)
    (X : Ω → ℝ) (t : ℕ → Ω → ℝ) (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ℓ (ξ (n + 1) ω - t n ω) - lam - gFun μ ℓ lam X (t n ω)

end OnlineUBSR


