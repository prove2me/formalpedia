-- Prove2me | Definitions.Def_GoldenRatioVI_egraalStep
-- name    : GoldenRatioVI_egraalStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:22:50.538993+00:00
-- url     : https://prove2.me/theorems/e2bb9e6f-02fd-4ec8-8f19-5b96dd616c8a
-- title:
--   Stepsize rule (15) of EGRAAL with $0/0=+\infty$
-- statement:
--   Let $F:\mathcal E\to\mathcal E$, $\varphi>1$, $\bar\lambda>0$, and let $\rho=\frac1\varphi+\frac1{\varphi^2}$. Given the previous stepsize $\lambda_{k-1}$, the previous ratio $\theta_{k-1}$ and the iterates $z^k, z^{k-1}$, the **EGRAAL stepsize** is
--   $$\lambda_k=\min\Big\{\rho\lambda_{k-1},\ \frac{\varphi\theta_{k-1}}{4\lambda_{k-1}}\,\frac{\|z^k-z^{k-1}\|^2}{\|F(z^k)-F(z^{k-1})\|^2},\ \bar\lambda\Big\},$$
--   with the convention $\frac00=+\infty$: if $F(z^k)=F(z^{k-1})$ the middle entry is $+\infty$ and $\lambda_k=\min\{\rho\lambda_{k-1},\bar\lambda\}$.
--
--   The middle entry is an estimate of the inverse local Lipschitz constant of $F$ from the two latest iterates; no linesearch is needed.
--
--   **Formalization Note** The case $F(z^k)=F(z^{k-1})$ is an explicit branch, so Lean's convention $x/0=0$ never enters the minimum.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (2018), §2.1, p. 5, Algorithm 1, eq. (15) and the convention 0/0 = +∞

import Mathlib

namespace GoldenRatioVI

/-- **The stepsize rule (15) of the Explicit Golden Ratio Algorithm, with `0/0 = +∞`.**
Malitsky, *Golden Ratio Algorithms for Variational Inequalities*, preprint (2018), §2.1, p. 5,
Algorithm 1, eq. (15):
"λk = min{ρλk−1, φθk−1/(4λk−1) · ‖zk − zk−1‖²/‖F(zk) − F(zk−1)‖², λ̄}", with "ρ = 1/φ + 1/φ²"
and "For simplicity, we adopt the convention 0/0 = +∞."

`egraalStep F phi lamPrev thetaPrev lbar zk zprev` is
* `min (ρ · lamPrev) lbar` if `F zk = F zprev`, and
* `min (min (ρ · lamPrev) (phi · thetaPrev / (4 · lamPrev) · ‖zk − zprev‖² / ‖F zk − F zprev‖²)) lbar`
  otherwise,
where `ρ = 1/phi + 1/phi²`.

**Formalization Note.** When `F zk = F zprev` the middle entry of the paper's minimum is `a/0` with
`a ≥ 0`, which is `+∞` (by the paper's convention `0/0 = +∞` when `a = 0`, and as usual when
`a > 0`); it therefore drops out of the minimum. The explicit `if` prevents Lean's `x / 0 = 0` from
putting `0` into the minimum. -/
noncomputable def egraalStep {E : Type*} [NormedAddCommGroup E] (F : E → E)
    (phi lamPrev thetaPrev lbar : ℝ) (zk zprev : E) : ℝ :=
  open Classical in
  if F zk = F zprev then min ((1 / phi + 1 / phi ^ 2) * lamPrev) lbar
  else min (min ((1 / phi + 1 / phi ^ 2) * lamPrev)
      (phi * thetaPrev / (4 * lamPrev) * (‖zk - zprev‖ ^ 2 / ‖F zk - F zprev‖ ^ 2))) lbar

end GoldenRatioVI


