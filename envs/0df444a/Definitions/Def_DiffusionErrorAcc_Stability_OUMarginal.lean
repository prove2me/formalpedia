-- Prove2me | Definitions.Def_DiffusionErrorAcc_Stability_OUMarginal
-- name    : DiffusionErrorAcc_Stability_OUMarginal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:58:21.317192+00:00
-- url     : https://prove2.me/theorems/8df34f2d-f0cf-4e17-8988-6a84ab341d32
-- title:
--   The Ornstein–Uhlenbeck marginals p_t = Law(e^{−t}Z_0 + √(1 − e^{−2t})G), the true score ∇log p_t and the posterior statistics f_t(y) = E[f(Z_0) | Z_t = y]
-- statement:
--   The forward diffusion is the Ornstein–Uhlenbeck SDE $dZ_t=-Z_t\,dt+\sqrt2\,dW_t$, $Z_0\sim p=\rho\,dx$ (2.1). Its marginal is $p_t=\mathrm{Law}(e^{-t}Z_0+\sqrt{1-e^{-2t}}\,G)$ with $G\sim N(0,I_d)$ independent of $Z_0$. With the Gaussian density $\varphi_s(w)=(2\pi s)^{-d/2}\exp(-\|w\|^2/(2s))$ (`gaussKernel`), the density of $p_t$ is
--   $$p_t(y)=\int\rho(z)\,\varphi_{1-e^{-2t}}(y-e^{-t}z)\,dz\quad(t>0),\qquad p_0=\rho$$
--   (`ouDensity`); `ouMarginal ρ t` is the law with this density, and the **true score** is $\nabla\log p_t(x)$, the gradient in $x$ of the log-density (`ouScore`).
--
--   The **posterior statistic** of a (real- or vector-valued) $f$ is $f_t(y)=\mathbb E[f(Z_0)\mid Z_t=y]$, given by Bayes' formula with the Gaussian kernel,
--   $$f_t(y)=\frac{\int f(z)\rho(z)\varphi_{1-e^{-2t}}(y-e^{-t}z)\,dz}{p_t(y)}\quad(t>0),\qquad f_0=f$$
--   (`ouPosterior`). For a vector field $V$, $V_t(y)=e^{-t}\,\mathbb E[V(Z_0)\mid Z_t=y]$ of (B.4) is `fun y => exp(−t) • ouPosterior ρ V t y`.
--
--   **Formalization Note.** Only $t\ge0$ is used. The joint weight $\rho(z)\varphi_{1-e^{-2t}}(y-e^{-t}z)$ is `ouJoint`.
-- source:
--   Giapitzakis, Moitra, Risteski, Rohatgi, Error accumulation in reverse diffusion with an imperfect score: beyond path-space analyses, STOC 2027 submission (manuscript sha256 c0118fd2…), p. 8, (2.1) and the marginal law p_t; p. 23 (posterior statistic f_t, Appendix B notation); p. 24, (B.4)

import Mathlib
import Definitions.Def_DiffusionErrorAcc_Stability_Densities

open MeasureTheory
open scoped ENNReal NNReal

namespace DiffusionErrorAcc.Stability

/-! # The Ornstein–Uhlenbeck marginals `p_t`, the true score `∇ log p_t` and the posterior
statistics `f_t(y) = E[f(Z_0) | Z_t = y]` (Giapitzakis–Moitra–Risteski–Rohatgi, (2.1) p. 8;
Appendix B notation p. 23; (B.4) p. 24)

The forward process `dZ_t = −Z_t dt + √2 dW_t`, `Z_0 ∼ p = ρ dx`, has marginal
`p_t = Law(e^{−t} Z_0 + √(1 − e^{−2t}) G)`, `G ∼ N(0, I_d)` independent of `Z_0`. For `t > 0`
its density is the Gaussian convolution
`p_t(y) = ∫ ρ(z) φ_{1−e^{−2t}}(y − e^{−t} z) dz`, and `p_0 = p`. Only `t ≥ 0` is used. -/

/-- The centred Gaussian density on `ℝ^d` with covariance `s I_d`:
`φ_s(w) = (2π s)^{−d/2} exp(−‖w‖² / (2s))` (used with `s = 1 − e^{−2t} > 0`). -/
noncomputable def gaussKernel (d : ℕ) (s : ℝ) (w : Rd d) : ℝ :=
  (2 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖w‖ ^ 2 / (2 * s))

/-- The joint weight `ρ(z) φ_{1−e^{−2t}}(y − e^{−t} z)` of `(Z_0, Z_t) = (z, y)` (density of the
joint law of `(Z_0, Z_t)` for `t > 0`). -/
noncomputable def ouJoint {d : ℕ} (ρ : Rd d → ℝ) (t : ℝ) (y z : Rd d) : ℝ :=
  ρ z * gaussKernel d (1 - Real.exp (-2 * t)) (y - Real.exp (-t) • z)

/-- The density of the OU marginal `p_t`: `ρ` at `t = 0`, and for `t > 0`
`p_t(y) = ∫ ρ(z) φ_{1−e^{−2t}}(y − e^{−t} z) dz`. -/
noncomputable def ouDensity {d : ℕ} (ρ : Rd d → ℝ) (t : ℝ) (y : Rd d) : ℝ :=
  if t = 0 then ρ y else ∫ z, ouJoint ρ t y z

/-- The OU marginal `p_t = Law(e^{−t} Z_0 + √(1 − e^{−2t}) G)` as a measure on `ℝ^d`
(`p_0 = p = densMeasure ρ`). -/
noncomputable def ouMarginal {d : ℕ} (ρ : Rd d → ℝ) (t : ℝ) : Measure (Rd d) :=
  densMeasure (ouDensity ρ t)

/-- The true score `∇ log p_t (x)`, the gradient in `x` of the log-density of `p_t`. -/
noncomputable def ouScore {d : ℕ} (ρ : Rd d → ℝ) (t : ℝ) (x : Rd d) : Rd d :=
  gradient (fun y => Real.log (ouDensity ρ t y)) x

/-- The posterior statistic `f_t(y) = E[f(Z_0) | Z_t = y]` of the forward OU process, by Bayes'
formula with the Gaussian kernel: `f_0 = f` and, for `t > 0`,
`f_t(y) = ∫ f(z) ρ(z) φ_{1−e^{−2t}}(y − e^{−t} z) dz / p_t(y)`. Defined for real or vector
valued `f`; with `f = V` a vector field, `e^{−t} f_t` is the field `V_t` of (B.4). -/
noncomputable def ouPosterior {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : Rd d → ℝ) (f : Rd d → F) (t : ℝ) (y : Rd d) : F :=
  if t = 0 then f y else (ouDensity ρ t y)⁻¹ • ∫ z, ouJoint ρ t y z • f z

end DiffusionErrorAcc.Stability


