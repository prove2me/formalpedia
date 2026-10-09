-- Prove2me | Definitions.Def_NonconvexSaddle_PGDVar_Setting
-- name    : NonconvexSaddle_PGDVar_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:10:12.789213+00:00
-- url     : https://prove2.me/theorems/ca274a17-f01d-460e-a0d5-c246a30a2d8e
-- title:
--   Assumption A, ε-second-order stationarity, the gradient descent map and the parameters of Eq. (6)
-- statement:
--   We work in $\mathbb R^d$ with the Euclidean norm $\|\cdot\|$; for a linear operator on $\mathbb R^d$, $\|\cdot\|$ is the spectral (operator) norm. For a differentiable $f:\mathbb R^d\to\mathbb R$ write $\nabla f$ for its gradient, and, when the gradient map is itself differentiable, $\nabla^2 f(x)$ for the Hessian, the derivative of $\nabla f$ at $x$.
--
--   1. **Gradient Lipschitz (Definition 1).** A differentiable $f$ is $\ell$-gradient Lipschitz if $\|\nabla f(x_1)-\nabla f(x_2)\|\le \ell\|x_1-x_2\|$ for all $x_1,x_2$.
--   2. **Hessian Lipschitz (Definition 2).** A twice-differentiable $f$ is $\rho$-Hessian Lipschitz if $\|\nabla^2 f(x_1)-\nabla^2 f(x_2)\|\le\rho\|x_1-x_2\|$ for all $x_1,x_2$.
--   3. **Assumption A.** $f$ is $\ell$-gradient Lipschitz and $\rho$-Hessian Lipschitz.
--   4. **$\varepsilon$-second-order stationary point (Definition 9).** $x$ is one if
--   $$\|\nabla f(x)\|\le\varepsilon \quad\text{and}\quad \nabla^2 f(x)\succeq -\sqrt{\rho\varepsilon}\,I .$$
--   5. **Global minimum.** $f^\star=\inf_x f(x)$.
--   6. **Gradient descent.** One step is $x\mapsto x-\eta\nabla f(x)$ (Eq. (1)); $x_t$ is its $t$-fold iterate from $x_0$.
--   7. **Parameters of Eq. (6).** For $\iota$ and the constants $\ell,\rho,\varepsilon$,
--   $$\eta=\frac1\ell,\qquad r=\frac{\varepsilon}{400\iota^3},\qquad \mathscr T=\frac{\ell}{\sqrt{\rho\varepsilon}}\cdot\iota,\qquad \mathscr F=\frac{1}{50\iota^3}\sqrt{\frac{\varepsilon^3}{\rho}},\qquad \mathscr S=\frac{1}{4\iota}\sqrt{\frac{\varepsilon}{\rho}},$$
--   together with the width $\omega=2^{2-\iota}\ell\mathscr S$ of Lemma 22.
--   8. **Perturbation law.** $\mathrm{Uniform}(B_0(r))$ is Lebesgue measure on the open ball of radius $r$ around $0$, normalized to total mass one.
--
--   These are the objects shared by every statement of the mission: the lemmas of §5 and Theorem 18 are written with them. Items 1–3 and 5 (Definitions 1 and 2, Assumption A, $f^\star$), the Euclidean space and the Hessian are imported from the group's shared module `NonconvexSaddle.PSGD.Setting`; this module declares items 4, 6, 7 and 8.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. The Hessian is `fderiv ℝ (gradient f) x`, a continuous linear map whose operator norm is the spectral norm; "twice differentiable" is the differentiability of $f$ and of its gradient map. The Loewner inequality of Definition 9 is written through the quadratic form, $\langle\nabla^2 f(x)v,v\rangle\ge-\sqrt{\rho\varepsilon}\|v\|^2$ for all $v$, which is $\lambda_{\min}(\nabla^2 f(x))\ge-\sqrt{\rho\varepsilon}$. $f^\star$ is Lean's real infimum, which equals the paper's $f^\star$ only for $f$ bounded below; every statement using it assumes this. $\mathscr T$ is given here as the real number $\ell\iota/\sqrt{\rho\varepsilon}$; statements take a natural number equal to it. The uniform law is `ProbabilityTheory.cond volume (ball 0 r)`.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, pp. 5–7 (§2.1 Notation, Definitions 1, 2, 9, Assumption A, Eq. (1)), p. 12 (Eq. (6)), p. 14 (ω in Lemma 22)

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open scoped RealInnerProductSpace

namespace NonconvexSaddle.PGDVar

/-- Definition 9 (p. 7): `x` is an `ε`-second-order stationary point of the `ρ`-Hessian Lipschitz `f`
if `‖∇f(x)‖ ≤ ε` and `∇²f(x) ⪰ −√(ρε)·I`. The Loewner inequality is written through the quadratic
form: `⟪∇²f(x) v, v⟫ ≥ −√(ρε)‖v‖²` for every `v`, i.e. `λ_min(∇²f(x)) ≥ −√(ρε)`. -/
def IsEpsSOSP {d : ℕ} (f : NonconvexSaddle.PSGD.E d → ℝ) (ρ ε : ℝ) (x : NonconvexSaddle.PSGD.E d) : Prop :=
  ‖gradient f x‖ ≤ ε ∧ ∀ v : NonconvexSaddle.PSGD.E d, -Real.sqrt (ρ * ε) * ‖v‖ ^ 2 ≤ ⟪NonconvexSaddle.PSGD.hess f x v, v⟫

/-- One gradient descent step `x ↦ x − η∇f(x)`, Eq. (1) (p. 6). -/
noncomputable def gdStep {d : ℕ} (f : NonconvexSaddle.PSGD.E d → ℝ) (η : ℝ) (x : NonconvexSaddle.PSGD.E d) : NonconvexSaddle.PSGD.E d :=
  x - η • gradient f x

/-- Step size of Eq. (6) (p. 12): `η = 1/ℓ`. -/
noncomputable def eta (ℓ : ℝ) : ℝ := 1 / ℓ

/-- Perturbation radius of Eq. (6) (p. 12): `r = ε/(400ι³)`. -/
noncomputable def radius (ε ι : ℝ) : ℝ := ε / (400 * ι ^ 3)

/-- The real number `ℓ/√(ρε)·ι`, the time interval `𝒯` of Eq. (6) (p. 12). The statements take `𝒯`
as a natural number equal to it. -/
noncomputable def timeInterval (ℓ ρ ε ι : ℝ) : ℝ := ℓ / Real.sqrt (ρ * ε) * ι

/-- The function decrease `ℱ = 1/(50ι³)·√(ε³/ρ)` of Eq. (6) (p. 12). -/
noncomputable def decr (ρ ε ι : ℝ) : ℝ := 1 / (50 * ι ^ 3) * Real.sqrt (ε ^ 3 / ρ)

/-- The localization radius `𝒮 = 1/(4ι)·√(ε/ρ)` of Eq. (6) (p. 12). -/
noncomputable def locRadius (ρ ε ι : ℝ) : ℝ := 1 / (4 * ι) * Real.sqrt (ε / ρ)

/-- The width `ω = 2^{2−ι}ℓ𝒮` of Lemma 22 (p. 14). -/
noncomputable def omega (ℓ ρ ε ι : ℝ) : ℝ := (2 : ℝ) ^ (2 - ι) * ℓ * locRadius ρ ε ι

/-- The uniform distribution `Uniform(B₀(r))` on the open Euclidean ball of radius `r` around `0`
(normalized Lebesgue measure; the closed ball has the same law). -/
noncomputable def uniformBall (d : ℕ) (r : ℝ) : MeasureTheory.Measure (NonconvexSaddle.PSGD.E d) :=
  ProbabilityTheory.cond MeasureTheory.volume (Metric.ball (0 : NonconvexSaddle.PSGD.E d) r)

end NonconvexSaddle.PGDVar


