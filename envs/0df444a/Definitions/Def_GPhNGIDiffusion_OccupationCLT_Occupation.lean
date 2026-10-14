-- Prove2me | Definitions.Def_GPhNGIDiffusion_OccupationCLT_Occupation
-- name    : GPhNGIDiffusion_OccupationCLT_Occupation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:24.452622+00:00
-- url     : https://prove2.me/theorems/493097d8-124b-4842-b700-d88080fdea74
-- title:
--   pp. 4, 7, 12, 16 — empirical average E^x_t(h), ∥h∥_∞, the Stein solution (3.2) and the weighted occupation time L^{ϵ,x}_t
-- statement:
--   Let $X$ be a solution flow of the limiting diffusion, $\mu$ a measure on $\mathbb R^d$ and $h:\mathbb R^d\to\mathbb R$.
--
--   1. The **empirical average** of $h$ along the path started at $x$ is
--   $$
--   \mathcal E^x_t(h)=\frac1t\int_0^t h(X^x_s)\,ds .
--   $$
--   2. The **essential supremum norm** is $\|h\|_\infty=\operatorname{ess\,sup}_{x\in\mathbb R^d}|h(x)|$ with respect to Lebesgue measure.
--   3. The **solution of the Stein equation** $\mathcal Af=h-\mu(h)$ (3.1) is the function (3.2)
--   $$
--   f(x)=-\int_0^\infty\big(P_th(x)-\mu(h)\big)\,dt .
--   $$
--   4. For $\epsilon>0$, the **weighted occupation time** is
--   $$
--   L^{\epsilon,x}_t=\int_0^t\Big[-\frac1{\epsilon^2}(e'X^x_s)^2+1\Big]\mathbf 1_{\{|e'X^x_s|\le\epsilon\}}\,ds .
--   $$
--
--   These are the objects of Theorem 1.3: its CLT is for $\sqrt t\,[\mathcal E^x_t(h)-\mu(h)]$ and its limiting variance is $\mu(|\sigma'\nabla f|^2)$.
--
--   **Formalization Note** The integral in (3) is a Bochner integral over $(0,\infty)$; its integrand is integrable for bounded measurable $h$ (Lemma 3.2), so $f$ is the paper's function and not a default value. "The solution to (3.1)" is pinned to the representation (3.2), as the paper's Lemma 3.2 and the proof of Proposition 3.1 do.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, pp. 3–4 (E^x_T); p. 7 (∥·∥_∞); p. 12, (3.1)–(3.2); p. 16 (L^{ϵ,x}_t)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Diffusion

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The empirical (occupation) average `E^x_t(h) = (1/t) ∫₀ᵗ h(X^x_s) ds` along one path. -/
noncomputable def occAvg (X : E d → ℝ≥0 → Ω → E d) (h : E d → ℝ) (x : E d) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  (t : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(t : ℝ), h (X x s.toNNReal ω)

/-- `∥h∥_∞ = ess sup_x |h(x)|` with respect to Lebesgue measure on `ℝᵈ` (§1.4). -/
noncomputable def supNorm (h : E d → ℝ) : ℝ :=
  (eLpNormEssSup h volume).toReal

/-- The solution (3.2) of the Stein equation (3.1): `f(x) = −∫₀^∞ (P_t h(x) − μ(h)) dt`. -/
noncomputable def steinSol (P : Measure Ω) (X : E d → ℝ≥0 → Ω → E d) (μ : Measure (E d))
    (h : E d → ℝ) (x : E d) : ℝ :=
  -∫ t in Set.Ioi (0 : ℝ), (semigroup P X t.toNNReal h x - ∫ y, h y ∂μ)

/-- The weighted occupation time (p. 16)
`L^{ǫ,x}_t = ∫₀ᵗ (1 − (e′X^x_s)²/ǫ²) 1{|e′X^x_s| ≤ ǫ} ds`. -/
noncomputable def weightedOcc (X : E d → ℝ≥0 → Ω → E d) (ϵ : ℝ) (x : E d) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ),
    if |eDot (X x s.toNNReal ω)| ≤ ϵ then -(eDot (X x s.toNNReal ω)) ^ 2 / ϵ ^ 2 + 1 else 0

end GPhNGIDiffusion.OccupationCLT


