-- Prove2me | Definitions.Def_ThinShellSampling_expTilt
-- name    : ThinShellSampling_expTilt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:25.648192+00:00
-- url     : https://prove2.me/theorems/3e6f51bd-528b-45f1-a832-9475cf59d87b
-- title:
--   Exponential and Gaussian tilts $\mu_\varphi\propto e^{-\varphi}\mu$, $\pi_t\propto e^{-\|x\|^2/(2t)}\pi$
-- statement:
--   For a measure $\mu$ and a function $\varphi$, the **exponential tilt** of $\mu$ by $\varphi$ is the probability measure
--
--   $$
--   \mu_\varphi(dx)=\frac{e^{-\varphi(x)}\,\mu(dx)}{\int e^{-\varphi}\,d\mu}.
--   $$
--
--   The **Gaussian tilt** of a measure $\pi$ on $\mathbb R^n$ at scale $t>0$ is $\pi_t(dx)\propto \exp\{-\|x\|^2/(2t)\}\,\pi(dx)$, a continuous version of Gaussian cooling.
--
--   These tilts give the quadratic tilts $\nu_s\propto e^{-s\langle x,Mx\rangle}\nu$ and $\nu_s\propto e^{-s\|M^{1/2}x+u\|^2}\nu$ of §4, the tilts $\nu_s\propto e^{-s\|x\|^2}\nu$ of §5.2, the annealing laws (6.1), and the backward kernel of the proximal sampler.
--
--   **Formalization Note** The normalizer $\int e^{-\varphi}\,d\mu$ lies in $[0,\infty]$; every use in the mission has it positive and finite, so the tilt is a probability measure.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.4 (PDF p.6) (Gaussian tilt); §4, pp.24–25; §5.2, p.31; (6.1), p.36

import Mathlib

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- **Exponential tilt** `μ_φ(dx) ∝ e^{−φ(x)} μ(dx)`: the measure `μ` reweighted by `e^{−φ}` and
normalized to total mass one.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity*, STOC 2027 submission
(manuscript sha256 25a041a9…). Used for the Gaussian tilt `π_t(dx) ∝ exp{−‖x‖²/(2t)} π(dx)` (§1.1,
p.4 = PDF p.6), the quadratic tilts `ν_s(dx) ∝ e^{−s⟨x,Mx⟩} ν(dx)` and `ν_s(dx) ∝ e^{−s q_u(x)} ν(dx)`
(§4, pp.24–25 = PDF pp.26–27), the tilts `ν_s(dx) ∝ e^{−s‖x‖²} ν(dx)` (§5.2, p.31 = PDF p.33), the
annealing laws (6.1) (p.36 = PDF p.38), and the backward kernel of the proximal sampler (§2, p.14).

**Formalization Note.** The normalizer is `Z = ∫ e^{−φ} dμ ∈ [0, ∞]`. Every use in this mission has
`0 < Z < ∞` (a probability measure with `φ ≥ 0`, or a set of positive finite volume with bounded
`φ`), so the result is a probability measure. If `Z = ∞` the result is the zero measure and if
`Z = 0` it is `∞ • 0 = 0`; neither case occurs. -/
noncomputable def expTilt {X : Type*} [MeasurableSpace X] (μ : Measure X) (φ : X → ℝ) :
    Measure X :=
  (∫⁻ x, ENNReal.ofReal (Real.exp (-φ x)) ∂μ)⁻¹ •
    μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))

/-- **Gaussian tilt** `π_t(dx) ∝ exp{−‖x‖²/(2t)} π(dx)` of a measure on `ℝⁿ`, for `t > 0`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.4 (PDF p.6): "For
`t > 0`, we denote a Gaussian tilt of `π` by `π_t(dx) ∝ exp{−‖x‖²/(2t)} π(dx)`". With `t = σ²` this
is the `π̄_{σ²}` of Algorithm 6.6 and Lemma 6.2.

**Formalization Note.** Only `t > 0` is used. -/
noncomputable def gaussTilt {n : ℕ} (π : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  expTilt π (fun x => ‖x‖ ^ 2 / (2 * t))

end ThinShellSampling


