-- Prove2me | Definitions.Def_ThinShellSampling_heatAdjoint
-- name    : ThinShellSampling_heatAdjoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:29.19622+00:00
-- url     : https://prove2.me/theorems/23102918-4959-4b09-aa63-eeb07d12be26
-- title:
--   Gaussian $\gamma_t$ and the heat adjoint $Q_t f=P_t(f\nu)/P_t\nu$
-- statement:
--   Let $\gamma_t$ be the centered Gaussian on $\mathbb R^n$ with covariance $tI_n$, with $\gamma_0=\delta_0$, and for a probability measure $\nu$ write $\nu_t=\nu*\gamma_t$. The **heat adjoint** is the operator $Q_t$, the $L^2(\nu)$-adjoint of the heat semigroup $P_tf=f*\gamma_t$, given for $t>0$ by
--
--   $$
--   Q_tf(y)=\frac{P_t(f\nu)}{P_t\nu}(y)=\frac{\int f(x)\,e^{-\|y-x\|^2/(2t)}\,\nu(dx)}{\int e^{-\|y-x\|^2/(2t)}\,\nu(dx)},
--   $$
--
--   and $Q_0=\mathrm{id}$. It maps $L^2(\nu)$ to $L^2(\nu_t)$ and is the backward step of the proximal sampler.
--
--   **Formalization Note** $\gamma_t$ is the image of Mathlib's `stdGaussian` under $x\mapsto\sqrt t\,x$. The Gaussian normalizing constants cancel in $Q_t$; for a probability measure $\nu$ the denominator is positive and the numerator integrable for $f\in L^p(\nu)$, $p\ge1$. Negative $t$ is not used.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.3 (PDF p.5); §3.1, p.21 (PDF p.23)

import Mathlib

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **The centered Gaussian `γ_t = N(0, t Iₙ)`** on `ℝⁿ`, for `t ≥ 0`, with `γ_0 = δ_0`.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity*, STOC 2027 submission
(manuscript sha256 25a041a9…), §1.1, p.3 (PDF p.5): "let `γ_t` denote the centered Gaussian with
covariance `tIₙ` … with `γ_0 = δ_0`"; §1.3, p.12 (PDF p.14).

**Formalization Note.** It is the push-forward of Mathlib's standard Gaussian `stdGaussian` under
`x ↦ √t · x`; at `t = 0` this is the Dirac mass at `0`. Only `t ≥ 0` is used. -/
noncomputable def gaussianT (n : ℕ) (t : ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => Real.sqrt t • x)

/-- **Heat adjoint** `Q_t f = P_t(fν)/P_tν`, the `L²(ν)`-adjoint of the heat semigroup.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.3 (PDF p.5): "We write
`ν_t = ν ∗ γ_t`, with `γ_0 = δ_0` and `P_0 = Q_0 = id`. … `Q_t f := P_t(fν)/P_tν`"; §3.1, p.21
(PDF p.23): `Q_t f(y) = ∫ f(x) ν(x) γ_t(y − x) dx / ∫ ν(x) γ_t(y − x) dx`.

**Formalization Note.** For `t > 0`,
`Q_t f(y) = ∫ f(x) e^{−‖y−x‖²/(2t)} ν(dx) / ∫ e^{−‖y−x‖²/(2t)} ν(dx)`; the Gaussian normalizing
constants cancel. For a probability measure `ν` the denominator is positive, and for `f ∈ L^p(ν)`,
`p ≥ 1`, the numerator integrand is integrable (the weight is at most `1`), so no junk value enters.
For `t ≤ 0` the operator is the identity (`Q_0 = id`; negative `t` is not used). -/
noncomputable def heatAdjoint {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  if t ≤ 0 then f
  else fun y =>
    (∫ x, f x * Real.exp (-‖y - x‖ ^ 2 / (2 * t)) ∂ν) /
      (∫ x, Real.exp (-‖y - x‖ ^ 2 / (2 * t)) ∂ν)

end ThinShellSampling


