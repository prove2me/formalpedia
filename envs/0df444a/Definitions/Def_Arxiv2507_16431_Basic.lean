-- Prove2me | Definitions.Def_Arxiv2507_16431_Basic
-- name    : Arxiv2507_16431_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T18:36:31.582659+00:00
-- url     : https://prove2.me/theorems/c5628729-3df9-51de-bf97-6b041efd8a09
-- title:
--   Helmholtz operator and scattered wavefield (Ma and Alkhalifah, Sec. 2.1)
-- statement:
--   Objects of Section 2.1 of Ma and Alkhalifah (2025).
--
--   1. **Model domain.** Points $(x,z)$ of the two-dimensional plane $\mathbb{R}^2$ with the Euclidean inner product; $\nabla^2=\partial_x^2+\partial_z^2$ is the Laplacian.
--   2. **Helmholtz operator (eq. 1).** For a velocity model $v(x,z)$ and an angular frequency $\omega$, the frequency-domain wave operator acts on a complex-valued wavefield $U(x,z)$ by
--   $$L(v,\omega)\,U=\frac{\omega^2}{v^2}\,U+\nabla^2U.$$
--   3. **Scattered wavefield (eq. 2).** For a full wavefield $U$ and a background wavefield $U_0$, the scattered wavefield is $\delta U=U-U_0$.
--
--   These are the objects in which the paper's learning target (the scattered wavefield) and its physics loss $J_{\text{pde}}$ (eq. 8) are written.
--
--   **Formalization Note** The paper writes eq. (1) as $L(v,\omega)U=f$ and calls $L$ "the linear wave equation operator" without giving its formula. The operator used here is the constant-density Helmholtz operator $\omega^2/v^2+\nabla^2$, the one whose scattering form is the paper's eq. (2). The Laplacian is Mathlib's, which is the trace of the second Fréchet derivative; at points where the function is not twice differentiable it takes a default value, so every statement assumes twice continuous differentiability where the Laplacian is used.
-- source:
--   Ma and Alkhalifah, An effective physics-informed neural operator framework for predicting wavefields, arXiv:2507.16431v1 (2025), Section 2.1 (Problem Statement), eqs. (1)-(2), PDF pp. 4-5

import Mathlib

/-!
X. Ma and T. Alkhalifah, *An effective physics-informed neural operator framework for predicting
wavefields*, arXiv:2507.16431v1 (2025): the frequency-domain wave (Helmholtz) operator of eq. (1)
and the scattered wavefield of eq. (2), Section 2.1.
-/

noncomputable section

namespace Arxiv2507_16431

/-- Section 2.1, p. 4: the two-dimensional model domain, points `(x, z)` written as vectors of
`ℝ²` with the Euclidean inner product (coordinate `0` is `x`, coordinate `1` is `z`). -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Eq. (1), Section 2.1, p. 4: the linear wave equation operator `L(v, ω)` in the frequency domain,
`L(v, ω) U = (ω² / v²) U + ∇² U`, for a velocity model `v(x, z)`, angular frequency `ω` and a
complex-valued wavefield `U(x, z)`. The paper does not write `L` out; this is the constant-density
operator whose scattering form is eq. (2). `∇²` is Mathlib's Laplacian. -/
def helmholtzOp (v : Plane → ℝ) (ω : ℝ) (U : Plane → ℂ) : Plane → ℂ :=
  fun x => ((ω ^ 2 / v x ^ 2 : ℝ) : ℂ) * U x + Laplacian.laplacian U x

/-- Eq. (2), second line, Section 2.1, p. 5: the scattered wavefield `δU = U - U₀`, the difference
between the full wavefield `U` and the background wavefield `U₀`. -/
def scatteredField (U U0 : Plane → ℂ) : Plane → ℂ :=
  fun x => U x - U0 x

end Arxiv2507_16431


