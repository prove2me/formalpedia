-- Prove2me | Definitions.Def_IllCondRegMem_phi
-- name    : IllCondRegMem_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:49.812745+00:00
-- url     : https://prove2.me/theorems/746956e0-f7d0-4532-bb5d-6fbe4ba1c3a9
-- title:
--   The smoothing kernel $\phi(t)=\frac{\sin(2Rt)}{\pi t}e^{-t^2/(2r^2)}$ and its Fourier transform
-- statement:
--   For parameters $R,r>0$ the **smoothing kernel** is
--   $$
--   \phi(t)=\frac{\sin(2Rt)}{\pi t}\,e^{-t^2/(2r^2)},\qquad \phi(0)=\frac{2R}{\pi},
--   $$
--   the value at $0$ being the continuous extension. Its **Fourier transform**, in the paper's non-unitary convention, is
--   $$
--   \hat\phi(\xi)=\int_{\mathbb R}\phi(t)\,e^{i\xi t}\,dt .
--   $$
--   The kernel is a band-limited sinc function damped by a Gaussian; convolving with it removes the high-frequency part of a density along one direction.
--
--   **Formalization Note** $\hat\phi$ is complex-valued and is not Mathlib's `Real.fourierIntegral` (which uses $e^{-2\pi i t\xi}$).
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), eq. (6), p.11 (PDF p.12); eq. (74), p.39 (PDF p.40); Fourier convention, p.12 (PDF p.13)

import Mathlib

open MeasureTheory

namespace IllCondRegMem

/-- **Smoothing kernel** `ϕ` (eq. (6)).
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), eq. (6),
p.11: "ϕ(t) := sin(2Rt)/(πt) · e^{−t²/(2r²)}, R, r > 0", with "the continuous extension
ϕ(0) = 2R/π" (App. A, eq. (74), p.39).

**Formalization Note.** The value at `t = 0` is the continuous extension `2R/π`. -/
noncomputable def phi (R r : ℝ) (t : ℝ) : ℝ :=
  if t = 0 then 2 * R / Real.pi
  else Real.sin (2 * R * t) / (Real.pi * t) * Real.exp (-t ^ 2 / (2 * r ^ 2))

/-- **Fourier transform of `ϕ`** in the paper's non-unitary convention.
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), §4, p.12:
"we use the non-unitary Fourier convention: for sufficiently nice f, we denote
f̂(ξ) = ∫ f(x) e^{iξᵀx}".

`phiHat R r ξ = ∫ ϕ(t) e^{iξt} dt`, a complex number.

**Formalization Note.** This is not Mathlib's `Real.fourierIntegral` (which uses `e^{−2πitξ}`);
the exponent is `+iξt` with no `2π`. -/
noncomputable def phiHat (R r ξ : ℝ) : ℂ :=
  ∫ t : ℝ, (phi R r t : ℂ) * Complex.exp (Complex.I * ξ * t)

end IllCondRegMem


