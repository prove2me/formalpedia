-- Prove2me | Definitions.Def_GeomDL_Blueprint_Fourier
-- name    : GeomDL_Blueprint_Fourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:38.068605+00:00
-- url     : https://prove2.me/theorems/97ade502-b9c7-42c5-8993-dc1d8cc28098
-- title:
--   §3.4, p. 23 — the Fourier transform x̂(ξ) = ∫ x(u)e^{−iξu} du and the shift S_v x(u) = x(u − v)
-- statement:
--   For a complex signal $x : \mathbb R \to \mathbb C$, the classical one-dimensional **Fourier transform** in the book's normalisation is
--   $$\hat x(\xi) = \int_{-\infty}^{+\infty} x(u)\, e^{-\mathrm i \xi u}\, \mathrm du, \qquad \xi \in \mathbb R,$$
--   and the **shift operator** by $v \in \mathbb R$ is $(S_v x)(u) = x(u - v)$.
--
--   These are the objects of the book's discussion of the Fourier modulus as a shift-invariant function.
--
--   **Formalization Note** The integral is the Bochner integral against Lebesgue measure, which Lean sets to $0$ when the integrand is not integrable. The exponent has no factor $2\pi$, unlike Mathlib's `Real.fourierIntegral`.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.4, Fourier transform display, p. 23; shift operator S_v, §4.2, p. 39

import Mathlib

namespace GeomDL.Blueprint

open MeasureTheory Complex

/-- Bronstein et al., §3.4, p. 23: the Fourier transform in the book's normalisation,
`x̂(ξ) = ∫ x(u) e^{−iξu} du`, for a complex signal `x : ℝ → ℂ` (Lebesgue measure on `ℝ`;
no `2π` in the exponent, unlike Mathlib's `𝓕`). The Bochner integral is `0` when the integrand
is not integrable. -/
noncomputable def fourierBook (x : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ u : ℝ, x u * Complex.exp (-(↑(ξ * u) * Complex.I))

/-- §4.2, p. 39 and §3.4, p. 25: the shift operator `(S_v x)(u) = x(u − v)`. -/
def shiftOp (v : ℝ) (x : ℝ → ℂ) : ℝ → ℂ :=
  fun u => x (u - v)

end GeomDL.Blueprint


