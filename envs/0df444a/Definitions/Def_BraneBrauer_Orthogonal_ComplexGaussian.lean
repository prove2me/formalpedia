-- Prove2me | Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian
-- name    : BraneBrauer_Orthogonal_ComplexGaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:59.024224+00:00
-- url     : https://prove2.me/theorems/4141d8d8-3db7-4e9d-a020-d296eddd78aa
-- title:
--   Standard circular complex Gaussian measure
-- statement:
--   A standard circular complex Gaussian variable is formed from two independent centered real Gaussians of variance $1/2$. Its law $\gamma_{\mathbb C}$ is the pushforward of their product law under
--   $$
--   (x,y)\longmapsto x+iy.
--   $$
--   This gives unit second absolute moment, $\mathbb E|Z|^2=1$, and supplies the covariance convention of the two-matrix oscillator model.
--
--   **Formalization Note** This separate definition is a reusable probability object. Its real and imaginary components are represented by `gaussianReal 0 (1/2)`; the complex map is continuous and measurable.
-- source:
--   Kimura & Ramgoolam, Branes, Anti-Branes and Brauer Algebras in Gauge-Gravity duality, arXiv:0709.2158v2, p. 28, (7.8) (Gaussian realization of the oscillator normalization)

import Mathlib

noncomputable section

namespace BraneBrauer.Orthogonal

/-- The standard circular complex Gaussian: independent real and imaginary parts,
each with variance one half. -/
def complexGaussian : MeasureTheory.Measure ℂ :=
  ((ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal)).prod
    (ProbabilityTheory.gaussianReal 0 (1 / 2 : NNReal))).map
    (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)

end BraneBrauer.Orthogonal


