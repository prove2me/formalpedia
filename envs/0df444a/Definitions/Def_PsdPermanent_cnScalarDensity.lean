-- Prove2me | Definitions.Def_PsdPermanent_cnScalarDensity
-- name    : PsdPermanent_cnScalarDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:41.5467+00:00
-- url     : https://prove2.me/theorems/8255951a-af38-47ec-a620-a95491c03c37
-- title:
--   The density of the scalar complex Gaussian $\mathcal{CN}(0,s)$
-- statement:
--   For $s>0$, the scalar complex Gaussian $\mathcal{CN}(0,s)$ has density
--   $$w\longmapsto\frac{1}{\pi s}\exp(-|w|^2/s)$$
--   with respect to Lebesgue measure on $\mathbb C$. It is the law of the one-dimensional projections $v_i^\dagger Z$ used in the lower bound.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3; proof of Theorem 7, p.8

import Mathlib

namespace PsdPermanent

/-- **The density of the scalar complex Gaussian CN(0, s).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3 (with `d = 1`, `X = s`) and proof of Theorem 7, p.8: "v_i† Z ∼ CN(0, v_i† X v_i)".

`cnScalarDensity s w = (π s)⁻¹ exp(−|w|²/s)`, a density with respect to Lebesgue measure on `ℂ`.

**Formalization Note.** The scalar law lives on `ℂ`, while `PsdPermanent.cnDensity` lives on
`Fin d → ℂ`; at `d = 1` they agree under `z ↦ z 0`. -/
noncomputable def cnScalarDensity (s : ℝ) (w : ℂ) : ℝ :=
  (Real.pi * s)⁻¹ * Real.exp (-(Complex.normSq w / s))

end PsdPermanent


