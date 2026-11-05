-- Prove2me | Definitions.Def_BoundEntGauss_omegaOne
-- name    : BoundEntGauss_omegaOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:02.86133+00:00
-- url     : https://prove2.me/theorems/e7dc66f1-18d2-4d0c-b272-71a10a8785dc
-- title:
--   The generating vector $\Omega_1$ of Eq. (11)
-- statement:
--   For real parameters $a,b,c,d,e,f$, the vector $\Omega_1\in\mathbb C^8$ in the coordinates $(x_1,p_1,x_2,p_2\mid x_3,p_3,x_4,p_4)$ is
--
--   $$
--   \Omega_1=(-a,\;ib,\;c,\;-id,\;e,\;-if,\;1,\;0).
--   $$
--
--   The family of covariance matrices of Section IV is built so that $\Omega_1$ is a null vector of $\gamma+i\sigma$; at $(a,b,c,d,e,f)=(1,1,2,3,1,1)$ it is the vector (10).
--
--   **Formalization Note** The paper takes $a,\dots,f>0$; the theorems state the positivity.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, Eq. (11), p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace BoundEntGauss

/-- **The generating vector Ω₁ of Eq. (11).**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV, Eq. (11), p. 4.

`Ω₁ = (−a, ib, c, −id, e, −if, 1, 0) ∈ ℂ⁸` in the coordinates `(x₁, p₁, x₂, p₂ | x₃, p₃, x₄, p₄)`.

**Formalization Note.** Coordinates as in `opS`. The paper requires `a, b, …, f > 0`; the
definition takes any reals, and the theorems state the positivity. -/
noncomputable def omegaOne (a b c d e f : ℝ) : QuadratureIndex 2 ⊕ QuadratureIndex 2 → ℂ :=
  Sum.elim (fun p => !![-(a : ℂ), (b : ℂ) * Complex.I; (c : ℂ), -((d : ℂ) * Complex.I)] p.1 p.2)
    (fun p => !![(e : ℂ), -((f : ℂ) * Complex.I); 1, 0] p.1 p.2)

end BoundEntGauss


