-- Prove2me | Definitions.Def_RQCMoments_arcsine
-- name    : RQCMoments_arcsine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:21.862566+00:00
-- url     : https://prove2.me/theorems/24e0b897-9420-4950-bae8-ecbbca2489f6
-- title:
--   Arcsine probability measure $\rho_R$ on $[0,R]$
-- statement:
--   For $R>0$, the **arcsine probability measure** $\rho_R$ on $[0,R]$ is
--   $$
--   d\rho_R(t)=\frac{dt}{\pi\sqrt{t(R-t)}},\qquad 0<t<R .
--   $$
--   Its orthonormal polynomials are rescaled Chebyshev polynomials of the first kind; it serves as a comparison measure for Christoffel functions (Lemma 4.3 and Theorem 4.4).
--
--   **Formalization Note** Lebesgue measure on the open interval $(0,R)$ with the stated density; the endpoints are null sets.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), (26), p.16 (PDF p.18)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- The arcsine probability measure `ρ_R` on `[0, R]` (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), (26), p.16):
`dρ_R(t) = dt / (π √(t(R − t)))` for `0 < t < R`.

**Formalization Note** Lebesgue measure restricted to the open interval `(0, R)` with the density
`1/(π √(t(R−t)))`; the endpoints are Lebesgue-null. It is a probability measure for `R > 0`. -/
noncomputable def arcsine (R : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioo 0 R)).withDensity
    (fun t => ENNReal.ofReal (1 / (Real.pi * Real.sqrt (t * (R - t)))))

end RQCMoments


