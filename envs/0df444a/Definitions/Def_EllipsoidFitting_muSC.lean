-- Prove2me | Definitions.Def_EllipsoidFitting_muSC
-- name    : EllipsoidFitting_muSC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:18.166971+00:00
-- url     : https://prove2.me/theorems/0aa69795-5e24-4fe4-83fc-ce03e056ab7f
-- title:
--   The semicircle distribution $\mu_{\mathrm{sc}}$
-- statement:
--   $\mu_{\mathrm{sc}}$ is the measure on $\mathbb R$ supported on $[-2,2]$ with density
--   $$
--   f_{\mathrm{sc}}(x)=\frac{\sqrt{4-x^2}}{2\pi}
--   $$
--   with respect to Lebesgue measure. It is the limiting spectral law of the inner matrices of the construction.
--
--   **Formalization Note** Lebesgue measure restricted to $[-2,2]$, `withDensity` the density above. That it is a probability measure is proved in the sanity file and is also a clause of the Definition 2.1 milestone.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Definition 2.1, p.7 (PDF p.9)

import Mathlib

set_option autoImplicit false

namespace EllipsoidFitting

open MeasureTheory

/-- **The semicircle distribution.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition
for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Definition 2.1, p.7: "Let µsc
be the semicircle distribution on [−2, 2], with density fsc(x) = √(4−x²)/(2π)".

`muSC` is the measure on `ℝ` with density `√(4 − x²)/(2π)` with respect to Lebesgue measure on
`[−2, 2]` (and no mass outside). -/
noncomputable def muSC : Measure ℝ :=
  (volume.restrict (Set.Icc (-2 : ℝ) 2)).withDensity
    (fun x => ENNReal.ofReal (Real.sqrt (4 - x ^ 2) / (2 * Real.pi)))

end EllipsoidFitting


