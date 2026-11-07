-- Prove2me | Definitions.Def_HeilmanMax3Cut_alpha3
-- name    : HeilmanMax3Cut_alpha3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:02.162881+00:00
-- url     : https://prove2.me/theorems/e1397309-a5c8-4f36-a2c7-53cf7bbc7bd5
-- title:
--   The Frieze–Jerrum constant $\alpha_3$
-- statement:
--   The approximation ratio of the Frieze–Jerrum semidefinite-programming algorithm for MAX-3-CUT is
--
--   $$\alpha_3=\inf_{-1/2\le\rho<1} r(\rho),\qquad r(\rho)=\frac{\tfrac32\bigl[1-3\bigl(\tfrac19+\frac{[\arccos(-\rho)]^2-[\arccos(\rho/2)]^2}{4\pi^2}\bigr)\bigr]}{1-\rho}.$$
--
--   The paper records $\alpha_3\approx .83600811464$, attained at $\rho=-1/2$.
--
--   **Formalization Note** The endpoint $\rho=1$ of the printed range is excluded: there the fraction is $0/0$ (undefined), while $r(\rho)\to+\infty$ as $\rho\to1^-$, so the infimum is unchanged. The set of values is nonempty and bounded below by $0$, so the real infimum is genuine.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (2), p.3

import Mathlib
import Definitions.Def_HeilmanMax3Cut_fjRatio

namespace HeilmanMax3Cut

/-- **The Frieze–Jerrum constant `α₃`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (2), p.3:
`α₃ := inf_{−1/2 ≤ ρ ≤ 1} (3/2)[1 − 3(1/9 + ([arccos(−ρ)]² − [arccos(ρ/2)]²)/(4π²))]/(1 − ρ) ≈ .83600811464`,
the approximation ratio of the Frieze–Jerrum semidefinite-programming algorithm for MAX-3-CUT.

**Formalization Note.** The infimum is the real `sInf` of the image of `fjRatio` on `[−1/2, 1)`.
The endpoint `ρ = 1` is excluded: the printed fraction is `0/0` there (undefined), and Lean's
`x / 0 = 0` would otherwise force `α₃ ≤ 0`. The ratio tends to `+∞` as `ρ → 1⁻`, so excluding the
undefined point does not change the infimum. The set is nonempty and bounded below by `0` (the
numerator is nonnegative on the range), so `sInf` is the true infimum. -/
noncomputable def alpha3 : ℝ :=
  sInf (fjRatio '' Set.Ico (-1 / 2 : ℝ) 1)

end HeilmanMax3Cut


