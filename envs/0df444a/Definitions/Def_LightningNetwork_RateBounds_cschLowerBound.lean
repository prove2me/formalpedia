-- Prove2me | Definitions.Def_LightningNetwork_RateBounds_cschLowerBound
-- name    : LightningNetwork_RateBounds_cschLowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:55.678453+00:00
-- url     : https://prove2.me/theorems/354e0e52-fccc-436b-9601-fa10df169bb7
-- title:
--   The lower bound (23)
-- statement:
--   For real parameters $\kappa$, $B$, $C$ and a commitment $m$, let
--
--   $$
--   H(m) \;=\; 2m + B\left(\frac{2}{\kappa^2 m^2} - \frac16\right) - \frac{2C}{\kappa^2}.
--   $$
--
--   In the proof of Theorem 2(ii) this is the lower bound (23) for the excess cost (21) of a symmetric channel with equal commitments $m$, obtained from $\operatorname{csch}^2 x > 1/x^2 - 1/3$.
--
--   **Formalization Note** For $\kappa \ne 0$ and $m \ne 0$ no denominator vanishes.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), eq. (23), p. 11

import Mathlib

namespace LightningNetwork.RateBounds

/-- **The lower bound (23).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), eq. (23), p. 11: "whereby (21) is bounded from
below by 2m + B(2/(κ²m²) − 1/6) − 2C/κ²."

`cschLowerBound κ B C m = 2m + B(2/(κ² m²) − 1/6) − 2C/κ²`.

**Formalization Note.** `κ`, `B`, `C` are free real parameters; for `κ ≠ 0`, `m ≠ 0` no
denominator vanishes. -/
noncomputable def cschLowerBound (κ B C m : ℝ) : ℝ :=
  2 * m + B * (2 / (κ ^ 2 * m ^ 2) - 1 / 6) - 2 * C / κ ^ 2

end LightningNetwork.RateBounds


