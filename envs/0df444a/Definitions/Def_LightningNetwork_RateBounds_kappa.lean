-- Prove2me | Definitions.Def_LightningNetwork_RateBounds_kappa
-- name    : LightningNetwork_RateBounds_kappa
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:06.087565+00:00
-- url     : https://prove2.me/theorems/56805a1d-fdaa-48f9-b0a0-f7a6f465247d
-- title:
--   The constant $\kappa$ of Theorem 2(ii)
-- statement:
--   For a payment rate $\lambda > 0$ and an interest rate $r > 0$, Theorem 2(ii) of the paper uses
--
--   $$
--   \kappa \;=\; \log\frac{r + 2\lambda + \sqrt{r(4\lambda + r)}}{2\lambda}.
--   $$
--
--   It is the logarithm of $\alpha_+$ at $\lambda_1 = \lambda_2 = \lambda$, equivalently $\kappa = \cosh^{-1}\bigl(1 + r/(2\lambda)\bigr)$, and it is positive; for small $r$, $\kappa \approx \sqrt{r/\lambda}$.
--
--   **Formalization Note** Literal transcription of the printed formula; the two equivalent forms are checked in the mission's verification file, not uploaded.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, Theorem 2(ii), p. 7

import Mathlib

namespace LightningNetwork.RateBounds

/-- **The constant κ of Theorem 2(ii).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, Theorem 2(ii), p. 7: "where κ = log((r + 2λ + √(r(4λ + r)))/(2λ))."

`kappa r lam = log((r + 2 lam + √(r(4 lam + r)))/(2 lam))`.

**Formalization Note.** Literal transcription. For `0 < lam`, `0 < r` the argument of the
logarithm exceeds `1`, so `κ > 0`; it equals `log α₊` at `λ1 = λ2 = lam` and
`arcosh(1 + r/(2 lam))` (proved in the mission's verification file, not uploaded). -/
noncomputable def kappa (r lam : ℝ) : ℝ :=
  Real.log ((r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam))

end LightningNetwork.RateBounds


