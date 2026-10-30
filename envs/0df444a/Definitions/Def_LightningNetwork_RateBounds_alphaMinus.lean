-- Prove2me | Definitions.Def_LightningNetwork_RateBounds_alphaMinus
-- name    : LightningNetwork_RateBounds_alphaMinus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:46:07.199336+00:00
-- url     : https://prove2.me/theorems/19d61dd3-c54d-4a28-9db0-543a44f9ba67
-- title:
--   The root $\alpha_-$ of eq. (4)
-- statement:
--   For payment rates $\lambda_1, \lambda_2$ and interest rate $r$, the smaller root in Theorem 1(ii) of the paper is
--
--   $$
--   \alpha_{-} \;=\; \frac{\lambda_1 + \lambda_2 + r - \sqrt{(\lambda_2-\lambda_1)^2 + r^2 + 2r(\lambda_2+\lambda_1)}}{2\lambda_2}.
--   $$
--
--   It enters the closed-form cost (3) of a bidirectional channel. At $\lambda_1 = \lambda_2$ it is the reciprocal of $\alpha_+$.
--
--   **Formalization Note** Literal transcription of (4) with the minus sign; no hypothesis is built in.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, Theorem 1(ii), eq. (4), p. 6

import Mathlib

namespace LightningNetwork.RateBounds

/-- **The root α₋ of (4).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, Theorem 1(ii), eq. (4), p. 6:
"α± = (λ1 + λ2 + r ± √((λ2 − λ1)² + r² + 2r(λ2 + λ1)))/(2λ2)."

`alphaMinus lam1 lam2 r = (lam1 + lam2 + r − √((lam2 − lam1)² + r² + 2r(lam2 + lam1)))/(2 lam2)`.

**Formalization Note.** Literal transcription of (4) with the `−` sign. -/
noncomputable def alphaMinus (lam1 lam2 r : ℝ) : ℝ :=
  (lam1 + lam2 + r - Real.sqrt ((lam2 - lam1) ^ 2 + r ^ 2 + 2 * r * (lam2 + lam1))) / (2 * lam2)

end LightningNetwork.RateBounds


