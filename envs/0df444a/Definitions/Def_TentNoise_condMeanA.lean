-- Prove2me | Definitions.Def_TentNoise_condMeanA
-- name    : TentNoise_condMeanA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:43.962232+00:00
-- url     : https://prove2.me/theorems/efac6849-554e-463d-b3b5-5b119cade743
-- title:
--   The reverse conditional mean $A(y)=u(y)+(y-1)u'(y)$
-- statement:
--   With $u(y)=\frac{b}{\pi N}\sin(\pi Ny)$ from Lemma B.3, the **reverse conditional mean** of the centered observable $\varphi(x)=x-\tfrac12$ under the fitted map is
--
--   $$
--   A(y):=u(y)+(y-1)\,u'(y).
--   $$
--
--   Lemma B.4 shows $A=R_u\varphi$, while the true dynamics give $R_f\varphi=0$; the frequency-$N$ oscillation of $A$ is what the lower-bound test functions detect.
--
--   **Formalization Note** Defined by the right-hand side of eq. (62); its identification with $(R_u\varphi)(y)$ is part of Lemma B.4. $u'$ is `deriv (pertU N b)`.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.4, p.27 (PDF p.27), eq. (62)

import Mathlib
import Definitions.Def_TentNoise_IsFitMap

namespace TentNoise

/-- The reverse conditional mean of the centered linear observable under Lemma B.3's fitted map,
`A(y) := u(y) + (y − 1) u′(y)` (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.4, p.27, eq. (62)).

**Formalization Note** Defined by the right-hand side of (62); that it equals `(R_u φ)(y)` for
`φ(x) = x − 1/2` is the content of Lemma B.4. `u′` is `deriv (pertU N b)`. -/
noncomputable def condMeanA (N : ℕ) (b y : ℝ) : ℝ :=
  pertU N b y + (y - 1) * deriv (pertU N b) y

end TentNoise


