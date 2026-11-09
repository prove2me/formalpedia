-- Prove2me | Definitions.Def_KSPolySign_certQ
-- name    : KSPolySign_certQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:37:18.4319+00:00
-- url     : https://prove2.me/theorems/5cfee805-58ee-45c2-a2b7-2bb2a7821e22
-- title:
--   The certificate quantity $\mathfrak q$
-- statement:
--   $$\mathfrak q = \delta\,(j_0^2 + 2\delta j_0 + \delta) + \frac1k\Big(B + \frac{(F-B)\,j}{(1+j_0)^2}\Big),$$
--   a function of $(y,u,v)$ (Definition 3.20). (Fraktur $\mathfrak q$, not the coefficient $q_i$.)
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32)

import Mathlib
import Definitions.Def_KSPolySign_certF
import Definitions.Def_KSPolySign_certB
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The certificate quantity `𝔮 = δ(j₀² + 2δj₀ + δ) + (1/k)(B + (F − B)j/(1 + j₀)²)`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…),
Definition 3.20, p.32 (PDF p.32) (fraktur `𝔮`, not the coefficient `q_i`). -/
noncomputable def certQ (y u v : ℝ) : ℝ :=
  deltaC y u v * (j0 ^ 2 + 2 * deltaC y u v * j0 + deltaC y u v) +
    1 / kC y u v * (certB y u v + (certF y u v - certB y u v) * jC y u v / (1 + j0) ^ 2)

end KSPolySign


