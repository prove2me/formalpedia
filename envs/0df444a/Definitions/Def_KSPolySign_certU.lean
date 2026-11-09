-- Prove2me | Definitions.Def_KSPolySign_certU
-- name    : KSPolySign_certU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:38:22.797938+00:00
-- url     : https://prove2.me/theorems/cd7ec742-0236-4606-82c9-e5aaa974bf06
-- title:
--   The certificate quantity $\mathfrak u$
-- statement:
--   $$\mathfrak u = B + \delta F - \frac{F\Lambda L}{2k(1+j_0)},$$
--   a function of $(y,u,v)$ (Definition 3.20). (Fraktur $\mathfrak u$, not the quadratic form $u_i$.)
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32)

import Mathlib
import Definitions.Def_KSPolySign_certF
import Definitions.Def_KSPolySign_certB
import Definitions.Def_KSPolySign_LC
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The certificate quantity `𝔲 = B + δF − FΛL/(2k(1 + j₀))`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32)
(fraktur `𝔲`, not the quadratic form `u_i`). -/
noncomputable def certU (y u v : ℝ) : ℝ :=
  certB y u v + deltaC y u v * certF y u v -
    certF y u v * LamC y u v * LC y u v / (2 * kC y u v * (1 + j0))

end KSPolySign


