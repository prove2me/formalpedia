-- Prove2me | Definitions.Def_KSPolySign_jC
-- name    : KSPolySign_jC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:34:35.408204+00:00
-- url     : https://prove2.me/theorems/5716d320-ae8b-41be-9e18-c1f81bba385c
-- title:
--   The scalar $j=\Lambda^2\delta/(4k)$
-- statement:
--   The quantity
--   $$j = \frac{\Lambda^2\delta}{4k}$$
--   of Definition 3.20, a function of $(y,u,v)$.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32)

import Mathlib
import Definitions.Def_KSPolySign_LamC
import Definitions.Def_KSPolySign_deltaC
import Definitions.Def_KSPolySign_kC
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The scalar `j = Λ²δ/(4k)`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32): "Define j := Λ²δ/(4k)". -/
noncomputable def jC (y u v : ℝ) : ℝ := LamC y u v ^ 2 * deltaC y u v / (4 * kC y u v)

end KSPolySign


