-- Prove2me | Definitions.Def_KSPolySign_certB
-- name    : KSPolySign_certB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:23.055234+00:00
-- url     : https://prove2.me/theorems/4b10d73a-fee9-4b1a-9158-f173fdff6f43
-- title:
--   The certificate quantity $B=2j_0-j-\delta(1+2j_0)$
-- statement:
--   $$B = 2j_0 - j - \delta(1+2j_0),$$
--   a function of $(y,u,v)$ (Definition 3.20).
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32)

import Mathlib
import Definitions.Def_KSPolySign_jC
import Definitions.Def_KSPolySign_j0
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The certificate quantity `B = 2j₀ − j − δ(1 + 2j₀)`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32). -/
noncomputable def certB (y u v : ℝ) : ℝ := 2 * j0 - jC y u v - deltaC y u v * (1 + 2 * j0)

end KSPolySign


