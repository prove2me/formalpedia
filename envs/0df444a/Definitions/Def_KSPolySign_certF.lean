-- Prove2me | Definitions.Def_KSPolySign_certF
-- name    : KSPolySign_certF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:00.427919+00:00
-- url     : https://prove2.me/theorems/b3aa5d7b-7c55-4617-80b1-bc278ae082a5
-- title:
--   The certificate quantity $F=j_0^2+2j_0-j$
-- statement:
--   $$F = j_0^2 + 2j_0 - j,$$
--   a function of the coordinate scalars $(y,u,v)$ (Definition 3.20). Lemma 5.2 shows $F>0$ at light states.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32)

import Mathlib
import Definitions.Def_KSPolySign_jC
import Definitions.Def_KSPolySign_j0
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The certificate quantity `F = j₀² + 2j₀ − j`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32). -/
noncomputable def certF (y u v : ℝ) : ℝ := j0 ^ 2 + 2 * j0 - jC y u v

end KSPolySign


