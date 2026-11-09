-- Prove2me | Definitions.Def_KSPolySign_j0
-- name    : KSPolySign_j0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:25.8682+00:00
-- url     : https://prove2.me/theorems/d3785cde-9936-44b4-9807-7b45798bdb5c
-- title:
--   The constant $j_0 = 43/50$
-- statement:
--   The constant
--   $$j_0 = \tfrac{43}{50}$$
--   of the covariance parameters (Definition 3.20).
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The constant `j₀ = 43/50`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32): "and j0 := 43/50". -/
noncomputable def j0 : ℝ := 43 / 50

end KSPolySign


