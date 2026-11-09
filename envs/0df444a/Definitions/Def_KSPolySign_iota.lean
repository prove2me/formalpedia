-- Prove2me | Definitions.Def_KSPolySign_iota
-- name    : KSPolySign_iota
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:25.173252+00:00
-- url     : https://prove2.me/theorems/a3258245-8357-45f2-97dc-7474c7b827a8
-- title:
--   The constant $\iota = 3.03$
-- statement:
--   The constant
--   $$\iota = 3.03 = \tfrac{303}{100}.$$
--   It weights the coupling $K_y$ of the matrix potential and enters every scalar quantity of the covariance certificate.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.2, p.18 (PDF p.18); Lemma A.2, p.73 (PDF p.73)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The constant `ι = 3.03`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.2, p.18 (PDF p.18): "define β(t) := √(1 − t²)
and ι := 3.03". Lemma A.2, p.73 (PDF p.73), uses the same value as the rational `303/100`. -/
noncomputable def iota : ℝ := 303 / 100

end KSPolySign


