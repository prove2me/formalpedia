-- Prove2me | Definitions.Def_KSPolySign_etaC
-- name    : KSPolySign_etaC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:12.390935+00:00
-- url     : https://prove2.me/theorems/0fc01d13-26ab-49fd-b20a-6c991eb43d1a
-- title:
--   The constant $\eta = 1 + 10^{-6}$
-- statement:
--   With $\kappa_{\mathrm{tr}} = 10^{-6}$, the constant
--   $$\eta = 1 + \kappa_{\mathrm{tr}} = \tfrac{1000001}{1000000}.$$
--   It appears in the coefficient $k$ of Definition 3.20 and in the numerator polynomials of Lemma A.2.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32); Lemma A.2, p.73 (PDF p.73)

import Mathlib
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The constant `η = 1 + κ_tr` with `κ_tr = 10⁻⁶`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32):
"Define κtr := 1/10⁶, η := 1 + κtr". Lemma A.2, p.73, writes it as `1000001/1000000`. -/
noncomputable def etaC : ℝ := 1 + 1 / 10 ^ 6

end KSPolySign


