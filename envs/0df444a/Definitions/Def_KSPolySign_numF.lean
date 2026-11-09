-- Prove2me | Definitions.Def_KSPolySign_numF
-- name    : KSPolySign_numF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:33:19.770255+00:00
-- url     : https://prove2.me/theorems/85ac459f-46c9-4338-aee8-5b68bd44dfa5
-- title:
--   The numerator polynomial $F_n$
-- statement:
--   $$F_n = (j_0^2+2j_0)\,g^2 - j_n,$$
--   one of the numerator polynomials of Lemma A.2.
--
--   Here $g=1+t^2$, $w_n=1-t^2$, $z_n=2t$, $j_n=\eta z_n^2/2$, $h_n=w_nH/\iota$, $r_n=\tfrac{2\eta}{\iota}w_n\big(g+z_n(1-H)(2V-1)\big)$, $s_{\mathrm{inv},n}=\tfrac{2\eta}{\iota}w_n^3$, with $\iota=303/100$, $\eta=1000001/1000000$, $j_0=43/50$.
--
--   **Formalization Note** A polynomial in $(t,H,V)$ with rational coefficients, represented by its real polynomial function.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), proof of Lemma A.2, p.73 (PDF p.73)

import Mathlib
import Definitions.Def_KSPolySign_iota
import Definitions.Def_KSPolySign_etaC
import Definitions.Def_KSPolySign_j0
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The numerator `F_n = (j₀² + 2j₀)g² − j_n`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), proof of Lemma A.2, p.73 (PDF p.73).

**Formalization Note** A polynomial in `(t, H, V)` with rational coefficients, represented by its
real polynomial function. The auxiliary polynomials are `g = 1 + t²`, `w_n = 1 − t²`, `z_n = 2t`,
`j_n = ηz_n²/2`, `h_n = w_nH/ι`, `r_n = (2η/ι)w_n(g + z_n(1 − H)(2V − 1))`, `s_{inv,n} = (2η/ι)w_n³`. -/
noncomputable def numF (t H V : ℝ) : ℝ :=
  let g : ℝ := 1 + t ^ 2
  let zn : ℝ := 2 * t
  let jn : ℝ := etaC * zn ^ 2 / 2
  (j0 ^ 2 + 2 * j0) * g ^ 2 - jn

end KSPolySign


