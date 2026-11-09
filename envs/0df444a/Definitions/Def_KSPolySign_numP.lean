-- Prove2me | Definitions.Def_KSPolySign_numP
-- name    : KSPolySign_numP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:15.181114+00:00
-- url     : https://prove2.me/theorems/d0234318-1b95-4725-b37f-3fffa7601e09
-- title:
--   The numerator polynomial $P_n$
-- statement:
--   $$P_n = U_n^2 - F_nQ_ng^2,\qquad g=1+t^2.$$
--   By Lemma A.2, $\mathfrak u^2-F\mathfrak q = P_n/g^{10}$ at the corresponding light coordinate.
--
--   Here $g=1+t^2$, $w_n=1-t^2$, $z_n=2t$, $j_n=\eta z_n^2/2$, $h_n=w_nH/\iota$, $r_n=\tfrac{2\eta}{\iota}w_n\big(g+z_n(1-H)(2V-1)\big)$, $s_{\mathrm{inv},n}=\tfrac{2\eta}{\iota}w_n^3$, with $\iota=303/100$, $\eta=1000001/1000000$, $j_0=43/50$.
--
--   **Formalization Note** A polynomial in $(t,H,V)$ with rational coefficients, represented by its real polynomial function.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), proof of Lemma A.2, p.73 (PDF p.73)

import Mathlib
import Definitions.Def_KSPolySign_numU
import Definitions.Def_KSPolySign_numQ
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The numerator `P_n = U_n² − F_nQ_ng²`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), proof of Lemma A.2, p.73 (PDF p.73).

**Formalization Note** A polynomial in `(t, H, V)` with rational coefficients, represented by its
real polynomial function. The auxiliary polynomials are `g = 1 + t²`, `w_n = 1 − t²`, `z_n = 2t`,
`j_n = ηz_n²/2`, `h_n = w_nH/ι`, `r_n = (2η/ι)w_n(g + z_n(1 − H)(2V − 1))`, `s_{inv,n} = (2η/ι)w_n³`. -/
noncomputable def numP (t H V : ℝ) : ℝ :=
  numU t H V ^ 2 - numF t H V * numQ t H V * (1 + t ^ 2) ^ 2

end KSPolySign


