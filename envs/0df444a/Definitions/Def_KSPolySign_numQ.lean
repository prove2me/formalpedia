-- Prove2me | Definitions.Def_KSPolySign_numQ
-- name    : KSPolySign_numQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:35:12.7022+00:00
-- url     : https://prove2.me/theorems/3a65b4ac-8a85-4930-b9c6-da7fe505856d
-- title:
--   The numerator polynomial $Q_n$
-- statement:
--   With $Q_{\mathrm{bloc},n} = j_0^2h_ng + (2j_0+1)h_n^2$ and $Q_{1,n} = B_ng^2 + (F_n-B_n)j_n/(1+j_0)^2$,
--   $$Q_n = Q_{\mathrm{bloc},n}\,g^4 + r_nQ_{1,n}.$$
--
--   Here $g=1+t^2$, $w_n=1-t^2$, $z_n=2t$, $j_n=\eta z_n^2/2$, $h_n=w_nH/\iota$, $r_n=\tfrac{2\eta}{\iota}w_n\big(g+z_n(1-H)(2V-1)\big)$, $s_{\mathrm{inv},n}=\tfrac{2\eta}{\iota}w_n^3$, with $\iota=303/100$, $\eta=1000001/1000000$, $j_0=43/50$.
--
--   **Formalization Note** A polynomial in $(t,H,V)$ with rational coefficients, represented by its real polynomial function.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), proof of Lemma A.2, p.73 (PDF p.73)

import Mathlib
import Definitions.Def_KSPolySign_numF
import Definitions.Def_KSPolySign_numB
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The numerator `Q_n = Q_{bloc,n}g⁴ + r_nQ_{1,n}`** with `Q_{bloc,n} = j₀²h_ng + (2j₀ + 1)h_n²` and
`Q_{1,n} = B_ng² + (F_n − B_n)j_n/(1 + j₀)²`. Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), proof of Lemma A.2, p.73 (PDF p.73).

**Formalization Note** A polynomial in `(t, H, V)` with rational coefficients, represented by its
real polynomial function. The auxiliary polynomials are `g = 1 + t²`, `w_n = 1 − t²`, `z_n = 2t`,
`j_n = ηz_n²/2`, `h_n = w_nH/ι`, `r_n = (2η/ι)w_n(g + z_n(1 − H)(2V − 1))`, `s_{inv,n} = (2η/ι)w_n³`. -/
noncomputable def numQ (t H V : ℝ) : ℝ :=
  let g : ℝ := 1 + t ^ 2
  let wn : ℝ := 1 - t ^ 2
  let zn : ℝ := 2 * t
  let jn : ℝ := etaC * zn ^ 2 / 2
  let hn : ℝ := wn * H / iota
  let rn : ℝ := 2 * etaC / iota * wn * (g + zn * (1 - H) * (2 * V - 1))
  let Qbloc : ℝ := j0 ^ 2 * hn * g + (2 * j0 + 1) * hn ^ 2
  let Q1 : ℝ := numB t H V * g ^ 2 + (numF t H V - numB t H V) * jn / (1 + j0) ^ 2
  Qbloc * g ^ 4 + rn * Q1

end KSPolySign


