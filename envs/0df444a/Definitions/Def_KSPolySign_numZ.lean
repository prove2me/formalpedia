-- Prove2me | Definitions.Def_KSPolySign_numZ
-- name    : KSPolySign_numZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:22.66943+00:00
-- url     : https://prove2.me/theorems/5f4d00c9-e724-4a9a-a953-698d2e83f127
-- title:
--   The numerator polynomial $Z_n$
-- statement:
--   $$Z_n = 2U_ng + h_nF_ng^3 - r_nF_ng^2 + \frac{r_nF_nj_n}{(1+j_0)^2}.$$
--
--   Here $g=1+t^2$, $w_n=1-t^2$, $z_n=2t$, $j_n=\eta z_n^2/2$, $h_n=w_nH/\iota$, $r_n=\tfrac{2\eta}{\iota}w_n\big(g+z_n(1-H)(2V-1)\big)$, $s_{\mathrm{inv},n}=\tfrac{2\eta}{\iota}w_n^3$, with $\iota=303/100$, $\eta=1000001/1000000$, $j_0=43/50$.
--
--   **Formalization Note** A polynomial in $(t,H,V)$ with rational coefficients, represented by its real polynomial function.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), proof of Lemma A.2, p.73 (PDF p.73)

import Mathlib
import Definitions.Def_KSPolySign_numU
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The numerator `Z_n = 2U_ng + h_nF_ng³ − r_nF_ng² + r_nF_nj_n/(1 + j₀)²`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), proof of Lemma A.2, p.73 (PDF p.73).

**Formalization Note** A polynomial in `(t, H, V)` with rational coefficients, represented by its
real polynomial function. The auxiliary polynomials are `g = 1 + t²`, `w_n = 1 − t²`, `z_n = 2t`,
`j_n = ηz_n²/2`, `h_n = w_nH/ι`, `r_n = (2η/ι)w_n(g + z_n(1 − H)(2V − 1))`, `s_{inv,n} = (2η/ι)w_n³`. -/
noncomputable def numZ (t H V : ℝ) : ℝ :=
  let g : ℝ := 1 + t ^ 2
  let wn : ℝ := 1 - t ^ 2
  let zn : ℝ := 2 * t
  let jn : ℝ := etaC * zn ^ 2 / 2
  let hn : ℝ := wn * H / iota
  let rn : ℝ := 2 * etaC / iota * wn * (g + zn * (1 - H) * (2 * V - 1))
  2 * numU t H V * g + hn * numF t H V * g ^ 3 - rn * numF t H V * g ^ 2 +
    rn * numF t H V * jn / (1 + j0) ^ 2

end KSPolySign


