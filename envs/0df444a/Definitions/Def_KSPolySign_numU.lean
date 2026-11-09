-- Prove2me | Definitions.Def_KSPolySign_numU
-- name    : KSPolySign_numU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:35:16.947291+00:00
-- url     : https://prove2.me/theorems/77206fad-dc7d-42fc-8a50-4c349f2c18d9
-- title:
--   The numerator polynomial $U_n$
-- statement:
--   With $T_n = r_ng - s_{\mathrm{inv},n} - 4j_nh_n$,
--   $$U_n = B_ng^3 + h_nF_ng^2 + \frac{F_nT_n}{2(1+j_0)}.$$
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

/-- **The numerator `U_n = B_ng³ + h_nF_ng² + F_nT_n/(2(1 + j₀))` with `T_n = r_ng − s_{inv,n} − 4j_nh_n`.**
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), proof of Lemma A.2, p.73 (PDF p.73).

**Formalization Note** A polynomial in `(t, H, V)` with rational coefficients, represented by its
real polynomial function. The auxiliary polynomials are `g = 1 + t²`, `w_n = 1 − t²`, `z_n = 2t`,
`j_n = ηz_n²/2`, `h_n = w_nH/ι`, `r_n = (2η/ι)w_n(g + z_n(1 − H)(2V − 1))`, `s_{inv,n} = (2η/ι)w_n³`. -/
noncomputable def numU (t H V : ℝ) : ℝ :=
  let g : ℝ := 1 + t ^ 2
  let wn : ℝ := 1 - t ^ 2
  let zn : ℝ := 2 * t
  let jn : ℝ := etaC * zn ^ 2 / 2
  let hn : ℝ := wn * H / iota
  let rn : ℝ := 2 * etaC / iota * wn * (g + zn * (1 - H) * (2 * V - 1))
  let sinvn : ℝ := 2 * etaC / iota * wn ^ 3
  let Tn : ℝ := rn * g - sinvn - 4 * jn * hn
  numB t H V * g ^ 3 + hn * numF t H V * g ^ 2 + numF t H V * Tn / (2 * (1 + j0))

end KSPolySign


