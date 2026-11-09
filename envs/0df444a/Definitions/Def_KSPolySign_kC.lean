-- Prove2me | Definitions.Def_KSPolySign_kC
-- name    : KSPolySign_kC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:32:08.516204+00:00
-- url     : https://prove2.me/theorems/c24b0fb5-b359-459f-9097-a492b4eb755c
-- title:
--   The scalar $k=\iota(-\beta'')/(2\eta pq)$
-- statement:
--   The coefficient
--   $$k = \frac{\iota(-\beta'')}{2\eta\,p\,q}$$
--   of Definition 3.20.
--
--   At an active coordinate of a light state, write $y=y_i\in(-1,1)$, $u=u_i$, $v=v_i$, $\beta=\sqrt{1-y^2}$, $\beta'=-y/\sqrt{1-y^2}$, $\beta''=-1/(1-y^2)^{3/2}$, $p=1+\iota\beta'v$, $q=1-\iota\beta'u$ (Definition 3.8), $c=\sqrt{\beta p/q}$, $d=\sqrt{\beta q/p}$, $\tau=\sqrt{pq/\beta}$, $\tilde u=cu$, $\tilde v=dv$ (Lemma 3.11).
--
--   **Formalization Note** A function of the three reals $(y,u,v)$; every quantity of Definitions 3.14, 3.19, 3.20 that enters it depends only on them.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32)

import Mathlib
import Definitions.Def_KSPolySign_iota
import Definitions.Def_KSPolySign_etaC
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The scalar `k = ι(−β″)/(2ηpq)`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32): "k_i := ι(−β″_i)/(2ηp_iq_i)".

**Formalization Note** A function of the scalars `(y, u, v) = (y_i, u_i, v_i)` of one active
coordinate, with `β = √(1 − y²)`, `β′ = −y/√(1 − y²)`, `β″ = −1/(1 − y²)^{3/2}` (the formulas printed on
p.8 for `−1 < y < 1`), `p = 1 + ιβ′v`, `q = 1 − ιβ′u` (Definition 3.8, p.22). Every quantity of
Definitions 3.14, 3.19, 3.20 and Lemma 3.11 that enters it depends only on `(y_i, u_i, v_i)`. -/
noncomputable def kC (y u v : ℝ) : ℝ :=
  let β' : ℝ := -y / Real.sqrt (1 - y ^ 2)
  let p : ℝ := 1 + iota * β' * v
  let q : ℝ := 1 - iota * β' * u
  let β'' : ℝ := -1 / (1 - y ^ 2) ^ ((3 : ℝ) / 2)
  iota * (-β'') / (2 * etaC * p * q)

end KSPolySign


