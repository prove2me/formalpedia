-- Prove2me | Definitions.Def_KSPolySign_LC
-- name    : KSPolySign_LC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:33:10.12135+00:00
-- url     : https://prove2.me/theorems/6397e9cb-0e51-44a0-858e-4aea5be1db91
-- title:
--   The scalar $L=\iota\sqrt{\tilde u\tilde v}(\tilde u-\tilde v)$
-- statement:
--   The local trace quantity
--   $$L = \iota\sqrt{\tilde u\tilde v}\,(\tilde u-\tilde v)$$
--   of Definition 3.19.
--
--   At an active coordinate of a light state, write $y=y_i\in(-1,1)$, $u=u_i$, $v=v_i$, $\beta=\sqrt{1-y^2}$, $\beta'=-y/\sqrt{1-y^2}$, $\beta''=-1/(1-y^2)^{3/2}$, $p=1+\iota\beta'v$, $q=1-\iota\beta'u$ (Definition 3.8), $c=\sqrt{\beta p/q}$, $d=\sqrt{\beta q/p}$, $\tau=\sqrt{pq/\beta}$, $\tilde u=cu$, $\tilde v=dv$ (Lemma 3.11).
--
--   **Formalization Note** A function of the three reals $(y,u,v)$; every quantity of Definitions 3.14, 3.19, 3.20 that enters it depends only on them.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.19, p.32 (PDF p.32); Lemma 3.11, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_KSPolySign_iota
import Definitions.Def_KSPolySign_beta
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The scalar `L = ι√(ũṽ)(ũ − ṽ)`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.19, p.32 (PDF p.32): "L_i := ι√(ũ_iṽ_i)(ũ_i − ṽ_i)",
with `ũ = cu`, `ṽ = dv`, `c = √(βp/q)`, `d = √(βq/p)` of Lemma 3.11, p.22 (PDF p.22).

**Formalization Note** A function of the scalars `(y, u, v) = (y_i, u_i, v_i)` of one active
coordinate, with `β = √(1 − y²)`, `β′ = −y/√(1 − y²)`, `β″ = −1/(1 − y²)^{3/2}` (the formulas printed on
p.8 for `−1 < y < 1`), `p = 1 + ιβ′v`, `q = 1 − ιβ′u` (Definition 3.8, p.22). Every quantity of
Definitions 3.14, 3.19, 3.20 and Lemma 3.11 that enters it depends only on `(y_i, u_i, v_i)`. -/
noncomputable def LC (y u v : ℝ) : ℝ :=
  let β' : ℝ := -y / Real.sqrt (1 - y ^ 2)
  let p : ℝ := 1 + iota * β' * v
  let q : ℝ := 1 - iota * β' * u
  let β : ℝ := beta y
  let c : ℝ := Real.sqrt (β * p / q)
  let d : ℝ := Real.sqrt (β * q / p)
  let ut : ℝ := c * u
  let vt : ℝ := d * v
  iota * Real.sqrt (ut * vt) * (ut - vt)

end KSPolySign


