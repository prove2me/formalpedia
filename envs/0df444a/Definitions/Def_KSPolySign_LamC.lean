-- Prove2me | Definitions.Def_KSPolySign_LamC
-- name    : KSPolySign_LamC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:58.404701+00:00
-- url     : https://prove2.me/theorems/d257c739-b1a8-4af0-9bcf-e479dada029f
-- title:
--   The scalar $\Lambda = g/(\tau\sqrt{\tilde u\tilde v})$
-- statement:
--   With $g=\beta'/\beta$, the coefficient
--   $$\Lambda = \frac{g}{\tau\sqrt{\tilde u\tilde v}}$$
--   of Definition 3.20.
--
--   At an active coordinate of a light state, write $y=y_i\in(-1,1)$, $u=u_i$, $v=v_i$, $\beta=\sqrt{1-y^2}$, $\beta'=-y/\sqrt{1-y^2}$, $\beta''=-1/(1-y^2)^{3/2}$, $p=1+\iota\beta'v$, $q=1-\iota\beta'u$ (Definition 3.8), $c=\sqrt{\beta p/q}$, $d=\sqrt{\beta q/p}$, $\tau=\sqrt{pq/\beta}$, $\tilde u=cu$, $\tilde v=dv$ (Lemma 3.11).
--
--   **Formalization Note** A function of the three reals $(y,u,v)$; every quantity of Definitions 3.14, 3.19, 3.20 that enters it depends only on them.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32); Lemma 3.11, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_KSPolySign_iota
import Definitions.Def_KSPolySign_beta
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The scalar `Λ = g/(τ√(ũṽ))` with `g = β′/β`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.20, p.32 (PDF p.32):
"g_i := β′_i/β_i, Λ_i := g_i/(τ_i√(ũ_iṽ_i))", with the scales `c = √(βp/q)`, `d = √(βq/p)`,
`τ = √(pq/β)` and `ũ = cu`, `ṽ = dv` of Lemma 3.11, p.22 (PDF p.22).

**Formalization Note** A function of the scalars `(y, u, v) = (y_i, u_i, v_i)` of one active
coordinate, with `β = √(1 − y²)`, `β′ = −y/√(1 − y²)`, `β″ = −1/(1 − y²)^{3/2}` (the formulas printed on
p.8 for `−1 < y < 1`), `p = 1 + ιβ′v`, `q = 1 − ιβ′u` (Definition 3.8, p.22). Every quantity of
Definitions 3.14, 3.19, 3.20 and Lemma 3.11 that enters it depends only on `(y_i, u_i, v_i)`. -/
noncomputable def LamC (y u v : ℝ) : ℝ :=
  let β' : ℝ := -y / Real.sqrt (1 - y ^ 2)
  let p : ℝ := 1 + iota * β' * v
  let q : ℝ := 1 - iota * β' * u
  let β : ℝ := beta y
  let c : ℝ := Real.sqrt (β * p / q)
  let d : ℝ := Real.sqrt (β * q / p)
  let τ : ℝ := Real.sqrt (p * q / β)
  let ut : ℝ := c * u
  let vt : ℝ := d * v
  let g : ℝ := β' / β
  g / (τ * Real.sqrt (ut * vt))

end KSPolySign


