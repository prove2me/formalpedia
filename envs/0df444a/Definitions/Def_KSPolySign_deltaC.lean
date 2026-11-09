-- Prove2me | Definitions.Def_KSPolySign_deltaC
-- name    : KSPolySign_deltaC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:34.853169+00:00
-- url     : https://prove2.me/theorems/2add4ba4-a08a-41b3-b83e-2354c6f4ac85
-- title:
--   The scalar $\delta=\Gamma^{-1}$
-- statement:
--   With $\Gamma = (\iota\beta uv)^{-1}$ (Definition 3.14), the scalar
--   $$\delta = \Gamma^{-1}$$
--   of Definition 3.19.
--
--   At an active coordinate of a light state, write $y=y_i\in(-1,1)$, $u=u_i$, $v=v_i$, $\beta=\sqrt{1-y^2}$, $\beta'=-y/\sqrt{1-y^2}$, $\beta''=-1/(1-y^2)^{3/2}$, $p=1+\iota\beta'v$, $q=1-\iota\beta'u$ (Definition 3.8), $c=\sqrt{\beta p/q}$, $d=\sqrt{\beta q/p}$, $\tau=\sqrt{pq/\beta}$, $\tilde u=cu$, $\tilde v=dv$ (Lemma 3.11).
--
--   **Formalization Note** A function of the three reals $(y,u,v)$; every quantity of Definitions 3.14, 3.19, 3.20 that enters it depends only on them.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.14, p.27 (PDF p.27); Definition 3.19, p.32 (PDF p.32)

import Mathlib
import Definitions.Def_KSPolySign_iota
import Definitions.Def_KSPolySign_beta
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **The scalar `δ = Γ⁻¹` with `Γ = (ιβuv)⁻¹`.** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Definition 3.14, p.27 (PDF p.27):
"Define Γ_i := (ιβ_i u_i v_i)⁻¹"; Definition 3.19, p.32 (PDF p.32): "δ_i := Γ_i⁻¹".

**Formalization Note** A function of the scalars `(y, u, v) = (y_i, u_i, v_i)` of one active
coordinate, with `β = √(1 − y²)`, `β′ = −y/√(1 − y²)`, `β″ = −1/(1 − y²)^{3/2}` (the formulas printed on
p.8 for `−1 < y < 1`), `p = 1 + ιβ′v`, `q = 1 − ιβ′u` (Definition 3.8, p.22). Every quantity of
Definitions 3.14, 3.19, 3.20 and Lemma 3.11 that enters it depends only on `(y_i, u_i, v_i)`. -/
noncomputable def deltaC (y u v : ℝ) : ℝ := ((iota * beta y * u * v)⁻¹)⁻¹

end KSPolySign


