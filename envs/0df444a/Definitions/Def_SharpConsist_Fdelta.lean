-- Prove2me | Definitions.Def_SharpConsist_Fdelta
-- name    : SharpConsist_Fdelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:34.830204+00:00
-- url     : https://prove2.me/theorems/ec49c377-3001-4399-ae22-dcfd68a9de27
-- title:
--   The flattened profiles $F_\delta$, $K_\delta$ of Eq. (5.5)
-- statement:
--   With $t,u,s,\phi_m$ as in Eq. (5.4), let $\delta=1/(64m)$ and $\operatorname{clip}(u,-\delta,\delta)=\min\{\delta,\max\{-\delta,u\}\}$. Eq. (5.5) moves the tangent point of the current profile towards $s$ and corrects the future branch:
--   $$z=t+\operatorname{clip}(u,-\delta,\delta),\qquad F_\delta(x,y)=v(z)+(s-z)\,v'(z)+\phi_m(s),\qquad K_\delta(x,y)=K(x,y)+32\delta e^{-s}.$$
--   Inside the band $|u|\le\delta$ one has $z=s$ and $F_\delta(x,y)=v(s)+\phi_m(s)$, which depends only on the size $s$.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, Eq. (5.5), p.14

import Mathlib
import Definitions.Def_SharpConsist_F

namespace SharpConsist

/-- The band half-width `δ = 1/(64m)`. Fu–Zhang–Tao, arXiv:2609.09986 (held version, sha256
874ec76c…), §5.2, p.14. -/
noncomputable def deltaM (m : ℕ) : ℝ := 1 / (64 * (m : ℝ))

/-- `clip(u, a, b) = min{b, max{a, u}}`, §5.2, p.14 (used with `a = −δ`, `b = δ`). -/
noncomputable def clip (u a b : ℝ) : ℝ := min b (max a u)

/-- The **flattened current profile** of Eq. (5.5), p.14:
`F_δ(x, y) = v(z) + (s − z) v′(z) + ϕ_m(s)` with `z = t + clip(u, −δ, δ)`, `t = ω_m y`, `u = x − y/m`,
`s = x + y`. -/
noncomputable def Fdelta (T : ℝ) (m : ℕ) (x y : ℝ) : ℝ :=
  v T (omegaM m * y + clip (x - y / (m : ℝ)) (-deltaM m) (deltaM m)) +
    ((x + y) - (omegaM m * y + clip (x - y / (m : ℝ)) (-deltaM m) (deltaM m))) *
      v' T (omegaM m * y + clip (x - y / (m : ℝ)) (-deltaM m) (deltaM m)) +
    phiM m (x + y)

/-- The **corrected future profile** of Eq. (5.5), p.14: `K_δ(x, y) = K(x, y) + 32 δ e^{−s}`,
`s = x + y`. -/
noncomputable def Kdelta (T : ℝ) (m : ℕ) (x y : ℝ) : ℝ :=
  K T m x y + 32 * deltaM m * Real.exp (-(x + y))

end SharpConsist


