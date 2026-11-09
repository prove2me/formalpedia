-- Prove2me | Definitions.Def_SharpConsist_F
-- name    : SharpConsist_F
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:39.326448+00:00
-- url     : https://prove2.me/theorems/ab36a810-578b-41c1-b1ed-1be31cd43106
-- title:
--   The lifted profiles $F$, $K$ of Eq. (5.4)
-- statement:
--   Fix $T$ and an integer $m\ge1$ (in the paper $m\ge32$). For normalized counts $(x,y)$ — in the instance, $x=|S\cap A|/k$ and $y=|S\cap\bar A|/k$ — set
--   $$\omega_m=1+\frac1m,\qquad t=\omega_m y,\qquad u=x-\frac ym,\qquad s=x+y,\qquad \phi_m(s)=\frac{32(1-e^{-s})}{m}.$$
--   Eq. (5.4) lifts the scalar profiles to
--   $$F(x,y)=v(t)+u\,v'(t)+\phi_m(s),\qquad K(x,y)=w(t)+u\,v'(t)+\phi_m(s).$$
--   Here $s$ is the normalized size of a set, $u$ its imbalance, and $\phi_m$ a common concave regularizer.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, Eq. (5.4), p.14

import Mathlib
import Definitions.Def_SharpConsist_v

namespace SharpConsist

/-- The lift factor `ω_m = 1 + 1/m`. Fu–Zhang–Tao, arXiv:2609.09986 (held version, sha256
874ec76c…), §5.2, p.14. -/
noncomputable def omegaM (m : ℕ) : ℝ := 1 + 1 / (m : ℝ)

/-- The common regularizer `ϕ_m(s) = 32(1 − e^{−s})/m`, §5.2, p.14. -/
noncomputable def phiM (m : ℕ) (s : ℝ) : ℝ := 32 * (1 - Real.exp (-s)) / (m : ℝ)

/-- The **lifted current profile** of Eq. (5.4), p.14: `F(x, y) = v(t) + u v′(t) + ϕ_m(s)` with
`t = ω_m y`, `u = x − y/m` and `s = x + y`. Here `x = |S ∩ A|/k` and `y = |S ∩ Ā|/k` are the
normalized counts of a queried set (§5.1, p.13). -/
noncomputable def F (T : ℝ) (m : ℕ) (x y : ℝ) : ℝ :=
  v T (omegaM m * y) + (x - y / (m : ℝ)) * v' T (omegaM m * y) + phiM m (x + y)

/-- The **lifted future profile** of Eq. (5.4), p.14: `K(x, y) = w(t) + u v′(t) + ϕ_m(s)`, with
`t, u, s` as for `F`. -/
noncomputable def K (T : ℝ) (m : ℕ) (x y : ℝ) : ℝ :=
  w T (omegaM m * y) + (x - y / (m : ℝ)) * v' T (omegaM m * y) + phiM m (x + y)

end SharpConsist


