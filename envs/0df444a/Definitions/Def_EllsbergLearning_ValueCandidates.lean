-- Prove2me | Definitions.Def_EllsbergLearning_ValueCandidates
-- name    : EllsbergLearning_ValueCandidates
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:43.987797+00:00
-- url     : https://prove2.me/theorems/d06f86ae-090e-43aa-ad41-77d8e06c77df
-- title:
--   The candidate value functions (44) and (50) built from $g(y;C,C')=\hat c(2y-1)\log\frac{y}{1-y}+Cy+C'$
-- statement:
--   Let $g(y;C,C')=\hat c(2y-1)\log\frac{y}{1-y}+Cy+C'$ for $0<y<1$ (43).
--
--   **Case (a.ii)**, with $(r^R,r^l)$ solving (32): $v(t,z)$ equals $(u_{00}-u_{01})(1-\overline m_t(z))+u_{01}$ if $z<\overline f(t,r^l)$; $g(\overline m_t(z);C_1,C_2)$ if $\overline f(t,r^l)\le z<\tilde z_t$; $g(\underline m_t(z);C_3,C_4)$ if $\tilde z_t\le z<\underline f(t,r^R)$; and $(u_{11}-u_{10})\underline m_t(z)+u_{10}$ if $\underline f(t,r^R)\le z$ (44), where $C_1=-\hat c\,l(\overline\pi)$, $C_3=-\hat c\,l(\underline\pi)$,
--   $$C_2=(u_{00}-u_{01})(1-r^l)+u_{01}-\hat c\Big[(2r^l-1)\log\frac{r^l}{1-r^l}-l(\overline\pi)r^l\Big],\quad C_4=(u_{11}-u_{10})r^R+u_{10}-\hat c\Big[(2r^R-1)\log\frac{r^R}{1-r^R}-l(\underline\pi)r^R\Big].$$
--
--   **Case (a.i)**, with $(r^l_1,r^l_2)$, $(r^R_1,r^R_2)$ solving (31), (30): $v(t,z)$ equals $(u_{00}-u_{01})(1-\overline m_t(z))+u_{01}$ if $z<\overline f(t,r^l_2)$; $g(\overline m_t(z);C_5,C_6)$ if $\overline f(t,r^l_2)\le z<\overline f(t,r^l_1)$; $u_2$ if $\overline f(t,r^l_1)\le z<\underline f(t,r^R_1)$; $g(\underline m_t(z);C_7,C_8)$ if $\underline f(t,r^R_1)\le z<\underline f(t,r^R_2)$; and $(u_{11}-u_{10})\underline m_t(z)+u_{10}$ if $\underline f(t,r^R_2)\le z$ (50), with $C_5=-\hat c\,l(r^l_1)$, $C_7=-\hat c\,l(r^R_1)$, $C_6=u_2-\hat c[(2r^l_1-1)\log\frac{r^l_1}{1-r^l_1}-l(r^l_1)r^l_1]$, $C_8=u_2-\hat c[(2r^R_1-1)\log\frac{r^R_1}{1-r^R_1}-l(r^R_1)r^R_1]$.
--
--   These are the value functions of the optimal stopping problem in the two cases of Theorem 4.2(a).
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §5.1, (43)–(44), pp.25–26; (50), p.28

import Definitions.Def_EllsbergLearning_CriticalValues

noncomputable section

namespace EllsbergLearning

namespace Params

variable (p : Params)

/-- The functions `gᵢ(y; C, C') = ĉ(2y − 1) log(y/(1 − y)) + C y + C'` for `0 < y < 1` of (43),
arXiv:1708.01890v2, p.25 (`g₁, …, g₄` differ only in their constants). -/
def gfun (C C' y : ℝ) : ℝ := p.chat * (2 * y - 1) * Real.log (y / (1 - y)) + C * y + C'

/-- The candidate value function (44) of case (a.ii) (arXiv:1708.01890v2, pp.25–26), built from the
indifference point `(π̲, π̄, z̃)` (`πL`, `πU`, `zt`) and the solution `(rᴿ, rˡ)` of (32):

* `(u₀₀ − u₀₁)(1 − m̄_t(z)) + u₀₁` if `z < f̄(t, rˡ)`;
* `g₁(m̄_t(z); C₁, C₂)` if `f̄(t, rˡ) ≤ z < z̃_t`;
* `g₂(m̲_t(z); C₃, C₄)` if `z̃_t ≤ z < f̲(t, rᴿ)`;
* `(u₁₁ − u₁₀)m̲_t(z) + u₁₀` if `f̲(t, rᴿ) ≤ z`;

with `C₁ = −ĉℓ(π̄)`, `C₃ = −ĉℓ(π̲)`,
`C₂ = (u₀₀ − u₀₁)(1 − rˡ) + u₀₁ − ĉ[(2rˡ − 1) log(rˡ/(1 − rˡ)) − ℓ(π̄)rˡ]`,
`C₄ = (u₁₁ − u₁₀)rᴿ + u₁₀ − ĉ[(2rᴿ − 1) log(rᴿ/(1 − rᴿ)) − ℓ(π̲)rᴿ]` (p.26). -/
def vA2 (πL πU : ℝ) (zt : ℝ → ℝ) (rR rl : ℝ) (t z : ℝ) : ℝ :=
  let C1 := -p.chat * ell πU
  let C3 := -p.chat * ell πL
  let C2 := (p.u 0 0 - p.u 0 1) * (1 - rl) + p.u 0 1 -
    p.chat * ((2 * rl - 1) * Real.log (rl / (1 - rl)) - ell πU * rl)
  let C4 := (p.u 1 1 - p.u 1 0) * rR + p.u 1 0 -
    p.chat * ((2 * rR - 1) * Real.log (rR / (1 - rR)) - ell πL * rR)
  if z < p.fUp t rl then (p.u 0 0 - p.u 0 1) * (1 - p.mUp t z) + p.u 0 1
  else if z < zt t then p.gfun C1 C2 (p.mUp t z)
  else if z < p.fLo t rR then p.gfun C3 C4 (p.mLo t z)
  else (p.u 1 1 - p.u 1 0) * p.mLo t z + p.u 1 0

/-- The candidate value function (50) of case (a.i) (arXiv:1708.01890v2, p.28), built from the
solutions `(r₁ˡ, r₂ˡ)` of (31) and `(r₁ᴿ, r₂ᴿ)` of (30):

* `(u₀₀ − u₀₁)(1 − m̄_t(z)) + u₀₁` if `z < f̄(t, r₂ˡ)`;
* `g₃(m̄_t(z); C₅, C₆)` if `f̄(t, r₂ˡ) ≤ z < f̄(t, r₁ˡ)`;
* `u₂` if `f̄(t, r₁ˡ) ≤ z < f̲(t, r₁ᴿ)`;
* `g₄(m̲_t(z); C₇, C₈)` if `f̲(t, r₁ᴿ) ≤ z < f̲(t, r₂ᴿ)`;
* `(u₁₁ − u₁₀)m̲_t(z) + u₁₀` if `f̲(t, r₂ᴿ) ≤ z`;

with `C₅ = −ĉℓ(r₁ˡ)`, `C₇ = −ĉℓ(r₁ᴿ)`, `C₆ = u₂ − ĉ[(2r₁ˡ − 1) log(r₁ˡ/(1 − r₁ˡ)) − ℓ(r₁ˡ)r₁ˡ]`,
`C₈ = u₂ − ĉ[(2r₁ᴿ − 1) log(r₁ᴿ/(1 − r₁ᴿ)) − ℓ(r₁ᴿ)r₁ᴿ]`. -/
def vA1 (r1l r2l r1R r2R : ℝ) (t z : ℝ) : ℝ :=
  let C5 := -p.chat * ell r1l
  let C7 := -p.chat * ell r1R
  let C6 := p.u₂ - p.chat * ((2 * r1l - 1) * Real.log (r1l / (1 - r1l)) - ell r1l * r1l)
  let C8 := p.u₂ - p.chat * ((2 * r1R - 1) * Real.log (r1R / (1 - r1R)) - ell r1R * r1R)
  if z < p.fUp t r2l then (p.u 0 0 - p.u 0 1) * (1 - p.mUp t z) + p.u 0 1
  else if z < p.fUp t r1l then p.gfun C5 C6 (p.mUp t z)
  else if z < p.fLo t r1R then p.u₂
  else if z < p.fLo t r2R then p.gfun C7 C8 (p.mLo t z)
  else (p.u 1 1 - p.u 1 0) * p.mLo t z + p.u 1 0

end Params

end EllsbergLearning


