-- Prove2me | Definitions.Def_TechBreakthrough_Model_Wb
-- name    : TechBreakthrough_Model_Wb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:35:26.525681+00:00
-- url     : https://prove2.me/theorems/9f3d244d-e9c8-474e-b849-8e31e5d544d7
-- title:
--   The function $W_b$ of (48)–(54)
-- statement:
--   Given a candidate $b$ from $\underline m$, the function $W_b$ on $J$ is
--
--   $$W(x,m)=[1-F(m)]R(x)\ \text{ on }S,\qquad W(x,m)=[1-F(m)]\frac{h_1(x)}{h_1(x_R)}R(x_R)\ \text{ on }(\alpha,x_R)\times[\underline m,\beta),$$
--
--   $$W(x,m)=A(m)h_1(x)+B(m)h_2(x)\ \text{ for }m\in[\underline m,\beta),\ x\in(b(m),m],\qquad W(x,m)=C(m)h_1(x)\ \text{ for }m<\underline m,$$
--
--   where
--
--   $$A(m)=\frac{1-F(m)}{\gamma S'(b(m))}[R'(b(m))h_2(b(m))-R(b(m))h_2'(b(m))],$$
--
--   $$B(m)=-\frac{1-F(m)}{\gamma S'(b(m))}[R'(b(m))h_1(b(m))-R(b(m))h_1'(b(m))],$$
--
--   $$C(m)=\frac{1-F(\underline m)}{h_1(x_R)}R(x_R)+\int_m^{\underline m}\frac{f(y)}{h_1(y)}G(y)\,dy.$$
--
--   This is the explicit solution given $b$.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, (48)–(54), pp.26–27

import Definitions.Def_TechBreakthrough_Model_E

namespace TechBreakthrough

namespace Model

variable (M : Model)

/-- The coefficient `A(m)` of (51), arXiv:2106.05112v1, p.26. -/
noncomputable def coefA (c : ℝ) (h₁ h₂ : ℝ → ℝ) (b : ℝ → ℝ) (m : ℝ) : ℝ :=
  (1 - M.F m) / (M.gamma c h₁ h₂ * M.scaleDeriv c (b m)) *
    (deriv M.R (b m) * h₂ (b m) - M.R (b m) * deriv h₂ (b m))

/-- The coefficient `B(m)` of (52), arXiv:2106.05112v1, p.26. -/
noncomputable def coefB (c : ℝ) (h₁ h₂ : ℝ → ℝ) (b : ℝ → ℝ) (m : ℝ) : ℝ :=
  -((1 - M.F m) / (M.gamma c h₁ h₂ * M.scaleDeriv c (b m))) *
    (deriv M.R (b m) * h₁ (b m) - M.R (b m) * deriv h₁ (b m))

/-- The coefficient `C(m)` of (54), arXiv:2106.05112v1, p.27. -/
noncomputable def coefC (h₁ : ℝ → ℝ) (xR mLow m : ℝ) : ℝ :=
  (1 - M.F mLow) / h₁ xR * M.R xR + ∫ y in m..mLow, M.f y / h₁ y * M.G y

/-- The function `W` built from a candidate `b` by (48)–(54), arXiv:2106.05112v1, pp.25–27:
`(1 − F(m)) R(x)` on `S`; `(1 − F(m)) h₁(x)/h₁(x_R) R(x_R)` on `(α, x_R) × [m̲, β)`;
`A(m)h₁(x) + B(m)h₂(x)` for `m ∈ [m̲, β)`, `x ∈ (b(m), m]`; `C(m)h₁(x)` for `m < m̲`. -/
noncomputable def Wb (c : ℝ) (h₁ h₂ : ℝ → ℝ) (xR mLow : ℝ) (b : ℝ → ℝ) (x m : ℝ) : ℝ :=
  if mLow ≤ m then
    if x < xR then (1 - M.F m) * (h₁ x / h₁ xR) * M.R xR
    else if x ≤ b m then (1 - M.F m) * M.R x
    else M.coefA c h₁ h₂ b m * h₁ x + M.coefB c h₁ h₂ b m * h₂ x
  else M.coefC h₁ xR mLow m * h₁ x

end Model

end TechBreakthrough


