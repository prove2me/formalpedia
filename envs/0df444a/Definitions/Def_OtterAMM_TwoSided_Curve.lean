-- Prove2me | Definitions.Def_OtterAMM_TwoSided_Curve
-- name    : OtterAMM_TwoSided_Curve
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:44:42.454189+00:00
-- url     : https://prove2.me/theorems/d9f5921d-8745-434a-9ec0-1710a28dffc7
-- title:
--   The concave AMM pricing curve with (A1)–(A4), the spot prices $\sigma_0,\rho_0$, the sell-X curve $H$, and one-sided compensation curves
-- statement:
--   A pool holds finite reserves $x_0>0$ of token $X$ and $y_0>0$ of token $Y$; $b=b_y$ with $0<b\le y_0$ is the curve's effective $Y$-payout capacity. A **pricing curve** is a function $F:(-b,+\infty)\to(-\infty,x_0)$ (a signed amount $y$ of $Y$ sent into the pool, $F(y)$ of $X$ sent out) with
--
--   - (A1) $F(0)=0$;
--   - (A2) $F$ is continuous, strictly increasing and concave;
--   - (A3) $F$ is differentiable at $0$ with $0<F'(0)<\infty$;
--   - (A4) $\lim_{p\downarrow -b}F(p)=-\infty$.
--
--   The initial prices are $\sigma_0:=F'(0)$ ($X$ per $Y$) and $\rho_0:=1/\sigma_0$ ($Y$ per $X$). The sell-X curve is
--   $$H:[0,+\infty)\to[0,b),\qquad H(x):=-F^{-1}(-x),$$
--   the inverse being taken on $(-b,+\infty)$.
--
--   A **one-sided compensation curve** (§3.1) is $G:[0,+\infty)\to\mathbb R_{\ge0}$ continuous, strictly increasing and concave with $G(0)=0$ and right derivative $G'_+(0)\in(0,+\infty)$; its initial slope is $\sigma_0(G):=G'_+(0)$, and $G'_+(y)$ denotes the right derivative. Finally, for a curve $G$, a slope $s$ and a length $M$, the **spot extension** is
--   $$\mathrm{spotExtend}(G,s,M)(y)=\begin{cases}s\,y,&y\le M,\\ s\,M+G(y-M),&y\ge M,\end{cases}$$
--   the shape of the curves $\tilde F^M_Y$ and $\tilde H^M_X$ of Eq. (8).
--
--   **Formalization Note.** $F$ is a total function `ℝ → ℝ`; (A2), the codomain bound and the domain of $F^{-1}$ are imposed on the open interval $(-b,+\infty)$ only, (A3) is `HasDerivAt F s 0` with $s>0$ and $\sigma_0$ = `deriv F 0`, (A4) is a limit along `𝓝[>] (-b)` to `atBot`. $H$ uses `Function.invFunOn F (Ioi (-b))`. One-sided curves are functions `ℝ → ℝ` whose conditions are imposed on $[0,+\infty)$; the right derivative is `derivWithin G (Ici y) y`. Nonnegativity of a one-sided curve on $[0,+\infty)$ follows from monotonicity and $G(0)=0$.
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), p. 7, §2.2 (PDF 9); p. 9, §3.1 (PDF 11); p. 11, Eq. (8) (PDF 13)

import Mathlib

set_option autoImplicit false

namespace OtterAMM.TwoSided

open Filter Topology

/-- The concave AMM pricing curve of §2.2 (p. 7) with assumptions (A1)–(A4).
The pool holds finite reserves `x0 > 0`, `y0 > 0`; `b` is the effective `Y`-payout capacity
`b_y`, with `0 < b ≤ y0`. The curve `F : (−b, +∞) → (−∞, x0)` is encoded as a function
`ℝ → ℝ`; every assumption is imposed on the open interval `(−b, +∞)` only, and values of `F`
outside it are never used. -/
structure PricingCurve where
  x0 : ℝ
  y0 : ℝ
  b : ℝ
  F : ℝ → ℝ
  x0_pos : 0 < x0
  y0_pos : 0 < y0
  b_pos : 0 < b
  b_le_y0 : b ≤ y0
  /-- codomain `(−∞, x0)` -/
  F_lt_x0 : ∀ p : ℝ, -b < p → F p < x0
  /-- (A1) -/
  A1 : F 0 = 0
  /-- (A2) continuous, strictly increasing and concave on `(−b, +∞)` -/
  A2_continuous : ContinuousOn F (Set.Ioi (-b))
  A2_strictMono : StrictMonoOn F (Set.Ioi (-b))
  A2_concave : ConcaveOn ℝ (Set.Ioi (-b)) F
  /-- (A3) differentiable at `0` with `0 < F'(0) < ∞` -/
  A3 : ∃ s : ℝ, 0 < s ∧ HasDerivAt F s 0
  /-- (A4) `lim_{p ↓ −b} F(p) = −∞` -/
  A4 : Tendsto F (𝓝[>] (-b)) atBot

namespace PricingCurve

/-- `σ0 := F'(0)` (X per Y). By (A3) this is the genuine derivative. -/
noncomputable def σ0 (C : PricingCurve) : ℝ := deriv C.F 0

/-- `ρ0 := 1 / σ0` (Y per X). -/
noncomputable def ρ0 (C : PricingCurve) : ℝ := 1 / C.σ0

/-- The sell-X curve `H(x) := −F⁻¹(−x)`, where `F⁻¹` is the inverse of `F` on `(−b, +∞)`
(it exists for every `x ≥ 0` by (A2) and (A4)); `H` is used only on `[0, +∞)`. -/
noncomputable def H (C : PricingCurve) (x : ℝ) : ℝ :=
  -Function.invFunOn C.F (Set.Ioi (-C.b)) (-x)

end PricingCurve

/-- The one-sided curve conditions of §3.1 (p. 9): `G : [0, +∞) → ℝ≥0` is continuous, strictly
increasing and concave, `G(0) = 0`, and the right derivative `G'₊(0)` exists and lies in
`(0, +∞)`. (Nonnegativity on `[0, +∞)` follows from monotonicity and `G 0 = 0`.) The function
is encoded on `ℝ`; only its values on `[0, +∞)` matter. -/
def IsOneSidedCurve (G : ℝ → ℝ) : Prop :=
  ContinuousOn G (Set.Ici 0) ∧ StrictMonoOn G (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) G ∧
    G 0 = 0 ∧ ∃ s : ℝ, 0 < s ∧ HasDerivWithinAt G s (Set.Ici 0) 0

/-- The right derivative `G'₊(y)`. -/
noncomputable def rightDeriv (G : ℝ → ℝ) (y : ℝ) : ℝ := derivWithin G (Set.Ici y) y

/-- The initial slope `σ0 := G'₊(0)` of a one-sided curve. -/
noncomputable def slope0 (G : ℝ → ℝ) : ℝ := rightDeriv G 0

/-- Extension of a one-sided curve `G` by an initial linear segment of slope `s` and length
`M` (Eq. (8)): `y ↦ s·y` on `[0, M]` and `s·M + G(y − M)` for `y ≥ M`. -/
noncomputable def spotExtend (G : ℝ → ℝ) (s M : ℝ) (y : ℝ) : ℝ :=
  if y ≤ M then s * y else s * M + G (y - M)

end OtterAMM.TwoSided


