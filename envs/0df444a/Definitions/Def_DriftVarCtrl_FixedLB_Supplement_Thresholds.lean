-- Prove2me | Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds
-- name    : DriftVarCtrl_FixedLB_Supplement_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:35:38.277599+00:00
-- url     : https://prove2.me/theorems/c6d0ddff-e230-46ba-958d-7566c4c0af7a
-- title:
--   (17), (20), (24), (25)–(29), (172), pp. 18–22 and EC-26 — h⁺, hᵀ, w, ξ_U, the Lambert-W upper curve, conditions (25)–(27), Ṽ and S*
-- statement:
--   The explicit thresholds and curves of the free-lower-boundary case. Write $v_i=2\mu_i/\sigma_i^2$ and $h^*_i=-M\mu_i/U$.
--
--   1. **Strict-inefficiency threshold** (17), Definition 4: for a control with drift $\mu$ and effective drift $v$, and an upper boundary $U'>0$,
--   $$h^+(U')=-\frac{M\mu}{U'\bigl(1-\frac{1-e^{-vU'}}{vU'}\bigr)},$$
--   and $h^+_i=h^+(U)$ for control $i$.
--   2. **Interaction thresholds** (20), read at the other control's $h^+$: $h^T_1=\frac1{d^L_2}(h^+_2-h^*_2)+h^*_1$ and $h^T_2=d^U_1(h^+_1-h^*_1)+h^*_2$, with $d^L_2,d^U_1$ the constants (13), (12) of the base mission.
--   3. **The quantity $w$ and the function $\xi_U$** (24): $w=\dfrac{v_2(\mu_2h_1-h_2\mu_1)}{h_1\mu_2(v_2-v_1)}$ and
--   $$\xi_U(h_1,h_2,w)=-\frac{w^{-\frac{v_2-v_1}{v_1}}v_1e^{-v_2U}h_1}{v_2^2\mu_1}+\frac{(\ln(w)wv_2^2-\ln(w)wv_2v_1-wv_2^2+v_1^2w+v_2^2)h_1}{v_1v_2^2\mu_1}-\frac{h_2}{\mu_2}U .$$
--   4. **Upper curve** (28): $\hat h_2(h_1)=\frac{\mu_2}{\mu_1}h_1\Bigl[1+\frac{v_2-v_1}{v_2}LW\bigl(-e^{-1-\frac{(-M)\mu_1v_1}{h_1}}\bigr)\Bigr]$, with $LW$ the principal branch of the Lambert W function; the lower curve (29) is $h_2=\frac{\sigma_2^2}{\sigma_1^2}h_1$.
--   5. **Conditions of Theorem 4**: (25) $h_2>\hat h_2(h_1)$; (26) $h_2<\frac{\sigma_2^2}{\sigma_1^2}h_1$; (27) $\frac{\sigma_2^2}{\sigma_1^2}h_1<h_2<\hat h_2(h_1)$.
--   6. **Control-1 branch and switching point** (172), Lemma 14: $\tilde V(x)=-\frac{h_1x}{\mu_1}-\frac{h_1e^{-v_1x}}{v_1\mu_1}+\frac{h_1}{v_1\mu_1}$ and $S^*=-\frac1{v_1}\ln w$ at the model's costs.
--
--   These quantities draw the regions of Figures 6 and 7 and are the thresholds of Theorems 3 and 4.
--
--   **Formalization Note** $h^+$, $h^T$, $\hat h_2$ do not involve the running costs. The power in $\xi_U$ is the real power and $\ln$ is `Real.log`; both are evaluated only at $w\in(0,1)$. The text layer of p. 20 loses the parentheses in the exponent $-(v_2-v_1)/v_1$; the page image has them. The Lambert W function is the platform definition `LiquidWelfareFPA.lambertW` (value $0$ below $-1/e$, never evaluated here).
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 18, Definition 4, (17); p. 19, (20); p. 20, (24) and w; pp. 20–22, (25)–(29); p. EC-26, (172) and S*

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants
import Definitions.Def_LiquidWelfareFPA_lambertW

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- The strict-inefficiency threshold `h⁺` of control `c` for an upper boundary `U'`
((17), Definition 4, Wang, Zenios, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 18):
`h⁺(U') = −Mμ / (U'(1 − (1 − e^{−vU'})/(vU')))`, with `v = 2μ/σ²` the effective drift of `c`.
It does not depend on the running costs. -/
noncomputable def hplusU (p : Params) (c : Ctrl) (U' : ℝ) : ℝ :=
  -p.M * p.mu c / (U' * (1 - (1 - Real.exp (-v p c * U')) / (v p c * U')))

/-- `h⁺ᵢ` at the model's own upper boundary `U` ((17), SSRN 3667132 p. 18). -/
noncomputable def hplus (p : Params) (c : Ctrl) : ℝ := hplusU p c p.U

/-- The interaction threshold `hᵀ₁ = (1/dᴸ₂)(h⁺₂ − h*₂) + h*₁` ((20), SSRN 3667132 p. 19), read at
the other control's `h⁺` (the point `(hᵀ₁, h⁺₂)` of Figure 6 and Lemma 13 (124)). -/
noncomputable def hT1 (p : Params) : ℝ :=
  1 / dL2 p * (hplus p .two - hstar p .two) + hstar p .one

/-- The interaction threshold `hᵀ₂ = dᵁ₁(h⁺₁ − h*₁) + h*₂` ((20), SSRN 3667132 p. 19), read at
the other control's `h⁺` (the point `(h⁺₁, hᵀ₂)` of Figure 6 and Lemma 13 (123)). -/
noncomputable def hT2 (p : Params) : ℝ :=
  dU1 p * (hplus p .one - hstar p .one) + hstar p .two

/-- The quantity `w = v₂(μ₂h₁ − h₂μ₁) / (h₁μ₂(v₂ − v₁))` of Theorem 3 (SSRN 3667132 p. 20), as a
function of the two costs `h₁, h₂`. -/
noncomputable def wFB (p : Params) (h₁ h₂ : ℝ) : ℝ :=
  v p .two * (p.μ₂ * h₁ - h₂ * p.μ₁) / (h₁ * p.μ₂ * (v p .two - v p .one))

/-- The function `ξ_U(h₁, h₂, w)` of (24) (SSRN 3667132 p. 20), with the upper boundary `U'` as an
argument:
`ξ_{U'}(h₁,h₂,w) = −w^{−(v₂−v₁)/v₁} v₁ e^{−v₂U'} h₁/(v₂²μ₁)
  + (ln(w) w v₂² − ln(w) w v₂v₁ − w v₂² + v₁² w + v₂²) h₁/(v₁v₂²μ₁) − (h₂/μ₂) U'`.
The power is `Real.rpow`; it is evaluated only at `w ∈ (0, 1)`. -/
noncomputable def xi (p : Params) (U' h₁ h₂ w : ℝ) : ℝ :=
  -(w ^ (-(v p .two - v p .one) / v p .one) * v p .one * Real.exp (-v p .two * U') * h₁
      / (v p .two ^ 2 * p.μ₁))
    + (Real.log w * w * v p .two ^ 2 - Real.log w * w * v p .two * v p .one - w * v p .two ^ 2
        + v p .one ^ 2 * w + v p .two ^ 2) * h₁ / (v p .one * v p .two ^ 2 * p.μ₁)
    - h₂ / p.μ₂ * U'

/-- The upper curve `ĥ₂(h₁) = (μ₂/μ₁) h₁ [1 + ((v₂ − v₁)/v₂) LW(−e^{−1−(−M)μ₁v₁/h₁})]` ((28),
SSRN 3667132 p. 22; the right-hand side of (25)), as a function of `h₁`. `LW` is the principal
branch of the Lambert W function on `[−1/e, ∞)` (`LiquidWelfareFPA.lambertW`); for `h₁ > 0` its
argument lies in `(−1/e, 0)`. -/
noncomputable def upperCurve (p : Params) (h₁ : ℝ) : ℝ :=
  p.μ₂ / p.μ₁ * h₁ * (1 + (v p .two - v p .one) / v p .two
    * LiquidWelfareFPA.lambertW (-Real.exp (-1 - (-p.M) * p.μ₁ * v p .one / h₁)))

/-- Condition (25) of Theorem 4 (SSRN 3667132 p. 20): `h₂ > ĥ₂(h₁)`. -/
def cond25 (p : Params) : Prop := upperCurve p p.h₁ < p.h₂

/-- Condition (26) of Theorem 4 (SSRN 3667132 p. 21): `h₂ < (σ₂²/σ₁²) h₁` (below the lower curve
(29)). -/
def cond26 (p : Params) : Prop := p.h₂ < p.σ₂ ^ 2 / p.σ₁ ^ 2 * p.h₁

/-- Condition (27) of Theorem 4 (SSRN 3667132 p. 21): `(σ₂²/σ₁²) h₁ < h₂ < ĥ₂(h₁)`. -/
def cond27 (p : Params) : Prop :=
  p.σ₂ ^ 2 / p.σ₁ ^ 2 * p.h₁ < p.h₂ ∧ p.h₂ < upperCurve p p.h₁

/-- The control-1 branch `Ṽ₁₂^{[0,S]}(x) = −h₁x/μ₁ − h₁e^{−v₁x}/(v₁μ₁) + h₁/(v₁μ₁)` of the
transformed system ((172), SSRN 3667132 p. EC-26): the solution of `h₁ + μ₁V′ + σ₁²/2 V″ = 0` with
`V(0) = V′(0) = 0`. -/
noncomputable def Vtil (p : Params) (x : ℝ) : ℝ :=
  -p.h₁ * x / p.μ₁ - p.h₁ * Real.exp (-v p .one * x) / (v p .one * p.μ₁) + p.h₁ / (v p .one * p.μ₁)

/-- The switching point `S* = −(1/v₁) ln w` of Theorem 4 (c) (SSRN 3667132 p. EC-26, Lemma 14),
at the model's costs. -/
noncomputable def Sstar (p : Params) : ℝ := -(1 / v p .one) * Real.log (wFB p p.h₁ p.h₂)

end DriftVarCtrl.FixedLB.Supplement


