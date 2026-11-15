-- Prove2me | Definitions.Def_FreeProbAMP_StateEvolution_Supplement_Density
-- name    : FreeProbAMP_StateEvolution_Supplement_Density
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:56:37.787207+00:00
-- url     : https://prove2.me/theorems/8c9b3e67-eefb-48fd-af9c-8bf23afea150
-- title:
--   The densities $f_\eta$, the moments $v_\eta$, $h_\eta$ (3.6)–(3.7) and $\alpha_0=32/(3\pi^2)$
-- statement:
--   Let $\varphi$ and $\Phi$ be the standard normal density and distribution function, and let $\Phi^{-1}$ be the standard normal quantile on $(0,1)$. For $\eta>0$ define the probability density (3.6)
--
--   $$f_\eta(z)=\frac{c_\eta}{(\eta+1-z^2)^2},\qquad -1\le z\le1,$$
--
--   and $f_\eta(z)=0$ for $|z|>1$, where $c_\eta=\big(\int_{-1}^1(\eta+1-z^2)^{-2}dz\big)^{-1}$. For $Z_\eta\sim f_\eta$ define (3.7)
--
--   $$v_\eta=\mathbb E[Z_\eta^2],\qquad h_\eta=2\,\mathbb E\Big[\varphi\Big(\Phi^{-1}\Big(\frac{1+Z_\eta}{2}\Big)\Big)\Big].$$
--
--   Finally $\alpha_0=32/(3\pi^2)$. These quantities parametrize the three-stage control of Theorem 3.3: $f_\eta$ is the stationary law of the second phase, $1-v_\eta$ is the residual variance left to the third phase, and $h_\eta$ is the mean of the third-phase control.
--
--   **Formalization Note.** Expectations against $Z_\eta$ are integrals against $f_\eta$ over $\mathbb R$. $\Phi^{-1}(p)$ is the least $x$ with $p\le\Phi(x)$ for $0<p<1$, and is set to $0$ for $p\notin(0,1)$; this only affects $z=\pm1$, a null set. The definitions are total in $\eta$, but only $\eta>0$ is used.
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 8, (3.6)–(3.7) and Theorem 3.3

import Mathlib

open MeasureTheory ProbabilityTheory
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution.Supplement

/-- The standard normal cumulative distribution function `Φ`. -/
def stdNormalCdf (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The standard normal density `φ = φ_1`. -/
def stdNormalPdf (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- The standard normal quantile `Φ⁻¹(p)` for `0 < p < 1`, as the least `x` with `p ≤ Φ(x)`.
At `p ∉ (0,1)` the value is set to `0`; it is only ever integrated against an absolutely
continuous law that gives these points probability zero. -/
def stdNormalQuantile (p : ℝ) : ℝ :=
  if 0 < p ∧ p < 1 then sInf {x : ℝ | p ≤ stdNormalCdf x} else 0

/-- The normalizing constant `c_η = (∫_{-1}^{1} (η + 1 - z^2)^{-2} dz)^{-1}` of (3.6). -/
def densityConst (η : ℝ) : ℝ :=
  (∫ z in Set.Icc (-1 : ℝ) 1, ((η + 1 - z ^ 2) ^ 2)⁻¹)⁻¹

/-- The probability density (3.6), submission p. 8:
`f_η(z) = c_η / (η + 1 - z^2)^2` for `-1 ≤ z ≤ 1`, and `0` elsewhere. -/
def density (η z : ℝ) : ℝ :=
  if z ∈ Set.Icc (-1 : ℝ) 1 then densityConst η / (η + 1 - z ^ 2) ^ 2 else 0

/-- `v_η = E[Z_η^2]` for `Z_η ∼ f_η`, (3.7). -/
def secondMoment (η : ℝ) : ℝ := ∫ z, z ^ 2 * density η z

/-- `h_η = 2 E[φ(Φ⁻¹((1 + Z_η)/2))]` for `Z_η ∼ f_η`, (3.7). -/
def hCoeff (η : ℝ) : ℝ :=
  2 * ∫ z, stdNormalPdf (stdNormalQuantile ((1 + z) / 2)) * density η z

/-- The threshold `α_0 = 32 / (3 π^2)` of Theorem 3.3. -/
def alpha0 : ℝ := 32 / (3 * Real.pi ^ 2)

end FreeProbAMP.StateEvolution.Supplement


