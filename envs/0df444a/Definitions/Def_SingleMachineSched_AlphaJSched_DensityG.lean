-- Prove2me | Definitions.Def_SingleMachineSched_AlphaJSched_DensityG
-- name    : SingleMachineSched_AlphaJSched_DensityG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:17:08.872181+00:00
-- url     : https://prove2.me/theorems/931853a6-798d-4900-808a-29c9ec099727
-- title:
--   The constants $\delta$, $c$ and the truncated exponential density $g$ of Theorem 3.9
-- statement:
--   For a real parameter $\gamma$ define
--   $$\delta=\gamma+\ln(2-\gamma),\qquad c=1+\frac{e^{-\gamma}}{\delta},\qquad g(\alpha)=\begin{cases}(c-1)e^{\alpha}&\text{if }0<\alpha\le\delta,\\0&\text{otherwise,}\end{cases}$$
--   the measure on $\mathbb R$ with density $g$ with respect to Lebesgue measure, and the mean
--   $$E_g[\alpha]=\int_0^1\alpha\,g(\alpha)\,d\alpha .$$
--   In Theorem 3.9, $\gamma\approx0.4835$ is the solution in $(0,1)$ of $\gamma+\ln(2-\gamma)=e^{-\gamma}((2-\gamma)e^\gamma-1)$; then $\delta\approx0.8999$, $c<1.6853$, $g$ is a probability density on $(0,1]$ and $E_g[\alpha]=c\delta-1$.
--
--   **Formalization Note.** The paper states $g$ on the domain $(0,1]$ with the case "if $\alpha\le\delta$"; the definition makes the domain explicit, so the support is $(0,\delta]$. The negative part of $g$ is clipped when it is used as a density (`ENNReal.ofReal`); under the hypothesis on $\gamma$, $c>1$ and $g\ge0$, so nothing is clipped. $E_g[\alpha]$ is written as an integral against $g$, not as the expectation of a random variable.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 185 (Theorem 3.9: γ, δ, c, g; Lemma 3.11: E_g[α])

import Mathlib

namespace SingleMachineSched.AlphaJSched

open MeasureTheory

/-- `δ := γ + ln(2 − γ)` (Theorem 3.9, p. 185). -/
noncomputable def delta (γ : ℝ) : ℝ :=
  γ + Real.log (2 - γ)

/-- `c := 1 + e^{−γ}/δ` (Theorem 3.9, p. 185). -/
noncomputable def cConst (γ : ℝ) : ℝ :=
  1 + Real.exp (-γ) / delta γ

/-- The density `g(α) = (c − 1) e^α` for `0 < α ≤ δ` and `0` otherwise (Theorem 3.9, p. 185). -/
noncomputable def gDens (γ : ℝ) (a : ℝ) : ℝ :=
  if 0 < a ∧ a ≤ delta γ then (cConst γ - 1) * Real.exp a else 0

/-- The measure on `ℝ` with density `g`. -/
noncomputable def gMeasure (γ : ℝ) : Measure ℝ :=
  volume.withDensity (fun a => ENNReal.ofReal (gDens γ a))

/-- `E_g[α] = ∫_0^1 α g(α) dα`, the mean of the density `g` (p. 185). -/
noncomputable def Eg (γ : ℝ) : ℝ :=
  ∫ a in Set.Ioc 0 1, a * gDens γ a

end SingleMachineSched.AlphaJSched


