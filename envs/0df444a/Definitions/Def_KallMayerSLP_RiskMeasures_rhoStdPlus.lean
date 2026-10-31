-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoStdPlus
-- name    : KallMayerSLP_RiskMeasures_rhoStdPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:11.207961+00:00
-- url     : https://prove2.me/theorems/f04f8d5c-7c38-47b2-a722-51940c6698af
-- title:
--   Upper standard semideviation $\rho^+_{\mathrm{Std}}=\sigma^+$
-- statement:
--   For $\vartheta\in\mathcal L^1_1$, $\rho^+_{\mathrm{Std}}(\vartheta):=\sigma^+(\vartheta):=\sqrt{\mathbb E\big[\big((\vartheta-\mathbb E[\vartheta])^+\big)^2\big]}$.
--
--   **Formalization Note** The value lies in $[0,\infty]$: the second moment is a Lebesgue integral of a nonnegative function and the square root is $x\mapsto x^{1/2}$ on $[0,\infty]$. On the printed domain $\mathcal L^1_1$ the second moment may be infinite; on $\mathcal L^2_1$ it is finite and the value is the real formula. The book writes $\sigma^+(x)$; the argument is $\vartheta$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.6 (K), p.188 (PDF 198)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Upper standard semideviation `ρ⁺_Std = σ⁺`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.6 (K), p.188 (PDF 198): `ρ⁺_Std(ϑ) := σ⁺(ϑ) := √(𝔼[((ϑ − 𝔼[ϑ])⁺)²])`, `ϑ ∈ 𝓛¹₁`.

**Formalization Note.** The value lies in `[0, ∞]`: the second moment is the lower Lebesgue integral `∫⁻`, and `√` is `x ↦ x^(1/2)` on `[0, ∞]`. On the printed domain `𝓛¹₁` the second moment can be infinite; on `𝓛²₁` the value is finite and equals the real formula. The book writes `σ⁺(x)`; the argument is `ϑ`. -/
noncomputable def rhoStdPlus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ≥0∞ :=
  (∫⁻ ω, ENNReal.ofReal (max (ϑ ω - ∫ ω', ϑ ω' ∂P) 0 ^ 2) ∂P) ^ (1 / 2 : ℝ)

end KallMayerSLP.RiskMeasures


