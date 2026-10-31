-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoQPlus
-- name    : KallMayerSLP_RiskMeasures_rhoQPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:09.822199+00:00
-- url     : https://prove2.me/theorems/e0644c17-547e-4e63-b5d2-f4f63e5ce4ac
-- title:
--   Upper quadratic deviation $\rho^+_Q$
-- statement:
--   For $\vartheta\in\mathcal L^1_1$, $\rho^+_Q(\vartheta):=\sqrt{\mathbb E[(\vartheta^+)^2]}$.
--
--   **Formalization Note** The value lies in $[0,\infty]$: the second moment is a Lebesgue integral of a nonnegative function and the square root is $x\mapsto x^{1/2}$ on $[0,\infty]$. On the printed domain $\mathcal L^1_1$ the second moment may be infinite; on $\mathcal L^2_1$ it is finite and the value is the real formula.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.5 (H), p.187 (PDF 197)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Upper quadratic deviation `ρ⁺_Q`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.5 (H), p.187 (PDF 197): `ρ⁺_Q(ϑ) := √(𝔼[(ϑ⁺)²])`, `ϑ ∈ 𝓛¹₁`.

**Formalization Note.** The value lies in `[0, ∞]`: the second moment is the lower Lebesgue integral `∫⁻`, and `√` is `x ↦ x^(1/2)` on `[0, ∞]`. On the printed domain `𝓛¹₁` the second moment can be infinite; on `𝓛²₁` the value is finite and equals the real formula. -/
noncomputable def rhoQPlus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ≥0∞ :=
  (∫⁻ ω, ENNReal.ofReal (max (ϑ ω) 0 ^ 2) ∂P) ^ (1 / 2 : ℝ)

end KallMayerSLP.RiskMeasures


