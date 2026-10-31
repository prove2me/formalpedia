-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoQMinus
-- name    : KallMayerSLP_RiskMeasures_rhoQMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:08.960744+00:00
-- url     : https://prove2.me/theorems/08555643-97fb-46d7-b3ab-d440feac27ff
-- title:
--   Lower quadratic deviation $\rho^-_Q$
-- statement:
--   For $\vartheta\in\mathcal L^1_1$, $\rho^-_Q(\vartheta):=\sqrt{\mathbb E[(\vartheta^-)^2]}$, with $t^-=\max\{0,-t\}$.
--
--   **Formalization Note** The value lies in $[0,\infty]$: the second moment is a Lebesgue integral of a nonnegative function and the square root is $x\mapsto x^{1/2}$ on $[0,\infty]$. On the printed domain $\mathcal L^1_1$ the second moment may be infinite; on $\mathcal L^2_1$ it is finite and the value is the real formula.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.5 (H), p.187 (PDF 197)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Lower quadratic deviation `ρ⁻_Q`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.5 (H), p.187 (PDF 197): `ρ⁻_Q(ϑ) := √(𝔼[(ϑ⁻)²])`, `ϑ ∈ 𝓛¹₁`, with `z⁻ = max{0, −z}`.

**Formalization Note.** The value lies in `[0, ∞]`: the second moment is the lower Lebesgue integral `∫⁻`, and `√` is `x ↦ x^(1/2)` on `[0, ∞]`. On the printed domain `𝓛¹₁` the second moment can be infinite; on `𝓛²₁` the value is finite and equals the real formula. -/
noncomputable def rhoQMinus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ≥0∞ :=
  (∫⁻ ω, ENNReal.ofReal (max (-ϑ ω) 0 ^ 2) ∂P) ^ (1 / 2 : ℝ)

end KallMayerSLP.RiskMeasures


