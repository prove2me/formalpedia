-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom
-- name    : BauerleRiederMDP_LQ_Supplement_CIRandom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:03:47.049122+00:00
-- url     : https://prove2.me/theorems/5700709b-3a98-5b6a-b16d-8460eecd9062
-- title:
--   The consumption-investment problem with random horizon
-- statement:
--   **The consumption-investment problem with random horizon** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.1, pp.267–269, PDF 277–279): a market with $d$ risky assets and a riskless bond with interest rate $0$; the relative risks $R_1, R_2, \dots $ are i.i.d. with law $\mu R$ on $[-1, \infty )^d$ satisfying Assumption (FM): (i) no arbitrage, (ii) $\mathbb E \|R_1\| < \infty $; the horizon $\tau $ is geometric with parameter $p \in  (0, 1)$, $\mathbb P (\tau  = n) = (1 - p)p^{n-1}$, independent of the market; $\beta  \in  (0, 1]$; $U_c, U_p : [0, \infty ) \to  \mathbb R _+$ are continuous utility functions with $dom U_c = dom U_p = [0, \infty )$.
--
--   **Formalization Note.** $\mathbb R ^d$ is $Fin d \to  \mathbb R $. (FM)(i) is the published one-period `NoArbitrageLaw` of the law of $R_1$, which for i.i.d. relative risks is equivalent to no arbitrage for every finite horizon (Theorem 3.1.5). Utility functions are the published `IsUtilityFunction` on $[0, \infty )$ (Definition 3.4.1), nonnegative on $[0, \infty )$; values off $[0, \infty )$ are unused.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.1, pp.267–269, PDF 277–279

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_NoArbitrageLaw

open MeasureTheory ProbabilityTheory
open BauerleRiederMDP.RegimeSwitching (IsUtilityFunction NoArbitrageLaw)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The consumption-investment problem with random horizon** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §9.1, pp.267–269, PDF 277–279): a market with `d`
risky assets and a riskless bond with interest rate `0`; the relative risks `R_1, R_2, …` are
i.i.d. with law `μR` on `[−1, ∞)^d` satisfying Assumption (FM): (i) no arbitrage, (ii)
`𝔼‖R_1‖ < ∞`; the horizon `τ` is geometric with parameter `p ∈ (0, 1)`, `ℙ(τ = n) = (1 − p)p^{n−1}`,
independent of the market; `β ∈ (0, 1]`; `U_c, U_p : [0, ∞) → ℝ_+` are continuous utility
functions with `dom U_c = dom U_p = [0, ∞)`.

**Formalization Note.** `ℝ^d` is `Fin d → ℝ`. (FM)(i) is the published one-period
`NoArbitrageLaw` of the law of `R_1`, which for i.i.d. relative risks is equivalent to no arbitrage
for every finite horizon (Theorem 3.1.5). Utility functions are the published
`IsUtilityFunction` on `[0, ∞)` (Definition 3.4.1), nonnegative on `[0, ∞)`; values off `[0, ∞)`
are unused. -/
structure CIRandom (d : ℕ) where
  μR : Measure (Fin d → ℝ)
  μR_prob : IsProbabilityMeasure μR
  support : ∀ᵐ z ∂μR, ∀ k, -1 ≤ z k
  noArbitrage : NoArbitrageLaw μR
  moment : ∫⁻ z, ‖z‖ₑ ∂μR < ⊤
  p : ℝ
  p_mem : p ∈ Set.Ioo (0 : ℝ) 1
  β : ℝ
  β_mem : β ∈ Set.Ioc (0 : ℝ) 1
  Uc : ℝ → ℝ
  Up : ℝ → ℝ
  Uc_util : IsUtilityFunction Uc (Set.Ici 0)
  Up_util : IsUtilityFunction Up (Set.Ici 0)
  Uc_nonneg : ∀ x, 0 ≤ x → 0 ≤ Uc x
  Up_nonneg : ∀ x, 0 ≤ x → 0 ≤ Up x

attribute [instance] CIRandom.μR_prob

end BauerleRiederMDP.LQ.Supplement


