-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_putReward
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_putReward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:14.890504+00:00
-- url     : https://prove2.me/theorems/5aff6df4-a96a-49d2-9b74-bc3bac013bde
-- title:
--   Expected discounted payoff $\mathbb E^{\mathbb Q}_x[\beta^\tau(K-S_\tau)^+]$ of an exercise time
-- statement:
--   For an exercise time $\tau$ and initial price $S_0=x$, the expected discounted payoff is
--   $$\mathbb E^{\mathbb Q}_x\big[\beta^\tau (K-S_\tau)^+\,\mathbf 1_{\{\tau<\infty\}}\big],$$
--   that is, the stopping reward for $\tau=\infty$ is zero.
--
--   **Formalization Note** The integrand is nonnegative, so the expectation is a lower Lebesgue integral with values in $[0,\infty]$; no integrability condition is needed. For $x\ge0$ it is at most $K$.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.1, p.337, PDF 345; proof of Theorem 11.1.3 a), p.338, PDF 346

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_beta
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_pathLaw
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_stock
import Definitions.Def_fd04_putPayoff

open MeasureTheory
open scoped ENNReal
open FinancialDerivatives.FD04 (putPayoff)

namespace BauerleRiederMDP.AmericanPut

/-- The **expected discounted exercise payoff** `𝔼^ℚ_x[β^τ (K − S_τ)⁺]` of an exercise time `τ`, with
stopping reward `0` on `{τ = ∞}` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance
(2011), §11.1, p.337, PDF 345 and the proof of Theorem 11.1.3 a), p.338, PDF 346).

**Formalization Note.** The integrand is nonnegative and bounded by `K`, so the expectation is taken as a
lower Lebesgue integral in `ℝ≥0∞` (no integrability side condition, no junk value); it is finite. The stock
starts at `S_0 = x` and `ℚ` is `pathLaw`. -/
noncomputable def BinomialMarket.putReward (M : BinomialMarket) (K x : ℝ)
    (τ : (ℕ → Bool) → ℕ∞) : ℝ≥0∞ :=
  ∫⁻ ω, (match τ ω with
    | ⊤ => 0
    | (n : ℕ) => ENNReal.ofReal (M.beta ^ n * putPayoff K (M.stock x n ω))) ∂M.pathLaw

end BauerleRiederMDP.AmericanPut


