-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_perpetualPut
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_perpetualPut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:25.577136+00:00
-- url     : https://prove2.me/theorems/86e78c4b-88d8-456f-924b-545dd884b8ba
-- title:
--   Price $P(x)=\sup_{\tau\le\infty}\mathbb E^{\mathbb Q}_x[\beta^\tau(K-S_\tau)]$ of the perpetual American put
-- statement:
--   The price at time zero of the **perpetual American put** with strike $K$ and initial stock price $x$ is
--   $$P(x):=\sup_{\tau\le\infty}\mathbb E^{\mathbb Q}_x\big[\beta^\tau(K-S_\tau)^+\big],$$
--   where the supremum runs over all stopping times with values in $\mathbb N_0\cup\{\infty\}$ and the stopping reward for $\tau=\infty$ is zero.
--
--   **Formalization Note** The book's display on p.337 writes $K-S_\tau$; the payoff here is $(K-S_\tau)^+$, as in the first display of the proof of Theorem 11.1.3 and by the remark on p.332. The two suprema are equal. The supremum is taken in $[0,\infty]$ and converted to a real number; for $x\ge0$ it is at most $K$, so the conversion is exact. Values at $x<0$ are never used.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.1, p.337, PDF 345

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_putReward
import Definitions.Def_BauerleRiederMDP_AmericanPut_IsStoppingTime

open MeasureTheory
open scoped ENNReal

namespace BauerleRiederMDP.AmericanPut

/-- The **price of the perpetual American put** with strike `K` at initial stock price `x` (Bäuerle & Rieder,
Markov Decision Processes with Applications to Finance (2011), §11.1, p.337, PDF 345):
`P(x) := sup_{τ ≤ ∞} 𝔼^ℚ_x[β^τ (K − S_τ)]`, where the stopping reward for `τ = ∞` is equal to zero.

**Formalization Note.** The payoff is `(K − S_τ)⁺` (book's reading, p.332 "we can equivalently choose `h⁺` as a
payoff", and the first display of the proof of Theorem 11.1.3, p.338); exercising where `K − S_τ < 0` is never
better than never exercising, so the two suprema coincide. The supremum runs over all stopping times with
values in `ℕ₀ ∪ {∞}` (`IsStoppingTime`) and is taken in `ℝ≥0∞`; it is at most `K`, so `toReal` is exact. -/
noncomputable def BinomialMarket.perpetualPut (M : BinomialMarket) (K x : ℝ) : ℝ :=
  (⨆ τ : {τ : (ℕ → Bool) → ℕ∞ // IsStoppingTime τ}, M.putReward K x τ.1).toReal

end BauerleRiederMDP.AmericanPut


