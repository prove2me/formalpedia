-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_bondPrice
-- name    : BauerleRiederMDP_NoArbitrage_FinancialMarket_bondPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:27.394309+00:00
-- url     : https://prove2.me/theorems/57ac0638-fb69-479e-938b-3d040b5089eb
-- title:
--   Bond price $S^0_n$
-- statement:
--   The riskless bond has price $S^0_0=1$ and $S^0_{n+1}=S^0_n(1+i_{n+1})$, that is
--   $$
--   S^0_n=\prod_{t=1}^{n}(1+i_t).
--   $$
--   It is the numéraire used to discount the stock prices.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.1, p.61 (PDF 75)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The price `S^0_n` of the riskless bond (Bäuerle & Rieder 2011, §3.1, p.61, PDF 75):
`S^0_0 ≡ 1` and `S^0_{n+1} := S^0_n (1 + i_{n+1})`, i.e. `S^0_n = ∏_{t<n} (1 + i_{t+1})`. -/
def FinancialMarket.bondPrice (M : FinancialMarket Ω P d) (n : ℕ) : ℝ :=
  ∏ t ∈ Finset.range n, (1 + M.i (t + 1))

end BauerleRiederMDP.NoArbitrage


