-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_ArbitrageFree
-- name    : BauerleRiederMDP_NoArbitrage_FinancialMarket_ArbitrageFree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:53.92599+00:00
-- url     : https://prove2.me/theorems/c8996471-a473-444f-9df8-913ffe42cd3b
-- title:
--   There are no arbitrage opportunities
-- statement:
--   A financial market is **free of arbitrage** ("there are no arbitrage opportunities") if no portfolio strategy is an arbitrage opportunity in the sense of Definition 3.1.4.
--
--   This is the standing assumption (FM)(i) of the book's portfolio problems and the left-hand side of Theorems 3.1.5, 4.1.1 and C.1.2.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 3.1.4, p.63 (PDF 77); Theorem 3.1.5 a), p.64 (PDF 78); Theorem C.1.2, p.365 (PDF 370)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio_IsArbitrage

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- "There are no arbitrage opportunities" (Bäuerle & Rieder 2011, Definition 3.1.4 and
Theorem 3.1.5 a), pp.63–64, PDF 77–78), or "the financial market is free of arbitrage"
(Theorem C.1.2, p.365, PDF 370): no portfolio strategy of the market is an arbitrage
opportunity. -/
def FinancialMarket.ArbitrageFree (M : FinancialMarket Ω P d) : Prop :=
  ¬ ∃ φ : Portfolio M, φ.IsArbitrage

end BauerleRiederMDP.NoArbitrage


