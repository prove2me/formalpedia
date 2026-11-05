-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_admissibleSet
-- name    : BauerleRiederMDP_NoArbitrage_admissibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:34.303002+00:00
-- url     : https://prove2.me/theorems/6ad3822f-96cc-4366-a41c-0f34fbe2b9b2
-- title:
--   Admissible one-period investments $D(x)$
-- statement:
--   In the one-period market (interest rate $i=i_1$, relative risk $R=R_1$) with a utility function $U$, the admissible investments in the risky assets at initial wealth $x$ are
--   $$
--   D(x)=\{a\in\mathbb R^d : (1+i)(x+a\cdot R)\in\operatorname{dom}U\ \ \mathbb P\text{-a.s.}\}.
--   $$
--   For $a\in D(x)$ the amount $x-a\cdot e$ is invested in the bond, and $(1+i)(x+a\cdot R)$ is the terminal wealth.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.1, p.77 (PDF 91)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_relRisk

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The admissible one-period investments in the risky assets (Bäuerle & Rieder 2011, §4.1, p.77,
PDF 91):
`D(x) := {a ∈ ℝ^d | (1 + i)(x + a · R) ∈ dom U ℙ-a.s.}`,
where `i = i_1`, `R = R_1` ("we skip the time index on `i_1`, `R̃_1` and `R_1`", p.76). -/
def admissibleSet (M : FinancialMarket Ω P d) (dom : Set ℝ) (x : ℝ) : Set (Fin d → ℝ) :=
  {a | ∀ᵐ ω ∂P, (1 + M.i 1) * (x + ∑ k, a k * M.relRisk 1 ω k) ∈ dom}

end BauerleRiederMDP.NoArbitrage


