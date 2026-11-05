-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_expectedUtility
-- name    : BauerleRiederMDP_NoArbitrage_expectedUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:30.936214+00:00
-- url     : https://prove2.me/theorems/1b77bfce-0582-4f40-80fe-d0f11ee36973
-- title:
--   One-period expected utility $u(x,a)$
-- statement:
--   In the one-period market with utility function $U$,
--   $$
--   u(x,a)=\mathbb E\,U\bigl((1+i)(x+a\cdot R)\bigr),\qquad a\in D(x),
--   $$
--   the expected utility of terminal wealth when $a$ is invested in the risky assets.
--
--   **Formalization Note** The expectation is computed in the extended reals as $\int U(\cdot)^+\,d\mathbb P-\int U(\cdot)^-\,d\mathbb P$, so the value $-\infty$ (possible for logarithmic utility) is represented. Under the standing assumption $\mathbb E\|R\|<\infty$ the positive part is finite. The book uses $u(x,a)$ only for $a\in D(x)$, where the values of $U$ outside $\operatorname{dom}U$ do not matter.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.1, p.77 (PDF 91)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_relRisk

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The one-period expected utility (Bäuerle & Rieder 2011, §4.1, p.77, PDF 91):
`u(x, a) := 𝔼 U((1 + i)(x + a · R))`, with `i = i_1` and `R = R_1`.

**Formalization Note** The expectation is taken in `EReal` as
`∫ U(·)⁺ dℙ − ∫ U(·)⁻ dℙ` (two Lebesgue integrals in `[0, ∞]`), so an expected utility of `−∞`
(e.g. logarithmic utility with mass near `0`) is `⊥` rather than a junk real value. The book
shows `u(x, a) < ∞` under its standing assumption `𝔼‖R‖ < ∞` (p.76), so the positive part is
finite in every statement of this mission and `EReal`'s `⊤ − ⊤ = ⊥` never occurs there. The book
uses `u(x, a)` only for `a ∈ D(x)`, where the argument of `U` lies in `dom U` almost surely; the
values of `U` outside `dom U` then do not affect `u(x, a)`. -/
noncomputable def expectedUtility (M : FinancialMarket Ω P d) (U : ℝ → ℝ) (x : ℝ)
    (a : Fin d → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (U ((1 + M.i 1) * (x + ∑ k, a k * M.relRisk 1 ω k))) ∂P : ENNReal) :
      EReal) -
    ((∫⁻ ω, ENNReal.ofReal (-U ((1 + M.i 1) * (x + ∑ k, a k * M.relRisk 1 ω k))) ∂P : ENNReal) :
      EReal)

end BauerleRiederMDP.NoArbitrage


