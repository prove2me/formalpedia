-- Prove2me | Definitions.Def_BauerleRiederMDP_NoArbitrage_valueFunction
-- name    : BauerleRiederMDP_NoArbitrage_valueFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:04.085869+00:00
-- url     : https://prove2.me/theorems/3413bf67-f50c-4db9-83c1-97cb569aade4
-- title:
--   One-period value function $v(x)$ (4.2)
-- statement:
--   The value of the one-period utility maximization problem is
--   $$
--   v(x)=\sup_{a\in D(x)}u(x,a). \tag{4.2}
--   $$
--   It is equivalent to maximizing $\mathbb E\,U(\varphi^0(1+i)+\varphi\cdot\tilde R)$ over the budget-feasible portfolios (4.1).
--
--   **Formalization Note** The supremum is taken in the extended reals, so $v(x)=+\infty$ (which happens when the market admits an arbitrage) is representable. For $x\in\operatorname{dom}U$, $a=0$ is admissible, so the supremum is over a nonempty set.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.2), p.77 (PDF 91)

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_admissibleSet
import Definitions.Def_BauerleRiederMDP_NoArbitrage_expectedUtility

open MeasureTheory

namespace BauerleRiederMDP.NoArbitrage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The value of the one-period utility maximization problem (Bäuerle & Rieder 2011, eq. (4.2),
p.77, PDF 91): `v(x) := sup_{a ∈ D(x)} u(x, a)`.

**Formalization Note** The supremum is taken in `EReal`, so `v(x) = +∞` is representable (it occurs
when the market admits an arbitrage); `D(x)` contains `a = 0` for `x ∈ dom U`, so the supremum is
over a nonempty set there. -/
noncomputable def valueFunction (M : FinancialMarket Ω P d) (dom : Set ℝ) (U : ℝ → ℝ) (x : ℝ) :
    EReal :=
  ⨆ a ∈ admissibleSet M dom x, expectedUtility M U x a

end BauerleRiederMDP.NoArbitrage


