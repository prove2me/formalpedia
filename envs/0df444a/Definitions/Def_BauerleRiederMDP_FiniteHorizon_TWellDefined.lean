-- Prove2me | Definitions.Def_BauerleRiederMDP_FiniteHorizon_TWellDefined
-- name    : BauerleRiederMDP_FiniteHorizon_TWellDefined
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:35.934687+00:00
-- url     : https://prove2.me/theorems/b285f852-7bc2-4ae2-88b8-24c87f7ff59b
-- title:
--   "$T_nv$ is well-defined"
-- statement:
--   For $v:E\to[-\infty,\infty)$, the operator value $T_nv$ is well defined when the integral $\int v(x')\,Q_n(dx'\mid x,a)$ exists for every $(x,a)\in D_n$, that is, when $\int v^+\,dQ_n$ and $\int v^-\,dQ_n$ are not both infinite.
--
--   This is the phrase "whenever the integral exists" of Definition 2.3.1, used in clause (ii) of the Structure Assumption.
--
--   **Formalization Note.** The integral `erealIntegral` returns $-\infty$ when both parts are infinite; this predicate is what excludes that case.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.3.1, p.19, and (SA_N) (ii), p.23

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)

namespace BauerleRiederMDP.FiniteHorizon

universe u

/-- "`T_n v` is well-defined" in (SA_N)(ii) (Bäuerle & Rieder (2011), p.23, PDF 38), for
`v ∈ IM(E)`: the integral `∫ v(x') Q_n(dx' | x, a)` in Definition 2.3.1 a) (p.19, PDF 34,
"whenever the integral exists") exists for every `(x, a) ∈ D_n`, that is, `∫ v⁺ dQ_n` and
`∫ v⁻ dQ_n` are not both infinite.

**Formalization Note.** `MDPFinance.Bellman.erealIntegral` returns `⊥` when both parts are
infinite. This predicate is what excludes that case. -/
def TWellDefined {E A : Type u} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) : Prop :=
  ∀ xa ∈ M.D n, ∫⁻ x', (v x' ⊔ 0).toENNReal ∂(M.Q n xa) < ⊤ ∨
    ∫⁻ x', ((-v x') ⊔ 0).toENNReal ∂(M.Q n xa) < ⊤

end BauerleRiederMDP.FiniteHorizon


