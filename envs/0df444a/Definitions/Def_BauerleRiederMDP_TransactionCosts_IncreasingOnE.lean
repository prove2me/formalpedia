-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_IncreasingOnE
-- name    : BauerleRiederMDP_TransactionCosts_IncreasingOnE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:13.951416+00:00
-- url     : https://prove2.me/theorems/e4461b40-4511-4da8-9625-5a446fb92dd3
-- title:
--   Increasing functions on $E$
-- statement:
--   A function $v:E\to[-\infty,\infty)$ is increasing if it is increasing in each component: $v(x)\le v(y)$ whenever $x,y\in E$, $x_0\le y_0$ and $x_1\le y_1$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, p.107 (PDF 121)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace

namespace BauerleRiederMDP.TransactionCosts

/-- A function `v : E → [−∞, ∞)` is *increasing* (Bäuerle & Rieder 2011, §4.5, p.107, PDF 121:
"increasing means that v is increasing in each component"): `v(x) ≤ v(y)` for all `x, y ∈ E`
with `x₀ ≤ y₀` and `x₁ ≤ y₁`. -/
def IncreasingOnE (v : ℝ × ℝ → EReal) : Prop :=
  ∀ x ∈ stateSpace, ∀ y ∈ stateSpace, x.1 ≤ y.1 → x.2 ≤ y.2 → v x ≤ v y

end BauerleRiederMDP.TransactionCosts


