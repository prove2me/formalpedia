-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_IsStochasticallyMonotone
-- name    : BauerleRiederMDP_AmericanPut_IsStochasticallyMonotone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:55.406011+00:00
-- url     : https://prove2.me/theorems/e148a2a4-fed9-4cdd-944b-ec27ebeb465f
-- title:
--   Stochastically monotone kernel on $\mathbb R$
-- statement:
--   A stochastic kernel $Q$ on $\mathbb R$ is **stochastically monotone** if $x\le x'$ implies $Q(\cdot\mid x)\le_{st}Q(\cdot\mid x')$, i.e.
--   $$Q\big((-\infty,t]\mid x\big)\ \ge\ Q\big((-\infty,t]\mid x'\big)\qquad\text{for all }t\in\mathbb R.$$
--
--   **Formalization Note** Definition B.3.13 phrases this as: $x\mapsto\int v(x')Q(dx'\mid x)$ is increasing for every increasing $v$ whenever the integral exists; the book notes right after the definition that this is equivalent to the stochastic-order form used here (Theorem B.3.3).
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, Definition B.3.13, p.363, PDF 369, with Definition B.3.2, p.359, PDF 365

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.AmericanPut

/-- A stochastic kernel `Q` on `ℝ` is **stochastically monotone** (Bäuerle & Rieder, Markov Decision Processes
with Applications to Finance (2011), Definition B.3.13, p.363, PDF 369): `x ≤ x'` implies
`Q(·|x) ≤_st Q(·|x')` in the usual stochastic order of Definition B.3.2 (p.359, PDF 365), i.e.
`Q((−∞, t] | x) ≥ Q((−∞, t] | x')` for all `t ∈ ℝ`.

**Formalization Note.** Definition B.3.13 states the property as "for all increasing `v : E → ℝ` the function
`x ↦ ∫ v(x') Q(dx'|x)` is increasing whenever the integral exists"; the book records right after it that this
holds if and only if `x ≤ x'` implies `Q(·|x) ≤_st Q(·|x')` (via Theorem B.3.3), and this distribution-function
form is the one used here, which avoids the "whenever the integral exists" clause. -/
def IsStochasticallyMonotone (Q : Kernel ℝ ℝ) : Prop :=
  ∀ x x' : ℝ, x ≤ x' → ∀ t : ℝ, Q x' (Set.Iic t) ≤ Q x (Set.Iic t)

end BauerleRiederMDP.AmericanPut


