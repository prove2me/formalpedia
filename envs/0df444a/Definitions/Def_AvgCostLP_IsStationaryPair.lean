-- Prove2me | Definitions.Def_AvgCostLP_IsStationaryPair
-- name    : AvgCostLP_IsStationaryPair
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:30:28.528999+00:00
-- url     : https://prove2.me/theorems/c3242721-c170-49f1-b753-e0dad9c70dc2
-- title:
--   Definition 2.2 — stationary pairs and stationary minimum pairs
-- statement:
--   For a stationary policy $\mu\in\Pi_s$ and $p\in\mathcal P(\mathbb X)$, the pair $(\mu,p)$ is a **stationary pair** if $p$ is an invariant probability measure of the Markov chain on $\mathbb X$ induced by $\mu$, that is,
--   $$p(B)=\int_{\mathbb X}\int_{\mathbb A}q(B\mid x,a)\,\mu(da\mid x)\,p(dx)\qquad\forall B\in\mathcal B(\mathbb X). \tag{3.4}$$
--   The set of stationary pairs is $\Delta_s$. A stationary pair $(\mu^*,p^*)$ is a **stationary minimum pair** if it is also a minimum pair, $J(\mu^*,p^*)=\rho^*$.
--
--   Stationary pairs are the feasible points of the primal linear program, up to the correspondence $\gamma(d(x,a))=\mu(da\mid x)p(dx)$.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Definition 2.2, p.6, and (3.4), p.9

import Mathlib
import Definitions.Def_AvgCostLP_avgCost

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AvgCostLP

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- Yu, arXiv:1905.12095v3, Definition 2.2(a), p.6, and (3.4), p.9: `(μ, p)` is a *stationary
pair* when `μ ∈ Π_s` is a stationary policy and the probability measure `p ∈ P(X)` is invariant
for the Markov chain on `X` induced by `μ`, i.e.
`p(B) = ∫_X ∫_A q(B | x, a) μ(da | x) p(dx)` for every Borel set `B ⊂ X`.
The set of all stationary pairs is `Δ_s`. -/
def IsStationaryPair (M : Model X A) (μ : StationaryPolicy M) (p : ProbabilityMeasure X) :
    Prop :=
  ∀ B : Set X, MeasurableSet B →
    (p : Measure X) B = ∫⁻ x, ∫⁻ a, M.q (x, a) B ∂(μ.kernel x) ∂(p : Measure X)

/-- Yu, arXiv:1905.12095v3, Definition 2.2(b), p.6 (with Definition 2.1): `(μ*, p*)` is a
*stationary minimum pair* when it is a stationary pair and a minimum pair, i.e.
`J(μ*, p*) = ρ*`, the average cost of the stationary policy `μ*` (as a policy in `Π`) from the
initial distribution `p*` equals the minimum average cost over all policies and initial
distributions. -/
def IsStationaryMinPair (M : Model X A) (μ : StationaryPolicy M) (p : ProbabilityMeasure X) :
    Prop :=
  IsStationaryPair M μ p ∧ avgCost M μ.toPolicy p = minAvgCost M

end AvgCostLP


