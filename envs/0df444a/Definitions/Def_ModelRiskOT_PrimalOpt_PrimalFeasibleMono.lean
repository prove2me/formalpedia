-- Prove2me | Definitions.Def_ModelRiskOT_PrimalOpt_PrimalFeasibleMono
-- name    : ModelRiskOT_PrimalOpt_PrimalFeasibleMono
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:50:40.57587+00:00
-- url     : https://prove2.me/theorems/0bec20be-16ba-401e-9b98-6a7a5c7c24dd
-- title:
--   Φ′_{µ,δ}: feasible plans concentrated on {f(x) ≤ f(y)} (§5, p. 26)
-- statement:
--   In the setting of the primal problem of Blanchet and Murthy (a Polish space $S$, a baseline probability measure $\mu$, a cost $c$, a function $f$ and a budget $\delta>0$), define the set of **monotone feasible plans**
--   $$\Phi'_{\mu,\delta}=\bigl\{\pi\in\Phi_{\mu,\delta}:\ \pi\bigl(\{(x,y)\in S\times S: f(x)\le f(y)\}\bigr)=1\bigr\}.$$
--   A plan in $\Phi'_{\mu,\delta}$ only moves mass from a point $x$ to points $y$ where $f$ is at least as large as at $x$.
--
--   Restricting the primal problem to $\Phi'_{\mu,\delta}$ does not change its value, and plans in $\Phi'_{\mu,\delta}$ have $\int f^-(y)\,d\pi\le\int f^-\,d\mu$; this is the set over which the existence proof of §5 works.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 26, §5, Additional notation

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_Basic

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-- **The set** `Φ′_{μ,δ}` (§5, Additional notation, p. 26): the plans `π ∈ Φ_{μ,δ}` concentrated
on `{(x, y) ∈ S × S : f(x) ≤ f(y)}`, i.e. `π({(x, y) : f(x) ≤ f(y)}) = 1`. -/
def primalFeasibleMono {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (f : S → ℝ)
    (μ : Measure S) (δ : ℝ) : Set (Measure (S × S)) :=
  {π | π ∈ ModelRiskOT.Duality.primalFeasible c μ δ ∧ π {p : S × S | f p.1 ≤ f p.2} = 1}

end ModelRiskOT.PrimalOpt


