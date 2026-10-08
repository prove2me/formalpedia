-- Prove2me | Definitions.Def_ModelRiskOT_PrimalOpt_PUSC
-- name    : ModelRiskOT_PrimalOpt_PUSC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:04:21.07073+00:00
-- url     : https://prove2.me/theorems/5e99812f-21ea-477e-80e8-8356057bd5c4
-- title:
--   Property 2 (P-USC) of Proposition 9 (p. 26)
-- statement:
--   Let $S$ be a Polish space, $\mu$ a probability measure on $S$, $c$ a cost, $f$ a function and $\delta>0$. The pair $(c,f)$ has **Property (P-USC)** if for every sequence $(\pi_n)_{n\ge1}\subseteq\Phi'_{\mu,\delta}$ that converges weakly to some $\pi^*\in\Phi_{\mu,\delta}$, $\pi_n\Rightarrow\pi^*$,
--   $$\limsup_{n\to\infty} I(\pi_n)\le I(\pi^*),$$
--   where $I(\pi)=\int f(y)\,d\pi(x,y)$.
--
--   The property is upper semicontinuity of the primal objective along weakly convergent sequences of monotone feasible plans; together with (P-Compactness) it yields existence of a primal optimizer.
--
--   **Formalization Note** Weak convergence is convergence in Mathlib's topology on `ProbabilityMeasure (S × S)` (convergence of integrals of bounded continuous functions). Sequences are indexed from $0$, which does not affect the condition. Values of $I$ are in `EReal`.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 26, Proposition 9, Property 2 (P-USC)

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_PrimalFeasibleMono

namespace ModelRiskOT.PrimalOpt

open MeasureTheory Filter Topology

/-- **Property 2 (P-USC)** of Proposition 9 (p. 26): for every sequence `(π_n)` in `Φ′_{μ,δ}` that
converges weakly (`π_n ⇒ π*`, convergence in the topology of `ProbabilityMeasure (S × S)`) to some
`π* ∈ Φ_{μ,δ}`, `limsup_n I(π_n) ≤ I(π*)`. -/
def PUSC {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (c : S → S → ℝ) (f : S → ℝ) (μ : Measure S) (δ : ℝ) : Prop :=
  ∀ (πs : ℕ → ProbabilityMeasure (S × S)) (πstar : ProbabilityMeasure (S × S)),
    (∀ n, ((πs n : ProbabilityMeasure (S × S)) : Measure (S × S)) ∈ primalFeasibleMono c f μ δ) →
    ((πstar : Measure (S × S)) ∈ ModelRiskOT.Duality.primalFeasible c μ δ) →
    Tendsto πs atTop (𝓝 πstar) →
    limsup (fun n => ModelRiskOT.Duality.primalObj f (πs n : Measure (S × S))) atTop ≤
      ModelRiskOT.Duality.primalObj f (πstar : Measure (S × S))

end ModelRiskOT.PrimalOpt


