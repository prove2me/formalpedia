-- Prove2me | Definitions.Def_BramsonQueueing_Instability_LuKumarPrimitives
-- name    : BramsonQueueing_Instability_LuKumarPrimitives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:50.270581+00:00
-- url     : https://prove2.me/theorems/420c63ae-c346-448b-b86a-b21cdf3290f4
-- title:
--   Poisson arrivals and independent exponential service requirements
-- statement:
--   On a probability space, let $A(t)$ count external arrivals during $(0,t]$. It is a rate-one Poisson process, jointly measurable and with right-continuous sample paths. Let $V_{k,n}$ be the service requirement of the $n$th visit to class $k$. These variables are mutually independent and independent of the entire arrival process, with
--   $$\mathbb P(V_{k,n}>x)=\exp(-x/m_k),\qquad x\ge0.$$
--   Requirements are measurable and almost surely strictly positive. The sum of the first $n$ requirements at a class is the actual cumulative service demand, not its mean. These primitives are independent of the claimed instability.
--
--   **Formalization Note** Service visits are indexed from zero. For initially present jobs, the first requirement includes any residual service; exponential memorylessness supports the queue-length state used here. The existing Poisson predicate is imported from the published baseline-assumptions definition. Only that predicate is imposed on the arrival process; no other restrictions from that baseline are imposed on this network.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), DOI 10.1007/978-3-540-68896-9, Section 3.1, printed 56–58 / PDF 64–66

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BramsonQueueing_Instability_LuKumarParameters

namespace BramsonQueueing.Instability

open MeasureTheory ProbabilityTheory

/-- Rate-one Poisson arrivals and mutually independent exponential service requirements.
Service index zero is the first requirement (a residual requirement for an initially
present job); memorylessness permits the queue-length initial state used in Chapter 3. -/
structure LuKumarPrimitives (Ω : Type*) [MeasureSpace Ω] (d : LuKumarParameters) where
  A : ℝ → Ω → ℕ
  V : Fin 4 → ℕ → Ω → ℝ
  poisson : ProcessingNetworks.Stability.IsPoissonProcess A 1
  arrival_measurable : Measurable (fun x : ℝ × Ω => A x.1 x.2)
  arrival_right : ∀ᵐ ω, ∀ t : ℝ, ContinuousWithinAt (fun s => A s ω) (Set.Ici t) t
  service_measurable : ∀ k n, Measurable (V k n)
  service_positive : ∀ᵐ ω, ∀ k n, 0 < V k n ω
  exponential : ∀ k n x, 0 ≤ x →
    ℙ {ω | x < V k n ω} = ENNReal.ofReal (Real.exp (-x / d.m k))
  services_independent : iIndepFun (fun kn : Fin 4 × ℕ => V kn.1 kn.2) ℙ
  arrivals_services_independent :
    IndepFun (fun ω => fun t => A t ω) (fun ω => fun k n => V k n ω) ℙ

/-- Structural projection of the imported Poisson predicate's zero initial count. -/
theorem LuKumarPrimitives.arrivals_zero {Ω : Type*} [MeasureSpace Ω]
    {d : LuKumarParameters} (p : LuKumarPrimitives Ω d) (ω : Ω) :
    p.A 0 ω = 0 := p.poisson.1 ω

/-- Actual work required by the first n visits to a class, not n times the mean. -/
noncomputable def serviceSum {Ω : Type*} [MeasureSpace Ω] {d : LuKumarParameters}
    (p : LuKumarPrimitives Ω d) (k : Fin 4) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, p.V k i ω

end BramsonQueueing.Instability


