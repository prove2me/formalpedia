-- Prove2me | Definitions.Def_BramsonQueueing_Fluid_Primitives
-- name    : BramsonQueueing_Fluid_Primitives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:25.082442+00:00
-- url     : https://prove2.me/theorems/1c132cd4-c74b-40ad-8b32-a5e6f87f0212
-- title:
--   Independent renewal, service, and routing primitives and their common strong-law event
-- statement:
--   On one probability space, each external class has a positive iid interarrival sequence with mean $1/\alpha_k$; each class has a positive iid service sequence with mean $m_k$. Each class also has iid routing decisions, taking values in the classes or departure from the network, with class-transition probabilities $P_{k\ell}$. All these sequences are independent of one another. Positivity is represented pointwise for the network's chosen primitive sample space. The routing count $\Phi_{k\ell}(n)$ counts destinations $\ell$ among the first $n$ decisions at class $k$.
--   The common event $G$ is defined by the simultaneous primitive strong laws:
--   $$\frac1n\sum_{i<n}\xi_k(i)\to\frac1{\alpha_k},\quad \frac1n\sum_{i<n}\gamma_k(i)\to m_k,\quad \frac{\Phi_{k\ell}(n)}n\to P_{k\ell}.$$
--   It is not defined in terms of fluid limits or stability. These iid assumptions imply probability one for $G$; that conclusion is not used as an assumed target fact.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Sections 4.1 and 4.3, printed 83, 101–102, 111 / PDF 91, 109–110, 119; equation (4.70).

import Definitions.Def_BramsonQueueing_Fluid_NetworkData
import Definitions.Def_BramsonQueueing_Fluid_Renewal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

instance routeMeasurableSpace (K : ℕ) : MeasurableSpace (Option (Fin K)) := ⊤

abbrev PrimitiveIndex {K J : ℕ} (d : NetworkData K J) :=
  {k : Fin K // k ∈ d.external} ⊕ (Fin K ⊕ Fin K)

/-- Real coding used solely to express independence of all primitive sequences. -/
noncomputable def primitiveCode {K J : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : NetworkData K J}
    (xi : {k : Fin K // k ∈ d.external} → PositiveIID Ω μ)
    (gamma : Fin K → PositiveIID Ω μ) (route : Fin K → ℕ → Ω → Option (Fin K))
    (i : PrimitiveIndex d) (ω : Ω) (n : ℕ) : ℝ :=
  match i with
  | .inl k => (xi k).beta n ω
  | .inr (.inl k) => (gamma k).beta n ω
  | .inr (.inr k) => match route k n ω with
    | none => 0
    | some l => l.val + 1

/-- Independent iid renewal/service/routing sequences with the source means.
Routing selects one new class or departure, not a general branching network. -/
structure PrimitiveTriple {K J : ℕ} (d : NetworkData K J) (Ω : Type*)
    [MeasurableSpace Ω] (μ : Measure Ω) where
  probability : IsProbabilityMeasure μ
  xi : {k : Fin K // k ∈ d.external} → PositiveIID Ω μ
  gamma : Fin K → PositiveIID Ω μ
  xi_positive : ∀ k n ω, 0 < (xi k).beta n ω
  gamma_positive : ∀ k n ω, 0 < (gamma k).beta n ω
  xi_mean : ∀ k, renewalMean (xi k) = 1 / d.alpha k
  gamma_mean : ∀ k, renewalMean (gamma k) = d.meanService k
  route : Fin K → ℕ → Ω → Option (Fin K)
  route_measurable : ∀ k n, Measurable (route k n)
  route_independent : ∀ k, iIndepFun (route k) μ
  route_identically_distributed : ∀ k n, IdentDistrib (route k n) (route k 0) μ μ
  route_law : ∀ k l, μ {ω | route k 0 ω = some l} = ENNReal.ofReal (d.routing k l)
  sequences_independent : iIndepFun (primitiveCode xi gamma route) μ

noncomputable def routingCount {K J : ℕ} {d : NetworkData K J} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (p : PrimitiveTriple d Ω μ)
    (k l : Fin K) (n : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).filter (fun i => p.route k i ω = some l)).card

/-- The common strong-law event (4.70), defined from primitives, not limits. -/
def PrimitiveGood {K J : ℕ} {d : NetworkData K J} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (p : PrimitiveTriple d Ω μ) (ω : Ω) : Prop :=
  (∀ k, RenewalGood (p.xi k) ω) ∧ (∀ k, RenewalGood (p.gamma k) ω) ∧
    ∀ k l, Tendsto (fun n : ℕ => (routingCount p k l n ω : ℝ) / n)
      atTop (𝓝 (d.routing k l))

end BramsonQueueing.Fluid


