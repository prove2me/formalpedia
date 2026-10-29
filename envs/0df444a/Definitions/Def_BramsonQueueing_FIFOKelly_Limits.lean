-- Prove2me | Definitions.Def_BramsonQueueing_FIFOKelly_Limits
-- name    : BramsonQueueing_FIFOKelly_Limits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:08:46.037041+00:00
-- url     : https://prove2.me/theorems/e3a86c79-93e4-4367-9b65-80a0fc483c9f
-- title:
--   Six-component fluid limits, admissible scaling and association
-- statement:
--   An admissible sequence has scales $a_n>0$ tending to infinity, bounded $|z_n|/a_n$, and $|u_n|/a_n,|v_n|/a_n\to0$. A fluid limit is a uniform-on-compact-time-interval limit of all six scaled paths along such a sequence at one sample point of the primitive strong-law event. Uniform convergence is expressed by the epsilon definition simultaneously in all class and station coordinates. A model is associated if its parameters agree with the network's, every admissible sequence has a convergent subsequence whose limit solves the model, and every fluid limit solves it. In particular, association includes existence and cannot hold by declaring the limit family empty. A bounded limsup in (4.71) is equivalent to a bound on the entire sequence, since its finitely many early ratios are finite.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, printed 111–113; PDF 119–121

import Definitions.Def_BramsonQueueing_FIFOKelly_Network

namespace BramsonQueueing.FIFOKelly

open Filter Set
open scoped BigOperators

def AdmissibleScaling {K J : ℕ} {S Ω : Type} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] (N : HLNetwork K J S Ω)
    (a : ℕ → ℝ) (x : ℕ → S) : Prop :=
  (∀ n, 0 < a n) ∧ Tendsto a atTop atTop ∧
  (∃ B : ℝ, ∀ n, ((N.coordinates (x n)).val.jobs.length : ℝ) / a n ≤ B) ∧
  Tendsto (fun n => (∑ k, |(N.coordinates (x n)).val.u k|) / a n) atTop (nhds 0) ∧
  Tendsto (fun n => (∑ k, |(N.coordinates (x n)).val.v k|) / a n) atTop (nhds 0)

/-- The epsilon definition of uniform convergence on every compact time
interval, simultaneously in all six finite-dimensional components. -/
def ScaledUOC {K J : ℕ} (a : ℕ → ℝ) (X : ℕ → SixPaths K J)
    (L : SixPaths K J) : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ n, n₀ ≤ n → ∀ t ∈ Icc 0 R,
      (∀ k, |(X n).A (a n*t) k / a n - L.A t k| < ε ∧
        |(X n).D (a n*t) k / a n - L.D t k| < ε ∧
        |(X n).T (a n*t) k / a n - L.T t k| < ε ∧
        |(X n).Z (a n*t) k / a n - L.Z t k| < ε) ∧
      (∀ j, |(X n).W (a n*t) j / a n - L.W t j| < ε ∧
        |(X n).Y (a n*t) j / a n - L.Y t j| < ε)

def IsFluidLimit {K J : ℕ} {S Ω : Type} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] (N : HLNetwork K J S Ω)
    (L : SixPaths K J) : Prop :=
  ∃ ω, GoodPrimitives N.parameters N.primitives ω ∧
    ∃ a x, AdmissibleScaling N a x ∧ ScaledUOC a (fun n => networkPaths N (x n) ω) L

/-- Association includes subsequential existence on every admissible sequence
and membership of every fluid limit; it cannot hold vacuously by deleting limits. -/
def Associated {K J : ℕ} {S Ω : Type} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] (N : HLNetwork K J S Ω)
    (M : FluidModel K J) : Prop :=
  M.parameters = N.parameters ∧
  (∀ ω, GoodPrimitives N.parameters N.primitives ω → ∀ a x,
    AdmissibleScaling N a x → ∃ i : ℕ → ℕ, StrictMono i ∧
      ∃ L, ScaledUOC (a ∘ i) (fun n => networkPaths N (x (i n)) ω) L ∧ M.Solution L) ∧
  (∀ L, IsFluidLimit N L → M.Solution L)

end BramsonQueueing.FIFOKelly


