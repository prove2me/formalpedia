-- Prove2me | Definitions.Def_BramsonQueueing_FIFOKelly_Primitives
-- name    : BramsonQueueing_FIFOKelly_Primitives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:05:38.425995+00:00
-- url     : https://prove2.me/theorems/b6b157da-9009-4a24-89b3-790de0f04d7d
-- title:
--   Independent renewal, service and routing primitives
-- statement:
--   Three families of independent random draws supply interarrival times, service times and routing destinations. Within each class and family the draws are identically distributed. Active interarrival draws and service draws are positive and integrable, with means $1/\alpha_k$ and $m_k$; routing chooses class $l$ with probability $P_{kl}$ or exits. Routing destinations are encoded by zero for exit and $l+1$ for class $l$. Indices start at zero for the first future draw; initial residuals are in the state. Unused external streams at zero external rates can be deterministic dummy streams. The common good event requires valid draws and the three strong laws (4.70), with routing counts divided by the sample size. This event contains no stability condition.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, printed 83, 101, 111; PDF 91, 109, 119

import Definitions.Def_BramsonQueueing_FIFOKelly_Parameters

namespace BramsonQueueing.FIFOKelly

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal

/-- The three independent families of iid draws. Routing is coded by 0
(exit) or k+1 (class k). Index 0 is the first future draw, not the residual. -/
structure Primitives (K : ℕ) (Ω : Type) where
  draw : Fin 3 → Fin K → ℕ → Ω → ℝ

def PrimitiveLaws {K J : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (p : Parameters K J) (U : Primitives K Ω) (μ : Measure Ω) : Prop :=
  IsProbabilityMeasure μ ∧
  (∀ a k n, Measurable (U.draw a k n)) ∧
  iIndepFun (fun i : Fin 3 × Fin K × ℕ => U.draw i.1 i.2.1 i.2.2) μ ∧
  (∀ a k n, IdentDistrib (U.draw a k n) (U.draw a k 0) μ μ) ∧
  (∀ k, 0 < p.data.lam k →
    (∀ᵐ ω ∂μ, 0 < U.draw 0 k 0 ω) ∧ Integrable (U.draw 0 k 0) μ ∧
    (∫ ω, U.draw 0 k 0 ω ∂μ) = (p.data.lam k)⁻¹) ∧
  (∀ k, (∀ᵐ ω ∂μ, 0 < U.draw 1 k 0 ω) ∧ Integrable (U.draw 1 k 0) μ ∧
    (∫ ω, U.draw 1 k 0 ω ∂μ) = p.data.m k) ∧
  (∀ k, ∀ᵐ ω ∂μ, U.draw 2 k 0 ω = 0 ∨
    ∃ l : Fin K, U.draw 2 k 0 ω = (l.val + 1 : ℕ)) ∧
  (∀ k l, μ {ω | U.draw 2 k 0 ω = (l.val + 1 : ℕ)} =
    ENNReal.ofReal (p.data.P k l))

noncomputable def routingCount {K : ℕ} {Ω : Type} (U : Primitives K Ω)
    (ω : Ω) (k l : Fin K) (n : ℕ) : ℕ :=
  (Finset.range n).filter (fun i => U.draw 2 k i ω = (l.val + 1 : ℕ)) |>.card

/-- The common primitive strong-law event, choosing the probability-one
version that also excludes nonpositive or invalid primitive draws. -/
def GoodPrimitives {K J : ℕ} {Ω : Type} (p : Parameters K J)
    (U : Primitives K Ω) (ω : Ω) : Prop :=
  (∀ k n, 0 < p.data.lam k → 0 < U.draw 0 k n ω) ∧
  (∀ k n, 0 < U.draw 1 k n ω) ∧
  (∀ k n, U.draw 2 k n ω = 0 ∨ ∃ l : Fin K,
    U.draw 2 k n ω = (l.val + 1 : ℕ)) ∧
  (∀ k, 0 < p.data.lam k → Tendsto
    (fun n : ℕ => (∑ i ∈ Finset.range n, U.draw 0 k i ω) / n)
    atTop (nhds (p.data.lam k)⁻¹)) ∧
  (∀ k, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, U.draw 1 k i ω) / n)
    atTop (nhds (p.data.m k))) ∧
  (∀ k l, Tendsto (fun n : ℕ => (routingCount U ω k l n : ℝ) / n)
    atTop (nhds (p.data.P k l)))

end BramsonQueueing.FIFOKelly


