-- Prove2me | Definitions.Def_KellyStochasticNetworks_MaxWeight_Network
-- name    : KellyStochasticNetworks_MaxWeight_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:13.943127+00:00
-- url     : https://prove2.me/theorems/029bca17-a0a8-4dd6-bf62-b3cdb8140707
-- title:
--   Finite schedules, Poisson queue transitions, and the MaxWeight rule
-- statement:
--   Let $R$ be a finite set of queues and $S\subseteq\mathbb N^R$ a finite nonempty set of feasible service schedules, closed under coordinatewise decrease. The admissible region is
--   $$\Lambda=\{v\ge0:\exists c_\sigma\ge0,\ \sum_{\sigma\in S}c_\sigma=1,\ v\le\sum_{\sigma\in S}c_\sigma\sigma\}.$$
--   For $\alpha>0$, the MaxWeight rule draws a schedule from a fixed state-dependent distribution supported on the maximizers of $\sum_r\sigma_rq_r^\alpha$. Independently, a fresh arrival vector has independent Poisson coordinates with rates $\lambda_r$. The transition is
--   $$q'_r=(q_r-\sigma_r)^++A_r.$$
--   Thus service never removes packets that are absent. The resulting probability kernel specifies the queue chain. The queue norm is Euclidean, and the main drift is $D(q)=\sum_rq_r^\alpha\mathbb E[q'_r-q_r\mid q]$.
--
--   For a coordinate with maximum feasible service $B$, define $Y=\max(A,B)$, where $A$ has the coordinate's Poisson law. The tail term used in Exercise D.1 is
--   $$T(K)=\mathbb E\left[\left(\left|(1+Y/K)^{\alpha+1}\right|+1\right)\mathbf1_{\{Y>\delta K\}}\right].$$
--   These definitions provide the scheduling model and the scalar increment envelope needed for the mission.
--
--   **Formalization Note** Queue lengths and schedules are natural numbers; natural subtraction implements the positive part. Arrival rates are nonnegative reals. The state space is countable and generally infinite. No uniform distribution among ties is stipulated in the source, so any fixed distribution supported on maximizers is allowed. The tail term is used for $K>0$.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 177–180, 213–215 (PDF pp. 185–188, 221–223), §7.8 and Example D.4 / Exercise D.1; DOI 10.1017/cbo9781139565363

import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Classical

open scoped NNReal

/- Imported dependency source, reproduced verbatim for standalone inspection.
/-- A discrete-time transition law on a countable state space. -/
def Chain (S : Type*) := S → PMF S

/-- Probability of reaching `j` in exactly `n` transitions from `i`. -/
noncomputable def transitionPower {S : Type*} (P : Chain S) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑' k, P i k * transitionPower P n k j

/-- Every state communicates with every other state. -/
def Irreducible {S : Type*} (P : Chain S) : Prop :=
  ∀ i j, ∃ n : ℕ, 0 < transitionPower P n i j

/-- Probability that times 1 through n all avoid K, starting from i at time 0. -/
noncomputable def avoidProbability {S : Type*} (P : Chain S) (K : Set S) :
    ℕ → S → ℝ≥0∞
  | 0, _ => 1
  | n + 1, i => ∑' j, if j ∈ K then 0 else P i j * avoidProbability P K n j

/-- Extended expected strictly positive hitting time, using the tail-sum formula.
Non-return has infinite cost, even if it occurs with positive probability less than one. -/
noncomputable def meanReturn {S : Type*} (P : Chain S) (K : Set S) (i : S) : ℝ≥0∞ :=
  ∑' n : ℕ, avoidProbability P K n i

/-- Every state has finite expected strictly positive return time. -/
def PositiveRecurrent {S : Type*} (P : Chain S) : Prop :=
  ∀ i, meanReturn P {i} i < ∞

/-- Real one-step drift; use only with the separately asserted absolute summability. -/
noncomputable def drift {S : Type*} (P : Chain S) (L : S → ℝ) (i : S) : ℝ :=
  ∑' j, (P i j).toReal * (L j - L i)

/-- Absolute integrability of a one-step increment on the countable state space. -/
def DriftIntegrable {S : Type*} (P : Chain S) (L : S → ℝ) (i : S) : Prop :=
  Summable (fun j => (P i j).toReal * |L j - L i|)
-/

namespace KellyStochasticNetworks.MaxWeight

/-- The finite, nonempty, downward-closed family of integer service schedules. -/
structure Network (R : Type*) [Fintype R] where
  schedules : Finset (R → ℕ)
  nonempty : schedules.Nonempty
  downward : ∀ σ ∈ schedules, ∀ π : R → ℕ, (∀ r, π r ≤ σ r) → π ∈ schedules

/-- Nonnegative arrival vectors dominated by a convex combination of schedules. -/
def capacityRegion {R : Type*} [Fintype R] (N : Network R) : Set (R → ℝ) :=
  {v | (∀ r, 0 ≤ v r) ∧ ∃ c : (R → ℕ) → ℝ,
    (∀ σ ∈ N.schedules, 0 ≤ c σ) ∧
    (∑ σ ∈ N.schedules, c σ) = 1 ∧
    ∀ r, v r ≤ ∑ σ ∈ N.schedules, c σ * (σ r : ℝ)}

noncomputable def scheduleWeight {R : Type*} [Fintype R]
    (α : ℝ) (q σ : R → ℕ) : ℝ :=
  ∑ r, (σ r : ℝ) * (q r : ℝ) ^ α

/-- A fixed state-dependent random tie rule, supported on maximizing schedules.
No distribution among ties is specified by the source. -/
def IsMaxWeight {R : Type*} [Fintype R] (N : Network R) (α : ℝ)
    (tie : (R → ℕ) → PMF (R → ℕ)) : Prop :=
  ∀ q σ, tie q σ ≠ 0 → σ ∈ N.schedules ∧
    ∀ π ∈ N.schedules, scheduleWeight α q π ≤ scheduleWeight α q σ

/-- Independent arrivals in a unit slot, with the stated Poisson rates. -/
noncomputable def arrivalLaw {R : Type*} [Fintype R] (lam : R → ℝ≥0) : PMF (R → ℕ) :=
  (Measure.pi (fun r => poissonMeasure (lam r))).toPMF

/-- Departures precede the new slot's arrivals. Natural subtraction suppresses unused service. -/
def nextQueue {R : Type*} (q σ a : R → ℕ) : R → ℕ :=
  fun r => q r - σ r + a r

/-- Actual homogeneous queue transition law: random schedule independent of fresh arrivals. -/
noncomputable def queueChain {R : Type*} [Fintype R] (lam : R → ℝ≥0)
    (tie : (R → ℕ) → PMF (R → ℕ)) : Chain (R → ℕ) :=
  fun q => (tie q).bind (fun σ => (arrivalLaw lam).map (nextQueue q σ))

/-- Euclidean queue size, made explicit rather than using the function-space sup norm. -/
noncomputable def queueNorm {R : Type*} [Fintype R] (q : R → ℕ) : ℝ :=
  Real.sqrt (∑ r, (q r : ℝ) ^ (2 : ℕ))

/-- The main drift in (7.14), using actual capped departures through the queue kernel. -/
noncomputable def weightedDrift {R : Type*} [Fintype R] (α : ℝ)
    (P : Chain (R → ℕ)) (q : R → ℕ) : ℝ :=
  ∑ r, (q r : ℝ) ^ α * drift P (fun x => (x r : ℝ)) q

/-- Coordinatewise finite service envelope used in Exercise D.1. -/
noncomputable def serviceBound {R : Type*} [Fintype R] (N : Network R) (r : R) : ℕ :=
  N.schedules.sup (fun σ => σ r)

/-- The envelope Y is the maximum of one Poisson arrival count and the service bound. -/
def incrementEnvelope (B a : ℕ) : ℝ := (max a B : ℕ)

/-- The second term of Exercise D.1(2), written as a tail integral.
This avoids a conditional expectation on a zero-probability tail event. -/
noncomputable def poissonTailRemainder (lam : ℝ≥0) (B : ℕ) (α δ K : ℝ) : ℝ :=
  ∫ a : ℕ, if δ * K < incrementEnvelope B a then
      |(1 + incrementEnvelope B a / K) ^ (α + 1)| + 1 else 0
    ∂poissonMeasure lam

end KellyStochasticNetworks.MaxWeight


