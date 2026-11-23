-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_MarkedRenewal
-- name    : CarlssonPartition_Approx_Supplement_MarkedRenewal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:19:13.951801+00:00
-- url     : https://prove2.me/theorems/05b63bc7-c506-4522-b046-e12087a164ae
-- title:
--   §3 — independently marked stationary renewal input and typical-order expectations
-- statement:
--   A stationary simple point process has measurable arrival times $T_n$, indexed by $T_0\le0<T_1$, a stationary probability $P$, and its arrival-centered Palm probability $P^0$. Its intensity is $\lambda>0$. Marks $Z_n$ shift with the arrival sequence. The renewal extension imposes the joint law
--    $$
--    \mathcal L_{P^0}\big((T_{n+1}-T_n,Z_n)_{n\in\mathbb Z}\big)
--      = (G\otimes H)^{\otimes\mathbb Z},\qquad
--    G((0,\infty))=1,\quad \int a\,G(da)=1/\lambda.
--    $$
--    Thus the interarrival distribution is general, with finite positive mean, rather than exponential. Marks and gaps are independent. The published Palm interface supplies stationarity and the counting definition of Palm probability; the new extension supplies renewal independence.
--
--    A nonnegative typical-order cost $C$ has expectation $\int C\,dP^0\in[0,\infty]$. Conditional expectations on mark events use restricted integrals divided by the event probability and have their intended interpretation only for measurable positive-probability events. These objects provide the arrival and cost layer for the stochastic routing model. They do not define a dispatching policy.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §3, pp. 6–7 (PDF 7–8); Palm interpretation of a randomly chosen order

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- A stationary independently marked renewal input, extending the published stationary
point-process/Palm interface. Renewal independence is an arrival-centered (Palm) property;
it is deliberately not imposed on the length-biased gap containing a stationary time. -/
structure MarkedRenewal (Ω M : Type*) [MeasurableSpace Ω] [MeasurableSpace M] where
  palm : PalmQueueing.Palm.PalmSetting Ω
  mark : ℤ → Ω → M
  marks_shift : PalmQueueing.Palm.IsMarkSequence palm.θ palm.N mark
  gapLaw : Measure ℝ
  markLaw : Measure M
  gap_probability : IsProbabilityMeasure gapLaw
  mark_probability : IsProbabilityMeasure markLaw
  gap_positive : gapLaw (Set.Ioi 0) = 1
  gap_integrable : Integrable (fun a : ℝ => a) gapLaw
  gap_mean : (∫ a : ℝ, a ∂gapLaw) = palm.lam⁻¹
  at_arrival : ∀ᵐ ω ∂palm.P0, palm.N.T 0 ω = 0
  /-- Measurability is separate from the law identity so `Measure.map` cannot default to zero. -/
  measurable_sequence : Measurable
    (fun ω => fun n : ℤ => (palm.N.T (n + 1) ω - palm.N.T n ω, mark n ω))
  /-- All gaps and marks, jointly, are iid with independent gap and mark coordinates. -/
  renewal_law : letI := gap_probability
    letI := mark_probability
    Measure.map (fun ω => fun n : ℤ =>
      (palm.N.T (n + 1) ω - palm.N.T n ω, mark n ω)) palm.P0 =
      Measure.infinitePi (fun _ : ℤ => gapLaw.prod markLaw)

/-- A typical-order nonnegative cost is integrated under Palm probability. Infinite
waiting time remains `⊤`; no Bochner default or `toReal` conversion is used. -/
def MarkedRenewal.expected {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (A : MarkedRenewal Ω M) (cost : Ω → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, cost ω ∂A.palm.P0

/-- Conditional typical-order expectation on a measurable mark event of positive mass.
The definition itself is total; source statements must require positive event probability. -/
def MarkedRenewal.expectedOn {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (A : MarkedRenewal Ω M) (cost : Ω → ℝ≥0∞) (B : Set M) : ℝ≥0∞ :=
  (∫⁻ ω in (A.mark 0 ⁻¹' B), cost ω ∂A.palm.P0) /
    A.palm.P0 (A.mark 0 ⁻¹' B)

end CarlssonPartition.Approx.Supplement


