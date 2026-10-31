-- Prove2me | Definitions.Def_CreditDefaultSwaps_Overhang_Controls
-- name    : CreditDefaultSwaps_Overhang_Controls
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:02:52.253477+00:00
-- url     : https://prove2.me/theorems/821ebf87-c560-4eaf-bf70-241cef2ea85d
-- title:
--   Filtered Brownian space and continuous-time investment, workout, and stopping controls
-- statement:
--   A risk-neutral probability space carries a real-indexed filtration and a standard Brownian motion relative to it. All null sets belong to the time-zero sigma algebra and the filtration is right-continuous at nonnegative times. The referenced Brownian definition supplies zero initial value, continuous paths, adaptedness, and independent Gaussian increments with variance equal to elapsed time.
--
--   A control consists of progressively measurable investment $a_t$, workout indicator $q_t$, and service flow $s_t$, together with a nonnegative stopping time $T$ that may be infinite. Investment lies in $\{0,i\}$ and is locally integrable. While alive and outside a workout, service equals the fixed contractual coupon. Negotiated service is constrained by Nash bargaining in the later admissibility definition. The controlled productivity is the concrete stochastic exponential
--   $$X_t=x\exp\left((\mu-\sigma^2/2)t+\int_0^t a_u\,du+\sigma Z_t\right).$$
--   Feedback policies must satisfy this same equation through their investment process; there is no independently supplied controlled transition law.
--
--   Differences from the source:
--   - encoding: usual filtered Brownian uncertainty and adapted measurable controls → a continuous Brownian version, progressive controls and explicit local integrability; reason: these give the standard nonanticipating stochastic-control interpretation and well-defined integrals.
--   - encoding: nonnegative continuous time and potentially infinite bankruptcy → real indexing with economically irrelevant negative-time extensions and a nonnegative $\operatorname{WithTop}(\mathbb R)$ stopping time; reason: infinity represents never defaulting without choosing a finite default value.
-- source:
--   Wong and Yu, Credit Default Swaps and Debt Overhang, Management Science (2021), DOI 10.1287/mnsc.2020.3953, supplied source.pdf, §2, equation (1) and footnote 8, printed pp. 6–7 (PDF pp. 7–8)

import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_CreditDefaultSwaps_Overhang_Primitives

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace CreditDefaultSwaps.Overhang

/-- The completed filtered risk-neutral Brownian probability space of footnote 8.
The filtration is indexed by reals; negative times have no economic role. -/
structure Noise (Ω : Type*) [m : MeasurableSpace Ω] where
  law : Measure Ω
  probability : IsProbabilityMeasure law
  filtration : Filtration ℝ m
  brownian : ℝ → Ω → ℝ
  standard : AtaBarjesteh23.Workload.IsDriftBM filtration law brownian 0 1
  complete : ∀ A : Set Ω, law A = 0 → MeasurableSet[filtration 0] A
  rightContinuous : ∀ t : ℝ, 0 ≤ t → filtration t = ⨅ s > t, filtration s

instance {Ω : Type*} [MeasurableSpace Ω] (N : Noise Ω) : IsProbabilityMeasure N.law :=
  N.probability

/-- Open-loop controls include the negotiated transfer, whose admissibility is
determined by the actual continuation values in `Admissible`. -/
structure Control (Ω : Type*) where
  investment : ℝ → Ω → ℝ
  workout : ℝ → Ω → Bool
  service : ℝ → Ω → ℝ
  bankruptcy : Ω → WithTop ℝ

/-- Stochastic exponential for the controlled productivity, before liquidation.
It is also defined after stopping only to evaluate the first hitting rule. -/
def productivity {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (x : ℝ) (c : Control Ω) (t : ℝ) (ω : Ω) : ℝ :=
  x * Real.exp ((p.mu - p.sigma ^ 2 / 2) * t +
    (∫ s in Icc 0 t, c.investment s ω) + p.sigma * N.brownian t ω)

/-- Measurability and timing constraints; no sign or ordering conclusion is assumed. -/
def ControlRegular {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (c : Control Ω) : Prop :=
  IsProgressive N.filtration c.investment ∧
  IsProgressive N.filtration c.workout ∧
  IsProgressive N.filtration c.service ∧
  IsStoppingTime N.filtration c.bankruptcy ∧
  (∀ ω, 0 ≤ c.bankruptcy ω) ∧
  (∀ ω t, 0 ≤ t → c.investment t ω = 0 ∨ c.investment t ω = p.improvement) ∧
  (∀ ω t, 0 ≤ t → IntegrableOn (fun s => c.investment s ω) (Icc 0 t)) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂N.law,
    (t : WithTop ℝ) < c.bankruptcy ω →
      c.workout t ω = false → c.service t ω = p.coupon)

end CreditDefaultSwaps.Overhang


