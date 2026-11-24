-- Prove2me | Definitions.Def_WaitTimePricing_Existence_Supplement_Arrivals
-- name    : WaitTimePricing_Existence_Supplement_Arrivals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:36:40.505657+00:00
-- url     : https://prove2.me/theorems/3ed11324-6dac-4b9f-bcfe-a87fc33bf652
-- title:
--   Poisson arrivals and their natural history
-- statement:
--   Let $A_n$ be the successive strictly positive arrival epochs of a simple, nonexplosive Poisson process of rate $\lambda$ on a probability space. Define
--   $$N_s=\#\{n:A_n\le s\},\qquad \mathcal F_s=\sigma(N_u:0\le u\le s).$$
--   The Poisson law and independent increments use the published general Poisson-process definition. This bundle supplies arrival epochs, their counting process, and their natural filtration, independently of pricing.
--
--   **Formalization Note** Epochs are indexed from zero, so $A_0$ is the first arrival. Regular versions are chosen on null paths. Counts include the endpoint; controls and workload are evaluated strictly before an arrival. This is the usual càdlàg convention equivalent to the paper's prearrival notation.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), pp. 6, 9–10, §3 and (9)

import Mathlib
import Mathlib.Probability.Process.Predictable
import Definitions.Def_levy_foundations_isPoissonProcess

set_option autoImplicit false
open scoped NNReal

namespace WaitTimePricing.Existence.Supplement
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), pp. 6, 9–10, Poisson arrivals.
Formalization Note: arrival 0 is the first positive arrival. Counts include the right endpoint;
workload and controls below use the strictly prearrival history. -/
def arrivalCount {Ω : Type*} (τ : ℕ → Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) : ℕ :=
  {n : ℕ | τ n ω ≤ s}.ncard

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 9, §3.2 (Poisson arrivals and their natural history).

A general simple, nonexplosive Poisson arrival stream; the probability law and independent
increments are the published `LevyFoundations.IsPoissonProcess`, not a queue-specific replacement.
Lin, Shang, Sun, SSRN 3709573 (version of October 12, 2020), pp. 6, 9, §3.
Formalization Note: regular paths are chosen everywhere, a version convention on null paths.
Count measurability records the defining random variables, not any workload or reward property. -/
structure Arrivals (Ω : Type*) [MeasurableSpace Ω] where
  law : Measure Ω
  probability : IsProbabilityMeasure law
  rate : ℝ≥0
  epoch : ℕ → Ω → ℝ≥0
  epoch_measurable : ∀ n, Measurable (epoch n)
  first_pos : ∀ ω, 0 < epoch 0 ω
  ordered : ∀ ω, StrictMono (fun n => epoch n ω)
  nonexplosive : ∀ ω, Tendsto (fun n => epoch n ω) atTop atTop
  count_measurable : ∀ s, StronglyMeasurable (arrivalCount epoch s)
  poisson : LevyFoundations.IsPoissonProcess (arrivalCount epoch) rate law

variable {Ω : Type*} [MeasurableSpace Ω]

instance (A : Arrivals Ω) : IsProbabilityMeasure A.law := A.probability

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 9, §3.2 (Poisson arrivals and their natural history).

The natural arrival-history filtration, with no additional information.
Lin, Shang, Sun, SSRN 3709573 (version of October 12, 2020), p. 9, §3.2. -/
def Arrivals.history (A : Arrivals Ω) : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural (arrivalCount A.epoch) A.count_measurable

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 9, §3.2 (Poisson arrivals and their natural history).

All predictable real price processes, before imposing the model's price interval. -/
abbrev PriceProcess (Ω : Type*) := ℝ≥0 → Ω → ℝ

end
end WaitTimePricing.Existence.Supplement


