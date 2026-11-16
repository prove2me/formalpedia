-- Prove2me | Definitions.Def_CalibratedMA_Randomized_Supplement_Learning
-- name    : CalibratedMA_Randomized_Supplement_Learning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:22:38.717439+00:00
-- url     : https://prove2.me/theorems/7d3de810-2540-49ad-ad8f-81c516a40e4e
-- title:
--   Sections 5–7 — sample learners and deterministic predictor wrappers
-- statement:
--   A deterministic predictor is a measurable function $p:X\to[0,1]$. It is evaluated through the published randomized-predictor interface as $Q_x=\delta_{p(x)}$; this introduces no new error measure. A training seed is an arbitrary probability space $(\Omega,\nu)$ chosen independently of the unknown distribution. A learner is a measurable evaluation map from its sample, seed and query context to a deterministic prediction or an admissible randomized prediction law. Every trained output is admissible.
--
--   For $n$ training examples from a labeled law $D$, the training law and success guarantee are
--   $$D^{\otimes n}\otimes\nu,\qquad
--   \Pr\{\mathrm{CMA}_D(Q;G)\le e\}\ge q.$$
--   Success includes measurability of that event. Both the sample and all training randomness are included; prediction randomness is inside the published CMA. Learners contain no data-distribution parameter. The explicit sample envelope used in Theorem 5.1 is
--   $$\left\lceil C\left(\frac{A}{\varepsilon^2}+\frac{A^{1/3}}{\varepsilon^{8/3}}\right)\log\frac{CB}{\varepsilon\delta}\right\rceil,
--   \quad A=\log(8|G|/\delta)+1,\quad B=A+(A/\varepsilon^2)^{1/3}.$$
--   These wrappers describe statistical experiments without assuming any learning guarantee. They support both upper and lower bounds.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), pp.21,31–32,36,43, Theorems 5.1, 6.1, 7.1; Algorithm 2; Appendix A Eq. (27)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Setting

open MeasureTheory
open scoped ENNReal

namespace CalibratedMA.Randomized.Supplement

/-- Sections 5–7: admissible deterministic output, embedded into the published predictor. -/
def IsDetPredictor {X : Type} [MeasurableSpace X] (p : X → ℝ) : Prop :=
  Measurable p ∧ ∀ x, p x ∈ Set.Icc (0 : ℝ) 1

noncomputable def pointPredictor {X : Type} (p : X → ℝ) : X → Measure ℝ :=
  fun x => Measure.dirac (p x)

/-- An independent training seed, fixed before the unknown distribution. -/
structure TrainingSeed where
  Ω : Type
  measurableSpace : MeasurableSpace Ω
  law : @Measure Ω measurableSpace
  probability : @IsProbabilityMeasure Ω measurableSpace law

attribute [instance] TrainingSeed.measurableSpace TrainingSeed.probability

/-- The actual law of n iid examples and an independent training seed. -/
noncomputable def trainingLaw {X : Type} [MeasurableSpace X] (n : ℕ)
    (D : Measure (X × ℝ)) (seed : TrainingSeed) :
    Measure ((Fin n → X × ℝ) × seed.Ω) :=
  (Measure.pi fun _ : Fin n => D).prod seed.law

/-- A training procedure returning an arbitrary admissible probability kernel. -/
structure RandomizedLearner (X : Type) [MeasurableSpace X] (n : ℕ) where
  seed : TrainingSeed
  output : ((Fin n → X × ℝ) × seed.Ω) → X → Measure ℝ
  admissible : ∀ z, IsRandomizedPredictor (output z)
  measurable_eval : Measurable (fun z : (((Fin n → X × ℝ) × seed.Ω) × X) =>
    output z.1 z.2)

/-- Training may randomize, while each trained output is a fixed measurable function. -/
structure DeterministicLearner (X : Type) [MeasurableSpace X] (n : ℕ) where
  seed : TrainingSeed
  output : ((Fin n → X × ℝ) × seed.Ω) → X → ℝ
  admissible : ∀ z, IsDetPredictor (output z)
  measurable_eval : Measurable (fun z : (((Fin n → X × ℝ) × seed.Ω) × X) =>
    output z.1 z.2)

/-- Genuine success probability, including measurability of the success event. -/
def RandomizedSuccess {X : Type} [MeasurableSpace X] {n : ℕ}
    (L : RandomizedLearner X n) (D : Measure (X × ℝ))
    (G : Finset (X → ℝ)) (err confidence : ℝ) : Prop :=
  MeasurableSet {z | CMA D (L.output z) G ≤ err} ∧
    ENNReal.ofReal confidence ≤ trainingLaw n D L.seed {z | CMA D (L.output z) G ≤ err}

def DeterministicSuccess {X : Type} [MeasurableSpace X] {n : ℕ}
    (L : DeterministicLearner X n) (D : Measure (X × ℝ))
    (G : Finset (X → ℝ)) (err confidence : ℝ) : Prop :=
  MeasurableSet {z | CMA D (pointPredictor (L.output z)) G ≤ err} ∧
    ENNReal.ofReal confidence ≤ trainingLaw n D L.seed
      {z | CMA D (pointPredictor (L.output z)) G ≤ err}

/-- The explicit logarithmic envelope of Algorithm 2 and Appendix A, Eq. (27). -/
noncomputable def deterministicSampleBound (C ε δ : ℝ) (cardG : ℕ) : ℕ :=
  let A := Real.log (8 * (cardG : ℝ) / δ) + 1
  let B := A + (A / ε ^ 2) ^ (1 / 3 : ℝ)
  ⌈C * (A / ε ^ 2 + A ^ (1 / 3 : ℝ) / ε ^ (8 / 3 : ℝ)) *
    Real.log (C * B / (ε * δ))⌉₊

end CalibratedMA.Randomized.Supplement


