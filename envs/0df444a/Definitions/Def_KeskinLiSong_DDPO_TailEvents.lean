-- Prove2me | Definitions.Def_KeskinLiSong_DDPO_TailEvents
-- name    : KeskinLiSong_DDPO_TailEvents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:48:09.706735+00:00
-- url     : https://prove2.me/theorems/91d8970f-5ec9-465f-97be-b40dfc089bf1
-- title:
--   Data-dependent probability events and noise-only integration
-- statement:
--   TailBound expresses a scalar event probability bounded almost surely by a random right side on the specified range. It keeps the random M_t and cycle endpoints inside their proper path functions, with no replacement by fixed samples. True-noise and residual proxy functions use the exact DDPO sample set. Noise-only probabilities fix the perishability path and integrate the entire noise sequence, recomputing observed histories and estimators. Prices are measurable functions of preceding observed history. ScoreMoment expresses the uniform finite score moment in Proposition 3, including existence of the gradient where used.
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), pp. 21–24; ec8

import Definitions.Def_KeskinLiSong_DDPO_Analysis

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

namespace KeskinLiSong.DDPO

/-- Literal interpretation of a probability bounded by a random right side:
the probability is a scalar and the inequality holds almost surely on the stated
range. No conditioning, averaging, or replacement of random indices occurs. -/
def TailBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (eligible : Ω → Prop) (error threshold rhs : Ω → ℝ) : Prop :=
  MeasurableSet {z | threshold z ≤ error z} ∧
  ∀ᵐ z ∂μ, eligible z → (μ {w | threshold w ≤ error w}).toReal ≤ rhs z

/-- Parameters computed from exactly the learner's observed history. -/
def thetaEstimate (mode : NoiseMode) (A : Model) {T : ℕ} (E : Environment A T)
    (L : Learner mode) (z : Paths T) (t : ℕ) := evaluate A E L.policy L.thetaHat z t

def xiEstimate (mode : NoiseMode) (A : Model) {T : ℕ} (E : Environment A T)
    (L : Learner mode) (z : Paths T) (t : ℕ) := evaluate A E L.policy L.xiHat z t

def effectiveSize (mode : NoiseMode) (A : Model) (u : Tuning A) {T : ℕ}
    (E : Environment A T) (L : Learner mode) (z : Paths T) (t : ℕ) : ℝ :=
  sampleSize u mode.version T (demandPath A E L.policy z) t

def trueProxy (mode : NoiseMode) (A : Model) (u : Tuning A) {T : ℕ}
    (E : Environment A T) (L : Learner mode) (z : Paths T) (t : ℕ) (p : ℝ) : ℝ :=
  Gemp A (xiEstimate mode A E L z t) (E.theta t)
    (samples u mode.version T (demandPath A E L.policy z) t)
    (sampleSize u mode.version T (demandPath A E L.policy z) t)
    (fun s => (innovation z s).1) p

def residualProxy (mode : NoiseMode) (A : Model) (u : Tuning A) {T : ℕ}
    (E : Environment A T) (L : Learner mode) (z : Paths T) (t : ℕ) (p : ℝ) : ℝ :=
  Gemp A (xiEstimate mode A E L z t) (thetaEstimate mode A E L z t)
    (samples u mode.version T (demandPath A E L.policy z) t)
    (sampleSize u mode.version T (demandPath A E L.policy z) t)
    (residual A E L.policy z (thetaEstimate mode A E L z t)) p

/-- Noise-only probability integrates innovations while keeping the perishability
sequence fixed. The history, reset times, and estimates are recomputed for every
noise sequence and are not frozen at observed values. -/
def combine (e q : ℕ → ℝ) : (ℕ → ℝ) × (ℕ → ℝ) := (e, q)

/-- A price chosen from the same observed information as the learner. -/
structure PriceSelection where
  price : (k : ℕ) → (Fin k → Observation × Action) → ℝ
  measurable : ∀ k, Measurable (price k)

def priceAt (A : Model) {T : ℕ} (E : Environment A T) (π : Policy)
    (p : PriceSelection) (z : Paths T) (t : ℕ) : ℝ := evaluate A E π p.price z t

/-- Moment condition in Proposition 3, with existence of the printed gradient
and integrability made explicit. No positive Fisher information is assumed. -/
def ScoreMoment {d : ℕ} (F : ExponentialFamily d) (ell : ℝ) : Prop :=
  (d : ℝ) < ell ∧ ∃ B : ℝ, ∀ phi ∈ F.parameterSet,
    (∀ᵐ z ∂F.law phi, DifferentiableAt ℝ (fun v => Real.log (F.density v z)) phi) ∧
    Integrable (fun z => ‖fderiv ℝ (fun v => Real.log (F.density v z)) phi‖ ^ ell) (F.law phi) ∧
    (∫ z, ‖fderiv ℝ (fun v => Real.log (F.density v z)) phi‖ ^ ell ∂F.law phi) ≤ B

end KeskinLiSong.DDPO


