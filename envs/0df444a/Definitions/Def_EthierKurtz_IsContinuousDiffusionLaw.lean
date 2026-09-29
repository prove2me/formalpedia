-- Prove2me | Definitions.Def_EthierKurtz_IsContinuousDiffusionLaw
-- name    : EthierKurtz_IsContinuousDiffusionLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:57:21.58115+00:00
-- url     : https://prove2.me/theorems/7b3743c0-bdc7-48fc-b581-a7c8579ea7f4
-- title:
--   Continuous diffusion martingale-problem law
-- statement:
--   A continuous process law with the specified initial distribution for which every smooth compactly supported test function satisfies the natural-past martingale identities for the diffusion generator.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 7, Section 4, Theorem 4.1 and Chapter 4 martingale-problem convention, printed pp. 173–174, 354 (PDF pp. 182–183, 363).

import Definitions.Def_EthierKurtz_diffusionMatrixOperator

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace EthierKurtz

/-- Continuous natural-past martingale problem on the smooth compact core.
Finite bounded measurable history tests express the entire natural filtration. -/
def IsContinuousDiffusionLaw {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (Q : Measure Ω)
    (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ t, Measurable (X t)) ∧ (∀ w, Continuous (fun t => X t w)) ∧
  Measure.map (X 0) Q = ν ∧
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    ∀ s t : ℝ≥0, s ≤ t → ∀ (k : ℕ) (r : Fin k → ℝ≥0),
    (∀ i, r i ≤ s) → ∀ h : Fin k → EuclideanSpace ℝ (Fin d) → ℝ,
    (∀ i, Measurable (h i) ∧ ∃ C : ℝ, ∀ x, |h i x| ≤ C) →
    (∫ w, (f (X t w) - f (X s w) -
      ∫ u in (s : ℝ)..(t : ℝ), diffusionMatrixOperator a b f (X u.toNNReal w)) *
      ∏ i, h i (X (r i) w) ∂Q) = 0

end EthierKurtz


