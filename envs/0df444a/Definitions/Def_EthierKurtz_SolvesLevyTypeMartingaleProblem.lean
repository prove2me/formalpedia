-- Prove2me | Definitions.Def_EthierKurtz_SolvesLevyTypeMartingaleProblem
-- name    : EthierKurtz_SolvesLevyTypeMartingaleProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:26:04.76949+00:00
-- url     : https://prove2.me/theorems/e994f0df-f56e-481a-a039-25d079d02412
-- title:
--   Solution of the nonautonomous Lévy-type martingale problem
-- statement:
--   A jointly measurable process with the prescribed initial law satisfying every smooth compactly supported compensated-generator identity against bounded continuous finite-history tests.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, Theorem 3.3 and equation (3.21), printed pp. 379–380 (PDF pp. 388–389); Chapter 4, Section 3, equation (3.4), printed pp. 173–174 (PDF pp. 182–183).

import Definitions.Def_EthierKurtz_levyTypeOperator

open MeasureTheory Filter
open scoped NNReal Topology ContDiff

namespace EthierKurtz

/-- Chapter 4 (3.4), specialized to the nonautonomous operator (3.21).
Smooth compact tests and the weighted-measure bounds make these integrands
bounded and integrable. Jointly measurable processes, without path restrictions,
are compared using all finite bounded-continuous histories. -/
def SolvesLevyTypeMartingaleProblem {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ≥0 × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : ℝ≥0 × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ν : ℝ≥0 × EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (P : Measure Ω)
    (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2) ∧
  Measure.map (X 0) P = μ ∧
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiff ℝ ∞ f → HasCompactSupport f →
    ∀ s t : ℝ≥0, s ≤ t → ∀ (n : ℕ) (r : Fin n → ℝ≥0),
      (∀ i, r i ≤ s) → ∀ h : Fin n → BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ,
        (∫ w, (f (X t w) - f (X s w) -
          ∫ u in (s : ℝ)..(t : ℝ),
            levyTypeOperator a b ν f u.toNNReal (X u.toNNReal w)) *
          ∏ i, h i (X (r i) w) ∂P) = 0

end EthierKurtz


