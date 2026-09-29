-- Prove2me | Definitions.Def_EthierKurtz_SolvesTimeInhomogeneousDiffusion
-- name    : EthierKurtz_SolvesTimeInhomogeneousDiffusion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:03:17.43072+00:00
-- url     : https://prove2.me/theorems/af6fe633-599f-4a92-b798-b2841c49dbed
-- title:
--   Solution of the time-inhomogeneous diffusion martingale problem
-- statement:
--   A jointly measurable process with the prescribed initial law that satisfies every smooth compactly supported diffusion martingale identity against bounded continuous finite-history tests.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, equation (1.24) and Theorem 1.7, printed pp. 370–371 (PDF pp. 379–380); Chapter 4, Section 3, equation (3.4), printed pp. 173–174 (PDF pp. 182–183).

import Definitions.Def_EthierKurtz_diffusionOperator

open MeasureTheory Filter
open scoped NNReal Topology ContDiff

namespace EthierKurtz

/-- Chapter 4 (3.4), with the time-dependent operator of Chapter 8 (1.24).
Bounded continuous history tests suffice by Chapter 4 p.174. The process is
jointly measurable; no continuous-path restriction is imposed. Under the
capstone hypotheses compact spatial tests make all integrands bounded on
bounded time intervals, so these are ordinary integrable moment identities. -/
def SolvesTimeInhomogeneousDiffusion {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ≥0 × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : ℝ≥0 × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
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
            diffusionOperator (fun x => a (u.toNNReal, x))
              (fun x => b (u.toNNReal, x)) f (X u.toNNReal w)) *
          ∏ i, h i (X (r i) w) ∂P) = 0

end EthierKurtz


