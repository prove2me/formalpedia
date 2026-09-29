-- Prove2me | Definitions.Def_EthierKurtz_HasBrownianItoIntegral
-- name    : EthierKurtz_HasBrownianItoIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:48:38.880703+00:00
-- url     : https://prove2.me/theorems/98a18f5a-cd5a-46a2-9afe-d7611d81623d
-- title:
--   Brownian Itô integral by step approximation
-- statement:
--   A local Brownian integral relation defined by predictable dyadic approximations in integrated squared error and convergence in probability of their stochastic sums.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 5, Section 2, printed pp. 280, 282–283, 286 (PDF pp. 289, 291–292, 295).

import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_itoStepSum

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Concrete local Itô integral relation for Brownian integrators: predictable
step approximations converge in integrated squared error in probability, and
their stochastic sums converge in probability to J. This is the localized
step-sum construction of source Section 2. No integral operator is postulated.
The square-integrability clause excludes default-zero Bochner integrals of
nonintegrable integrands. Here H is pathwise bounded on compact time intervals. -/
def HasBrownianItoIntegral (P : Measure Ω) (ℱ : ℝ≥0 → MeasurableSpace Ω)
    (W H J : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ (t : ℝ≥0) ω, IntervalIntegrable (fun u : ℝ => H u.toNNReal ω ^ 2)
    volume 0 t.val) ∧
  ∀ t : ℝ≥0, ∃ a : ℕ → ℕ → Ω → ℝ,
    (∀ (n k : ℕ), k < 2 ^ n → Measurable[ℱ ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (a n k)) ∧
    (∀ n, ∃ C : ℝ, ∀ k, k < 2 ^ n → ∀ ω, |a n k ω| ≤ C) ∧
    TendstoInMeasure P
      (fun n ω => ∫ u in (0 : ℝ)..t.val,
        (itoStepValue t n (a n) u ω - H u.toNNReal ω) ^ 2)
      atTop (fun _ => (0 : ℝ)) ∧
    TendstoInMeasure P (fun n => itoStepSum W t n (a n)) atTop (J t)

end EthierKurtz


