-- Prove2me | Definitions.Def_EthierKurtz_diffusionDiscrepancy
-- name    : EthierKurtz_diffusionDiscrepancy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:56:36.329665+00:00
-- url     : https://prove2.me/theorems/8a3e52c0-e58b-4a7e-9cde-511c5b83120a
-- title:
--   Localized characteristic discrepancy
-- statement:
--   The stopped uniform discrepancy between a characteristic process and the time integral of a state-dependent coefficient along the process path.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 7, Section 4, Theorem 4.1, equations (4.6)–(4.7), printed p. 354 (PDF p. 363).

import Mathlib

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- Stopped uniform discrepancy from the integrated state-dependent coefficient. -/
noncomputable def diffusionDiscrepancy {Ω : Type*} {d : ℕ}
    (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (Y : ℝ≥0 → Ω → ℝ)
    (c : EuclideanSpace ℝ (Fin d) → ℝ) (T : ℝ≥0)
    (τ : Ω → WithTop ℝ≥0) (w : Ω) : ℝ≥0∞ :=
  ⨆ t : {t : ℝ≥0 // t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ w},
    ENNReal.ofReal |Y t.val w -
      ∫ s in (0 : ℝ)..(t.val : ℝ), c (X s.toNNReal w)|

end EthierKurtz


