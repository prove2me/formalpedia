-- Prove2me | Definitions.Def_EthierKurtz_expectedStoppedMaxJump
-- name    : EthierKurtz_expectedStoppedMaxJump
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:56:25.63627+00:00
-- url     : https://prove2.me/theorems/4683615b-7302-409f-856b-f230ce15646a
-- title:
--   Expected maximum jump before a stopped horizon
-- statement:
--   The nonnegative extended expectation of the largest jump, raised to a specified power, up to both a deterministic horizon and a random stopping time.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 7, Section 4, Theorem 4.1, equations (4.3)–(4.5), printed p. 354 (PDF p. 363).

import Mathlib

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- The largest jump before a random horizon, including a jump at the horizon. -/
noncomputable def expectedStoppedMaxJump {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) (Y : ℝ≥0 → Ω → E)
    (p : ℕ) (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ w, ⨆ t : {t : ℝ≥0 // 0 < t ∧ t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ w},
    ENNReal.ofReal (‖Y t.val w - Function.leftLim (fun s => Y s w) t.val‖ ^ p) ∂P

end EthierKurtz


