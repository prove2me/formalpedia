-- Prove2me | Definitions.Def_EthierKurtz_expectedMaxJump
-- name    : EthierKurtz_expectedMaxJump
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:55:38.646605+00:00
-- url     : https://prove2.me/theorems/d29bb502-0e58-4685-8a71-8ef286067f32
-- title:
--   Expected maximum jump before a deterministic horizon
-- statement:
--   The nonnegative extended expectation of the largest path jump, raised to a specified power, before a fixed horizon.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 7, Section 1, Theorem 1.4, equations (1.14), (1.16), and (1.17), printed pp. 339–340 (PDF pp. 348–349).

import Mathlib

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- Nonnegative extended expectation of the largest jump to the power p.
The supremum excludes time zero, whose jump is zero by convention. -/
noncomputable def expectedMaxJump {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) (X : ℝ≥0 → Ω → E)
    (p : ℕ) (T : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, ⨆ t : Set.Ioc (0 : ℝ≥0) T,
    ENNReal.ofReal (‖X t.val ω - Function.leftLim (fun s => X s ω) t.val‖ ^ p) ∂P

end EthierKurtz


