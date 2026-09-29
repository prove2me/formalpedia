-- Prove2me | Definitions.Def_EthierKurtz_diffusionExit
-- name    : EthierKurtz_diffusionExit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:56:14.354973+00:00
-- url     : https://prove2.me/theorems/31ed2319-a044-4661-9aba-16264af9b365
-- title:
--   Localized exit time for a càdlàg process
-- statement:
--   The first time at which either the current value or the left limit of a path reaches the prescribed radius.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 7, Section 4, Theorem 4.1, stopping-time convention, printed p. 354 (PDF p. 363).

import Mathlib

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- Exit includes both the value and the left limit; the empty infimum is ∞. -/
noncomputable def diffusionExit {Ω : Type*} {d : ℕ}
    (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (r : ℝ) (w : Ω) :
    WithTop ℝ≥0 :=
  sInf {t | ∃ s : ℝ≥0, t = s ∧
    (r ≤ ‖X s w‖ ∨ (0 < s ∧ r ≤ ‖Function.leftLim (fun u => X u w) s‖))}

end EthierKurtz


