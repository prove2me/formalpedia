-- Prove2me | Definitions.Def_MetricMinTest_Tester_Accepts
-- name    : MetricMinTest_Tester_Accepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:09.851422+00:00
-- url     : https://prove2.me/theorems/4ad080e2-3379-4dae-af54-96d9543fc6cc
-- title:
--   Acceptance event of a sequential tester
-- statement:
--   The tester **accepts** on $(\xi,\omega)$ if it stops at a finite step and its decision on the final history is accept. A tester that never stops does not accept. Once the tester has stopped the history no longer changes, so the decision is well defined.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Tester_hist

namespace MetricMinTest

/-- **The event `A = accept`.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC
2027 submission (manuscript sha256 dcece193…ad32bb), §2 p.6.

**Formalization Note.** The tester stops at a finite step and its decision on the final history
is `accept`. After the first stop the history no longer changes, so any stopping step gives the
same decision. A tester that never stops does not accept. -/
def Tester.Accepts {ι : Type} [DecidableEq ι] (T : Tester ι) (ξ : T.Ξ) (ω : ι → ℕ → ℝ) : Prop :=
  ∃ n : ℕ, T.next ξ (T.hist ξ ω n) = none ∧ T.accept ξ (T.hist ξ ω n) = true

end MetricMinTest


