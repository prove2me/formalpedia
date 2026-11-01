-- Prove2me | Definitions.Def_LocalDOvS_SUS_retPt
-- name    : LocalDOvS_SUS_retPt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:27:45.286556+00:00
-- url     : https://prove2.me/theorems/9f40c9cb-a61f-4826-ab1c-1058e1cfe112
-- title:
--   Solution returned by a run
-- statement:
--   The **solution returned** by a run of $A$ on tape $\omega$ is the decision named by the stopping step issued at time $\tau_A(\omega)$.
--
--   **Formalization Note** For a run that never stops the value is a junk $0$; every guarantee of the mission counts such a run as a failure.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §2.1, p.8

import Mathlib
import Definitions.Def_LocalDOvS_SUS_stopTime

namespace LocalDOvS.SUS

/-- The solution returned by a run of `A` on tape `ω` (Zhang–Zheng–Lavaei, arXiv:2012.02427v2,
§2.1, p.8): the decision `x` of the `Step.stop x` issued at the stopping time.

**Formalization Note.** Meaningful only when `stopTime A ω < ⊤`; for a run that never stops the
value is a junk `0`, and every guarantee of this mission (`IsPGS`) counts such a run as a
failure. -/
noncomputable def retPt (A : SeqAlg) (ω : ℕ × ℕ → ℝ) : ℕ :=
  match A (histAt A ω (stopTime A ω).toNat) with
  | .stop x => x
  | .sample _ => 0

end LocalDOvS.SUS


