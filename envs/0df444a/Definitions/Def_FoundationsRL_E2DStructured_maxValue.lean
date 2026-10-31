-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_maxValue
-- name    : FoundationsRL_E2DStructured_maxValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:50.852637+00:00
-- url     : https://prove2.me/theorems/d5a8d4d0-1cf4-4ed9-802b-e6948730c081
-- title:
--   The optimal value $f(\pi_f)$
-- statement:
--   For a reward function $f:\Pi\to\mathbb R$ with maximizer $\pi_f\in\arg\max_{\pi\in\Pi}f(\pi)$, the optimal value is
--   $$f(\pi_f)=\max_{\pi\in\Pi}f(\pi).$$
--   It is the benchmark against which the regret of a decision is measured in the Decision-Estimation Coefficient.
--
--   **Formalization Note** The decision space $\Pi$ is written `D`, since `Π` is a Lean token. The value is the real supremum of $f$; it is used only for functions that attain their maximum (`IsRewardClass`), so the supremum is the maximum.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.15), p. 65

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The optimal value `f(π_f) = max_π f(π)` of a reward function (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 65, (4.15)).

**Formalization Note.** The decision space `Π` of the notes is written `D` (`Π` is a Lean token).
`maxValue f` is the real supremum of `f`; every use is under `IsRewardClass`, where `f` attains its
maximum, so the supremum is the book's `f(π_f)` and no junk value arises. -/
noncomputable def maxValue {D : Type*} (f : D → ℝ) : ℝ := ⨆ π, f π

end FoundationsRL.E2DStructured


