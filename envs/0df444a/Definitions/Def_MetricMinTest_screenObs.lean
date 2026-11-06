-- Prove2me | Definitions.Def_MetricMinTest_screenObs
-- name    : MetricMinTest_screenObs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:14.338937+00:00
-- url     : https://prove2.me/theorems/22b05c68-2041-4db5-b7b6-cef52baa116f
-- title:
--   Observation $X_s$ at the $s$-th draw
-- statement:
--   When indices $I_1,I_2,\dots$ are drawn and queried in turn, $X_s$ is a fresh observation from index $I_s$.
--
--   **Formalization Note** In the stack-of-streams model, the $s$-th draw (from $0$) reads entry $c$ of the stream of $I_s$, where $c$ is the number of earlier draws equal to $I_s$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Lemma B.1, p.22

import Mathlib

namespace MetricMinTest

/-- **Observation `X_s` of a draw sequence** (Lemma B.1). Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Lemma B.1, p.22:
"let X_s be a fresh observation from index I_s".

**Formalization Note.** In the stack-of-streams model, the `s`-th draw (0-based) reads the next
unread entry of stream `I s`: `X_s = ω (I s) c` with `c = #{s' < s : I s' = I s}`. -/
def screenObs {ι : Type} [DecidableEq ι] (I : ℕ → ι) (ω : ι → ℕ → ℝ) (s : ℕ) : ℝ :=
  ω (I s) ((Finset.range s).filter (fun s' => I s' = I s)).card

end MetricMinTest


