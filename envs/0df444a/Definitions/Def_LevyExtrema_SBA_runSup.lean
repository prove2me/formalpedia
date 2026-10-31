-- Prove2me | Definitions.Def_LevyExtrema_SBA_runSup
-- name    : LevyExtrema_SBA_runSup
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:50.696554+00:00
-- url     : https://prove2.me/theorems/80e40c5e-19ed-4e61-90bd-1c2a49bba3a4
-- title:
--   Running supremum $\overline{f}_t=\sup\{f_s:s\in[0,t]\}$ of a path
-- statement:
--   For a path $f:[0,\infty)\to\mathbb R$ and a time $t\ge0$, the **running supremum** of $f$ over $[0,t]$ is
--
--   $$\overline{f}_t=\sup\{f_s : s\in[0,t]\}.$$
--
--   The paper uses it for right-continuous paths with left limits, which are bounded on compact intervals, so the supremum is finite. For a Lévy process $X$ the random variable $\overline X_T$ is the supremum whose simulation the mission studies.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$ and the supremum is the real `sSup` of the image $f([0,t])$, which is the true supremum on bounded sets; every use in the mission is on a càdlàg path.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, §1.1, p. 3 (notation before Theorem 1)

import Mathlib

open scoped NNReal

namespace LevyExtrema.SBA

/-- **Running supremum f̄_t of a path.**
González Cázares, Mijatović, Uribe Bravo, *Geometrically Convergent Simulation of the Extrema of
Lévy Processes*, arXiv:1810.11039v3, §1.1, p. 3: "for a right-continuous function
f : [0, ∞) → R with left-hand limits, we denote by f̄_t = sup{f_s : s ∈ [0, t]} its supremum over
the interval [0, t]".

`runSup f t = sSup (f '' [0, t])`.

**Formalization Note.** Time is `ℝ≥0`. The real `sSup` is the true supremum only on sets that are
bounded above; the paper applies f̄ only to càdlàg paths, which are bounded on compact intervals,
and every use in this mission is on a path of a Lévy process in the sense of
`SingCtrlLevy.Barrier.IsLevyWith` (every path càdlàg). -/
noncomputable def runSup (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  sSup (f '' Set.Icc 0 t)

end LevyExtrema.SBA


