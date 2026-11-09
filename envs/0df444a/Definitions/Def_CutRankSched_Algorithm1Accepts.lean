-- Prove2me | Definitions.Def_CutRankSched_Algorithm1Accepts
-- name    : CutRankSched_Algorithm1Accepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:37:05.285158+00:00
-- url     : https://prove2.me/theorems/1c9ab434-de45-41d0-b93d-6b42f296a6f4
-- title:
--   Algorithm 1 answers Yes
-- statement:
--   **Algorithm 1** on an instance and budget $L$ answers Yes exactly when
--
--   1. $n = 0$ or $L \ge n$ (line 1), or otherwise
--   2. $n \le mL$ (line 3 does not reject) and the state set of the dynamic program is nonempty at every cut, equivalently at cut $n$ (lines 18–20).
--
--   **Formalization Note** An empty state set stays empty, so testing the last cut is the test of line 18 at every cut.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Algorithm 1, p.10

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_dpSet

set_option autoImplicit false

namespace CutRankSched

/-- Algorithm 1 answers **Yes** on budget `L` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Algorithm 1, p.10): line 1 accepts when
`n = 0` or `L ≥ n`; otherwise line 3 rejects when `n > mL`; otherwise the DP runs, line 18
rejects as soon as `DP = ∅`, and line 20 accepts.

**Formalization Note** An empty `DP` stays empty, so "no cut has an empty `DP`" is "the `DP` at
cut `n` is nonempty". -/
def Algorithm1Accepts (I : Instance) (L : ℕ) : Prop :=
  I.n = 0 ∨ I.n ≤ L ∨ (¬ I.m * L < I.n ∧ (dpSet I L I.n).Nonempty)

end CutRankSched


