-- Prove2me | Definitions.Def_SchedComplexity_OneMachine_Problems
-- name    : SchedComplexity_OneMachine_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:40:53.903149+00:00
-- url     : https://prove2.me/theorems/64df93b0-75b1-4962-97cb-5071cd1890bb
-- title:
--   The recognition problems $n|1|L_{\max}\le0|\sum w_jC_j$, $n|1|r_n\ge0|L_{\max}$, $n|1||\sum w_jU_j$, $n|1|r_n\ge0,w_j=1|\sum w_jU_j$
-- statement:
--   Section 2 of the paper replaces an optimization problem by its recognition version: *does a solution with value $\le y$ exist?* This file defines, as languages of binary strings, the recognition versions of the four single-machine problems of Theorem 4(b), (c), (e), (f). In each case a string belongs to the language iff it is the code of an instance $I$ together with a threshold $y\in\mathbb N$ such that $I$ belongs to the problem class and some feasible schedule meets the stated condition.
--
--   1. $n|1|L_{\max}\le0|\sum w_jC_j$: at least one job and all release dates are $0$; the schedule must meet every due date ($C_j\le d_j$ for all $j$ — the paper: "only schedules whereby all due dates are met are to be considered") and satisfy $\sum w_jC_j\le y$.
--   2. $n|1|r_n\ge0|L_{\max}$: there is at least one job and $r_j=0$ for all jobs except the last; the schedule satisfies $L_{\max}=\max_j L_j\le y$, that is, $C_j-d_j\le y$ for every job.
--   3. $n|1||\sum w_jU_j$: at least one job and all release dates are $0$; the schedule satisfies $\sum w_jU_j\le y$.
--   4. $n|1|r_n\ge0,w_j=1|\sum w_jU_j$: at least one job, $r_j=0$ except for the last job, all weights $1$; the schedule satisfies $\sum w_jU_j\le y$.
--
--   Instances outside the class are not in the language. These are the right-hand sides of the mission's goal.
--
--   **Formalization Note** The threshold $y$ is a natural number in all four languages; for $L_{\max}$, whose values can be negative, this restricts the recognition question to $y\ge0$, which suffices for the paper's reduction ($y=0$). "$L_{\max}\le y$" is stated as "$L_j\le y$ for every $j$", which is equivalent for $n\ge1$. Each instance is coded with all four data per job, so the code of an instance of problem 2 also carries (unconstrained) weights. Codes use `encNats` from `ProjSchedTW.Complexity.Encoding`.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 4 (Section 2), pp. 6-7 (Section 3), p. 16 (Theorem 4(b),(c),(e),(f))

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_OneMachine_Model

namespace SchedComplexity.OneMachine

open CookPvsNP ProjSchedTW.Complexity

/-- The recognition version of `n|1|L_max≤0|∑w_jC_j` (Brucker, Lenstra & Rinnooy Kan, Report
BW 43/75, pp. 4, 7): binary codes of a nonempty instance `I` with all release dates `0` and a threshold
`y ∈ ℕ` such that some feasible schedule meets every due date (`C_j ≤ d_j` for all `j`; only such
schedules are considered) and has `∑ w_j C_j ≤ y`. -/
def langLmaxSumWC : Lang BSym :=
  { x | ∃ (I : Instance) (y : ℕ), x = encNats (I.codeList y) ∧ 0 < I.n ∧ I.AllReleasedAtZero ∧
      ∃ B, I.IsFeasible B ∧ (∀ j, I.C B j ≤ I.d j) ∧ I.sumWC B ≤ y }

/-- The recognition version of `n|1|r_n≥0|L_max` (pp. 4, 7): binary codes of an instance `I` with
at least one job, release date `0` for every job except the last one, and a threshold `y ∈ ℕ`,
such that some feasible schedule has `L_max ≤ y`, i.e. `C_j - d_j ≤ y` for every job `j`. -/
def langRnLmax : Lang BSym :=
  { x | ∃ (I : Instance) (y : ℕ), x = encNats (I.codeList y) ∧ I.OnlyLastReleased ∧
      ∃ B, I.IsFeasible B ∧ ∀ j, I.lateness B j ≤ (y : ℤ) }

/-- The recognition version of `n|1||∑w_jU_j` (pp. 4, 7): binary codes of a nonempty instance `I` with all
release dates `0` and a threshold `y ∈ ℕ` such that some feasible schedule has `∑ w_j U_j ≤ y`. -/
def langSumWU : Lang BSym :=
  { x | ∃ (I : Instance) (y : ℕ), x = encNats (I.codeList y) ∧ 0 < I.n ∧ I.AllReleasedAtZero ∧
      ∃ B, I.IsFeasible B ∧ I.sumWU B ≤ y }

/-- The recognition version of `n|1|r_n≥0,w_j=1|∑w_jU_j` (pp. 4, 7): binary codes of an instance
`I` with at least one job, release date `0` for every job except the last one, all weights `1`,
and a threshold `y ∈ ℕ` such that some feasible schedule has `∑ w_j U_j ≤ y`. -/
def langRnUnitSumWU : Lang BSym :=
  { x | ∃ (I : Instance) (y : ℕ), x = encNats (I.codeList y) ∧ I.OnlyLastReleased ∧
      I.UnitWeights ∧ ∃ B, I.IsFeasible B ∧ I.sumWU B ≤ y }

end SchedComplexity.OneMachine


