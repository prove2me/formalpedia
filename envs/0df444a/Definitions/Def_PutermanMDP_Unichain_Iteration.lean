-- Prove2me | Definitions.Def_PutermanMDP_Unichain_Iteration
-- name    : PutermanMDP_Unichain_Iteration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:31:36.914138+00:00
-- url     : https://prove2.me/theorems/84bf4026-c4b6-49dd-a3ff-f50503d8a71c
-- title:
--   Unichain policy evaluation, improvement and the exact stopping test
-- statement:
--   For an admissible stationary decision rule $d$, a scalar $g$ and vector $h$ evaluate $d$ when
--   $$g+h(s)=r(s,d(s))+\sum_jp(j\mid s,d(s))h(j)\quad(s\in S).$$
--   No additive normalization is required: this is the underdetermined evaluation system (8.6.1).
--
--   An improvement step from $d$ to $d'$ chooses an $h$-improving rule, maximizing $r(s,a)+\sum_jp(j\mid s,a)h(j)$ at every state. If the whole incumbent rule $d$ is already maximizing, $d'=d$ is required. This is the printed wording “setting $d_{n+1}=d_n$ if possible”; it does not impose separate retention at each tied state when the whole incumbent is not maximizing.
--
--   A run is a sequence $(d_n,g_n,h_n)_{n\ge0}$ satisfying evaluation and improvement at each index. The stopping index is the first $n$ with $d_{n+1}=d_n$. Sequences continue past that index only to make runs total objects; the algorithm returns at the first equality.
--
--   This describes the algorithm's operations without putting solvability, finite termination, Bellman equality, or average optimality into its definition. The goal asserts both the existence of runs from every initial rule and termination of every such run.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, p. 378 (PDF 394), §8.6.1, steps 1–4 and (8.6.1)–(8.6.7)

import Mathlib
import Definitions.Def_PutermanMDP_Unichain_PolicyData
open MarkovDecisionProcesses

namespace PutermanMDP.Unichain

variable {S A : Type*} [Fintype S] [Fintype A]

/-- Policy evaluation, exactly (8.6.1). The scalar and vector are solved for;
no particular additive normalization of the vector is imposed. -/
def Evaluates (M : StationaryMDP S A) (d : Rule M) (g : ℝ) (h : S → ℝ) : Prop :=
  ∀ s, g + h s = M.reward s (d.val s) + ∑ j, M.trans s (d.val s) j * h j

/-- Step 3, (8.6.2): choose a maximizing decision rule, retaining the incumbent
rule if it is itself maximizing. This is the printed whole-rule retention test. -/
def Improves (M : StationaryMDP S A) (d d' : Rule M) (h : S → ℝ) : Prop :=
  IsImproving M h d'.val ∧ (IsImproving M h d.val → d' = d)

/-- Steps 1--3 continued past stopping, solely to represent arbitrary runs by
sequences. Step 4 stops at the first adjacent equality. Only evaluation and
improvement are assumed, not termination, Bellman equality or optimality. -/
def IsRun (M : StationaryMDP S A) (d : ℕ → Rule M) (g : ℕ → ℝ)
    (h : ℕ → S → ℝ) : Prop :=
  (∀ n, Evaluates M (d n) (g n) (h n)) ∧
  (∀ n, Improves M (d n) (d (n + 1)) (h n))

/-- The exact stopping test in step 4. -/
def StopsAt (M : StationaryMDP S A) (d : ℕ → Rule M) (n : ℕ) : Prop :=
  d (n + 1) = d n ∧ ∀ k < n, d (k + 1) ≠ d k

end PutermanMDP.Unichain


