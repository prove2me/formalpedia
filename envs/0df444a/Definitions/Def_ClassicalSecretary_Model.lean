-- Prove2me | Definitions.Def_ClassicalSecretary_Model
-- name    : ClassicalSecretary_Model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T12:47:36.884213+00:00
-- url     : https://prove2.me/theorems/ac24fea5-7f6c-4d07-8418-195087c3a6b2
-- title:
--   Classical secretary problem: rank-based stopping rules, success probability, cutoff rules
-- statement:
--   This file sets up the classical secretary problem.
--
--   There are $n$ applicants, interviewed one at a time in a uniformly random order. An order is a permutation $\sigma$ of $\{0,\dots,n-1\}$: the applicant interviewed at time $i$ has quality $\sigma(i)$, and larger is better.
--
--   1. **Relative rank** (`relRank σ j`): the number of applicants interviewed before time $j$ who are worse than the applicant interviewed at time $j$.
--   2. **History** (`history σ i`): the list of relative ranks of the applicants interviewed at times $0,1,\dots,i$. This is exactly the information available right after the interview at time $i$, and it has length $i+1$.
--   3. **Stopping rule** (`StoppingRule`): a function from histories to $\{\text{accept},\text{reject}\}$. The rule stops at time $i$ (`StopsAt`) if it accepts at time $i$ and rejected at every earlier time. It **wins** on $\sigma$ (`Wins`) if it stops at a time $i$ whose applicant is the best of all $n$ (`IsBest`). A rule that never accepts does not win.
--   4. **Success probability** (`successProb n s`):
--   $$P_n(s) = \frac{\#\{\sigma : s \text{ wins on } \sigma\}}{n!}.$$
--   5. **Optimal success probability** (`optimalProb n`): $V_n = \sup_s P_n(s)$ over all stopping rules.
--   6. **Cutoff rule** (`cutoffRule r`): reject the first $r-1$ applicants, then accept the first **candidate**, i.e. the first applicant who is better than everyone interviewed before them. In terms of the history at time $i$: accept iff $i+1 \ge r$ and the last relative rank equals $i$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Times are 0-based (`Fin n`), and the cutoff $r$ is 1-based as in the source. Stopping rules are deterministic. A randomized rule is a mixture of deterministic ones and cannot do better. Because a rule sees the whole history, it also knows the current time.
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, section "Formulation" (model) and section "Deriving the optimal policy" (cutoff rule, first paragraph).

import Mathlib

/-!
# The classical secretary problem: model

`n` applicants are interviewed one at a time, in a uniformly random order.
An ordering is a permutation `σ : Equiv.Perm (Fin n)`: the applicant interviewed at time
`i : Fin n` (times are `0, 1, …, n - 1`) has absolute quality `σ i`, larger meaning better,
so the best applicant is the one with quality `n - 1`.

The interviewer only sees relative ranks: after interviewing the applicant at time `i`
they know, for each `j ≤ i`, how many of the applicants interviewed before time `j`
were worse than the applicant interviewed at time `j`.  A (deterministic) stopping rule maps
this observed history to the decision "accept the current applicant" (`true`) or
"reject and continue" (`false`).  The rule wins on `σ` if the applicant it accepts is the
best of all `n` applicants.
-/

open Finset

namespace ClassicalSecretary

/-- The relative rank of the applicant interviewed at time `j`: the number of applicants
interviewed strictly before time `j` who are worse than them. -/
def relRank {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin n) : ℕ :=
  #{k : Fin n | k < j ∧ σ k < σ j}

/-- The information available right after the interview at time `i`: the list of relative
ranks of the applicants interviewed at times `0, 1, …, i` (in interview order). Its length is
`i + 1`, the number of applicants seen so far. -/
def history {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : List ℕ :=
  ((List.finRange n).take (i.val + 1)).map (relRank σ)

/-- A stopping rule based only on relative ranks: given the history of relative ranks
observed so far, decide whether to accept (`true`) the applicant just interviewed. -/
abbrev StoppingRule := List ℕ → Bool

/-- The rule `s` stops (accepts) at time `i` on ordering `σ`: it accepts at time `i`
and rejected every earlier applicant. -/
def StopsAt {n : ℕ} (s : StoppingRule) (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  s (history σ i) = true ∧ ∀ j : Fin n, j < i → s (history σ j) = false

instance {n : ℕ} (s : StoppingRule) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    Decidable (StopsAt s σ i) := by
  unfold StopsAt; infer_instance

/-- The applicant interviewed at time `i` is the best of all `n` applicants. -/
def IsBest {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∀ j : Fin n, σ j ≤ σ i

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Decidable (IsBest σ i) := by
  unfold IsBest; infer_instance

/-- The rule `s` wins on ordering `σ`: the applicant it accepts is the overall best.
If the rule never accepts anybody, it does not win. -/
def Wins {n : ℕ} (s : StoppingRule) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ i : Fin n, StopsAt s σ i ∧ IsBest σ i

instance {n : ℕ} (s : StoppingRule) (σ : Equiv.Perm (Fin n)) : Decidable (Wins s σ) := by
  unfold Wins; infer_instance

/-- The probability that the rule `s` selects the best of `n` applicants when all `n!`
interview orders are equally likely. -/
noncomputable def successProb (n : ℕ) (s : StoppingRule) : ℝ :=
  (#{σ : Equiv.Perm (Fin n) | Wins s σ} : ℝ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)

/-- The optimal success probability with `n` applicants: the supremum of `successProb n s`
over all rank-based stopping rules `s`. -/
noncomputable def optimalProb (n : ℕ) : ℝ :=
  ⨆ s : StoppingRule, successProb n s

/-- The cutoff rule with cutoff `r`: reject the first `r - 1` applicants, then accept the first
applicant who is better than every applicant interviewed before them (a *candidate*).
At time `i` the history has length `i + 1` (the 1-based position of the current applicant),
and the current applicant is a candidate iff their relative rank equals `i`. -/
def cutoffRule (r : ℕ) : StoppingRule := fun h =>
  decide (r ≤ h.length) && decide (h.getLast? = some (h.length - 1))

end ClassicalSecretary


