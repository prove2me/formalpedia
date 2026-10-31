-- Prove2me | Definitions.Def_DworczakDACC_State
-- name    : DworczakDACC_State
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:03.406008+00:00
-- url     : https://prove2.me/theorems/8977bbde-c9e5-466f-8253-0328b51df645
-- title:
--   State of the DACC algorithm (budget sets, applicant sets, matching, CC stack, round)
-- statement:
--   A **state** of the DACC algorithm records:
--
--   1. for every agent $i$, its **budget set** $B_i\subseteq N_i$ (the partners $i$ may still propose to; the outside option $\emptyset$ is always available and not stored);
--   2. for every agent $i$, the set $A_i\subseteq N_i$ of agents who have **applied** to $i$;
--   3. the current **matching** $\mu$, with $\mu(i)=\emptyset$ for an unmatched agent;
--   4. the stack $CC$ of agents waiting to be **compensated** (top of the stack first);
--   5. the number of rounds played so far.
--
--   The **initial state** has $B_i=N_i$ (the whole other side, acceptable or not), $A_i=\emptyset$, everyone unmatched, an empty stack and no round played, as in lines 1–3 of Algorithm 1.
--
--   **Formalization Note** The matching is stored from both sides (`mateM` for men, `mateW` for women); the budget-invariant milestone states that the two views agree along every run. The round counter is the paper's $k-1$, so the next proposer named by the order is $\Phi(\text{round})$. Physical time is the index of the run, not a field.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Algorithm 1, main block, lines 1–3, p. 8

import Mathlib

namespace DworczakDACC

/-- **The state of the DACC algorithm: budget sets, applicant sets, matching, CC stack, round.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017),
Algorithm 1, main block, lines 1–3, p. 8.

* `budM d ⊆ H`, `budW h ⊆ D`: the budget sets `B_i` (the outside option `∅` is always available
  and is not stored);
* `appM d ⊆ H`, `appW h ⊆ D`: the sets `A_i` of agents who have applied to `i`;
* `mateM d`, `mateW h`: the current matching `µ` seen from each side (`none` = unmatched, `µ(i) = ∅`);
* `stack`: the compensation-chain stack `CC`, head = top;
* `round`: the number of applications made so far by the agents `Φ(·)` named by the order
  (the paper's `k − 1`, so the next order-proposer is `Φ round` with 0-based `Φ`).

**Formalization Note.** The matching is stored from both sides; the budget-invariant milestone
(`budget_invariant`) asserts that the two views agree along every run. The paper's physical time
`t` is the index of the run (`run`), not a field. -/
structure State (D H : Type*) where
  /-- Budget set `B_d ⊆ W` of man `d`. -/
  budM : D → Finset H
  /-- Budget set `B_h ⊆ M` of woman `h`. -/
  budW : H → Finset D
  /-- `A_d`: the women who have applied to man `d`. -/
  appM : D → Finset H
  /-- `A_h`: the men who have applied to woman `h`. -/
  appW : H → Finset D
  /-- `µ(d)`; `none` is the outside option `∅`. -/
  mateM : D → Option H
  /-- `µ(h)`; `none` is the outside option `∅`. -/
  mateW : H → Option D
  /-- The stack `CC`; the head of the list is the top of the stack. -/
  stack : List (D ⊕ H)
  /-- Number of order-proposals made so far (the paper's `k − 1`). -/
  round : ℕ

/-- **The initial state of DACC** (Algorithm 1, main block, lines 1–3, p. 8): `B_i := N_i`
(every budget set is the whole other side), `A_i := ∅`, `µ := ∅` (everyone unmatched),
`CC := ∅`, and no round played yet. -/
def State.init (D H : Type*) [Fintype D] [Fintype H] : State D H where
  budM := fun _ => Finset.univ
  budW := fun _ => Finset.univ
  appM := fun _ => ∅
  appW := fun _ => ∅
  mateM := fun _ => none
  mateW := fun _ => none
  stack := []
  round := 0

end DworczakDACC


