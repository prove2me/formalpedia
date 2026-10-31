-- Prove2me | Definitions.Def_DworczakDACC_step
-- name    : DworczakDACC_step
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:40.521367+00:00
-- url     : https://prove2.me/theorems/c0684558-5f39-46cf-93ad-83b97ad7dff9
-- title:
--   One pass of the DACC main loop (corrected stack exit)
-- statement:
--   One pass of the main loop of DACC($\Phi$), from a state $s$:
--
--   1. if $s$ satisfies the stopping criterion, the loop has exited and $s$ is unchanged;
--   2. otherwise, if the stack $CC$ is empty, the agent $\Phi(k)$ of the current round $k$ applies, the round counter increases by one, and the agents pushed during the application form the new stack;
--   3. otherwise the agent $i$ on top of $CC$ applies; the agents pushed during the application are placed on top of $i$; and $i$ is removed from $CC$ if afterwards $\mu(i)\neq\emptyset$ or **no acceptable partner is left in $B_i$**.
--
--   An order-proposer who skips (already holds its best option, or has no acceptable partner left) still uses up its round.
--
--   **Formalization Note** Correction of Algorithm 1, step 4(b)iii: the printed exit test is "$\mu(i)\ne\emptyset$ or $B_i=\emptyset$". Budget sets start as the whole other side and an agent never proposes to an unacceptable partner, so unacceptable partners never leave $B_i$; under the printed test a compensated agent with no acceptable partner left applies to $\emptyset$ forever and DACC need not stop (the mission description gives a three-by-three counterexample). The corrected test, "$\arg\max\{B_i\cup\{\emptyset\};\succ^i\}=\emptyset$", is the paper's own convention (footnote 7, "if there are no acceptable partners in $i$'s budget set, we skip"), and coincides with the printed one when every partner is acceptable. A Boolean parameter resolves the (a)/(b) order of "$i$ applies".
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Algorithm 1, main block, line 4 (a)–(c), p. 8 (step 4(b)iii corrected)

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_State
import Definitions.Def_DworczakDACC_bestM
import Definitions.Def_DworczakDACC_bestW
import Definitions.Def_DworczakDACC_Stopped
import Definitions.Def_DworczakDACC_applies

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **One pass of the main loop of DACC(Φ), with the stack exit corrected.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017),
Algorithm 1, main block, line 4, p. 8:

* while `∃ i ∈ N, µ(i) ≺ⁱ argmax{Bᵢ; ≻ⁱ}`:
  (a) if `CC = ∅`: `i := Φ(k)`; `i` applies; `k := k + 1`;
  (b) else: `i :=` the top of `CC`; `i` applies; if `µ(i) ≠ ∅` or [corrected] `i` has no
      acceptable partner left in `Bᵢ`, remove `i` from `CC`;
  (c) `t := t + 1`.

`step Mk Φ ab s`: if the stopping criterion holds in `s` the loop has exited and `s` is returned
unchanged. Otherwise, with an empty stack the order-proposer `Φ s.round` applies, the round
counter increases and the agents pushed during the application form the new stack; with a
non-empty stack `i :: rest` the top agent `i` applies, the agents pushed during the application
land on top of `i`, and the entry `i` is removed when `i` is matched afterwards or the best option
of its budget set is `∅`. `ab` resolves the order of blocks (a)/(b) of "i applies".

**Formalization Note.** Correction of step 4(b)iii: the printed exit test "µ(i) ≠ ∅ or Bᵢ = ∅"
is replaced by "µ(i) ≠ ∅ or argmax{Bᵢ ∪ {∅}; ≻ⁱ} = ∅". Budget sets start as the whole other
side and unacceptable partners never leave them, so under the printed test a compensated agent
with no acceptable partner left stays on top of `CC` forever and DACC need not stop (counterexample
in the mission description). The paper's own convention (procedure step 2, footnote 7: "if there
are no acceptable partners in i's budget set, we skip") gives the corrected test, and the two
coincide when every partner is acceptable. A skipped order-proposal still uses up its round. -/
def step (Mk : Market D H) (Φ : ℕ → D ⊕ H) (ab : Bool) (s : State D H) : State D H :=
  if Stopped Mk s then s else
  match s.stack with
  | [] =>
    let r := applies Mk ab (Φ s.round) s
    { r.1 with stack := r.2, round := s.round + 1 }
  | i :: rest =>
    let r := applies Mk ab i s
    let done : Bool :=
      match i with
      | Sum.inl d => (r.1.mateM d).isSome || (bestM Mk d (r.1.budM d)).isNone
      | Sum.inr h => (r.1.mateW h).isSome || (bestW Mk h (r.1.budW h)).isNone
    { r.1 with stack := r.2 ++ (if done then rest else i :: rest) }

end DworczakDACC


