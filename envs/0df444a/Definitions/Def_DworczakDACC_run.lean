-- Prove2me | Definitions.Def_DworczakDACC_run
-- name    : DworczakDACC_run
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:50.713302+00:00
-- url     : https://prove2.me/theorems/c497f50d-a788-4791-8d69-a6408dbae9a0
-- title:
--   The run of DACC($\Phi$): the state after $t$ passes of the main loop
-- statement:
--   The **run** of DACC($\Phi$) is the sequence of states $s_0,s_1,s_2,\dots$ with $s_0$ the initial state and $s_{t+1}$ obtained from $s_t$ by one pass of the main loop, in which the order of blocks (a) and (b) of "$i$ applies" is $\operatorname{ord}(t)$.
--
--   Once the stopping criterion holds, every later state equals the stopped state.
--
--   **Formalization Note** Time is $0$-based: $s_t$ is the state at the paper's time $t+1$. The run is a total function of time; freezing it after the stop encodes the exit of the while loop. The parameter $\operatorname{ord}:\mathbb N\to\{\text{true},\text{false}\}$ is footnote a's freedom to execute (a) and (b) "in any order, even random".
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Algorithm 1, p. 8

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_State
import Definitions.Def_DworczakDACC_step

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **The run of DACC(Φ): the state after `t` passes of the main loop.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017),
Algorithm 1, p. 8 (the counter `t` "keeps track of time").

`run Mk Φ ord 0` is the initial state (`State.init`) and `run Mk Φ ord (t + 1)` is one pass of
the loop from `run Mk Φ ord t`, with blocks (a)/(b) of "i applies" in the order `ord t`.

**Formalization Note.** Time is 0-based: `run … t` is the state at the paper's time `t + 1`
(before the `(t+1)`-th pass). The run is a total function of time: once the stopping criterion
holds, `step` returns its argument, so the state is frozen (the while loop has exited).
`ord : ℕ → Bool` is footnote a's freedom to execute (a) and (b) "in any order, even random",
fixed per time step. -/
def run (Mk : Market D H) (Φ : ℕ → D ⊕ H) (ord : ℕ → Bool) : ℕ → State D H
  | 0 => State.init D H
  | t + 1 => step Mk Φ (ord t) (run Mk Φ ord t)

end DworczakDACC


