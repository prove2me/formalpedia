-- Prove2me | Definitions.Def_RotationLadder_Protocol_ladderLevel
-- name    : RotationLadder_Protocol_ladderLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:37.630305+00:00
-- url     : https://prove2.me/theorems/6e6be8d4-8a6d-4894-81f4-264fc332b015
-- title:
--   The ladder walk of Fig. 3
-- statement:
--   The ladder walk records the level held after $t$ copies of $|H\rangle$ have been consumed. It starts at $L_0=-1$, meaning that no state is held. From $-1$ the next copy gives level $0$. From a level $L\ge0$ the next copy gives
--
--   $$L_{t+1}=\begin{cases}L_t+1&\text{if }u_t<p_{0,L_t},\\ L_t-1&\text{otherwise.}\end{cases}$$
--
--   **Formalization Note** Level $-1$ stands for the discarded stabilizer state. One copy is needed to leave it, which gives the paper's accounting: two copies at the first node, and two new copies after outcome 1 at the first node.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 3 and Fig. 3

import Mathlib
import Definitions.Def_RotationLadder_Protocol_LadderTape
import Definitions.Def_RotationLadder_Protocol_ladderProb

namespace RotationLadder.Protocol

/-- **The ladder walk of Fig. 3.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, p. 3: "Every time a step is taken along this ladder of states, one copy of `|H⟩` is
consumed, except at the first node of the ladder (the production of state `|H_0⟩`) when we require
two copies of `|H⟩`: if the outcome 1 is measured at the first node, we discard the output and
start with two new copies of `|H⟩`."

`ladderLevel u t` is the level held after `t` copies of `|H⟩` have been consumed. Level `-1` means
that no state is held. From `-1` the next copy gives `|H_0⟩`. From level `L ≥ 0` the next copy goes
up with probability `p_(0,L)` and down otherwise.

**Formalization Note.** Level `-1` is the discarded `|H_(-1)⟩`. Taking one copy to leave it gives
two copies for the first node and two new copies after a failure at the first node, as the paper
says, and `Cost+=2` in Fig. 3. `toNat` is applied only to `L ≠ -1`; the walk never goes below `-1`.
-/
noncomputable def ladderLevel (u : LadderTape) : ℕ → ℤ
  | 0 => -1
  | t + 1 =>
    if ladderLevel u t = -1 then 0
    else if ((u t : unitInterval) : ℝ) < ladderProb (ladderLevel u t).toNat then
      ladderLevel u t + 1
    else ladderLevel u t - 1

end RotationLadder.Protocol


