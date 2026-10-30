-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_halveLoop
-- name    : ConsensusHalvingItems_Additive_halveLoop
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:32:42.178339+00:00
-- url     : https://prove2.me/theorems/40b2ad64-489c-41f3-b69f-8a4124cd9808
-- title:
--   The while loop of Step 3
-- statement:
--   The while loop of Step 3: starting from a state $(T, x)$, it repeats the iteration of Step 3 until the test finds no solution of $S \cup T$ other than $x$, and then outputs $x$ (Step 4). Each iteration charges one tick.
--
--   **Formalization Note** The loop is written with a fuel parameter (a bound on the number of iterations) so that it is a terminating recursion; when the fuel is exhausted it returns the current point. The algorithm calls it with fuel $m + 1$, which is never exhausted because each iteration adds a new item to $T$. No statement of the mission assumes anything about the fuel.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, Steps 3 and 4, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_tick
import Definitions.Def_ConsensusHalvingItems_Additive_loopStep

namespace ConsensusHalvingItems.Additive

/-- **The while loop of Step 3, with fuel.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, Steps 3 and 4, p. 5: "While there exists a
solution (y1, . . . , ym) ≠ (x1, . . . , xm) to S ∪ T, do the following: …", "4. Output
(x1, . . . , xm)."

`halveLoop u fuel T x`: with fuel `0` it returns `x`; with fuel `f + 1` it ticks once and runs
`loopStep u T x`; on `none` (no other solution of S ∪ T) it returns `x` (Step 4), and on
`some (T', x')` it continues from `(T', x')` with fuel `f`.

**Formalization Note.** The fuel makes the recursion structural. `halve` calls the loop with fuel
`m + 1`; every iteration adds a new index to `T ⊆ Fin m` (milestone `loopStep_freezes`), so the
fuel is never exhausted before the loop ends. No statement of the mission assumes anything about
the fuel. -/
def halveLoop {n m : ℕ} (u : Fin n → Fin m → ℚ) :
    ℕ → Finset (Fin m) → (Fin m → ℚ) → StateM ℕ (Fin m → ℚ)
  | 0, _, x => pure x
  | f + 1, T, x => do
    tick 1
    match ← loopStep u T x with
    | none => pure x
    | some (T', x') => halveLoop u f T' x'

end ConsensusHalvingItems.Additive


