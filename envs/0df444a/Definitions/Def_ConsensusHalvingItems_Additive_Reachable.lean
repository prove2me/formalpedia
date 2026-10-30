-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_Reachable
-- name    : ConsensusHalvingItems_Additive_Reachable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:34:56.308424+00:00
-- url     : https://prove2.me/theorems/1f9bbcb2-8d08-4f7a-8887-108e5c41f2d9
-- title:
--   States of the algorithm's loop
-- statement:
--   The states of the while loop of Step 3 are pairs $(T, x)$ of a frozen set and a point. The start state is $(\emptyset, (1/2, \dots, 1/2))$, and every state obtained from a reachable state by one iteration of Step 3 is reachable. These are the states the algorithm constructs; the invariants of the paper's proof are statements about them.
--
--   **Formalization Note** An inductive predicate; iterations are run with the tick counter started at $0$, which does not affect their result.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, Steps 1–3, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_loopStep

namespace ConsensusHalvingItems.Additive

/-- **The states of the algorithm's loop.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, Steps 1–3, p. 5: the loop starts from
"x1 = x2 = · · · = xm = 1/2" and "T = ∅" and each execution of Step 3 updates `x` and `T`.

`Reachable u (T, x)` holds for the start state `(∅, x ≡ 1/2)` and for every state obtained from
a reachable state by one iteration `loopStep` that returns `some (T', x')`.

**Formalization Note.** The iteration is run from tick `0`; its result does not depend on the
start value of the counter. These are exactly the states the page constructs: statements about
the loop quantify over them, not over arbitrary pairs `(T, x)`. -/
inductive Reachable {n m : ℕ} (u : Fin n → Fin m → ℚ) : Finset (Fin m) × (Fin m → ℚ) → Prop
  | init : Reachable u (∅, fun _ => 1 / 2)
  | step {T T' : Finset (Fin m)} {x x' : Fin m → ℚ} :
      Reachable u (T, x) → ((loopStep u T x).run 0).1 = some (T', x') → Reachable u (T', x')

end ConsensusHalvingItems.Additive


