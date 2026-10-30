-- Prove2me | Definitions.Def_NisanRonen_Rounding_IsValid
-- name    : NisanRonen_Rounding_IsValid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:20:18.502487+00:00
-- url     : https://prove2.me/theorems/1a5721b5-7f32-4e97-9655-84257f675278
-- title:
--   Admissible strategy in the bounded problem
-- statement:
--   Let $0 < a < b$ and let agent $i$ have type $t^i \in [a,b]^k$. A strategy $(d^i, e^i)$ is **admissible** for agent $i$ if
--
--   1. its declaration lies in the type space: $a \le d^i_j \le b$ for every task $j$;
--   2. it never performs an allocated task faster than possible: for every allocation $x$ and every task $j \in x^i$, $e^i(x)_j \ge t^i_j$.
--
--   Entries of $e^i(x)$ for tasks not allocated to $i$ are unconstrained and never used.
--
--   **Formalization Note** Declarations range over the bounded type space $[a,b]^k$ of the bounded scheduling problem.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 20, p. 187 (PDF p. 22): "An agent may lie or choose to perform any task j allocated to it, in any time t̃_j ≥ t^i_j"; Definition 33, p. 192 (PDF p. 27): "a ≤ t^i_j ≤ b"; Definition 19, p. 186

import Mathlib
import Definitions.Def_NisanRonen_Rounding_Strategy

namespace NisanRonen.Rounding

/-- **Admissible strategy of agent `i` of type `t^i` in the bounded problem** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001),
Definition 20, p. 187: "An agent may lie or choose to perform any task j allocated to it, in any
time t̃_j ≥ t^i_j"; Definition 33, p. 192: types satisfy `a ≤ t^i_j ≤ b`).

The declaration lies in the type space `[a, b]^k`, and for every decision `x` every task
allocated to `i` is executed in time at least `t^i_j`.

**Formalization Note** Declarations range over the bounded type space `[a, b]^k` of
Definition 33 (Definition 19: "The agents' declarations are simply to report their types").
Unallocated entries of `exec x` are unconstrained and never used. -/
def IsValid {n k : ℕ} (a b : ℝ) (ti : Fin k → ℝ) (i : Fin n) (σ : Strategy n k) : Prop :=
  (∀ j, a ≤ σ.decl j ∧ σ.decl j ≤ b) ∧ ∀ (x : Fin k → Fin n) (j : Fin k), x j = i → ti j ≤ σ.exec x j

end NisanRonen.Rounding


