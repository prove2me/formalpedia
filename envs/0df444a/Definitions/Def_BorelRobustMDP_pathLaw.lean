-- Prove2me | Definitions.Def_BorelRobustMDP_pathLaw
-- name    : BorelRobustMDP_pathLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:18.685194+00:00
-- url     : https://prove2.me/theorems/98e48ce1-bda9-482f-9d6f-e66aaacdb4a3
-- title:
--   The law of motion (2.4) by forward composition, and the path cost
-- statement:
--   Starting from a path of length $m$ at calendar time $n$, the path law after $j$ further transitions is built forwards: draw the action from its law, draw the disturbance from its law, and move to $T_{n+j}(x,a,z)$. The path cost is the accumulated one-stage cost $\sum_{i<j}c_{n+i}(X_i,A_i,X_{i+1})$, and the total cost adds the terminal cost $c_N$ of the last state.
--
--   These are the finite-horizon form of the Ionescu–Tulcea measure (2.4) and the cost in (2.5).
--
--   **Formalization Note.** The construction uses `Measure.bind`, so it does not presuppose Lemma 2.4; `bind` is $0$ on a non-measurable family, and Lemma 3.3 states that the laws of policy pairs are probability measures.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, (2.3)–(2.5), p.5

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_RobustModel

open MeasureTheory
open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- The law of motion by forward composition (Bäuerle & Glauner, arXiv:2007.13103v1, (2.3)–(2.4),
p.5): starting from a path `h` of length `m` at calendar time `n`, the law of the path after `j`
further transitions. At step `j` the action has law `act j h'`, the disturbance has law
`nat j (h', a)`, and the next state is `T_{n+j}(x, a, z)`.

**Formalization Note.** This is the finite Ionescu-Tulcea measure, written with `Measure.bind` so that
the definition does not depend on Lemma 2.4. `bind` is `0` on a non-measurable family; Lemma 3.3
states that the laws of policy pairs are probability measures. No value function or operator enters
here. -/
noncomputable def pathLaw (R : RobustModel E A Z N) (m n : ℕ)
    (act : (j : ℕ) → Hist E A (m + j) → Measure A)
    (nat : (j : ℕ) → Hist E A (m + j) × A → Measure Z)
    (h : Hist E A m) : (j : ℕ) → Measure (Hist E A (m + j))
  | 0 => Measure.dirac h
  | j + 1 => (pathLaw R m n act nat h j).bind fun h' =>
      (act j h').bind fun a =>
        (nat j (h', a)).map fun z =>
          ((h', a, R.T (n + j) (histState (m + j) h', a) z) : Hist E A (m + j + 1))

/-- The accumulated one-stage cost `Σ_{i<j} c_{n+i}(X_i, A_i, X_{i+1})` along the `j` transitions
after a path of length `m`, at calendar times `n, n + 1, …`. -/
noncomputable def pathCost (R : RobustModel E A Z N) (m n : ℕ) :
    (j : ℕ) → Hist E A (m + j) → ℝ
  | 0, _ => 0
  | j + 1, h =>
      let w : Hist E A (m + j) × A × E := h
      pathCost R m n j w.1 + R.c (n + j) (histState (m + j) w.1, w.2.1) w.2.2

/-- The cost in (2.5) (Bäuerle & Glauner, arXiv:2007.13103v1, p.5): accumulated one-stage cost plus
terminal cost of the final state of the path. -/
noncomputable def totalCost (R : RobustModel E A Z N) (m n j : ℕ) (h : Hist E A (m + j)) : ℝ :=
  pathCost R m n j h + R.cN (histState (m + j) h)

end BorelRobustMDP


