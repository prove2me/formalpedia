-- Prove2me | Definitions.Def_ThreeSum19202796Base_17
-- name    : ThreeSum19202796Base_17
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-23T23:42:56.253213+00:00
-- url     : https://prove2.me/theorems/b42725ee-afc0-4e94-a92d-74ea6954036a
-- title:
--   3SUM base layer — Def_ThreeSum19202796Base_17
-- statement:
--   Base-layer declarations for the ternary 3SUM layer transplant from JoshuaQFEX/3sum-bound (Apache-2.0).
-- source:
--   https://github.com/JoshuaQFEX/3sum-bound (commit eda5da36565f) [Apache-2.0]

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
-- Recovery bundle: the Light tactic-layer proofs (Lang.Tactics) with Light tactics expanded
-- at call sites (the platform bans `macro` registration in submissions).

import Definitions.Def_ThreeSum19202796Base_15
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Tactics for proofs about programs

A proof about a program follows the text of the program from top to bottom.  The goal is always
`Ends lim P d s ⟨frame l, μ⟩ T Q`, and the statement at the head of `s` decides what comes next:

| the head of the program | what to write                  | what it is told                       |
|-------------------------|--------------------------------|---------------------------------------|
| `x := e`                | `(focus ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
      (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_))); refine Light.Ends.setToThen z` ?_ ?_ ?_; on_goal -1 => (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ])
  (first | omega | ((ring_nf); (omega)))
  (omega)
  (simp [] <;> (first | omega | ((ring_nf); (omega)))); on_goal -1 => (((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)); try (try with_unfolding_none refine Light.Ends.skip ?_))                  | the value `z` of `e`                  |
| `mem[a] := e`           | `(focus ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
      (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_))); refine Light.Ends.storeToThen b z` ?_ ?_ ?_; on_goal -1 => (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ])
  (first | omega | ((ring_nf); (omega)))
  (omega)
  (simp [] <;> (first | omega | ((ring_nf); (omega)))); on_goal -1 => (((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)); try (try with_unfolding_none refine Light.Ends.skip ?_))              | the address `b` and the value `z`     |
| `if c then … else …`    | `light_if h₁ h₂ : p`           | what the test says, and two names     |
| `x := p(args)`          | `(first | refine fact ?_ | apply fact) <;> (first | omega | ((ring_nf); (omega))) with …`       | what the procedure does (`Meets`)     |
| a piece with a lemma    | `light_piece fact with …`      | what the piece does (`Ends`)          |
| `skip`, nothing else    | `(try with_unfolding_none refine Light.Ends.skip ?_)`                   |                                       |
| a loop, nothing else    | `refine Ends.forFrame …`       | invariant and number of rounds        |
| a loop, then more       | `refine Ends.next _ (…)`       | the loop's rule with `(hT := le_rfl)` |

Each tactic works whether or not more program follows, hands the steps that are left to the rest of
the program, and proves the side conditions (the expressions stay within the limits and have the
values that were given, the time suffices) by `(((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))` and `(simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ])
  (first | omega | ((ring_nf); (omega)))
  (omega)
  (simp [] <;> (first | omega | ((ring_nf); (omega))))`.  What is left is the
goal about the rest of the program, or `Q` of the last state.  After `light_if` there are two goals,
first the one in which the test holds.  The patterns after `with` take apart, as those of `rintro`
do, what holds after the call or the piece.  Goals for holes `?_` in a `fact` come before the goal
about the rest of the program.

The side conditions are decided by linear arithmetic over the hypotheses in the context.
`light_facts H` puts the fields of a record `H` there.  What a side condition needs beyond that is
named after `using`: the content of a cell that is read, a definition to be unfolded, a running time
to be unfolded: `(focus ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
      (repeat
        with_unfolding_none
          first
          | refine Light.Ends.seqAssoc ?_
          | refine Light.Ends.skipThen ?_))); refine Light.Ends.setToThen K[j] ?_ ?_ ?_; on_goal -1 => (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hkey])
  (first | omega | ((ring_nf); (omega)))
  (omega)
  (simp [hkey] <;> (first | omega | ((ring_nf); (omega)))); on_goal -1 => (((try have := Light.Std.space_le (by assumption)));
    ((try have := Light.Std.const_le (by assumption)));
    (simp [Light.Limits.Addr, abs_le, -abs_mul, hkey] <;> omega)); try (try with_unfolding_none refine Light.Ends.skip ?_))`.

A program that is a definition is replaced by its text when a single statement is treated.  A
definition that stands at the head of a sequence stays closed: it is a piece, for `light_piece`.
-/

@[expose] public section

namespace Light

/-! ## Records -/

/-! ## One statement -/

end Light


