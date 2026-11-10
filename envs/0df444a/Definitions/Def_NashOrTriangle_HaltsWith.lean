-- Prove2me | Definitions.Def_NashOrTriangle_HaltsWith
-- name    : NashOrTriangle_HaltsWith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:48:27.558829+00:00
-- url     : https://prove2.me/theorems/741639c1-0f9b-46d4-8320-8fd60dfcff34
-- title:
--   The run halts in a state satisfying a property
-- statement:
--   The run of a program on a game, with a given oracle and input, **halts** (a halt instruction is executed) and the halted state satisfies a given property — typically bounds on the number of oracle calls and steps together with correctness of the answer. Halted states do not change, so the counters of the halted state are the totals of the run.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Theorem 2.1, pp.4–5 (PDF pp.5–6)

import Mathlib
import Definitions.Def_NashOrTriangle_OracleMachine

namespace NashOrTriangle

/-- The run of `P` on game `M` with oracle `adv` from input `x` halts (a `halt` instruction is
executed) and the halted state satisfies `Q`. Halted states stutter, so `Q` is evaluated on the
final state: its call counters and `work` are the totals of the run.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 2.1, printed pp. 4–5 (PDF pp. 5–6). -/
def HaltsWith {A B : Type*} (P : Program) (M : A → B → ℚ) {δ : ℝ} (adv : BRAdversary M δ)
    (x : ℤ → ℝ) (Q : State A B → Prop) : Prop :=
  ∃ n : ℕ, (run P M adv x n).output.isSome ∧ Q (run P M adv x n)

end NashOrTriangle


