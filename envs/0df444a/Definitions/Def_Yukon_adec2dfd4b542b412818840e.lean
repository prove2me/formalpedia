-- Prove2me | Definitions.Def_Yukon_adec2dfd4b542b412818840e
-- name    : Yukon_adec2dfd4b542b412818840e
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:03:22.606139+00:00
-- url     : https://prove2.me/theorems/b3fc1092-71f8-4841-a7aa-743ac8c88620
-- title:
--   YukonModule.PolyFun.PFunctor.Dynamical.Behavior.part0
-- statement:
--   Source module PolyFun.PFunctor.Dynamical.Behavior.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Dynamical/Behavior.lean
--
--   yukon-proof-operation:d0a9222507369c8985febcc736ab93ddb8a56d3d0a60821ba150dfd8e21b1d8c
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZDBhOTIyMjUwNzM2OWM4OTg1ZmViY2M3MzZhYjkzZGRiOGE1NmQzZDBhNjA4MjFiYTE1MGRmZDhlMjFiMWQ4YyIsImhhc2giOiJhNGY5ZDE2NzYzYTZjNTg1NDNiMjU3MjRmODc4OWQ2OGExNzA0MzJiMmI2M2JmNmI0N2QxYmI2MGI0MmQ2N2I1Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9hZGVjMmRmZDRiNTQyYjQxMjgxODg0MGUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Definitions.Def_Yukon_dbc5cc8253a92dbe9fea91bc

public import Definitions.Def_Yukon_f4aa983659c0ad198a975e5b



public import Mathlib.Data.PFunctor.Univariate.M
public import Init
public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Logic.Equiv.Prod
meta import Definitions.Def_Yukon_dbc5cc8253a92dbe9fea91bc
meta import Definitions.Def_Yukon_f4aa983659c0ad198a975e5b
set_option backward.isDefEq.respectTransparency.types false
/-!
# Closed-loop behaviour of Moore machines

Closing a Moore machine on itself with a feedback map `f : O → I`
(`MooreMachine.feedback`) yields an autonomous closed system that runs forever. Its
observable behaviour is the ℕ-indexed stream of outputs read off the iterated states.
This file ties the `feedback` combinator (the "pattern") to the `iterate` /
`trajectory` of the resulting closed system (the "matter" it runs on, in the
Niu–Spivak slogan).

* `MooreMachine.feedbackStep` — the closed-loop transition, equal to
  `(feedback f m).step` by `feedback_step`.
* `MooreMachine.feedbackStream` — the output stream of the closed-loop system.
* `MooreMachine.next_iterate_feedback` — its trajectory spine is the state iterate.
-/

@[expose] public section

universe u uO uI

namespace PFunctor

namespace MooreMachine

variable {S : Type u} {O : Type uO} {I : Type uI}

/-- The closed-loop transition: advance the state by feeding the current output back
through `f` as the next input. This is definitionally `(feedback f m).step` (see
`feedback_step`); it is phrased directly on `m` so the resulting stream's universes do
not depend on the phantom direction universe of the closed interface `X`. -/
def feedbackStep (f : O → I) (m : MooreMachine S O I) (st : S) : S :=
  m.transition st (f (m.output st))

/-- The output observed at time `n` once the machine is closed on itself by feeding
its output back through `f`: the original Moore output read off each closed-loop state. -/
def feedbackStream (f : O → I) (m : MooreMachine S O I) (st : S) (n : ℕ) : O :=
  m.output ((m.feedbackStep f)^[n] st)

@[simp] theorem feedbackStream_zero (f : O → I) (m : MooreMachine S O I) (st : S) :
    m.feedbackStream f st 0 = m.output st := rfl

/-- The closed-loop output stream advances by feeding the current output back as the
next input. -/
theorem feedbackStream_succ (f : O → I) (m : MooreMachine S O I) (st : S) (n : ℕ) :
    m.feedbackStream f st (n + 1) = m.feedbackStream f (m.transition st (f (m.output st))) n :=
  rfl

/-- The trajectory spine of the closed-loop system is the iterate of its states:
the closed system's "matter" is exactly its state stream. -/
theorem next_iterate_feedback (f : O → I) (m : MooreMachine S O I) (st : S) (n : ℕ) :
    (CofreeC.next)^[n] (DynSystem.trajectory (feedback f m) st)
      = DynSystem.trajectory (feedback f m) ((feedback f m).iterate st n) :=
  DynSystem.next_iterate_trajectory (feedback f m) st n

end MooreMachine

end PFunctor


