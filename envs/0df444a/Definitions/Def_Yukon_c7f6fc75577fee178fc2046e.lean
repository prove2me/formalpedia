-- Prove2me | Definitions.Def_Yukon_c7f6fc75577fee178fc2046e
-- name    : Yukon_c7f6fc75577fee178fc2046e
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:53:40.422974+00:00
-- url     : https://prove2.me/theorems/5ae15426-a635-4969-8b24-2f814553b750
-- title:
--   YukonModule.PolyFun.PFunctor.Handler.part0
-- statement:
--   Source module PolyFun.PFunctor.Handler.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Handler.lean
--
--   yukon-proof-operation:9c7fc2ed0a8591fd3cc367f1ddad987a7be244b78e8307ab6cff0066c654e110
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OWM3ZmMyZWQwYTg1OTFmZDNjYzM2N2YxZGRhZDk4N2E3YmUyNDRiNzhlODMwN2FiNmNmZjAwNjZjNjU0ZTExMCIsImhhc2giOiIyYzUyZDU4ZmM4ZWMyZjQ3ZTA2ODYxNGNhYTBhNmYyZmNiZmFjZGU2NjhkYjdmNTFmOGYxZDZjOTU1MzgyYzQ4Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9jN2Y2ZmM3NTU3N2ZlZTE3OGZjMjA0NmUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Definitions.Def_Yukon_e56a429acec69be6a69f4fcc



public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
meta import Definitions.Def_Yukon_e56a429acec69be6a69f4fcc
set_option backward.isDefEq.respectTransparency.types false
/-!
# Monadic Handlers for Polynomial Functors

A `PFunctor.Handler m q` chooses a direction of `q` at each position, with the
choice interpreted in the type constructor `m`. This is the generic interface
consumed by `FreeM.liftM`; it does not depend on machines or dynamical systems.
In particular, taking `m := StateT σ n` threads one shared runtime state through
every handled position. That ambient state is distinct from a dynamical
system's private operational state.
-/

@[expose] public section

universe u v uA uI

namespace PFunctor

/-- A **handler** for the interface `q`: a monadic choice of direction at each
position (a Kleisli section of `q`). With `m := Id` this is an ordinary
dependent choice of one direction at every position, while a probabilistic
monad gives a randomized choice. -/
abbrev Handler (m : Type u → Type v) (q : PFunctor.{uA, u}) :=
  (a : q.A) → m (q.B a)

namespace Handler

/-- An effectful stateful handler for `q`: on each position it reads a state,
performs effects in `m`, and returns a direction together with the next state.

This is a transparent name for `Handler (StateT S m) q`, so it introduces no
new data or laws. At `m := Id` it is the pure Kleisli--Mealy presentation used
by `Responder.equivStateHandler`. -/
abbrev Stateful (m : Type u → Type v) (S : Type u)
    (q : PFunctor.{uA, u}) :=
  Handler (StateT S m) q

/-- Combine monadic handlers for an indexed family into a handler for its
indexed coproduct. -/
def sigma {I : Type uI} {P : I → PFunctor.{uA, u}} {m : Type u → Type v}
    (f : (i : I) → PFunctor.Handler m (P i)) : PFunctor.Handler m (PFunctor.sigma P) :=
  fun a => f a.1 a.2

@[simp]
theorem sigma_apply {I : Type uI} {P : I → PFunctor.{uA, u}} {m : Type u → Type v}
    (f : (i : I) → PFunctor.Handler m (P i)) (i : I) (a : (P i).A) : sigma f ⟨i, a⟩ = f i a :=
  rfl

end Handler

end PFunctor


