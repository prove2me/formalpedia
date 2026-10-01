-- Prove2me | Definitions.Def_Yukon_1ba351e678ec6ebc0aa89b54
-- name    : Yukon_1ba351e678ec6ebc0aa89b54
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:58:39.335547+00:00
-- url     : https://prove2.me/theorems/96624247-b44d-4255-87c0-8ef0c787eb38
-- title:
--   YukonModule.PolyFun.PFunctor.Free.Resumption.part0
-- statement:
--   Source module PolyFun.PFunctor.Free.Resumption.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Free/Resumption.lean
--
--   yukon-proof-operation:659b63718a94791e5d723f9424f16345313d2a6a44e96c23c9624b950ae4f5af
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NjU5YjYzNzE4YTk0NzkxZTVkNzIzZjk0MjRmMTYzNDUzMTNkMmE2YTQ0ZTk2YzIzYzk2MjRiOTUwYWU0ZjVhZiIsImhhc2giOiI0NTFhNzNlNGEzODQ5NmJiYTM0NGVlNjE2YThlNWU3NDYyODBmZTRkMTVkZWYxZjgyZmFlN2Q2ODE0YWMzMWJlIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8xYmEzNTFlNjc4ZWM2ZWJjMGFhODliNTQiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Definitions.Def_Yukon_724dee21e2f24de1aadc0f0e

public import Definitions.Def_Yukon_23b15ee82bcbbb99402b2172



public import Mathlib.Data.PFunctor.Univariate.M
public import Init
public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
meta import Definitions.Def_Yukon_724dee21e2f24de1aadc0f0e
meta import Definitions.Def_Yukon_23b15ee82bcbbb99402b2172
set_option backward.isDefEq.respectTransparency.types false
/-!
# Embedding finite free programs into resumptions

This module contains the canonical inclusion of the initial-algebra
`FreeM p β` into the final-coalgebra `Resumption p β`. Keeping the bridge
above both foundational modules lets the base resumption API remain
independent of the free-monad layer.
-/

@[expose] public section

universe uA uB uA₂ uB₂ uα uβ

namespace PFunctor.FreeM

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ}

/-- Embed a finite free program into the corresponding tau-free resumption. -/
def toResumption : FreeM p α → Resumption p α
  | .pure value => Resumption.pure value
  | .liftBind position next =>
      Resumption.query position fun direction => toResumption (next direction)

@[simp] theorem toResumption_pure (value : α) :
    toResumption (pure value : FreeM p α) = Resumption.pure value := rfl

@[simp] theorem toResumption_liftBind (position : p.A)
    (next : p.B position → FreeM p α) :
    toResumption ((FreeM.lift position).bind next) =
      Resumption.query position fun direction => toResumption (next direction) := rfl

theorem dest_toResumption_pure (value : α) :
    Resumption.dest (toResumption (pure value : FreeM p α)) = Sum.inl value := rfl

theorem dest_toResumption_liftBind (position : p.A)
    (next : p.B position → FreeM p α) :
    Resumption.dest (toResumption (FreeM.liftBind position next)) =
      Sum.inr ⟨position, fun direction => toResumption (next direction)⟩ := by
  rw [FreeM.liftBind_eq, toResumption_liftBind, Resumption.dest_query]

@[simp] theorem toResumption_bind (program : FreeM p α) (k : α → FreeM p β) :
    toResumption (FreeM.bind program k) =
      Resumption.bind (toResumption program) (fun value => toResumption (k value)) := by
  induction program with
  | pure value =>
      change toResumption (k value) =
        Resumption.bind (Resumption.pure value) (fun result => toResumption (k result))
      rw [Resumption.bind_pure_left]
  | lift_bind position next ih =>
      change toResumption
          (FreeM.liftBind position (fun direction => FreeM.bind (next direction) k)) =
        Resumption.bind
          (Resumption.query position fun direction => toResumption (next direction))
          (fun value => toResumption (k value))
      rw [FreeM.liftBind_eq, toResumption_liftBind, Resumption.bind_query]
      congr 1
      funext direction
      exact ih direction

@[simp] theorem toResumption_map (f : α → β) (program : FreeM p α) :
    toResumption (FreeM.map f program) = Resumption.map f (toResumption program) := by
  induction program with
  | pure value =>
      change Resumption.pure (f value) = Resumption.map f (Resumption.pure value)
      rw [Resumption.map_pure]
  | lift_bind position next ih =>
      change toResumption
          (FreeM.liftBind position (fun direction => FreeM.map f (next direction))) =
        Resumption.map f
          (Resumption.query position fun direction => toResumption (next direction))
      rw [FreeM.liftBind_eq, toResumption_liftBind, Resumption.map_query]
      congr 1
      funext direction
      exact ih direction

@[simp] theorem toResumption_mapLens {q : PFunctor.{uA₂, uB₂}}
    (lens : Lens p q) (program : FreeM p α) :
    toResumption (program.mapLens lens) =
      Resumption.mapLens lens (toResumption program) := by
  induction program with
  | pure value => simp
  | lift_bind position next ih =>
      rw [FreeM.mapLens_lift_bind, toResumption_liftBind]
      change Resumption.query (lens.toFunA position)
          (fun direction => toResumption
            ((next (lens.toFunB position direction)).mapLens lens)) =
        Resumption.mapLens lens
          (Resumption.query position fun direction => toResumption (next direction))
      rw [Resumption.mapLens_query]
      congr 1
      funext direction
      exact ih (lens.toFunB position direction)

/-- The finite-program embedding is injective: regarding a well-founded tree
as a possibly infinite tree loses no information. -/
theorem toResumption_injective : Function.Injective (toResumption (p := p) (α := α)) := by
  intro left
  induction left with
  | pure value =>
      intro right h
      cases right with
      | pure value' =>
          have hdest := congrArg Resumption.dest h
          simp only [dest_toResumption_pure] at hdest
          cases hdest
          rfl
      | liftBind position next =>
          have hdest := congrArg Resumption.dest h
          change Sum.inl value = Sum.inr
            (Sigma.mk position (fun direction => toResumption (next direction)) :
              p.Obj (Resumption p α)) at hdest
          exact (Sum.inl_ne_inr hdest).elim
  | lift_bind position next ih =>
      intro right h
      cases right with
      | pure value =>
          have hdest := congrArg Resumption.dest h
          change (Sum.inr
            (Sigma.mk position (fun direction => toResumption (next direction)) :
              p.Obj (Resumption p α))) =
            Sum.inl value at hdest
          exact (Sum.inr_ne_inl hdest).elim
      | liftBind position' next' =>
          have hdest := Sum.inr.inj (congrArg Resumption.dest h)
          have hposition : position = position' := (Sigma.mk.inj hdest).1
          cases hposition
          have hnext : (fun direction => toResumption (next direction)) =
              fun direction => toResumption (next' direction) :=
            eq_of_heq (Sigma.mk.inj hdest).2
          apply congrArg (FreeM.liftBind position)
          funext direction
          exact ih direction (congrFun hnext direction)

section MonadHom

variable {p : PFunctor.{uA, uB}}

/-- The finite-program embedding as a monad homomorphism. -/
def toResumptionHom : FreeM p →ᵐ Resumption p where
  toFun _ := toResumption
  toFun_pure' _ := rfl
  toFun_bind' := toResumption_bind

@[simp] theorem toResumptionHom_apply (program : FreeM p α) :
    toResumptionHom program = toResumption program := rfl

end MonadHom

end PFunctor.FreeM


