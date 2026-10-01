-- Prove2me | Definitions.Def_Yukon_dec25d5b26c5465c24348b33
-- name    : Yukon_dec25d5b26c5465c24348b33
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:03:30.26946+00:00
-- url     : https://prove2.me/theorems/75843ec8-bebf-4d9f-bcbc-075b2714d517
-- title:
--   YukonModule.PolyFun.PFunctor.Free.Path.Execution.part0
-- statement:
--   Source module PolyFun.PFunctor.Free.Path.Execution.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Free/Path/Execution.lean
--
--   yukon-proof-operation:ff3d913e3945cb1d7c80d2aa12d977f0dfecbc0b989c5be0e5db8f06548b41ef
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZmYzZDkxM2UzOTQ1Y2IxZDdjODBkMmFhMTJkOTc3ZjBkZmVjYmMwYjk4OWM1YmUwZTVkYjhmMDY1NDhiNDFlZiIsImhhc2giOiIxNTBjNTc3MjU0OGEyM2I5ZGFkODY4ZjY2MzMyNTZiZGU0MzJlZmUyNTExNjNhNTVjYjQ0MTJhMDZhZTRjYzY0Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9kZWMyNWQ1YjI2YzU0NjVjMjQzNDhiMzMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Definitions.Def_Yukon_5f72f990f3206a29ca7cf412

public import Definitions.Def_Yukon_66130de5114377d74318aca2



public import Batteries.Tactic.Lint
public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
meta import Definitions.Def_Yukon_5f72f990f3206a29ca7cf412
meta import Definitions.Def_Yukon_66130de5114377d74318aca2
set_option backward.isDefEq.respectTransparency.types false
/-!
# Executing paths through free polynomial programs

This file equips a free polynomial program with its canonical path-producing
execution and erases completed paths to polynomial traces. The constructions
are structural and independent of any interpretation of the polynomial.
-/

@[expose] public section

universe uA uB v w

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- Execute a free program while returning the typed path selected by the
answers received during that execution. -/
def withPath : (program : FreeM P α) → FreeM P (Path program)
  | .pure _ => pure ⟨⟩
  | .liftBind a next =>
      FreeM.liftBind a fun answer =>
        FreeM.map (fun path : Path (next answer) =>
          (⟨answer, path⟩ : Path (FreeM.liftBind a next))) (withPath (next answer))

@[simp] theorem withPath_pure (x : α) :
    withPath (pure x : FreeM P α) = pure ⟨⟩ := rfl

@[simp] theorem withPath_liftBind (a : P.A) (next : P.B a → FreeM P α) :
    withPath ((FreeM.lift a).bind next) =
      FreeM.liftBind a fun answer =>
        FreeM.map (fun path : Path (next answer) =>
          (⟨answer, path⟩ : Path (FreeM.liftBind a next))) (withPath (next answer)) := rfl

/-- Forget the dependent path returned by `withPath`, retaining the selected
leaf payload. This recovers the original program exactly. -/
@[simp] theorem map_output_withPath : (program : FreeM P α) →
    FreeM.map (output program) (withPath program) = program
  | .pure _ => rfl
  | .liftBind a next => by
      simp only [withPath, FreeM.map]
      apply congrArg (FreeM.liftBind a)
      funext answer
      rw [← FreeM.comp_map]
      exact map_output_withPath (next answer)

/-- Binding after path execution exposes the root answer and tail path
without leaving a dependent `map` in the term. -/
theorem withPath_liftBind_bind {γ : Type w} (a : P.A)
    (next : P.B a → FreeM P α)
    (k : Path (FreeM.liftBind a next) → FreeM P γ) :
    FreeM.bind (withPath (FreeM.liftBind a next)) k =
      FreeM.liftBind a fun answer =>
        FreeM.bind (withPath (next answer)) fun suffix =>
          k (⟨answer, suffix⟩ : Path (FreeM.liftBind a next)) := by
  change FreeM.liftBind a (fun answer =>
      FreeM.bind
        (FreeM.map (fun path : Path (next answer) =>
          (⟨answer, path⟩ : Path (FreeM.liftBind a next)))
          (withPath (next answer))) k) = _
  apply congrArg (FreeM.liftBind a)
  funext answer
  rw [← FreeM.bind_pure_comp, FreeM.bind_assoc]
  rfl

namespace Path

/-- Erase a typed path to the universal list of polynomial events. -/
def trace : (program : FreeM P α) → Path program → PFunctor.TraceList P
  | .pure _, _ => []
  | .liftBind a next, ⟨answer, tail⟩ =>
      ⟨a, answer⟩ :: trace (next answer) tail

@[simp] theorem trace_pure (x : α) (path : Path (pure x : FreeM P α)) :
    trace (pure x) path = [] := rfl

@[simp] theorem trace_liftBind (a : P.A) (next : P.B a → FreeM P α)
    (answer : P.B a) (tail : Path (next answer)) :
    trace ((FreeM.lift a).bind next) ⟨answer, tail⟩ =
      ⟨a, answer⟩ :: trace (next answer) tail := rfl

end Path

end PFunctor.FreeM


