-- Prove2me | Definitions.Def_Yukon_d5677f095c6f5bc42a19ec97
-- name    : Yukon_d5677f095c6f5bc42a19ec97
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:12:21.831998+00:00
-- url     : https://prove2.me/theorems/f6974ee7-ad6d-44e2-a5aa-f1b9c77f83f3
-- title:
--   YukonModule.PolyFun.PFunctor.Handler.Normalization.part0
-- statement:
--   Source module PolyFun.PFunctor.Handler.Normalization.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Handler/Normalization.lean
--
--   yukon-proof-operation:29cdf9ee8cbeaa6e0c59bdbb464437fa46cef5e675cc08566f9975a4114fff2f
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MjljZGY5ZWU4Y2JlYWE2ZTBjNTliZGJiNDY0NDM3ZmE0NmNlZjVlNjc1Y2MwODU2NmY5OTc1YTQxMTRmZmYyZiIsImhhc2giOiI3ZmE1ZWRmMzFmMzNkZDcwMjA2ZDFhNTM4ZmY3Y2I1NTAxMTI0OThjZTU2ZGFhMTkzNWQ2ZjdkNmQwOGEzMzMwIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9kNTY3N2YwOTVjNmY1YmM0MmExOWVjOTciLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Mathlib.Control.Monad.Writer
public import Definitions.Def_Yukon_93f1119fb1dbe077a1e685c4



public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Init
public import Lean.Message
public import Batteries.Tactic.Lint.Basic
public import Batteries.Tactic.Lint
public import Mathlib.CategoryTheory.Monad.Types
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
meta import Definitions.Def_Yukon_93f1119fb1dbe077a1e685c4
set_option backward.isDefEq.respectTransparency.types false
/-!
# Handler normalization

The `handler_nf` simp set exposes the next structural layer of a free or
stateful handler computation. It unfolds `FreeM.liftM`,
`PFunctor.Handler.Stateful.run`, and the standard `StateT` and `WriterT`
run operations without importing a tactic framework.

Use `simp only [handler_nf]` when a proof needs a stable, explicit handler
normal form. Downstream libraries can extend the set with equations for their
own handler combinators.
-/

@[expose] public section

attribute [handler_nf]
  PFunctor.FreeM.liftM_pure
  PFunctor.FreeM.liftM_lift_bind
  PFunctor.FreeM.liftM_bind
  PFunctor.FreeM.liftM_lift
  PFunctor.Handler.Stateful.run_pure
  PFunctor.Handler.Stateful.run_lift
  PFunctor.Handler.Stateful.run_liftBind
  PFunctor.Handler.Stateful.run_bind
  PFunctor.Handler.Stateful.reindex_apply
  StateT.run_bind
  StateT.run_get
  StateT.run_set
  StateT.run_modifyGet
  StateT.run_pure
  StateT.run_monadLift
  WriterT.run_bind
  WriterT.run_map
  WriterT.run_liftM
  WriterT.run_pure
  WriterT.run_tell


