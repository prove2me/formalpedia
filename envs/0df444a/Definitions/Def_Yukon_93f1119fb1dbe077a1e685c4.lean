-- Prove2me | Definitions.Def_Yukon_93f1119fb1dbe077a1e685c4
-- name    : Yukon_93f1119fb1dbe077a1e685c4
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:05:38.011299+00:00
-- url     : https://prove2.me/theorems/5f89ead4-15a5-464c-955f-024acbc020dc
-- title:
--   YukonModule.PolyFun.PFunctor.Handler.Normalization.Attr.part0
-- statement:
--   Source module PolyFun.PFunctor.Handler.Normalization.Attr.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Handler/Normalization/Attr.lean
--
--   yukon-proof-operation:3796d6b98d6ee257019395fce8724a3b51c7c68ba98471fce33d3d992f863bf3
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Mzc5NmQ2Yjk4ZDZlZTI1NzAxOTM5NWZjZTg3MjRhM2I1MWM3YzY4YmE5ODQ3MWZjZTMzZDNkOTkyZjg2M2JmMyIsImhhc2giOiI0OTgzODM2NjRlNGRmZTUyZTQ1NjcxYWFlMWYzNTM2ZDM0NDgxZjI4NThjZGRlMjhlMGU0YzFmNjUxYzZiZTk0Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85M2YxMTE5ZmIxZGJlMDc3YTFlNjg1YzQiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Definitions.Def_Yukon_117c11ed2c735a2904af9c20



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
meta import Definitions.Def_Yukon_117c11ed2c735a2904af9c20
set_option backward.isDefEq.respectTransparency.types false
/-!
# Handler normalization attribute

This module declares the `handler_nf` simp attribute. The structural handler
rules are registered by `PolyFun.PFunctor.Handler.Normalization`.
-/

@[expose] public section

/-- Simp set for structural normalization of free and stateful handlers. -/
register_simp_attr handler_nf


