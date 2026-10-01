-- Prove2me | Definitions.Def_Yukon_b274322d0e11762f90f047d3
-- name    : Yukon_b274322d0e11762f90f047d3
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:12:53.322679+00:00
-- url     : https://prove2.me/theorems/e5dd1300-c44d-45bc-8662-fa5812e53e7d
-- title:
--   YukonModule.ArkLib.ToVCVio.OracleComp.EvalDist.part0
-- statement:
--   Source module ArkLib.ToVCVio.OracleComp.EvalDist.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ToVCVio/OracleComp/EvalDist.lean
--
--   yukon-proof-operation:ccbde332335e88c08f4c789941f2ac9e5addc6899dc2af8c07da4f7691582a81
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Y2NiZGUzMzIzMzVlODhjMDhmNGM3ODk5NDFmMmFjOWU1YWRkYzY4OTlkYzJhZjhjMDdkYTRmNzY5MTU4MmE4MSIsImhhc2giOiJkNjE2Yjk0YzkwOWJiN2QzNjMwNDkxODYwZWRhNmZkZjcwYzcwMGUxMDkzMTY4MWEzMGUzNjk4Y2QyY2E4YjM1Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9iMjc0MzIyZDBlMTE3NjJmOTBmMDQ3ZDMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Definitions.Def_Yukon_94b8f5dc056c300eb1adf1dd

import Definitions.Def_Yukon_2b5744019605f484379c669d



import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Finset.Card
import Init
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Batteries.Control.OptionT
import Batteries.Control.AlternativeMonad
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Tactic.Common
import Mathlib.Init
import Lean.Message
import Batteries.Tactic.Lint.Basic
import Batteries.Tactic.Lint
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Vector.Basic
set_option backward.isDefEq.respectTransparency.types false
/-!
# Additions to VCV-io's `OracleComp.EvalDist`
-/


