-- Prove2me | Definitions.Def_Yukon_e7d71a5b07c89fdadd7f5ccf
-- name    : Yukon_e7d71a5b07c89fdadd7f5ccf
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:30:37.442925+00:00
-- url     : https://prove2.me/theorems/703cc6dc-7629-4a3c-8289-53af321862d0
-- title:
--   YukonModule.ArkLib.Data.Probability.KoalaBear.part0
-- statement:
--   Source module ArkLib.Data.Probability.KoalaBear.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/Probability/KoalaBear.lean
--
--   yukon-proof-operation:53ee9a9cfd3cd02d1f8e7347104cb0b63fac5022341be69f3531c3600eeb0e8e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZDM0MzFiMmRlZTU0YjZhZTQ1NTNmNTVkNTQ5NjczZjNlZDQ0Mjg5OTczZDU0ZmI4Yjg3YWJmMmRmMTI1N2RjNSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjUzZWU5YTljZmQzY2QwMmQxZjhlNzM0NzEwNGNiMGI2M2ZhYzUwMjIzNDFiZTY5ZjM1MzFjMzYwMGVlYjBlOGUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9lN2Q3MWE1YjA3Yzg5ZmRhZGQ3ZjVjY2YiLCJ2IjoyfQ]

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Definitions.Def_Yukon_7bdfb5c7976bc55dd3e2bf3e

import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7



import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.FinEnum
import Init.Data.UInt.Lemmas
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.List.Sym
import Init
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Card
import Mathlib.Data.Vector.Defs
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Batteries.Control.AlternativeMonad
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Batteries.Control.OptionT
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Tactic.Common
import Mathlib.Init
import Lean.Message
import Batteries.Tactic.Lint.Basic
import Batteries.Tactic.Lint
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.ComputeDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_Yukon_cd1b61f69d8bf8bcce480752
import Definitions.Def_Yukon_db9e62887577419e408bc32c
set_option backward.isDefEq.respectTransparency.types false
/-!
# Computable sampling for the KoalaBear sextic extension

This file gives `KoalaBear.Ext6` a pinned `SampleableType` implementation. It samples a vector of
six independent base-field limbs and transports that vector through the executable coefficient
representation of the extension field. In particular, it does not enumerate the `q ^ 6` extension
elements or use `SampleableType.ofFintype`.
-/

open OracleComp

namespace KoalaBear.Ext6

/-- The executable equivalence between six base-field coefficients and the sextic extension. -/
def coeffsEquiv : Vector Field 6 ≃ Ext6 where
  toFun := fun v => CompPoly.Extension.Ext.ofVector (P := ext6Params) v
  invFun := fun x => CompPoly.Extension.Ext.coeffs (P := ext6Params) x
  left_inv _ := rfl
  right_inv _ := rfl

/-- Boolean equality on `Ext6` agrees with propositional equality coefficientwise. -/
instance instLawfulBEq : LawfulBEq Ext6 :=
  inferInstanceAs (LawfulBEq (Vector Field 6))

/-- Sample `Ext6` by sampling its six base-field coefficients independently. -/
def sample : ProbComp Ext6 :=
  coeffsEquiv <$> ($ᵗ (Vector Field 6))

/-- The pinned six-base-limb sampler for `KoalaBear.Ext6`. -/
@[reducible] def sampleableType : SampleableType Ext6 :=
  SampleableType.ofEquiv coeffsEquiv

instance instSampleableType : SampleableType Ext6 := sampleableType

/-- The canonical `Ext6` uniform sample is definitionally the six-limb sampler above. -/
theorem uniformSample_eq_sample : ($ᵗ Ext6) = sample := rfl

/-- Sampling six independent base limbs induces the uniform distribution on `Ext6`. -/
theorem evalDist_sample :
    𝒟[sample] = liftM (PMF.uniformOfFintype Ext6) := by
  rw [← uniformSample_eq_sample]
  exact evalDist_uniformSample Ext6

end KoalaBear.Ext6


