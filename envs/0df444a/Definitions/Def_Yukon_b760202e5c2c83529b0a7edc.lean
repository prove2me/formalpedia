-- Prove2me | Definitions.Def_Yukon_b760202e5c2c83529b0a7edc
-- name    : Yukon_b760202e5c2c83529b0a7edc
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T19:15:47.610852+00:00
-- url     : https://prove2.me/theorems/d5971665-15a6-435d-ab86-ac1ff37fba31
-- title:
--   YukonModule.ProximityPrize.Benchmark.IRSProfile.part0
-- statement:
--   Source module ProximityPrize.Benchmark.IRSProfile. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/Benchmark/IRSProfile.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/Benchmark/IRSProfile.lean
--
--   yukon-proof-operation:7cde5483927b16dcf9ce89702263ea5041376d3081f0e0394c0330c9ff074e1e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMTRkNjNkZmJlNjQwNWRlNTNhMTNjZjY5MjY0NmZlYWMxYjFkMmFkYzI2MzNlNjZjNTI3NWYyYTk3NzVlYzVkZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjdjZGU1NDgzOTI3YjE2ZGNmOWNlODk3MDIyNjNlYTUwNDEzNzZkMzA4MWYwZTAzOTRjMDMzMGM5ZmYwNzRlMWUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9iNzYwMjAyZTVjMmM4MzUyOWIwYTdlZGMiLCJ2IjoyfQ]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import Definitions.Def_Yukon_71d1d3a20b96d112661d47d7

import Definitions.Def_Yukon_5354c49d2fbaa2daf6fb4ee4

import Definitions.Def_Yukon_3692b77ddd308e8e341b6d3a

import Definitions.Def_Yukon_1d12cd42de48e1c5386cddc7



import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.Log
import Init.Data.Vector.OfFn
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Init
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Set.Finite.Basic
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
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.DepRewrite
import Mathlib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.FieldTheory.Finiteness
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import Mathlib.Data.Finsupp.Fin
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.FinEnum
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Rat.Star
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Aesop
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Basic
import Init.Data.List.FinRange
import Mathlib.Data.Matrix.Reflection
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Batteries.Tactic.Lint
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Tactic.Common
import Mathlib.Init
import Lean.Message
import Batteries.Tactic.Lint.Basic
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Batteries.Control.Lemmas
import Mathlib.Data.Vector.Defs
import Batteries.Control.OptionT
import Batteries.Control.AlternativeMonad
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Init.Data.UInt.Lemmas
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.List.Sym
import Mathlib.Order.Basic
import Mathlib.Control.Monad.Writer
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Set.Card
import Init.Data.Vector.Lemmas
import Mathlib.Control.Lawful
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Logic.Equiv.Sum
import Std.Tactic.Do
import Std.Internal.Do.Assertion
import Mathlib.Algebra.Order.Monoid.Defs
import Init.Data.String.Lemmas.Iterate
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Splits
import Init.Data.String.Iterate
import Init.Data.String.Defs
import Init.Omega
import Init.Data.Slice.Lemmas
import Init.Data.Nat.Mod
import Init.Data.List.TakeDrop
import Init.Data.List.Range
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Range
import Init.Data.Iterators.Lemmas
import Init.Data.Range
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Std.Do.Triple.SpecLemmas
import Init.Data.Slice.Array
import Init.Data.Range.Polymorphic
import Init.Data.Range.Polymorphic.Iterators
import Init.While
import Init.Syntax
import Lean.Meta.Sym.Pattern
import Lean.Meta.Tactic.Simp
import Lean.Meta.Match.MatcherApp
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Do.Attr
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Sym.Apply
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finsupp.Order
import Std.Data.HashMap.Lemmas
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Logic.Equiv.Prod
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Use
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Sym.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Attr.Register
import Batteries.Data.Vector.Lemmas
import Mathlib.Data.Vector.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.AdjoinRoot
import Lean.Compiler.IR
import Definitions.Def_Yukon_2d0e6914e1f35ef62dbe39e4
import Definitions.Def_Yukon_06fd17bede7d9846a07acaa7
import Definitions.Def_Yukon_95e1f6c57ba6527ee61187a2
import Definitions.Def_Yukon_e9ee7c0e88307b8acac3260e
import Definitions.Def_Yukon_c3fcb43d1ba4a8df9eead5d4
import Definitions.Def_Yukon_b64c002b9f6caec7014c6911
import Definitions.Def_Yukon_cd1b61f69d8bf8bcce480752
import Definitions.Def_Yukon_01021eded3220e2800cfca71
import Definitions.Def_Yukon_db9e62887577419e408bc32c
import Definitions.Def_Yukon_7bdfb5c7976bc55dd3e2bf3e
import Definitions.Def_Yukon_cdb86a7d352f997352680dd3
import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7
import Definitions.Def_Yukon_e7d71a5b07c89fdadd7f5ccf
set_option backward.isDefEq.respectTransparency.types false
/-!
# The interleaved-RS challenge profile

This file owns the concrete downstream choices which intentionally do not live
in ArkLib: the field, smooth evaluation domain, code dimensions, repetition
count, and the public argument-size estimate.
-/

namespace ProximityPrize.Benchmark.IRSProfile

open Code ToyProblem ToyProblem.Impl.IRS
open scoped NNReal

abbrev Field := _root_.KoalaBear.Ext6
abbrev Index := Fin (2 ^ 18)

def totalDimension : Nat := 2 ^ 20
def interleaving : Nat := 8
def baseDimension : Nat := 2 ^ 17
def domainSize : Nat := 2 ^ 18
def repetitions : Nat := 128

theorem interleaving_dvd_totalDimension : interleaving ∣ totalDimension := by
  norm_num [interleaving, totalDimension]

theorem totalDimension_div_interleaving :
    totalDimension / interleaving = baseDimension := by
  norm_num [totalDimension, interleaving, baseDimension]

local instance  _root_.ProximityPrize.Benchmark.IRSProfile.instNeZeroNatInterleaving : NeZero interleaving := ⟨by norm_num [interleaving]⟩
local instance  _root_.ProximityPrize.Benchmark.IRSProfile.instNeZeroNatBaseDimension : NeZero baseDimension := ⟨by norm_num [baseDimension]⟩

/-- The size-`2^18` KoalaBear multiplicative NTT domain. -/
def baseNttDomain : CompPoly.CPolynomial.NTT.Domain _root_.KoalaBear.Field :=
  CompPoly.CPolynomial.NTT.KoalaBear.domainOfLogN 18 (by
    norm_num [_root_.KoalaBear.twoAdicity])

/-- The smooth base-field domain, embedded coefficient-wise in the sextic field. -/
def domain : Index ↪ Field where
  toFun i := CompPoly.Extension.Ext.ofBase (baseNttDomain.node i)
  inj' := by
    intro i j hij
    apply Fin.ext
    have hcoeff := congrArg
      (fun x : Field => CompPoly.Extension.Ext.coeff x (0 : Fin 6)) hij
    simp only [CompPoly.Extension.Ext.coeff_ofBase, Fin.val_zero, if_pos] at hcoeff
    exact baseNttDomain.primitive.pow_inj i.isLt j.isLt hcoeff

def encoder :
    (Fin totalDimension → Field) →ₗ[Field]
      (Index → Fin interleaving → Field) :=
  ToyProblem.Impl.IRS.encoder totalDimension interleaving
    interleaving_dvd_totalDimension domain

noncomputable def code : ModuleCode Index Field (Fin interleaving → Field) :=
  ReedSolomon.Interleaved.irsCode domain totalDimension interleaving

noncomputable def baseCode : ModuleCode Index Field Field :=
  ReedSolomon.code domain baseDimension

theorem encoder_injective : Function.Injective encoder := by
  exact ToyProblem.Impl.IRS.encoder_injective totalDimension interleaving
    interleaving_dvd_totalDimension domain (by
      norm_num [totalDimension, interleaving, domainSize])

theorem encoder_range : Set.range encoder = (code : Set _) := by
  exact ToyProblem.Impl.IRS.encoder_range totalDimension interleaving
    interleaving_dvd_totalDimension domain







set_option maxRecDepth 20000 in
theorem minDistance :
    Code.minDist (code : Set (Index → Fin interleaving → Field)) = 131073 := by
  unfold code
  rw [ReedSolomon.Interleaved.minDist_irsCode domain totalDimension interleaving
    (by norm_num [totalDimension, interleaving, domainSize])]
  norm_num [totalDimension, interleaving]

set_option maxRecDepth 20000 in
theorem baseMinDistance :
    Code.minDist (baseCode : Set (Index → Field)) = 131073 := by
  unfold baseCode
  rw [ReedSolomon.minDist_eq_card_sub_min_add_1]
  norm_num [baseDimension]

/-- The exact relative-distance value shared by the base and interleaved codes. -/
noncomputable def minRelativeDistance : ℝ≥0 := (131073 : ℝ≥0) / 262144







/-- ArkLib's stable fixed-radius façade for this exact protocol profile. -/
noncomputable def parameters :
    ToyProblem.FixedRadiusParameters (ι := Index) (F := Field)
      (A := Fin interleaving → Field) where
  k := totalDimension
  t := repetitions
  code := code
  encoder := encoder
  encoder_injective := encoder_injective
  encoder_range := encoder_range

def merkleOpeningEstimateBits : Nat :=
  repetitions * (256 * 18 + 62 * interleaving)




def merkleOpeningEstimateBytes : Nat := merkleOpeningEstimateBits / 8




end ProximityPrize.Benchmark.IRSProfile


