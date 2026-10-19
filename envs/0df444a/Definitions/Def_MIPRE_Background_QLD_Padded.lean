-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Padded
-- name    : MIPRE_Background_QLD_Padded
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:52:12.117647+00:00
-- url     : https://prove2.me/theorems/fd2643d4-1e67-49ee-99b4-782d56a658ad
-- title:
--   Definitions of Padded: The padded space, and the sublines of a padded line Blueprint `lem:qld-sublines`
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Padded` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The padded space, and the sublines of a padded line. Blueprint `lem:qld-sublines`. The combining stage compares a measurement of *pairs* of `m`-variable polynomials with a low-degree test, and a low-degree test wants a single polynomial in a number of variables dividing `q`. The paper's device is to pad: work over `F_q^{4m}`, whose coordinates split as `u = (x, z, alpha, beta, w)` with `x, z` in `F_q^m`, `alpha, beta` in `F_q` and `w` in `F_q^{2m-2}` the dummy coordinates, and to combine the pair `(f_X, f_Z)` into the single polynomial `alpha f_X(x) + beta f_Z(z)`. Admissibility makes `m` a…
--
--   **Definitions** (33): `MIPRE.QLD.LPData` (The data a line-point pair of the seeded test is generated from: the point, the seed, and the raw diagonal direction.); `MIPRE.QLD.LPData.dir` (The direction of the line this data presents.); `MIPRE.QLD.LPData.question` (The question of type `t` this data presents, as the seeded test computes it.); `MIPRE.QLD.LPData.toSample` (The sample whose questions this data generates.); `MIPRE.QLD.PadCase` (Where a coordinate position of the padded space lies: in the `X` block, in the `Z` block, at `alpha` or `beta`, or among the dummy…); `MIPRE.QLD.PadSum` (The padded index type as a disjoint union of blocks: the `X` block, the `Z` block, and the `2m` positions holding `alpha`, `beta` and the…); `MIPRE.QLD.aIdx` (The position of the `alpha` coordinate.); `MIPRE.QLD.alph` (The `alpha` coordinate of a padded point.); `MIPRE.QLD.avgAll` (The average of `h` over all the data of a line-point pair: `q^m` points, `q` seeds, `q^m` raw directions.); `MIPRE.QLD.avgRestr` (The average of `h` over the data of a line-point pair with axis index `i`: the restricted law `D_{ty,i}`, whose seed ranges over one block…); `MIPRE.QLD.avgSub` (The average of `g` over the subline sampling space at a fixed padded seed: two padded points and two fresh seed-and-direction pairs.); `MIPRE.QLD.avgSubAB` (The normalized version.); `MIPRE.QLD.bIdx` (The position of the `beta` coordinate.); `MIPRE.QLD.bet` (The `beta` coordinate of a padded point.); and -3 more.
--
--   **Embedded lemmas** (49): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `dir_aline`, `dir_dline`, `dir_point`, `aIdx_ne_bIdx`, `aIdx_val`, `alph_add`, `alph_shiftAB`, `alph_smul`, `bIdx_val`, `bet_add`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Padded` (`MIPRE/Background/QLD/Padded.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 62 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Padded.lean; blueprint lem:qld-padded-lines, lem:qld-sublines

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Padded.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Pairwise
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Win
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Definitions.Def_MIPRE_Background_QLD_WinMS
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Assembly
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Main
import Definitions.Def_MIPRE_Background_QLD_Ortho
import Definitions.Def_MIPRE_Background_QLD_Consistency
import Definitions.Def_MIPRE_Background_QLD_Commutation
import Definitions.Def_MIPRE_Background_QLD_Expanded
import Definitions.Def_MIPRE_Background_QLD_Swap
import Definitions.Def_MIPRE_Background_QLD_Combined
import Definitions.Def_MIPRE_Background_QLD_Lines
import Definitions.Def_MIPRE_Foundations_Blocks
import Theorems.Thm_MIPRE_LIDT_CL_chi_val

/-!
# The padded space, and the sublines of a padded line

Blueprint `lem:qld-sublines`. The combining stage compares a measurement of *pairs* of
`m`-variable polynomials with a low-degree test, and a low-degree test wants a single polynomial
in a number of variables dividing `q`. The paper's device is to pad: work over `F_q^{4m}`, whose
coordinates split as `u = (x, z, alpha, beta, w)` with `x, z` in `F_q^m`, `alpha, beta` in `F_q`
and `w` in `F_q^{2m-2}` the dummy coordinates, and to combine the pair `(f_X, f_Z)` into the
single polynomial `alpha f_X(x) + beta f_Z(z)`. Admissibility makes `m` a power of two, so
`2m + 2` never divides `q = 2^k`, while `4m` does as soon as `4m <= q`; that is the whole reason
the dummy block is there.

This file is the geometry of that padding, and it is deliberately free of operators.

## The two pieces

* **The seed's block and offset.** The seeded test reads an axis index off a seed through
  `chi`, which is "which of the `m` equal blocks of `F` does `s` fall into". `seedEquiv` names
  the corresponding bijection `F ~ Fin m x Fin (q/m)`, with `chi` as its first component. Two
  things follow that the subline construction needs: a seed can be *retargeted* to a prescribed
  block keeping its offset (`seedIn`), and a uniform seed retargeted to a fixed block is uniform
  on that block's fibre (`sum_seedIn`). The paper's "choose `s_X` uniformly at random subject to
  `chi(s_X) = i`" is exactly this.
* **The blocks of `F_q^{4m}`.** `xIdx`, `zIdx`, `aIdx`, `bIdx` are the coordinate positions and
  `xBlk`, `zBlk`, `alph`, `bet` the projections. `padCase` classifies a coordinate position into
  the four blocks, which is the case distinction the construction of `lem:qld-sublines` branches
  on: whether the padded line's direction moves an `X` coordinate, a `Z` coordinate, or only
  `alpha`, `beta` and the dummy coordinates.

## Why `4m` and not `2m + 2`

`aIdx` and `bIdx` sit at positions `2m` and `2m + 1`, so the dummy block is positions
`2m + 2, ..., 4m - 1`, of size `2m - 2`. Every index bound below needs only `1 <= m`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset MIPRE.LIDT MIPRE.LIDT.CL

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-! ## The seed's block and offset -/

section Seed

variable [NeZero m]

omit [DecidableEq F] in
theorem mul_card_div (hm : m ∣ Fintype.card F) : m * (Fintype.card F / m) = Fintype.card F :=
  Nat.mul_div_cancel' hm

/-- A seed's block and offset: the bijection `F ~ Fin m x Fin (q/m)` whose first component is
`chi`, available because `m` divides `q`. -/
def seedEquiv (hm : m ∣ Fintype.card F) : F ≃ Fin m × Fin (Fintype.card F / m) :=
  (Fintype.equivFin F).trans ((finCongr (mul_card_div hm).symm).trans finProdFinEquiv.symm)

omit [DecidableEq F] in
/-- The first component of `seedEquiv` is `chi`: both are "divide the index by the block size". -/
@[simp] theorem seedEquiv_fst (hm : m ∣ Fintype.card F) (s : F) :
    (seedEquiv hm s).1 = chi hm s := by
  apply Fin.ext
  rw [chi_val]
  rfl

/-- The seed in block `i` with the same offset as `s`. For a fixed `i` this turns a uniform seed
into a uniform seed of axis index `i`, which is the paper's "`s_X` uniformly at random subject to
`chi(s_X) = i`". -/
def seedIn (hm : m ∣ Fintype.card F) (i : Fin m) (s : F) : F :=
  (seedEquiv hm).symm (i, (seedEquiv hm s).2)

omit [DecidableEq F] in
@[simp] theorem chi_seedIn (hm : m ∣ Fintype.card F) (i : Fin m) (s : F) :
    chi hm (seedIn hm i s) = i := by
  rw [← seedEquiv_fst hm, seedIn, Equiv.apply_symm_apply]

omit [DecidableEq F] in
/-- Retargeting a seed to its own block does nothing. -/
@[simp] theorem seedIn_self (hm : m ∣ Fintype.card F) (s : F) :
    seedIn hm (chi hm s) s = s := by
  rw [seedIn, ← seedEquiv_fst hm]
  exact congrArg _ (Prod.mk.eta) |>.trans ((seedEquiv hm).symm_apply_apply s)

end Seed

/-! ## The blocks of the padded space -/

section Blocks

variable (m)

/-- The position of the `i`-th `X` coordinate of the padded space. -/
def xIdx [NeZero m] (i : Fin m) : Fin (4 * m) :=
  ⟨(i : ℕ), by have := i.isLt; have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

/-- The position of the `i`-th `Z` coordinate of the padded space. -/
def zIdx [NeZero m] (i : Fin m) : Fin (4 * m) :=
  ⟨m + (i : ℕ), by have := i.isLt; have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

/-- The position of the `alpha` coordinate. -/
def aIdx [NeZero m] : Fin (4 * m) :=
  ⟨2 * m, by have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

/-- The position of the `beta` coordinate. -/
def bIdx [NeZero m] : Fin (4 * m) :=
  ⟨2 * m + 1, by have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

variable {m} [NeZero m]

@[simp] theorem xIdx_val (i : Fin m) : (xIdx m i : ℕ) = (i : ℕ) := rfl
@[simp] theorem zIdx_val (i : Fin m) : (zIdx m i : ℕ) = m + (i : ℕ) := rfl
@[simp] theorem aIdx_val : (aIdx m : ℕ) = 2 * m := rfl
@[simp] theorem bIdx_val : (bIdx m : ℕ) = 2 * m + 1 := rfl

theorem xIdx_ne_aIdx (i : Fin m) : xIdx m i ≠ aIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [xIdx_val, aIdx_val] at this
  have := i.isLt
  omega

theorem xIdx_ne_bIdx (i : Fin m) : xIdx m i ≠ bIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [xIdx_val, bIdx_val] at this
  have := i.isLt
  omega

theorem zIdx_ne_aIdx (i : Fin m) : zIdx m i ≠ aIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [zIdx_val, aIdx_val] at this
  have := i.isLt
  omega

theorem zIdx_ne_bIdx (i : Fin m) : zIdx m i ≠ bIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [zIdx_val, bIdx_val] at this
  have := i.isLt
  omega

theorem aIdx_ne_bIdx : aIdx m ≠ bIdx m := by
  intro h
  have := congrArg Fin.val h
  simp only [aIdx_val, bIdx_val] at this
  omega

/-- The `X` block of a padded point. -/
def xBlk (u : Point F (4 * m)) : Point F m := fun i => u (xIdx m i)

/-- The `Z` block of a padded point. -/
def zBlk (u : Point F (4 * m)) : Point F m := fun i => u (zIdx m i)

/-- The `alpha` coordinate of a padded point. -/
def alph (u : Point F (4 * m)) : F := u (aIdx m)

/-- The `beta` coordinate of a padded point. -/
def bet (u : Point F (4 * m)) : F := u (bIdx m)

@[simp] theorem xBlk_apply (u : Point F (4 * m)) (i : Fin m) : xBlk u i = u (xIdx m i) := rfl
@[simp] theorem zBlk_apply (u : Point F (4 * m)) (i : Fin m) : zBlk u i = u (zIdx m i) := rfl

@[simp] theorem xBlk_zero : xBlk (0 : Point F (4 * m)) = (0 : Point F m) := rfl
@[simp] theorem zBlk_zero : zBlk (0 : Point F (4 * m)) = (0 : Point F m) := rfl

@[simp] theorem xBlk_add (u v : Point F (4 * m)) : xBlk (u + v) = xBlk u + xBlk v := rfl
@[simp] theorem zBlk_add (u v : Point F (4 * m)) : zBlk (u + v) = zBlk u + zBlk v := rfl
@[simp] theorem xBlk_smul (t : F) (u : Point F (4 * m)) : xBlk (t • u) = t • xBlk u := rfl
@[simp] theorem zBlk_smul (t : F) (u : Point F (4 * m)) : zBlk (t • u) = t • zBlk u := rfl
@[simp] theorem alph_add (u v : Point F (4 * m)) : alph (u + v) = alph u + alph v := rfl
@[simp] theorem bet_add (u v : Point F (4 * m)) : bet (u + v) = bet u + bet v := rfl
@[simp] theorem alph_smul (t : F) (u : Point F (4 * m)) : alph (t • u) = t * alph u := rfl
@[simp] theorem bet_smul (t : F) (u : Point F (4 * m)) : bet (t • u) = t * bet u := rfl

/-! ### Which block a coordinate position lies in -/

/-- Where a coordinate position of the padded space lies: in the `X` block, in the `Z` block, at
`alpha` or `beta`, or among the dummy coordinates. The construction of `lem:qld-sublines`
branches on this. -/
inductive PadCase (m : ℕ) [NeZero m]
  | xc (i : Fin m)
  | zc (i : Fin m)
  | ab
  | dum

/-- The block a coordinate position lies in. -/
def padCase (j : Fin (4 * m)) : PadCase m :=
  if h : (j : ℕ) < m then .xc ⟨(j : ℕ), h⟩
  else if h' : (j : ℕ) < 2 * m then .zc ⟨(j : ℕ) - m, by omega⟩
  else if (j : ℕ) < 2 * m + 2 then .ab
  else .dum

/-! ### The blocks of a single coordinate and of a truncated direction

These are the only geometric facts the subline construction needs: they say which block of the
padded direction is nonzero, and what it is. -/

end Blocks

/-! ## The sublines of a padded line

Blueprint `lem:qld-sublines`. The paper's `D` is a sampling procedure, and this is that procedure:
`subX` and `subZ` read the two `m`-dimensional line-point pairs off a padded one together with a
pair of fresh seeds and raw directions.

The shape of the construction is forced by what Property 2 demands. Moving along the padded line
moves the `X` block along the `X` block of the padded direction, so if that block is nonzero the
`X` subline has no choice: its direction must be exactly that block, and the only freedom left is
*which seed* presents it, which is where `seedIn` comes in. If the block vanishes the `X` block is
constant along the padded line, the containment is free, and the subline is sampled fresh.

The four cases of `padCase` say which blocks vanish, and they do not say the same thing for the
two line types. For an axis-parallel padded line the direction is a single coordinate, so at most
one of the two blocks is nonzero. For a diagonal padded line the direction is `v` truncated below
the axis index, so an index in the `X` block leaves the whole `Z` block untouched: both blocks are
then nonzero, and the `Z` subline is forced too --- at axis index `0`, since nothing of its
direction is truncated. That asymmetry is the only place `subZ` looks at the line type.
-/

section Sub

/-- The data a line-point pair of the seeded test is generated from: the point, the seed, and the
raw diagonal direction. This is the part of `MIPRE.LIDT.CL.Sample` that the line questions read,
and it has the same shape in the padded dimension `4m` and the unpadded dimension `m`. -/
structure LPData (F : Type*) (m : ℕ) where
  /-- The sampled point. -/
  pt : Point F m
  /-- The seed, which selects the axis index through `chi`. -/
  s : F
  /-- The raw diagonal direction, truncated by `zeroBelow` before use. -/
  raw : Point F m
  deriving DecidableEq, Fintype

variable [NeZero m]

instance : NeZero (4 * m) :=
  ⟨by have := Nat.pos_of_ne_zero (NeZero.ne m); omega⟩

/-- Truncating below the first coordinate truncates nothing. -/
@[simp] theorem zeroBelow_zero (v : Point F m) : zeroBelow (0 : Fin m) v = v := by
  funext k
  show (if (k : ℕ) < ((0 : Fin m) : ℕ) then (0 : F) else v k) = v k
  rw [if_neg (by simp)]

/-- The sample whose questions this data generates. Both players are given the same type, which is
all that the line questions read. -/
def LPData.toSample (t : CL.Ty) (c : LPData F m) : CL.Sample F m := ⟨t, t, c.pt, c.s, c.raw⟩

/-- The question of type `t` this data presents, as the seeded test computes it. -/
def LPData.question (hm : m ∣ Fintype.card F) (t : CL.Ty) (c : LPData F m) : CL.Question F m :=
  (c.toSample t).question hm t

/-- The direction of the line this data presents. -/
def LPData.dir (hm : m ∣ Fintype.card F) (t : CL.Ty) (c : LPData F m) : Point F m :=
  CL.Question.dir hm (c.question hm t)

@[simp] theorem LPData.dir_point (hm : m ∣ Fintype.card F) (c : LPData F m) :
    c.dir hm .point = 0 := rfl

@[simp] theorem LPData.dir_aline (hm : m ∣ Fintype.card F) (c : LPData F m) :
    c.dir hm .aline = Pi.single (chi hm c.s) 1 := rfl

@[simp] theorem LPData.dir_dline (hm : m ∣ Fintype.card F) (c : LPData F m) :
    c.dir hm .dline = zeroBelow (chi hm c.s) c.raw := rfl

/-- The `X`-side subline data, as a function of the block the padded axis index lies in. Splitting
the case distinction out of `subX` is what lets a proof rewrite the block and then reduce. -/
def subXof (hm : m ∣ Fintype.card F) (k : PadCase m) (P : LPData F (4 * m))
    (e : F × Point F m) : LPData F m :=
  match k with
  | .xc i => ⟨xBlk P.pt, seedIn hm i e.1, xBlk P.raw⟩
  | _ => ⟨xBlk P.pt, e.1, e.2⟩

/-- The `X`-side subline data of a padded line-point pair. The point is the `X` block of the padded
point; the direction is forced to the `X` block of the padded direction when that block is nonzero,
with the fresh seed `e.1` supplying only the offset inside the forced block, and is sampled from `e`
when it vanishes. No case distinction on the line type is needed here: an axis index in the `X`
block forces the `X` block of the direction for both types at once. -/
def subX (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) : LPData F m :=
  subXof hm (padCase (chi hm4 P.s)) P e

/-- The `Z`-side subline data, as a function of the line type and of the block the padded axis index
lies in. -/
def subZof (hm : m ∣ Fintype.card F) (t : CL.Ty) (k : PadCase m) (P : LPData F (4 * m))
    (e : F × Point F m) : LPData F m :=
  match t, k with
  | .dline, .xc _ => ⟨zBlk P.pt, seedIn hm 0 e.1, zBlk P.raw⟩
  | _, .zc i => ⟨zBlk P.pt, seedIn hm i e.1, zBlk P.raw⟩
  | _, _ => ⟨zBlk P.pt, e.1, e.2⟩

/-- The `Z`-side subline data. A diagonal padded line whose axis index lies in the `X` block leaves
the whole `Z` block of its direction intact, so the `Z` subline is forced, at axis index `0` since
nothing of its direction is truncated; an axis-parallel one leaves that block zero, so the `Z`
subline is free. That is the one asymmetry between the two sides. -/
def subZ (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (P : LPData F (4 * m)) (e : F × Point F m) : LPData F m :=
  subZof hm t (padCase (chi hm4 P.s)) P e

section Eqns

variable (hm : m ∣ Fintype.card F) (t : CL.Ty) (i : Fin m) (P : LPData F (4 * m))
  (e : F × Point F m)

@[simp] theorem subXof_xc :
    subXof hm (.xc i) P e = ⟨xBlk P.pt, seedIn hm i e.1, xBlk P.raw⟩ := rfl
@[simp] theorem subXof_zc : subXof hm (.zc i) P e = ⟨xBlk P.pt, e.1, e.2⟩ := rfl
@[simp] theorem subXof_ab : subXof hm (.ab) P e = ⟨xBlk P.pt, e.1, e.2⟩ := rfl
@[simp] theorem subXof_dum : subXof hm (.dum) P e = ⟨xBlk P.pt, e.1, e.2⟩ := rfl

@[simp] theorem subZof_dline_xc :
    subZof hm .dline (.xc i) P e = ⟨zBlk P.pt, seedIn hm 0 e.1, zBlk P.raw⟩ := rfl
@[simp] theorem subZof_point_xc : subZof hm .point (.xc i) P e = ⟨zBlk P.pt, e.1, e.2⟩ := rfl
@[simp] theorem subZof_aline_xc : subZof hm .aline (.xc i) P e = ⟨zBlk P.pt, e.1, e.2⟩ := rfl
@[simp] theorem subZof_zc :
    subZof hm t (.zc i) P e = ⟨zBlk P.pt, seedIn hm i e.1, zBlk P.raw⟩ := by cases t <;> rfl
@[simp] theorem subZof_ab : subZof hm t (.ab) P e = ⟨zBlk P.pt, e.1, e.2⟩ := by cases t <;> rfl
@[simp] theorem subZof_dum : subZof hm t (.dum) P e = ⟨zBlk P.pt, e.1, e.2⟩ := by cases t <;> rfl

end Eqns

@[simp] theorem subX_pt (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)
    (P : LPData F (4 * m)) (e : F × Point F m) : (subX hm4 hm P e).pt = xBlk P.pt := by
  rw [subX]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _ <;> rfl

@[simp] theorem subZ_pt (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty)
    (P : LPData F (4 * m)) (e : F × Point F m) : (subZ hm4 hm t P e).pt = zBlk P.pt := by
  rw [subZ]
  rcases h : padCase (chi hm4 P.s) with i | i | _ | _ <;> cases t <;> rfl

/-! ### Property 2 of `lem:qld-sublines`: the blocks of the padded direction -/

/-! ### Property 2 of `lem:qld-sublines`, the containment -/

section Containment

-- The canonical representative and the parameter are those of the seeded test, whose field is the
-- binary field the Pauli basis test works over.
variable [Algebra (ZMod 2) F]

/-! ### Property 3 of `lem:qld-sublines`

The paper's Property 3 --- an axis-parallel padded line has axis-parallel sublines --- is
definitional here, because the line type is a parameter handed to both sides rather than something
the construction chooses. What is *not* definitional, and is the reason the paper needs the
property, is that the two directions then agree in the way `xBlk_dir_sub` and `zBlk_dir_sub` state;
those are the lemmas a consumer should cite. -/

end Containment

end Sub

/-! ## The padded space as a product of its blocks

`lem:qld-sublines`' second property is distributional: under a uniform point of a padded line the
two sublines are drawn from a mixture of *products* of restricted laws, with each side's point
conditionally uniform on its line. What makes that true is that the `X` and `Z` blocks of a uniform
padded point are uniform and independent, and that is a statement about the index type: `Fin (4m)`
is the disjoint union of the `X` block, the `Z` block, and the `2m` positions above them. `padEquiv`
names that decomposition and `sum_point_pad` is the resulting product identity.
-/

section Product

variable [NeZero m]

/-- The padded index type as a disjoint union of blocks: the `X` block, the `Z` block, and the `2m`
positions holding `alpha`, `beta` and the dummy coordinates. -/
abbrev PadSum (m : ℕ) := (Fin m ⊕ Fin m) ⊕ Fin (2 * m)

/-- The block decomposition of the padded index type. The `X` block lands on positions
`0, ..., m-1` and the `Z` block on `m, ..., 2m-1`, which is exactly `xIdx` and `zIdx`. -/
def padEquiv (m : ℕ) : PadSum m ≃ Fin (4 * m) :=
  ((Equiv.sumCongr (finSumFinEquiv (m := m) (n := m)) (Equiv.refl (Fin (2 * m)))).trans
    finSumFinEquiv).trans (finCongr (by ring))

@[simp] theorem padEquiv_inl_inl (i : Fin m) : padEquiv m (.inl (.inl i)) = xIdx m i := by
  apply Fin.ext
  simp [padEquiv, finSumFinEquiv, Fin.castAdd, Fin.castLE, xIdx]

@[simp] theorem padEquiv_inl_inr (i : Fin m) : padEquiv m (.inl (.inr i)) = zIdx m i := by
  apply Fin.ext
  simp [padEquiv, finSumFinEquiv, Fin.castAdd, Fin.castLE, Fin.natAdd, zIdx]

end Product

/-! ## The law of the sublines

`lem:qld-sublines`' second property is that under a uniform point of a padded line the pair of
sublines is drawn from a mixture of *products* of restricted line-point laws, each side's point
conditionally uniform on its own line. `sumRestr` and `sumAll` are the two laws, unnormalized, and
`sumSub` is the sum over the sampling space; the four branch identities below say which product each
branch of the construction gives, and with what multiplicity.
-/

section Law

variable [NeZero m]

/-- The sum of `h` over the data of a line-point pair whose axis index is `i`: the restricted law
`D_{ty,i}` of `def:ith-restricted-line`, unnormalized. The seed ranges over the fibre of `chi` above
`i`, written through `seedEquiv` as an offset. -/
def sumRestr (hm : m ∣ Fintype.card F) (i : Fin m) {M : Type*} [AddCommMonoid M]
    (h : LPData F m → M) : M :=
  ∑ pt : Point F m, ∑ o : Fin (Fintype.card F / m), ∑ raw : Point F m,
    h ⟨pt, (seedEquiv hm).symm (i, o), raw⟩

/-- The sum of `h` over all the data of a line-point pair: the unrestricted seeded law,
unnormalized. -/
def sumAll {M : Type*} [AddCommMonoid M] (h : LPData F m → M) : M :=
  ∑ pt : Point F m, ∑ s : F, ∑ raw : Point F m, h ⟨pt, s, raw⟩

/-- The sum over the subline sampling space at a fixed padded seed: the padded point and the padded
raw direction, and a fresh seed and raw direction for each side. -/
def sumSub (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    {M : Type*} [AddCommMonoid M] (g : LPData F m → LPData F m → M) : M :=
  ∑ pt : Point F (4 * m), ∑ raw : Point F (4 * m), ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
    g (subX hm4 hm ⟨pt, s, raw⟩ eX) (subZ hm4 hm t ⟨pt, s, raw⟩ eZ)

end Law

/-! ## From sums to averages

The four branch identities are sum identities with an explicit multiplicity: the assignments to the
coordinates and to the fresh randomness that the construction does not read. Dividing by the number
of terms turns them into the statement `lem:qld-sublines` makes --- an identity of *laws*, with no
constant left over. The average over the subline sampling space is exactly the average over a
product of two line-point laws, restricted on a side exactly when the padded direction forces that
side's subline.
-/

section Average

variable [NeZero m]

/-- The average of `h` over all the data of a line-point pair: `q^m` points, `q` seeds, `q^m` raw
directions. -/
def avgAll (h : LPData F m → ℝ) : ℝ := ((Fintype.card F : ℝ) ^ (2 * m + 1))⁻¹ * sumAll h

/-- The average of `h` over the data of a line-point pair with axis index `i`: the restricted law
`D_{ty,i}`, whose seed ranges over one block of `q/m` elements. -/
def avgRestr (hm : m ∣ Fintype.card F) (i : Fin m) (h : LPData F m → ℝ) : ℝ :=
  ((Fintype.card F : ℝ) ^ (2 * m) * ((Fintype.card F / m : ℕ) : ℝ))⁻¹ * sumRestr hm i h

/-- The average of `g` over the subline sampling space at a fixed padded seed: two padded points and
two fresh seed-and-direction pairs. -/
def avgSub (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (g : LPData F m → LPData F m → ℝ) : ℝ :=
  ((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹ * sumSub hm4 hm t s g

/-! ### The restricted law is the unrestricted one up to a factor of `m`

The paper's `def:ith-restricted-line` splits the line-point distribution by axis index and observes
that an approximation holding at error `delta` on average holds on each restricted law at
`2m * delta` --- the `2` being the mixture over the two line types, which here is a parameter rather
than something mixed over, so the factor is `m`. This is where every factor of `m` in
`delta_combine = m * poly(eps, md/q)` comes from, and it is one line on top of
`sumAll_eq_sum_sumRestr`: the `m` restricted laws are nonnegative and average to the unrestricted
one, so each of them is at most `m` times it. -/

/-! ### The unrestricted law is the uniform average over the data

`pairs_of_lines_prod` is stated as a uniform average over `LPData F m x LPData F m`; `avgAll` is the
same average written as nested sums. One equiv identifies them. -/

/-- The data of a line-point pair, as a triple. -/
def lpEquiv (F : Type*) (m : ℕ) : LPData F m ≃ Point F m × F × Point F m where
  toFun c := (c.pt, c.s, c.raw)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Linearity and monotonicity of the averages -/

/-! ### The padded law is dominated by the product law

This is the distributional content of the paper's Claims 17-1 to 17-3, and it is stronger than what
those claims extract. The paper's `\cnote` on the conclusion of `lem:qld-4-13` says the joint law of
the two sublines-with-points is **not** a product, because "for diagonal lines both coordinates share
the line parameter", and the three claims are written to use only the marginals. That is right about
conditioning on the *padded* line: given it, the two blocks of a uniform point on it move with one
parameter. But the quantity to be bounded conditions only on the two *sublines*, which know each
block's coset in its own space and not the relative offset --- and `avgSub_free` and its three
companions say that at a fixed padded seed the joint law is exactly a product of the two marginals,
each of them restricted or not according to `padCase`. Combining that with the restricted-law
transfer bounds the padded law by `m^2` times the product of the two unrestricted laws, uniformly in
the padded seed and the line type. -/

end Average

/-! ## The `alpha` and `beta` coordinates of the padded point

The measurement of `lem:qld-padded-lines` reads `alpha` and `beta` at the sampled padded point, which
`avgSub` does not carry. They are coordinates of the padded point outside the `X` and `Z` blocks, so
translating the point in those two coordinates alone leaves both sublines untouched --- which makes
the `(alpha, beta)` average *uniform and independent of everything else*, and a bound that holds for
every fixed `(alpha, beta)` therefore holds for the joint law. No refinement of the block
decomposition is needed. -/

section AlphaBeta

variable [NeZero m]

/-- Translating the padded point in its `alpha` and `beta` coordinates only. -/
def shiftAB (c d : F) (u : Point F (4 * m)) : Point F (4 * m) :=
  u + (Pi.single (aIdx m) c + Pi.single (bIdx m) d)

@[simp] theorem xBlk_shiftAB (c d : F) (u : Point F (4 * m)) :
    xBlk (shiftAB c d u) = xBlk u := by
  funext i
  simp [shiftAB, xBlk, Pi.single_eq_of_ne (xIdx_ne_aIdx i), Pi.single_eq_of_ne (xIdx_ne_bIdx i)]

@[simp] theorem zBlk_shiftAB (c d : F) (u : Point F (4 * m)) :
    zBlk (shiftAB c d u) = zBlk u := by
  funext i
  simp [shiftAB, zBlk, Pi.single_eq_of_ne (zIdx_ne_aIdx i), Pi.single_eq_of_ne (zIdx_ne_bIdx i)]

@[simp] theorem alph_shiftAB (c d : F) (u : Point F (4 * m)) :
    alph (shiftAB c d u) = alph u + c := by
  simp only [shiftAB, alph, Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne aIdx_ne_bIdx, add_zero]

@[simp] theorem bet_shiftAB (c d : F) (u : Point F (4 * m)) :
    bet (shiftAB c d u) = bet u + d := by
  simp only [shiftAB, bet, Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm aIdx_ne_bIdx), zero_add]

@[simp] theorem shiftAB_zero (u : Point F (4 * m)) : shiftAB (0 : F) 0 u = u := by
  simp only [shiftAB, Pi.single_zero, add_zero]

/-- The inner average of the subline sampling space, at a fixed padded point. -/
def sumSubAt (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (pt : Point F (4 * m)) (h : LPData F m → LPData F m → ℝ) : ℝ :=
  ∑ raw : Point F (4 * m), ∑ eX : F × Point F m, ∑ eZ : F × Point F m,
    h (subX hm4 hm ⟨pt, s, raw⟩ eX) (subZ hm4 hm t ⟨pt, s, raw⟩ eZ)

/-- The padded average with `alpha` and `beta` carried. -/
def sumSubAB (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (g : F → F → LPData F m → LPData F m → ℝ) : ℝ :=
  ∑ pt : Point F (4 * m), sumSubAt hm4 hm t s pt (g (alph pt) (bet pt))

/-- The normalized version. -/
def avgSubAB (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (t : CL.Ty) (s : F)
    (g : F → F → LPData F m → LPData F m → ℝ) : ℝ :=
  ((Fintype.card F : ℝ) ^ (10 * m + 2))⁻¹ * sumSubAB hm4 hm t s g

end AlphaBeta

end MIPRE.QLD


