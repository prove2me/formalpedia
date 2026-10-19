-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Product
-- name    : MIPRE_Background_QLD_Product
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:53:26.594144+00:00
-- url     : https://prove2.me/theorems/e708da98-3bbe-4d9c-a1b5-205978cf9c40
-- title:
--   Definitions of Product: A content, and a product of two independent line-point pairs `lem:qld-pairs-of-lines` is proved on the Pauli basis…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Product` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A content, and a product of two independent line-point pairs. `lem:qld-pairs-of-lines` is proved on the Pauli basis test's own question distribution: one `Content`, carrying both sides' points but a **single** seed and a **single** raw direction, so the `X` line and the `Z` line it presents are not independent. `lem:qld-padded-lines` needs the same conclusion on a **product** of two independent line-point laws, which is what `lem:qld-sublines` delivers. The transfer is available, and the reason is worth stating before the machinery: **no hypothesis of the pasting lemma involves both lines.**…
--
--   **Definitions** (15): `MIPRE.QLD.Content.lpX` (The `X`-side line-point data a content carries: its `X` point, its seed, its raw direction.); `MIPRE.QLD.Content.lpZ` (The `Z`-side line-point data a content carries: the **same** seed and raw direction, with the `Z` point.); `MIPRE.QLD.FactorsX` (`PX` reads the content only through its `X` line-point data.); `MIPRE.QLD.FactorsZ` (`PZ` reads the content only through its `Z` line-point data.); `MIPRE.QLD.contentSplitPts` (A content splits as its two points and everything else.); `MIPRE.QLD.contentSplitX` (A content splits as (its `X` data, its `Z` point) and its probes.); `MIPRE.QLD.contentSplitZ` (The mirror of `contentSplitX`.); `MIPRE.QLD.ofLPX` (A content assembled from `X`-side line-point data and a `Z` point.); `MIPRE.QLD.ofLPZ` (A content assembled from `Z`-side line-point data and an `X` point.); `MIPRE.QLD.pairCX` (The `X`-side content a pair of line-point data presents: the `X` side's own line-point data, with the `Z` side's point as the content's…); `MIPRE.QLD.pairCZ` (The `Z`-side content.); `MIPRE.QLD.pairDirX` (The `X` line's direction, read off a pair through the content the `X` side presents.); `MIPRE.QLD.pairShift` (The shift on a pair of line-point data: move the `X` side's point, leave the `Z` side alone.); `MIPRE.QLD.pairSplitX` (A pair of line-point data splits as (the `X` one, the `Z` one's point) and the `Z` one's line.); `MIPRE.QLD.pairSplitZ` (The mirror of `pairSplitX`.).
--
--   **Embedded lemmas** (10): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `lpX_ofLPX`, `lpZ_ofLPZ`, `pairCX_pairShift`, `pairCZ_pairShift`, `pairDirX_eq`, `pairShift_zero`, `uX_ofLPX`, `uX_ofLPZ`, `uZ_ofLPX`, `uZ_ofLPZ`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Product` (`MIPRE/Background/QLD/Product.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 63 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Product.lean; blueprint lem:qld-padded-lines

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Product.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_QLD_Padded

/-!
# A content, and a product of two independent line-point pairs

`lem:qld-pairs-of-lines` is proved on the Pauli basis test's own question distribution: one
`Content`, carrying both sides' points but a **single** seed and a **single** raw direction, so the
`X` line and the `Z` line it presents are not independent. `lem:qld-padded-lines` needs the same
conclusion on a **product** of two independent line-point laws, which is what `lem:qld-sublines`
delivers.

The transfer is available, and the reason is worth stating before the machinery: **no hypothesis of
the pasting lemma involves both lines.** Each marginal consistency involves one line and the two
points; the fine self-consistency and the collision term involve one line only. So the only laws
that have to agree are

* one side's line-point data on its own,
* one side's line-point data together with the *other side's point*,
* the two points.

and each of those has the same law under a content as under a product, because a content's two
points and its seed and raw direction are independent and uniform. This file says that three times,
and each proof is one line on top of `MIPRE.avg_comp_equiv_fst`: exhibit the splitting of each
sample space that isolates the part the quantity depends on, and the marginals match.

What the file does *not* claim is that the two laws agree on anything involving both lines --- they
do not, and that is the content of the paper's restriction to product distributions.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]

/-! ## Reading a content as line-point data, and back -/

/-- The `X`-side line-point data a content carries: its `X` point, its seed, its raw direction. -/
def Content.lpX (c : Content F m) : LPData F m := ⟨c.uX, c.s, c.v⟩

/-- The `Z`-side line-point data a content carries: the **same** seed and raw direction, with the
`Z` point. That sharing is exactly why a content is not a product of two independent line-point
pairs. -/
def Content.lpZ (c : Content F m) : LPData F m := ⟨c.uZ, c.s, c.v⟩

/-- A content assembled from `X`-side line-point data and a `Z` point. The probe registers are
irrelevant to every line quantity, so they are set to zero. -/
def ofLPX (d : LPData F m) (uZ : Point F m) : Content F m := ⟨d.pt, uZ, d.s, d.raw, 0, 0⟩

/-- A content assembled from `Z`-side line-point data and an `X` point. -/
def ofLPZ (d : LPData F m) (uX : Point F m) : Content F m := ⟨uX, d.pt, d.s, d.raw, 0, 0⟩

@[simp] theorem lpX_ofLPX (d : LPData F m) (uZ : Point F m) : (ofLPX d uZ).lpX = d := rfl
@[simp] theorem lpZ_ofLPZ (d : LPData F m) (uX : Point F m) : (ofLPZ d uX).lpZ = d := rfl
@[simp] theorem uZ_ofLPX (d : LPData F m) (uZ : Point F m) : (ofLPX d uZ).uZ = uZ := rfl
@[simp] theorem uX_ofLPX (d : LPData F m) (uZ : Point F m) : (ofLPX d uZ).uX = d.pt := rfl
@[simp] theorem uX_ofLPZ (d : LPData F m) (uX : Point F m) : (ofLPZ d uX).uX = uX := rfl
@[simp] theorem uZ_ofLPZ (d : LPData F m) (uX : Point F m) : (ofLPZ d uX).uZ = d.pt := rfl

/-! ## The three splittings, on each of the two sample spaces

Each pair of equivalences isolates the same part of the sample --- the part a hypothesis of the
pasting lemma can depend on --- on the content side and on the product side. `avg_comp_equiv_fst`
then says both uniform averages equal the uniform average over that part. -/

/-- A content splits as (its `X` data, its `Z` point) and its probes. -/
def contentSplitX : Content F m ≃ (LPData F m × Point F m) × (F × F) where
  toFun c := ((c.lpX, c.uZ), (c.rX, c.rZ))
  invFun p := ⟨p.1.1.pt, p.1.2, p.1.1.s, p.1.1.raw, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A pair of line-point data splits as (the `X` one, the `Z` one's point) and the `Z` one's line. -/
def pairSplitX : LPData F m × LPData F m ≃ (LPData F m × Point F m) × (F × Point F m) where
  toFun p := ((p.1, p.2.pt), (p.2.s, p.2.raw))
  invFun q := (q.1.1, ⟨q.1.2, q.2.1, q.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The mirror of `contentSplitX`. -/
def contentSplitZ : Content F m ≃ (LPData F m × Point F m) × (F × F) where
  toFun c := ((c.lpZ, c.uX), (c.rX, c.rZ))
  invFun p := ⟨p.1.2, p.1.1.pt, p.1.1.s, p.1.1.raw, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The mirror of `pairSplitX`. -/
def pairSplitZ : LPData F m × LPData F m ≃ (LPData F m × Point F m) × (F × Point F m) where
  toFun p := ((p.2, p.1.pt), (p.1.s, p.1.raw))
  invFun q := (⟨q.1.2, q.2.1, q.2.2⟩, q.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A content splits as its two points and everything else. -/
def contentSplitPts :
    Content F m ≃ (Point F m × Point F m) × (F × Point F m × F × F) where
  toFun c := ((c.uX, c.uZ), (c.s, c.v, c.rX, c.rZ))
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## The three laws that agree -/

/-! ## The change of variables, at the product

`MIPRE.QLD.sum_shift_gen` (in `Lines.lean`, where the content instance of it lives) needs only a
finite sample space, a shift action on it, and a direction the shift does not move. So it applies to a
*pair* of line-point data with the shift acting on the `X` side only, which is what the product form
of the pasting lemma's collision term needs; all that is required here is the action and its three
properties.
-/

/-! ### The shift on a pair, and what it leaves alone -/

variable [Algebra (ZMod 2) F] {hm : m ∣ Fintype.card F}

/-- The shift on a pair of line-point data: move the `X` side's point, leave the `Z` side alone. -/
def pairShift (w : Point F m) (p : LPData F m × LPData F m) : LPData F m × LPData F m :=
  (⟨p.1.pt + w, p.1.s, p.1.raw⟩, p.2)

/-- The `X` line's direction, read off a pair through the content the `X` side presents. -/
def pairDirX (PX : LinePres F m hm .X) (p : LPData F m × LPData F m) : Point F m :=
  PX.dir (ofLPX p.1 p.2.pt)

@[simp] theorem pairShift_zero (p : LPData F m × LPData F m) : pairShift 0 p = p := by
  rw [pairShift, add_zero]

/-! ## `lem:qld-pairs-of-lines`, at a product of two independent line-point pairs

`pairs_of_lines_gen` asks for a content per side and a shift both sides see as a shift of the `X`
point. A pair of line-point data supplies exactly that: each side's content is its own point, seed
and raw direction, with the *other* side's point filled in as the content's other point --- which no
quantity of that side's line depends on --- and `pairShift` moves the `X` point. So the product form
is an instance, with nothing to prove beyond the two `rfl`s below.
-/

/-- The `X`-side content a pair of line-point data presents: the `X` side's own line-point data, with
the `Z` side's point as the content's other point. -/
def pairCX (p : LPData F m × LPData F m) : Content F m := ofLPX p.1 p.2.pt

/-- The `Z`-side content. Its seed and raw direction are the `Z` side's own, independent of the `X`
side's --- which is the whole difference from a single content. -/
def pairCZ (p : LPData F m × LPData F m) : Content F m := ofLPZ p.2 p.1.pt

@[simp] theorem pairDirX_eq (PX : LinePres F m hm .X) (p : LPData F m × LPData F m) :
    pairDirX PX p = PX.dir (pairCX p) := rfl

@[simp] theorem pairCX_pairShift (w : Point F m) (p : LPData F m × LPData F m) :
    pairCX (pairShift w p) = Content.shiftPt .X w (pairCX p) := rfl

@[simp] theorem pairCZ_pairShift (w : Point F m) (p : LPData F m × LPData F m) :
    pairCZ (pairShift w p) = Content.shiftPt .X w (pairCZ p) := rfl

variable {d : ℕ} {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ε : ℝ}

/-! ### The combined point measurement, indexed by the pair of points

`lem:qld-combined-points` is stated over the Pauli basis test's own contents, and the measurement it
produces is indexed by them. Every quantity it is bounded against depends on the content only through
its **two points**, so the same construction runs at the pair of points and gives a measurement that
any sample space carrying two points can use --- in particular a pair of line-point data, where the
content-indexed version would have to be fed contents with zeroed probes and the averages would not
match. -/

/-! ## The line data of one side factors through that side's line-point data

Every quantity of the `X` line --- the measurement, the parameter, the collision probability ---
reads the content only through its `X` point, its seed and its raw direction, which is exactly
`Content.lpX`. Saying so once is what lets a content-level bound be read as a bound on the product,
through `avg_content_eq_pair_X`: the two laws agree on quantities of `(lpX, uZ)`, and this is the
proof that the quantities in question are of that shape.

The hypothesis is the three data a `LinePres` carries. Both line presentations satisfy it by `rfl`:
`dirOf` and `ddirOf` read the seed and the raw direction, the base point is the canonical
representative of the side's own point, and `Content.question` at a line type reads nothing else. -/

section Factor

variable {M : Question F m → POVM (Answer F m d) dB}

/-- `PX` reads the content only through its `X` line-point data. -/
def FactorsX (PX : LinePres F m hm .X) : Prop :=
  ∀ (c : Content F m) (u : Point F m),
    PX.base (ofLPX c.lpX u) = PX.base c ∧ PX.dir (ofLPX c.lpX u) = PX.dir c
      ∧ (ofLPX c.lpX u).question hm PX.ty = c.question hm PX.ty

/-- `PZ` reads the content only through its `Z` line-point data. -/
def FactorsZ (PZ : LinePres F m hm .Z) : Prop :=
  ∀ (c : Content F m) (u : Point F m),
    PZ.base (ofLPZ c.lpZ u) = PZ.base c ∧ PZ.dir (ofLPZ c.lpZ u) = PZ.dir c
      ∧ (ofLPZ c.lpZ u).question hm PZ.ty = c.question hm PZ.ty

/-! ### The four bounds, read on the product

Each is the content-level bound with `avg_content_eq_pair_X` or `avg_content_eq_pair_Z` applied and
the factoring lemmas used to put the summand in the shape those identities need. -/

end Factor

/-! ## `lem:qld-pairs-of-lines` on the product, from the game

The product form of the pasting conclusion, with only game-level hypotheses on the `X` and `Z` line
presentations. Every input is the content-level one of `pairs_of_lines_of_items`, read on the product
through the four transfer identities above; the combined point measurement is the one indexed by the
pair of points, which is what makes the reading possible. -/

section Game

end Game

end MIPRE.QLD


