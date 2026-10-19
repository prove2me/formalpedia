-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Combine
-- name    : MIPRE_Background_QLD_Combine
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:54:38.157602+00:00
-- url     : https://prove2.me/theorems/6a42c4f2-741d-42ef-a84a-b3d16f83def7
-- title:
--   Definitions of Combine: The combining map and the padded line measurement Blueprint `lem:qld-padded-lines`, the definitional half
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Combine` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The combining map and the padded line measurement. Blueprint `lem:qld-padded-lines`, the definitional half. The pairs-of-lines stage measures a *pair* of line polynomials, one per basis; the low-degree test over the padded space `F_q^{4m}` wants a *single* polynomial on a single padded line. The bridge is the paper's combining map: on the padded point `u = (x, z, alpha, beta, w)` the combined polynomial takes the value `alpha * f_X(x) + beta * f_Z(z)`. Three things have to be said about it, and this file says them. * **It is a polynomial of degree at most `md + 1` on the padded line.**…
--
--   **Definitions** (16): `MIPRE.QLD.DegLE` (**Degree at most `k`**, as a predicate on coefficient vectors: everything above `k` vanishes.); `MIPRE.QLD.SubRand` (The fresh randomness the subline construction draws: a seed and a raw direction per side.); `MIPRE.QLD.aAffOf` (`alpha` along the padded line.); `MIPRE.QLD.affEval` (An affine map `t |-> a.1 + a.2 * t` of the line parameter, as the pair of its coefficients.); `MIPRE.QLD.affPoly` (The degree-one polynomial an affine map is.); `MIPRE.QLD.bAffOf` (`beta` along the padded line.); `MIPRE.QLD.combine` (**The combining map.** The four affine maps are, in order: `alpha` and `beta` along the padded line, and the parameter of the `X` and `Z`…); `MIPRE.QLD.combinePoly` (The polynomial `alpha(t) f_X(x(t)) + beta(t) f_Z(z(t))` with all four substitutions affine.); `MIPRE.QLD.ofPoly` (The coefficient vector of degree at most `n` a polynomial truncates to.); `MIPRE.QLD.padCombine` (**The combining map at a padded line and its two sublines.**); `MIPRE.QLD.padLineMats` (**The padded line measurement `Q-hat^l`.** Its outcomes are line polynomials of degree at most `md + 1` on the padded line, and on an…); `MIPRE.QLD.padShift` (Moving the padded point along the padded line by `tau`.); `MIPRE.QLD.subAff` (**The affine substitution the subline's parametrization induces.** The constant term is the parameter of the unshifted block, and the…); and -11 more.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `padShift_pt`, `padShift_raw`, `padShift_s`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Combine` (`MIPRE/Background/QLD/Combine.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 64 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Combine.lean; blueprint lem:qld-padded-lines

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Combine.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_QLD_Product

/-!
# The combining map and the padded line measurement

Blueprint `lem:qld-padded-lines`, the definitional half. The pairs-of-lines stage measures a *pair*
of line polynomials, one per basis; the low-degree test over the padded space
`F_q^{4m}` wants a *single* polynomial on a single padded line. The bridge is the paper's combining
map: on the padded point `u = (x, z, alpha, beta, w)` the combined polynomial takes the value

  `alpha * f_X(x) + beta * f_Z(z)`.

Three things have to be said about it, and this file says them.

* **It is a polynomial of degree at most `md + 1` on the padded line.** Restricted to the padded
  line the two evaluations become evaluations of `f_X` and `f_Z` at *affine* functions of the padded
  parameter --- which is exactly Property 2 of `lem:qld-sublines`, made quantitative --- and the
  factors `alpha` and `beta` are affine in it too. So the whole thing is a product of an affine
  polynomial with a degree-`md` one, and `combine` is that polynomial, built through Mathlib's
  `Polynomial` and truncated back to a coefficient vector.
* **On an axis-parallel padded line the degree drops to `d`.** The padded direction is a single
  coordinate, and the case distinction is the one `padCase` already makes: in the `X` and `Z` blocks
  `alpha` and `beta` are constant along the line, so the degree is that of `f_X` and `f_Z`; at
  `alpha`, `beta` or a dummy coordinate *both* blocks are constant along the line, so the combined
  polynomial is affine. The first case needs `f_X` and `f_Z` to have degree `d`, which is
  `lem:qld-axis-degree`; the second needs only `d >= 1`.
* **The measurement.** `padLineMats` is the paper's `Q-hat^l`: the conditional average, over the
  fresh randomness the subline construction draws, of the pasted line measurement
  `T^{l_X,l_Z}`, coarse-grained by the combining map. It is a POVM.

What is *not* here is the consistency bound `delta_combine`; see the blueprint.

## The affine data, and why the whole geometry is in `xBlk_dir_sub`

The one calculation behind the affine substitutions is this. Moving along the padded line moves the
`X` block by `tau * xBlk(dir)`, and `xBlk_dir_sub` says that block is *either* the `X` subline's own
direction *or* zero. In the first case the parameter on the subline moves by exactly `tau`, in the
second it does not move at all --- so in both cases it is `p0 + c * tau` with `c` one or zero, and
`subAff` is that pair. Nothing else about the construction is used.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.CL
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

/-! ## Affine maps of the line parameter -/

section Aff

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- An affine map `t |-> a.1 + a.2 * t` of the line parameter, as the pair of its coefficients. -/
def affEval (a : F × F) (t : F) : F := a.1 + a.2 * t

/-- The degree-one polynomial an affine map is. -/
def affPoly (a : F × F) : Polynomial F := Polynomial.C a.1 + Polynomial.C a.2 * Polynomial.X

/-! ## Coefficient vectors and polynomials, the other way

`toPoly` (in `Lines.lean`) reads a coefficient vector as a polynomial; `ofPoly` truncates a
polynomial to a coefficient vector, and agrees with it in value as soon as the degree fits. -/

/-- The coefficient vector of degree at most `n` a polynomial truncates to. -/
def ofPoly (n : ℕ) (p : Polynomial F) : LinePoly F n := fun i => p.coeff (i : ℕ)

/-- **Degree at most `k`**, as a predicate on coefficient vectors: everything above `k` vanishes.
The answer alphabet is `LinePoly F (m d)` throughout, so a sharper degree bound on an
axis-parallel line is a property of the vector rather than a change of type. -/
def DegLE (f : LinePoly F n) (k : ℕ) : Prop := ∀ i : Fin (n + 1), k < (i : ℕ) → f i = 0

/-! ## The combining map -/

/-- The polynomial `alpha(t) f_X(x(t)) + beta(t) f_Z(z(t))` with all four substitutions affine. -/
def combinePoly (aAff bAff xAff zAff : F × F) (fX fZ : LinePoly F n) : Polynomial F :=
  affPoly aAff * (toPoly fX).comp (affPoly xAff)
    + affPoly bAff * (toPoly fZ).comp (affPoly zAff)

/-- **The combining map.** The four affine maps are, in order: `alpha` and `beta` along the padded
line, and the parameter of the `X` and `Z` blocks on their sublines. -/
def combine (aAff bAff xAff zAff : F × F) (fX fZ : LinePoly F n) : LinePoly F (n + 1) :=
  ofPoly (n + 1) (combinePoly aAff bAff xAff zAff fX fZ)

end Aff

/-! ## The affine substitution a subline induces -/

section SubAff

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
  [NeZero m]

/-- **The affine substitution the subline's parametrization induces.** The constant term is the
parameter of the unshifted block, and the linear term is `1` exactly when the padded direction moves
the block along a nondegenerate subline. -/
def subAff (W w x : Point F m) : F × F :=
  (CL.lineParam (CL.rep W x) W x, if w = W ∧ W ≠ 0 then 1 else 0)

end SubAff

/-! ## The affine data of a padded line and its sublines -/

section Padded

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- Moving the padded point along the padded line by `tau`. -/
def padShift (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (tau : F) (P : LPData F (4 * m)) :
    LPData F (4 * m) := ⟨P.pt + tau • P.dir hm4 ty, P.s, P.raw⟩

@[simp] theorem padShift_pt (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (tau : F)
    (P : LPData F (4 * m)) : (padShift hm4 ty tau P).pt = P.pt + tau • P.dir hm4 ty := rfl

@[simp] theorem padShift_s (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (tau : F)
    (P : LPData F (4 * m)) : (padShift hm4 ty tau P).s = P.s := rfl

@[simp] theorem padShift_raw (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (tau : F)
    (P : LPData F (4 * m)) : (padShift hm4 ty tau P).raw = P.raw := rfl

variable (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F)

/-! ### The four affine maps -/

/-- `alpha` along the padded line. -/
def aAffOf (ty : CL.Ty) (P : LPData F (4 * m)) : F × F := (alph P.pt, alph (P.dir hm4 ty))

/-- `beta` along the padded line. -/
def bAffOf (ty : CL.Ty) (P : LPData F (4 * m)) : F × F := (bet P.pt, bet (P.dir hm4 ty))

/-- The parameter of the `X` block on the `X` subline, along the padded line. -/
def xAffOf (ty : CL.Ty) (P : LPData F (4 * m)) (e : F × Point F m) : F × F :=
  subAff ((subX hm4 hm P e).dir hm ty) (xBlk (P.dir hm4 ty)) (xBlk P.pt)

/-- The parameter of the `Z` block on the `Z` subline, along the padded line. -/
def zAffOf (ty : CL.Ty) (P : LPData F (4 * m)) (e : F × Point F m) : F × F :=
  subAff ((subZ hm4 hm ty P e).dir hm ty) (zBlk (P.dir hm4 ty)) (zBlk P.pt)

/-! ### The parameter identity

A line presentation reads the subline data through `ofLPX` / `ofLPZ`; the two hypotheses say it reads
it as the seeded test does --- the base point is the canonical representative of the point in the
direction, and the direction is the one the data presents. Both hold for `aPres` and `dPres` by
`rfl`. -/

/-! ### The padded combining map -/

/-- **The combining map at a padded line and its two sublines.** -/
def padCombine (ty : CL.Ty) (d : ℕ) (P : LPData F (4 * m)) (eX eZ : F × Point F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) : LinePoly F (m * d + 1) :=
  combine (aAffOf hm4 ty P) (bAffOf hm4 ty P) (xAffOf hm4 hm ty P eX) (zAffOf hm4 hm ty P eZ)
    q.1 q.2

/-! ### The degree bound on an axis-parallel padded line -/

end Padded

/-! ## The padded line measurement

The paper's `Q-hat^l_f` is the conditional average, over the sublines the construction of
`lem:qld-sublines` draws for the given padded line, of the pasted line measurement
`T^{l_X,l_Z}_{f_X,f_Z}`, coarse-grained by the combining map. Conditioning on the padded line means
averaging over the fresh randomness the construction draws --- a seed and a raw direction per side
--- and nothing else, so the conditional average is a plain uniform average over `SubRand`. -/

section POVM

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dB : Type} [Fintype dB] [DecidableEq dB] {hm : m ∣ Fintype.card F}
  {M : Question F m → POVM (Answer F m d) dB}

/-- The fresh randomness the subline construction draws: a seed and a raw direction per side. -/
abbrev SubRand (F : Type*) (m : ℕ) := (F × Point F m) × (F × Point F m)

/-- The pair of subline data a padded line and the fresh randomness produce --- the sample the
product form of `lem:qld-pairs-of-lines` is stated over. -/
def subPair (hm4 : 4 * m ∣ Fintype.card F) (hm : m ∣ Fintype.card F) (ty : CL.Ty)
    (P : LPData F (4 * m)) (e : SubRand F m) : LPData F m × LPData F m :=
  (subX hm4 hm P e.1, subZ hm4 hm ty P e.2)

/-- **The padded line measurement `Q-hat^l`.** Its outcomes are line polynomials of degree at most
`md + 1` on the padded line, and on an axis-parallel padded line `degLE_padCombine_aline` sharpens
that to `d`. -/
def padLineMats (hm4 : 4 * m ∣ Fintype.card F) (ty : CL.Ty) (PX : LinePres F m hm .X)
    (PZ : LinePres F m hm .Z) (M : Question F m → POVM (Answer F m d) dB)
    (P : LPData F (4 * m)) (f : LinePoly F (m * d + 1)) :
    Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ :=
  ((Fintype.card (SubRand F m) : ℝ))⁻¹ • ∑ e : SubRand F m,
    ∑ q ∈ univ.filter fun q : LinePoly F (m * d) × LinePoly F (m * d) =>
        padCombine hm4 hm ty d P e.1 e.2 q = f,
      pasteLine PX PZ d M (pairCX (subPair hm4 hm ty P e)) (pairCZ (subPair hm4 hm ty P e)) q

end POVM

end MIPRE.QLD


