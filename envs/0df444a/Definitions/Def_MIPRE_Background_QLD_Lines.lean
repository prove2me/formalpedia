-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Lines
-- name    : MIPRE_Background_QLD_Lines
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:48:53.442598+00:00
-- url     : https://prove2.me/theorems/9570159c-cb45-4cc6-9854-5a1ceda1228d
-- title:
--   Definitions of Lines: Pairs of lines Blueprint `lem:qld-pairs-of-lines`, the paper's `lem:qld-xz-lines`
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Lines` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pairs of lines. Blueprint `lem:qld-pairs-of-lines`, the paper's `lem:qld-xz-lines`. The combined point measurement of `lem:qld-combined-points` returns both bases' values at the two sampled points; this stage replaces it by a measurement returning a *pair of line polynomials*, one per basis, which is what the padding stage can then compare with a low-degree test. The analytic content is the pasting lemma (`MIPRE/Foundations/Pasting.lean`). What this file supplies is its four hypotheses at the QLD line measurements, and there are three pieces of bookkeeping in the way. * **The marginal step.**…
--
--   **Definitions** (19): `MIPRE.QLD.Bas.other` (The other basis.); `MIPRE.QLD.Content.shiftAlong` (The content shifted along a direction it determines itself.); `MIPRE.QLD.Content.shiftPt` (Adding a vector to the content's `W`-point, leaving everything else alone.); `MIPRE.QLD.Content.shiftV` (Adding a vector to the content's diagonal direction, leaving everything else alone.); `MIPRE.QLD.LinePres` (A line presentation: what the content tells a player about the line on side `W`.); `MIPRE.QLD.LinePres.lineEvalMats` (The same measurement, coarse-grained by evaluation at the sampled point's parameter.); `MIPRE.QLD.LinePres.lineMats` (The expanded line measurement the presentation carries, as a family of matrices.); `MIPRE.QLD.LinePres.param` (The parameter of the sampled point on the line.); `MIPRE.QLD.aPres` (The axis-parallel line presentation on side `W`.); `MIPRE.QLD.collProb` (The collision probability of a presentation: the fraction of parameters at which two distinct line polynomials of degree at most `m d` can…); `MIPRE.QLD.dPres` (The diagonal line presentation on side `W`.); `MIPRE.QLD.deltaPairs` (**The error of `lem:qld-pairs-of-lines`**, the paper's `delta_P`: `poly(eps, eps_c)` with `eps_c` the average collision probability of the…); `MIPRE.QLD.deltaPairsD` (The marginal consistency the pasting lemma is fed.); `MIPRE.QLD.extHat` (The state the dilated joint point measurement acts on: the expanded state with one `F_q x F_q` register adjoined to each party.); and -5 more.
--
--   **Embedded lemmas** (28): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `shiftPt_other_pt`, `shiftPt_pt`, `shiftPt_pt_X_Z`, `shiftPt_pt_Z_X`, `shiftPt_pt_other`, `shiftPt_s`, `shiftPt_v`, `shiftPt_zero`, `shiftV_s`, `shiftV_v`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Lines` (`MIPRE/Background/QLD/Lines.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 60 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Lines.lean; blueprint lem:qld-pairs-of-lines

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Lines.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_aOp_sum

/-!
# Pairs of lines

Blueprint `lem:qld-pairs-of-lines`, the paper's `lem:qld-xz-lines`. The combined point measurement
of `lem:qld-combined-points` returns both bases' values at the two sampled points; this stage
replaces it by a measurement returning a *pair of line polynomials*, one per basis, which is what
the padding stage can then compare with a low-degree test.

The analytic content is the pasting lemma (`MIPRE/Foundations/Pasting.lean`). What this file
supplies is its four hypotheses at the QLD line measurements, and there are three pieces of
bookkeeping in the way.

* **The marginal step.** `lem:qld-combined-points` gives the joint measurement against the
  *ordered product* of the two point measurements; the pasting lemma wants each marginal against a
  single line measurement. `sum_xSqNorm_marg_le'` takes the first step and a three-term triangle
  through Bob's own point measurement takes the second.
* **The extended space.** The joint measurement lives on each party's space enlarged by one
  `F_q x F_q` register (the Naimark dilation); the line measurements live on the unenlarged ones.
  `xSqNorm_extVec2_aOp` transports the latter.
* **The probe.** The pasting lemma's collision term needs the point to be uniform on its line once
  the line is fixed. Here the content determines both, so the factorization is produced by
  *shifting the point along the direction the content itself carries*: for each fixed shift the map
  is a bijection of contents, the line data is invariant under it, and the parameter of the point
  moves by exactly the shift.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

/-! ## Line polynomials as polynomials

`LinePoly F n` is a coefficient vector, which is what makes the answer alphabets finite types. To
count the parameters at which two of them agree one wants Mathlib's `Polynomial`, and the bridge is
one definition and three lemmas. -/

section Poly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The polynomial a coefficient vector represents. -/
def toPoly (f : LinePoly F n) : Polynomial F :=
  ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (f i)

end Poly

/-! ## The parameter of a shifted point -/

section Shift

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- **The canonical representative does not see a shift along the direction**: the shifted point is
on the same line. -/
theorem rep_add_smul (w x : Point F m) (t : F) :
    MIPRE.LIDT.CL.rep w (x + t • w) = MIPRE.LIDT.CL.rep w x := by
  rw [MIPRE.LIDT.CL.rep, MIPRE.LIDT.CL.rep, map_add,
    show (MIPRE.CL.canonLin (Submodule.span F {w})) (t • w) = 0 from by
      rw [← LinearMap.mem_ker, MIPRE.CL.ker_canonLin]
      exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self w),
    add_zero]

end Shift

/-! ## Shifting the content's point along its line

The pasting lemma's collision term needs the point to be uniform on its line once the line is
fixed. The content determines both, so the factorization is produced by *shifting*: for each fixed
shift `t` the map `c |-> c + t . dir(c)` on the `W`-point is a bijection of contents, so averaging
over contents and averaging over `(c, t)` give the same thing; the line data is invariant under it;
and the parameter of the point moves by exactly `t`. -/

section ContentShift

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ} [NeZero m]

/-- Adding a vector to the content's `W`-point, leaving everything else alone. -/
def Content.shiftPt (W : Bas) (w : Point F m) (c : Content F m) : Content F m :=
  match W with
  | .X => { c with uX := c.uX + w }
  | .Z => { c with uZ := c.uZ + w }

@[simp] theorem Content.shiftPt_s (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W w c).s = c.s := by cases W <;> rfl

@[simp] theorem Content.shiftPt_v (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W w c).v = c.v := by cases W <;> rfl

@[simp] theorem Content.shiftPt_pt (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W w c).pt W = c.pt W + w := by cases W <;> rfl

@[simp] theorem Content.shiftPt_pt_X_Z (w : Point F m) (c : Content F m) :
    (Content.shiftPt .X w c).pt .Z = c.pt .Z := rfl

@[simp] theorem Content.shiftPt_pt_Z_X (w : Point F m) (c : Content F m) :
    (Content.shiftPt .Z w c).pt .X = c.pt .X := rfl

@[simp] theorem Content.shiftPt_zero (W : Bas) (c : Content F m) :
    Content.shiftPt W 0 c = c := by
  cases W <;> · rw [Content.shiftPt, add_zero]

/-- The content shifted along a direction it determines itself. -/
def Content.shiftAlong (W : Bas) (dir : Content F m → Point F m) (t : F) (c : Content F m) :
    Content F m :=
  Content.shiftPt W (t • dir c) c

/-- Adding a vector to the content's diagonal direction, leaving everything else alone. The other
shift the argument needs: it is what makes a *degenerate* diagonal line rare. -/
def Content.shiftV (w : Point F m) (c : Content F m) : Content F m := { c with v := c.v + w }

@[simp] theorem Content.shiftV_s (w : Point F m) (c : Content F m) :
    (Content.shiftV w c).s = c.s := rfl

@[simp] theorem Content.shiftV_v (w : Point F m) (c : Content F m) :
    (Content.shiftV w c).v = c.v + w := rfl

@[simp] theorem Content.shiftV_zero (c : Content F m) : Content.shiftV 0 c = c := by
  rw [Content.shiftV, add_zero]

end ContentShift

/-! ## What the shift leaves alone

The line a content presents --- its question, its base point and its direction --- is invariant
under shifting the point along that direction, and so therefore is the line measurement. The point's
parameter is the only thing that moves. -/

section Invariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- The other basis. -/
def Bas.other : Bas → Bas
  | .X => .Z
  | .Z => .X

@[simp] theorem Content.shiftPt_pt_other (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W w c).pt W.other = c.pt W.other := by cases W <;> rfl

@[simp] theorem Content.shiftPt_other_pt (W : Bas) (w : Point F m) (c : Content F m) :
    (Content.shiftPt W.other w c).pt W = c.pt W := by cases W <;> rfl

theorem dirOf_shiftPt (hm : m ∣ Fintype.card F) (W : Bas) (w : Point F m) (c : Content F m) :
    dirOf hm (Content.shiftPt W w c) = dirOf hm c := by
  rw [dirOf, dirOf, Content.shiftPt_s]

theorem ddirOf_shiftPt (hm : m ∣ Fintype.card F) (W : Bas) (w : Point F m) (c : Content F m) :
    ddirOf hm (Content.shiftPt W w c) = ddirOf hm c := by
  rw [ddirOf, ddirOf, Content.shiftPt_s, Content.shiftPt_v]

theorem abaseOf_shiftAlong (hm : m ∣ Fintype.card F) (W : Bas) (t : F) (c : Content F m) :
    abaseOf hm W (Content.shiftAlong W (dirOf hm) t c) = abaseOf hm W c := by
  rw [abaseOf, abaseOf, Content.shiftAlong, dirOf_shiftPt, Content.shiftPt_pt, rep_add_smul]

theorem dbaseOf_shiftAlong (hm : m ∣ Fintype.card F) (W : Bas) (t : F) (c : Content F m) :
    dbaseOf hm W (Content.shiftAlong W (ddirOf hm) t c) = dbaseOf hm W c := by
  rw [dbaseOf, dbaseOf, Content.shiftAlong, ddirOf_shiftPt, Content.shiftPt_pt, rep_add_smul]

theorem question_aline_shiftAlong (hm : m ∣ Fintype.card F) (W : Bas) (t : F) (c : Content F m) :
    (Content.shiftAlong W (dirOf hm) t c).question hm (.aline W) = c.question hm (.aline W) := by
  rw [Content.question, Content.question, Content.shiftAlong, Content.shiftPt_s,
    Content.shiftPt_pt, dirOf]
  congr 1
  exact rep_add_smul _ _ _

theorem question_dline_shiftAlong (hm : m ∣ Fintype.card F) (W : Bas) (t : F) (c : Content F m) :
    (Content.shiftAlong W (ddirOf hm) t c).question hm (.dline W) = c.question hm (.dline W) := by
  rw [Content.question, Content.question, Content.shiftAlong, Content.shiftPt_s,
    Content.shiftPt_v, Content.shiftPt_pt, ddirOf]
  congr 1
  exact rep_add_smul _ _ _

theorem question_aline_shiftPt_other (hm : m ∣ Fintype.card F) (W : Bas) (w : Point F m)
    (c : Content F m) :
    (Content.shiftPt W.other w c).question hm (.aline W) = c.question hm (.aline W) := by
  cases W <;> rfl

theorem question_dline_shiftPt_other (hm : m ∣ Fintype.card F) (W : Bas) (w : Point F m)
    (c : Content F m) :
    (Content.shiftPt W.other w c).question hm (.dline W) = c.question hm (.dline W) := by
  cases W <;> rfl

end Invariance

/-! ## The line presentations, and the measurements they carry

A *line presentation* on one side is the question type the line is asked at together with its base
point and direction as functions of the content, and the six invariances the shift argument needs:
shifting either point along the relevant direction changes neither the direction, nor the base
point, nor the question. Both line types of both sides are presentations, and the pairs-of-lines
lemma is proved once for any pair of them. -/

section Pres

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- A line presentation: what the content tells a player about the line on side `W`. -/
structure LinePres (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    (m : ℕ) [NeZero m] (hm : m ∣ Fintype.card F) (W : Bas) where
  /-- The question type the line is asked at. -/
  ty : Ty
  /-- The base point of the line. -/
  base : Content F m → Point F m
  /-- The direction of the line. -/
  dir : Content F m → Point F m
  /-- Shifting the side's own point along the direction does not change the direction. -/
  dir_shift : ∀ (c : Content F m) (w : Point F m), dir (Content.shiftPt W w c) = dir c
  /-- ... nor the base point. -/
  base_shift : ∀ (c : Content F m) (t : F),
    base (Content.shiftPt W (t • dir c) c) = base c
  /-- ... nor the question. -/
  question_shift : ∀ (c : Content F m) (t : F),
    (Content.shiftPt W (t • dir c) c).question hm ty = c.question hm ty
  /-- Shifting the *other* side's point changes none of the three. -/
  dir_shift_other : ∀ (c : Content F m) (w : Point F m),
    dir (Content.shiftPt W.other w c) = dir c
  base_shift_other : ∀ (c : Content F m) (w : Point F m),
    base (Content.shiftPt W.other w c) = base c
  question_shift_other : ∀ (c : Content F m) (w : Point F m),
    (Content.shiftPt W.other w c).question hm ty = c.question hm ty

namespace LinePres

variable {hm : m ∣ Fintype.card F} {W : Bas}

/-- The parameter of the sampled point on the line. -/
def param (P : LinePres F m hm W) (c : Content F m) : F :=
  MIPRE.LIDT.CL.lineParam (P.base c) (P.dir c) (c.pt W)

/-- The expanded line measurement the presentation carries, as a family of matrices. -/
def lineMats {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) d') (c : Content F m) :
    LinePoly F (m * d) → Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  fun f => (((hatLinePOVM (m * d) hm M W P.ty P.base P.dir c).mats f).val)

/-- The same measurement, coarse-grained by evaluation at the sampled point's parameter. -/
def lineEvalMats {d' : Type} [Fintype d'] [DecidableEq d'] (P : LinePres F m hm W) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) d') (c : Content F m) :
    F → Matrix (d' × Anc F m) (d' × Anc F m) ℂ :=
  fun a => ((((hatLinePOVM (m * d) hm M W P.ty P.base P.dir c).map
    fun f => LinePoly.eval f (P.param c)).mats a).val)

end LinePres

/-! ### The four presentations, and the collision count -/

variable {hm : m ∣ Fintype.card F} {W : Bas}

/-- The axis-parallel line presentation on side `W`. -/
def aPres (hm : m ∣ Fintype.card F) (W : Bas) : LinePres F m hm W where
  ty := .aline W
  base := abaseOf hm W
  dir := dirOf hm
  dir_shift c w := dirOf_shiftPt hm W w c
  base_shift c t := abaseOf_shiftAlong hm W t c
  question_shift c t := question_aline_shiftAlong hm W t c
  dir_shift_other c w := dirOf_shiftPt hm W.other w c
  base_shift_other c w := by rw [abaseOf, abaseOf, dirOf_shiftPt, Content.shiftPt_other_pt]
  question_shift_other c w := question_aline_shiftPt_other hm W w c

/-- The diagonal line presentation on side `W`. -/
def dPres (hm : m ∣ Fintype.card F) (W : Bas) : LinePres F m hm W where
  ty := .dline W
  base := dbaseOf hm W
  dir := ddirOf hm
  dir_shift c w := ddirOf_shiftPt hm W w c
  base_shift c t := dbaseOf_shiftAlong hm W t c
  question_shift c t := question_dline_shiftAlong hm W t c
  dir_shift_other c w := ddirOf_shiftPt hm W.other w c
  base_shift_other c w := by rw [dbaseOf, dbaseOf, ddirOf_shiftPt, Content.shiftPt_other_pt]
  question_shift_other c w := question_dline_shiftPt_other hm W w c

/-- The collision probability of a presentation: the fraction of parameters at which two distinct
line polynomials of degree at most `m d` can agree. It is `m d / q` unless the line is degenerate,
and then the outcome map separates nothing. -/
def collProb (P : LinePres F m hm W) (d : ℕ) (c : Content F m) : ℝ :=
  if ∃ j, P.dir c j ≠ 0 then (m * d : ℝ) / (Fintype.card F : ℝ) else 1

end Pres

/-! ## The two sides, uniformly

Both sides of the pairs-of-lines lemma are proved by the same argument, so the side is a parameter
and the `(X, Z)` outcome pair is read through it. -/

section Sides

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- The value of an `(X, Z)` outcome pair on side `W`. -/
def valOf (W : Bas) (p : F × F) : F :=
  match W with
  | .X => p.1
  | .Z => p.2

/-- Reading an `(X, Z)` outcome pair as (this side, the other side). -/
def pairEquiv (W : Bas) : F × F ≃ F × F :=
  match W with
  | .X => Equiv.refl _
  | .Z => Equiv.prodComm F F

@[simp] theorem valOf_pairEquiv (W : Bas) (r : F × F) : valOf W (pairEquiv W r) = r.1 := by
  cases W <;> rfl

@[simp] theorem valOf_other_pairEquiv (W : Bas) (r : F × F) :
    valOf W.other (pairEquiv W r) = r.2 := by
  cases W <;> rfl

end Sides

/-! ## The hypotheses of the pasting lemma, at the line measurements -/

section Pairs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ} {ε : ℝ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}

@[simp] theorem aPres_ty (hm : m ∣ Fintype.card F) (W : Bas) :
    (aPres (F := F) (m := m) hm W).ty = .aline W := rfl

@[simp] theorem aPres_base (hm : m ∣ Fintype.card F) (W : Bas) :
    (aPres (F := F) (m := m) hm W).base = abaseOf hm W := rfl

@[simp] theorem aPres_dir (hm : m ∣ Fintype.card F) (W : Bas) :
    (aPres (F := F) (m := m) hm W).dir = dirOf hm := rfl

@[simp] theorem dPres_ty (hm : m ∣ Fintype.card F) (W : Bas) :
    (dPres (F := F) (m := m) hm W).ty = .dline W := rfl

@[simp] theorem dPres_base (hm : m ∣ Fintype.card F) (W : Bas) :
    (dPres (F := F) (m := m) hm W).base = dbaseOf hm W := rfl

@[simp] theorem dPres_dir (hm : m ∣ Fintype.card F) (W : Bas) :
    (dPres (F := F) (m := m) hm W).dir = ddirOf hm := rfl

/-- The state the dilated joint point measurement acts on: the expanded state with one
`F_q x F_q` register adjoined to each party. -/
def extHat (ψ : dA × dB → ℂ) :
    ((dA × Anc F m) × (F × F)) × ((dB × Anc F m) × (F × F)) → ℂ :=
  extVec2 (hatVec (F := F) (m := m) ψ) ((0 : F), (0 : F)) ((0 : F), (0 : F))

/-! ## The pasted line measurement -/

/-- **The pasted line measurement** `T^{l_X, l_Z}_{f_X, f_Z}`: Bob's `X`-line measurement
sandwiching his `Z`-line measurement, carried to his enlarged space.

The two lines are read off **two** contents, one per side. On the Pauli basis test's own question
distribution they are the same content, which is how `lem:qld-pairs-of-lines` uses this; the
combining stage needs them independent, and then they are not. Nothing in the pasting lemma forces
them to agree --- none of its hypotheses involves both lines --- which is why one definition serves
both. -/
def pasteLine (PX : LinePres F m hm .X) (PZ : LinePres F m hm .Z) (d : ℕ)
    (M : Question F m → POVM (Answer F m d) dB) (cX cZ : Content F m)
    (q : LinePoly F (m * d) × LinePoly F (m * d)) :
    Matrix ((dB × Anc F m) × (F × F)) ((dB × Anc F m) × (F × F)) ℂ :=
  aOp (PX.lineMats d M cX q.1 * PZ.lineMats d M cZ q.2 * PX.lineMats d M cX q.1)

/-! ## The lemma -/

/-! ## The lemma, from the game -/

/-- The larger of the two ordered-product constants of `lem:qld-combined-points`. -/
def kappaPairs (ε : ℝ) : ℝ := 4 * deltaQ ε + 461411328 * ε

/-- The marginal consistency the pasting lemma is fed. -/
def deltaPairsD (ε : ℝ) : ℝ :=
  2 * (10 * kappaPairs ε) + 2 * (2 * (172 * ε) + 2 * (172 * ε))

/-- **The error of `lem:qld-pairs-of-lines`**, the paper's `delta_P`: `poly(eps, eps_c)` with
`eps_c` the average collision probability of the outcome map, which for an axis-parallel line is
`m d / q`. -/
def deltaPairs (ε εc : ℝ) : ℝ :=
  deltaPairsD ε / 2 + Real.sqrt (deltaPairsD ε / 2)
    + Real.sqrt (32 * deltaPairsD ε + 4 * Real.sqrt (172 * ε) + 2 * εc)

/-! ### The items of `lem:qld-expanded-lines`, in the shape the assembly wants -/

end Pairs

end MIPRE.QLD

end


