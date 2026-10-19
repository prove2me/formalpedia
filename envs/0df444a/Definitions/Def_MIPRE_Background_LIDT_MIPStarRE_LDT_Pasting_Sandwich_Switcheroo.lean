-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:45:11.040642+00:00
-- url     : https://prove2.me/theorems/28b670de-ac1e-4c9f-aeaf-e99552a94498
-- title:
--   Definitions of Switcheroo: Section 12 — Sandwich constructions: switcheroo families Switcheroo, complete-part, and half-product operator families
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Sandwich.Switcheroo` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 12 — Sandwich constructions: switcheroo families. Switcheroo, complete-part, and half-product operator families.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (23): `MIPStarRE.LDT.Pasting.completePartPointProductLeft` (Concrete family for `G^x_g G^y`.); `MIPStarRE.LDT.Pasting.completePartPointProductRight` (Concrete family for `G^y G^x_g`.); `MIPStarRE.LDT.Pasting.completePartTotalProductLeft` (Concrete family for `G^x G^y`.); `MIPStarRE.LDT.Pasting.completePartTotalProductRight` (Concrete family for `G^y G^x`.); `MIPStarRE.LDT.Pasting.gHatHalfProductOutcomeOperator` (The ordered half-product `\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`.); `MIPStarRE.LDT.Pasting.gHatHalfProductTotalOperator` (The total half-product `\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`.); `MIPStarRE.LDT.Pasting.gHatPairProductLeft` (Concrete family for the pairwise product `\widehat G^x_g \widehat G^y_h`.); `MIPStarRE.LDT.Pasting.gHatPairProductRight` (Concrete family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`.); `MIPStarRE.LDT.Pasting.gHatRotatedHalfProductOutcomeOperator` (The cyclically rotated half-product `\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`.); `MIPStarRE.LDT.Pasting.gHatRotatedHalfProductTotalOperator` (The total cyclically rotated half-product.); `MIPStarRE.LDT.Pasting.gHatSelfConsistencyLeftFamily` (Left tensor-placement for `\widehat G^x_g`.); `MIPStarRE.LDT.Pasting.gHatSelfConsistencyRightFamily` (Right tensor-placement for `\widehat G^x_g`.); and 0 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Sandwich.Switcheroo` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 30 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Sandwich/Switcheroo.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SProd
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Families

set_option backward.isDefEq.respectTransparency false

/-!
# Section 12 — Sandwich constructions: switcheroo families

Switcheroo, complete-part, and half-product operator families.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyLeft {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((M x).toSubMeas)

/-- Right tensor-placement for the auxiliary family `M^x_o`. -/
def switcherooSelfConsistencyRight {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxSubMeas (SliceQuestion params) Outcome (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((M x).toSubMeas)

/-- Concrete hypothesis family for `G^x_g M^y_o`. -/
noncomputable def switcherooPointProductLeft
    {Outcome : Type*} [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete hypothesis family for `M^y_o G^x_g` on the
`Polynomial params × Outcome` outcome type. -/
noncomputable def switcherooPointProductRight
    {Outcome : Type*} [Fintype Outcome] (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params × Outcome) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((family.meas q.1).toSubMeas)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `G^x M^y_o`. -/
noncomputable def switcherooAggregateLeft {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.1)
        ((M q.2).toSubMeas)

/-- Concrete aggregate family for `M^y_o G^x`. -/
noncomputable def switcherooAggregateRight {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((M q.2).toSubMeas)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y`. -/
noncomputable def completePartPointProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x_g`. -/
noncomputable def completePartPointProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x G^y`. -/
noncomputable def completePartTotalProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        (completePartSubMeas params family q.1)
        (completePartSubMeas params family q.2)

/-- Concrete family for `G^y G^x`. -/
noncomputable def completePartTotalProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (completePartSubMeas params family q.2)
        (completePartSubMeas params family q.1)

/-- Concrete family for `G^x_g G^y_⊥`. -/
noncomputable def incompletePartPointProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        ((family.meas q.1).toSubMeas)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_g`. -/
noncomputable def incompletePartPointProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (Polynomial params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family q.2)
        ((family.meas q.1).toSubMeas)

/-- Concrete family for `G^x_⊥ G^y_⊥`. -/
noncomputable def incompletePartTotalProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnRight
        (incompletePartSubMeas params family q.1)
        (incompletePartSubMeas params family q.2)

/-- Concrete family for `G^y_⊥ G^x_⊥`. -/
noncomputable def incompletePartTotalProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) Unit (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      multiplyByTotalOnLeft
        (incompletePartSubMeas params family q.2)
        (incompletePartSubMeas params family q.1)

/-- Left tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- Right tensor-placement for `\widehat G^x_g`. -/
noncomputable def gHatSelfConsistencyRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) (GHatOutcome params) (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) ((gHatIdxMeas params family x).toSubMeas)

/-- Concrete family for the pairwise product `\widehat G^x_g \widehat G^y_h`. -/
noncomputable def gHatPairProductLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- Concrete family for the reversed pairwise product `\widehat G^y_h \widehat G^x_g`. -/
noncomputable def gHatPairProductRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxOpFamily (SlicePairQuestion params) (GHatOutcome params × GHatOutcome params) (ι × ι) :=
  fun q =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((gHatIdxMeas params family q.1).toSubMeas)
        ((gHatIdxMeas params family q.2).toSubMeas)

/-- The ordered half-product `\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductOutcomeOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0) *
        gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs)

/-- The total half-product
`\sum_{g_1,\dots,g_k} \widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k}`. -/
noncomputable def gHatHalfProductTotalOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      ((gHatIdxMeas params family (xs 0)).toSubMeas).total *
        gHatHalfProductTotalOperator params family k (pointTupleTail xs)

/-- The cyclically rotated half-product
`\widehat G^{x_2}_{g_2} \cdots \widehat G^{x_k}_{g_k} \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatRotatedHalfProductOutcomeOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → MIPStarRE.Quantum.Op ι
  | 0, _xs, _gs =>
      1
  | k + 1, xs, gs =>
      gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) (gHatTupleOutcomeTail gs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).outcome (gs 0)

/-- The total cyclically rotated half-product. -/
noncomputable def gHatRotatedHalfProductTotalOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (k : ℕ) → PointTuple params k → MIPStarRE.Quantum.Op ι
  | 0, _xs =>
      1
  | k + 1, xs =>
      gHatHalfProductTotalOperator params family k (pointTupleTail xs) *
        ((gHatIdxMeas params family (xs 0)).toSubMeas).total

/-- Splitting a nonempty completed-outcome tuple into its first outcome and tail. -/
def gHatTupleOutcomeConsEquiv' (params : Parameters) [FieldModel params.q] (k : ℕ) :
    GHatTupleOutcome params (k + 1) ≃ GHatOutcome params × GHatTupleOutcome params k where
  toFun gs := (gs 0, gHatTupleOutcomeTail gs)
  invFun p := Fin.cons p.1 p.2
  left_inv gs := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  right_inv p := by
    cases p
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

end MIPStarRE.LDT.Pasting


