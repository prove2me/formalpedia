-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:58.552153+00:00
-- url     : https://prove2.me/theorems/f148229e-4155-4e72-94dd-325325c34ea9
-- title:
--   Definitions of Approximation: Section 10 — commutativity points approximation layer Restricted-diagonal approximation infrastructure for…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.Approximation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 10 — commutativity points approximation layer. Restricted-diagonal approximation infrastructure for commutativity at points.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (9): `MIPStarRE.LDT.CommutativityPoints.opFamilyOfOutcome` (Build an operator family from its outcomes, taking the total to be their sum.); `MIPStarRE.LDT.CommutativityPoints.pointNextEquiv` (Decompose a point in `Point params.next` into its truncated point and final coordinate.); `MIPStarRE.LDT.CommutativityPoints.pointPairOutcomeSwapEquiv`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.Approximation.0.MIPStarRE.LDT.CommutativityPoints.lastRestrictedDirectionEquiv` (At the final restriction index, a restricted diagonal direction records all `m` coordinates, so it is equivalent to an unrestricted point…); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.Approximation.0.MIPStarRE.LDT.CommutativityPoints.lastRestrictedSampleEquivDiagonalLine` (At the final restriction index, a restricted diagonal sample is exactly a full diagonal line: the sample point becomes the base point and…); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.Approximation.0.MIPStarRE.LDT.CommutativityPoints.lastRestrictionIndex` (The final restriction index, corresponding to the paper's `m`-restricted diagonal-lines test.); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.Approximation.0.MIPStarRE.LDT.CommutativityPoints.rawAnswerDiagonalLineAnswerFamily` (Evaluate each answer-valued restricted diagonal measurement at the distinguished base parameter `zeroCoord`.); and -2 more.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `answer_sampledDiagonalLineApproximation`, `answer_sampledDiagonalLineConsistency`, `lastRestrictionIndex_val_succ`, `sampledDiagonalLineApproximation`, `sampledDiagonalLineConsistency`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.Approximation` (`MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/Approximation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 31 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/Approximation.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/CommutativityPoints/Approximation.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/Approximation.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Order.Monoid.NatCast
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
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
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
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Theorems.Thm_MIPStarRE_LDT_DiagonalLine_rebaseAt_rebase
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_simeqToApprox
import Theorems.Thm_MIPStarRE_LDT_bipartiteConsError_nonneg
import Theorems.Thm_MIPStarRE_LDT_postprocess_total

set_option backward.isDefEq.respectTransparency false

/-!
# Section 10 — commutativity points approximation layer

Restricted-diagonal approximation infrastructure for commutativity at points.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators

/-- The final restriction index, corresponding to the paper's `m`-restricted
diagonal-lines test. -/
def lastRestrictionIndex (params : Parameters) : Fin params.m :=
  ⟨params.m - 1, Nat.sub_lt params.hm Nat.zero_lt_one⟩

/-- Decompose a point in `Point params.next` into its truncated point and final coordinate. -/
def pointNextEquiv (params : Parameters) [FieldModel params.q] :
    Point params.next ≃ Point params × Fq params where
  toFun := fun u => (truncatePoint params u, pointHeight params u)
  invFun := fun ux => appendPoint params ux.1 ux.2
  left_inv := fun u => by
    funext i
    by_cases h : i.1 < params.m
    · simp [appendPoint, truncatePoint, h]
    · have hi : i.1 = params.m := by
        have hi_lt : i.1 < params.m + 1 := by
          simpa [Parameters.next] using i.2
        omega
      have hlast : i = lastCoord params := by
        apply Fin.ext
        simp [lastCoord, hi]
      simp [appendPoint, truncatePoint, pointHeight, hlast]
  right_inv := fun ⟨u, x⟩ => by
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]

/-- Build an operator family from its outcomes, taking the total to be their sum. -/
noncomputable def opFamilyOfOutcome {Outcome : Type*} [Fintype Outcome]
    (outcome : Outcome → MIPStarRE.Quantum.Op ι) :
    OpFamily Outcome ι where
  outcome := outcome
  total := ∑ a : Outcome, outcome a

abbrev pointPairOutcomeSwapEquiv (params : Parameters) :
    PointPairOutcome params ≃ PointPairOutcome params :=
  Equiv.prodComm _ _

lemma lastRestrictionIndex_val_succ
    (params : Parameters) :
    (lastRestrictionIndex params).val + 1 = params.m := by
  have hm := params.hm
  dsimp [lastRestrictionIndex]
  omega

/-- At the final restriction index, a restricted diagonal direction records all
`m` coordinates, so it is equivalent to an unrestricted point of `Point params`. -/
noncomputable def lastRestrictedDirectionEquiv
    (params : Parameters)
    [FieldModel params.q] :
    (Fin ((lastRestrictionIndex params).val + 1) → Fq params) ≃ Point params where
  toFun := extendRestrictedDirection (lastRestrictionIndex params)
  invFun := fun direction i =>
    direction ⟨i.val, by
      have h := lastRestrictionIndex_val_succ params
      omega⟩
  left_inv := fun free => by
    funext i
    have hlt : i.val < params.m := by
      have h := lastRestrictionIndex_val_succ params
      omega
    have hle : (⟨i.val, hlt⟩ : Fin params.m).val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨i.val, Nat.lt_succ_of_le hle⟩ : Fin ((lastRestrictionIndex params).val + 1)) = i := by
      ext
      try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    rw [← hidx]
    simp [extendRestrictedDirection, hle]
  right_inv := fun direction => by
    funext k
    have hk : k.val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨k.val, by
            have h := lastRestrictionIndex_val_succ params
            omega⟩ : Fin params.m) = k := by
      ext
      try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    rw [← hidx]
    simp [extendRestrictedDirection, hk]

/-- At the final restriction index, a restricted diagonal sample is exactly a
full diagonal line: the sample point becomes the base point and the restricted
direction determines all line coefficients. -/
noncomputable def lastRestrictedSampleEquivDiagonalLine
    (params : Parameters)
    [FieldModel params.q] :
    RestrictedDiagonalSample params (lastRestrictionIndex params) ≃ DiagonalLine params where
  toFun := fun s =>
    { base := s.1
      direction := lastRestrictedDirectionEquiv params s.2 }
  invFun := fun ℓ =>
    (ℓ.base, (lastRestrictedDirectionEquiv params).symm ℓ.direction)
  left_inv := fun ⟨base, free⟩ => by
    refine Prod.ext rfl ?_
    funext i
    have hlt : i.val < params.m := by
      have h := lastRestrictionIndex_val_succ params
      omega
    have hle : (⟨i.val, hlt⟩ : Fin params.m).val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨i.val, Nat.lt_succ_of_le hle⟩ : Fin ((lastRestrictionIndex params).val + 1)) = i := by
      ext
      try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    rw [← hidx]
    simp [lastRestrictedDirectionEquiv, extendRestrictedDirection, hle]
  right_inv := fun ⟨base, direction⟩ => by
    change
      ({ base := base,
         direction := extendRestrictedDirection (lastRestrictionIndex params)
           (fun i => direction ⟨i.val, by
             have h := lastRestrictionIndex_val_succ params
             omega⟩) } : DiagonalLine params) =
      ({ base := base, direction := direction } : DiagonalLine params)
    congr
    funext k
    have hk : k.val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨k.val, by
            have h := lastRestrictionIndex_val_succ params
            omega⟩ : Fin params.m) = k := by
      ext
      try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    rw [← hidx]
    simp [extendRestrictedDirection, hk]

/-- Rebase the last restricted diagonal sample so that its distinguished base
point appears at the queried parameter. This identifies the corrected diagonal
test sample space with the shared point-with-diagonal-line questions used in
the commutativity-at-points argument. -/
noncomputable def rebasedLastRestrictedQuestionEquiv
    (params : Parameters)
    [FieldModel params.q] :
    (RestrictedDiagonalSample params (lastRestrictionIndex params) × Fq params) ≃
      PointDiagonalLineQuestion params where
  toFun := fun st =>
    let ℓ := lastRestrictedSampleEquivDiagonalLine params st.1
    (DiagonalLine.rebaseAt ℓ (subCoord zeroCoord st.2), st.2)
  invFun := fun q =>
    let ℓ := DiagonalLine.rebaseAt q.1 q.2
    ((lastRestrictedSampleEquivDiagonalLine params).symm ℓ, q.2)
  left_inv := fun ⟨s, t⟩ => by
    simp [DiagonalLine.rebaseAt_rebase, addCoord_subCoord_left]
  right_inv := fun ⟨ℓ, t⟩ => by
    simp [DiagonalLine.rebaseAt_rebase, addCoord_subCoord_right]

/-- Evaluate each restricted diagonal measurement at the distinguished base
parameter `zeroCoord`, matching the corrected paper definition of the diagonal
branch. -/
noncomputable def rawDiagonalLineAnswerFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    postprocess
      ((strategy.diagonalMeasurement { base := s.1, direction := v }).toSubMeas)
      (· zeroCoord)

/-- Consistency transfer for the corrected diagonal branch at the final
restriction index.

The corrected test samples a restricted diagonal line and compares the point
measurement at its distinguished base point with the diagonal measurement
postprocessed by evaluation at `zeroCoord`. The global diagonal-line test bound
therefore controls this last restricted slice in particular. -/
lemma sampledDiagonalLineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamily strategy (lastRestrictionIndex params))
      (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError
        params gamma) := by
  let j := lastRestrictionIndex params
  let err : Fin params.m → Error := fun j =>
    bipartiteConsError strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (diagonalPointAnswerFamily strategy j)
      (rawDiagonalLineAnswerFamily params strategy j)
  have herr_nonneg : ∀ j : Fin params.m, 0 ≤ err j := by
    intro j'
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j'))
      (diagonalPointAnswerFamily strategy j')
      (rawDiagonalLineAnswerFamily params strategy j')
  have hsum_bound : ∑ j' : Fin params.m, err j' ≤ gamma * (params.m : Error) := by
    have hm_nonneg : 0 ≤ (params.m : Error) := by
      positivity
    have hm_ne : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hdiag := hgood.diagonalLineTest
    dsimp [SymStrat.diagonalFailureProbability, err] at hdiag
    calc
      ∑ j' : Fin params.m, err j'
        = (params.m : Error) * ((1 / (params.m : Error)) * ∑ j' : Fin params.m, err j') := by
            field_simp [hm_ne]
      _ ≤ (params.m : Error) * gamma := by
            exact mul_le_mul_of_nonneg_left hdiag hm_nonneg
      _ = gamma * (params.m : Error) := by ring
  have hj_le : err j ≤ gamma * (params.m : Error) := by
    calc
      err j ≤ ∑ j' : Fin params.m, err j' := by
        exact Finset.single_le_sum (fun j' _ => herr_nonneg j') (Finset.mem_univ j)
      _ ≤ gamma * (params.m : Error) := hsum_bound
  refine ⟨?_⟩
  simpa [j, err, restrictedDiagonalLinesConsistencyError] using hj_le

/-- Convert the corrected restricted diagonal consistency estimate into the
corresponding SDD approximation bound.

This is the final-slice version of the diagonal branch that feeds the
commutativity-at-points argument. It packages the consistency estimate through
`Preliminaries.simeqToApprox`. -/
lemma sampledDiagonalLineApproximation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (IdxSubMeas.liftLeft
        (diagonalPointAnswerFamily strategy (lastRestrictionIndex params)))
      (IdxSubMeas.liftRight
        (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params)))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let pointFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s => (strategy.pointMeasurement s.1).toMeasurement
  let lineFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s =>
      { toSubMeas := rawDiagonalLineAnswerFamily params strategy j s
        total_eq_one :=
          calc
            (rawDiagonalLineAnswerFamily params strategy j s).total =
                ((strategy.diagonalMeasurement
                  { base := s.1
                    direction := extendRestrictedDirection j s.2 }).toSubMeas).total := by
              dsimp [rawDiagonalLineAnswerFamily]
              rw [postprocess_total]
            _ = 1 :=
              (strategy.diagonalMeasurement
                { base := s.1
                  direction := extendRestrictedDirection j s.2 }).total_eq_one }
  have hcons := sampledDiagonalLineConsistency params strategy eps delta gamma hgood
  have hcons' :
      ConsRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (restrictedDiagonalLinesConsistencyError params gamma) := by
    change ConsRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamilyOf strategy.pointMeasurement (lastRestrictionIndex params))
      (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError params gamma)
    exact hcons
  have happrox :
      Preliminaries.BipartiteSDDRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (2 * restrictedDiagonalLinesConsistencyError params gamma) :=
    Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      pointFamily lineFamily
      (restrictedDiagonalLinesConsistencyError params gamma) hcons'
  refine ⟨?_⟩
  simpa [j, pointFamily, lineFamily, diagonalPointAnswerFamily,
    pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
    Preliminaries.BipartiteSDDRel, sddError, IdxMeas.toIdxSubMeas,
    IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    happrox.leftRightSquaredDistanceBound

/-- Evaluate each answer-valued restricted diagonal measurement at the
distinguished base parameter `zeroCoord`. -/
noncomputable def rawAnswerDiagonalLineAnswerFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    postprocess
      ((strategy.diagonalMeasurement { base := s.1, direction := v }).toSubMeas)
      (· zeroCoord)

/-- The answer-valued diagonal-line test controls the final restricted
diagonal slice. -/
lemma answer_sampledDiagonalLineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy (lastRestrictionIndex params))
      (rawAnswerDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError params gamma) := by
  let j := lastRestrictionIndex params
  let err : Fin params.m → Error := fun j =>
    bipartiteConsError strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j)
      (rawAnswerDiagonalLineAnswerFamily params strategy j)
  have herr_nonneg : ∀ j : Fin params.m, 0 ≤ err j := by
    intro j'
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j'))
      (AnswerSymStrat.diagonalPointAnswerFamily strategy j')
      (rawAnswerDiagonalLineAnswerFamily params strategy j')
  have hsum_bound : ∑ j' : Fin params.m, err j' ≤ gamma * (params.m : Error) := by
    have hm_nonneg : 0 ≤ (params.m : Error) := by
      positivity
    have hm_ne : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hdiag := hgood.diagonalLineTest
    dsimp [AnswerSymStrat.diagonalFailureProbability, err,
      AnswerSymStrat.diagonalLineAnswerFamily, rawAnswerDiagonalLineAnswerFamily] at hdiag
    calc
      ∑ j' : Fin params.m, err j'
        = (params.m : Error) * ((1 / (params.m : Error)) * ∑ j' : Fin params.m, err j') := by
            field_simp [hm_ne]
      _ ≤ (params.m : Error) * gamma := by
            exact mul_le_mul_of_nonneg_left hdiag hm_nonneg
      _ = gamma * (params.m : Error) := by ring
  have hj_le : err j ≤ gamma * (params.m : Error) := by
    calc
      err j ≤ ∑ j' : Fin params.m, err j' := by
        exact Finset.single_le_sum (fun j' _ => herr_nonneg j') (Finset.mem_univ j)
      _ ≤ gamma * (params.m : Error) := hsum_bound
  refine ⟨?_⟩
  simpa [j, err, restrictedDiagonalLinesConsistencyError] using hj_le

/-- The answer-valued restricted diagonal test gives the same SDD
approximation at the final restriction index as the ordinary diagonal test. -/
lemma answer_sampledDiagonalLineApproximation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (IdxSubMeas.liftLeft
        (AnswerSymStrat.diagonalPointAnswerFamily strategy (lastRestrictionIndex params)))
      (IdxSubMeas.liftRight
        (rawAnswerDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params)))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let pointFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s => (strategy.pointMeasurement s.1).toMeasurement
  let lineFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s =>
      { toSubMeas := rawAnswerDiagonalLineAnswerFamily params strategy j s
        total_eq_one :=
          calc
            (rawAnswerDiagonalLineAnswerFamily params strategy j s).total =
                ((strategy.diagonalMeasurement
                  { base := s.1
                    direction := extendRestrictedDirection j s.2 }).toSubMeas).total := by
              dsimp [rawAnswerDiagonalLineAnswerFamily]
              rw [postprocess_total]
            _ = 1 :=
              (strategy.diagonalMeasurement
                { base := s.1
                  direction := extendRestrictedDirection j s.2 }).total_eq_one }
  have hcons := answer_sampledDiagonalLineConsistency params strategy eps delta gamma hgood
  have hcons' :
      ConsRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (restrictedDiagonalLinesConsistencyError params gamma) := by
    change ConsRel strategy.state
      (uniformDistribution (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamilyOf strategy.pointMeasurement (lastRestrictionIndex params))
      (rawAnswerDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError params gamma)
    exact hcons
  have happrox :
      Preliminaries.BipartiteSDDRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (2 * restrictedDiagonalLinesConsistencyError params gamma) :=
    Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      pointFamily lineFamily
      (restrictedDiagonalLinesConsistencyError params gamma) hcons'
  refine ⟨?_⟩
  simpa [j, pointFamily, lineFamily, AnswerSymStrat.diagonalPointAnswerFamily,
    pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
    Preliminaries.BipartiteSDDRel, sddError, IdxMeas.toIdxSubMeas,
    IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    happrox.leftRightSquaredDistanceBound

end MIPStarRE.LDT.CommutativityPoints


