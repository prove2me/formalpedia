-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:19:51.021438+00:00
-- url     : https://prove2.me/theorems/5ac76db1-79b7-49d2-b69f-6a902cc0b763
-- title:
--   Definitions of StrategyCore: Section 3 — Strategy core Base state-invariance and strategy structures for the low individual degree test
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyCore` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 3 — Strategy core. Base state-invariance and strategy structures for the low individual degree test.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (40): `MIPStarRE.LDT.AnswerSymStrat` (Paper-level symmetric strategy data whose diagonal-line answers are functions.); `MIPStarRE.LDT.AnswerSymStrat.IsGood` (Goodness data for an answer-valued symmetric strategy.); `MIPStarRE.LDT.AnswerSymStrat.axisParallelFailureProbability` (Axis-parallel failure surrogate for an answer-valued symmetric strategy.); `MIPStarRE.LDT.AnswerSymStrat.axisParallelLineAnswerFamily` (Sampled line answers in the axis-parallel lines test for an answer-valued symmetric strategy, evaluated at the base point.); `MIPStarRE.LDT.AnswerSymStrat.axisParallelPointAnswerFamily` (Sampled point answers in the axis-parallel lines test for an answer-valued symmetric strategy.); `MIPStarRE.LDT.AnswerSymStrat.diagonalFailureProbability` (Diagonal-line failure surrogate for an answer-valued symmetric strategy.); `MIPStarRE.LDT.AnswerSymStrat.diagonalLineAnswerFamily` (Sampled diagonal-line answers in the restricted diagonal test for an answer-valued symmetric strategy, evaluated at the base point.); `MIPStarRE.LDT.AnswerSymStrat.diagonalPointAnswerFamily` (Sampled point answers in the restricted diagonal test for an answer-valued symmetric strategy.); `MIPStarRE.LDT.AnswerSymStrat.selfConsistencyFailureProbability` (Self-consistency failure surrogate for an answer-valued symmetric strategy.); `MIPStarRE.LDT.AxisParallelCovariantMeasurement` (Axis-parallel line measurements bundled with the stronger transport-level rebasing covariance.); and 30 more.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `restrictedDiagonalSampleNonempty`, `swapDensity_add`, `swapDensity_smul`, `swapDensity_swapDensity`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyCore` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyCore.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyCore.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/StrategyCore.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyCore.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finite.Defs
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
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
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

set_option backward.isDefEq.respectTransparency false

/-!
# Section 3 — Strategy core

Base state-invariance and strategy structures for the low individual degree test.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

instance : Fintype Role where
  elems := {Role.A, Role.B}
  complete r := by
    cases r <;> simp

/-- The SWAP reindexing on `ι × ι`: permutes the two tensor factors.
`swapDensity M (i₁,i₂) (j₁,j₂) = M (i₂,i₁) (j₂,j₁)`. -/
def swapDensity {ι : Type*} (M : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  Matrix.of fun (ij : ι × ι) (kl : ι × ι) => M (ij.2, ij.1) (kl.2, kl.1)

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

@[simp] lemma swapDensity_swapDensity {ι : Type*}
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (swapDensity X) = X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

@[simp] lemma swapDensity_add {ι : Type*}
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X + Y) = swapDensity X + swapDensity Y := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

@[simp] lemma swapDensity_smul {ι : Type*} (c : ℂ)
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (c • X) = c • swapDensity X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- Permutation-invariance for a bipartite state on `ι × ι`.

The primary datum is that the density operator is fixed by the SWAP reindexing,
`swapDensity ψ.density = ψ.density`.  We also cache the frequently used
one-sided expectation consequence
`ev ψ (leftTensor M) = ev ψ (rightTensor M)`.
This matches the symmetric-strategy construction used in the paper
(Section 3) and exposes enough symmetry to swap fully bipartite
consistency expressions. -/
structure PermInvState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) : Prop where
  /-- The density operator is fixed by the SWAP reindexing. -/
  density_swap : swapDensity ψ.density = ψ.density
  /-- Swapping tensor factors preserves one-sided expectation values. -/
  swap_ev : ∀ (M : MIPStarRE.Quantum.Op ι),
    ev ψ (leftTensor (ι₂ := ι) M) =
      ev ψ (rightTensor (ι₁ := ι) M)

/-- Direct outcome-level covariance for axis-parallel-line measurements.

Rebasing a line question by `t` and reparametrizing an outcome polynomial by
the same translation leaves the corresponding projector unchanged. -/
def AxisParallelMeasurementReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t : Fq params) (f : AxisLinePolynomial params),
    (M (ℓ.rebaseAt t)).outcome (AxisLinePolynomial.reparamAt f t) =
      (M ℓ).outcome f

/-- Direct outcome-level covariance for diagonal-line measurements.

Rebasing a line question by `t` and reparametrizing an outcome polynomial by
the same translation leaves the corresponding projector unchanged. -/
def DiagonalMeasurementReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params) (f : DiagonalLinePolynomial params),
    (M (ℓ.rebaseAt t)).outcome (DiagonalLinePolynomial.reparamAt f t) =
      (M ℓ).outcome f

/-- Reparametrization invariance for diagonal-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter.

At the answer level, the geometric identity is
`DiagonalLinePolynomial.reparamAt_apply_zero`. This predicate is stronger: it
asserts that the *measurement family itself* is covariant under rebasing the
question index. -/
def DiagonalEvaluationReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t a : Fq params),
    (postprocess ((M (DiagonalLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

/-- Reparametrization invariance for axis-parallel-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter. -/
def AxisParallelEvaluationReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t a : Fq params),
    (postprocess ((M (AxisParallelLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

namespace AxisParallelLine

/-- Transport an axis-parallel-line measurement along rebasing of the line
question by translating its polynomial outcomes. -/
noncomputable def transportMeasurement {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (AxisLinePolynomial params) ι) (t : Fq params) :
    ProjMeas (AxisLinePolynomial params) ι :=
  ProjMeas.transport (AxisLinePolynomial.reparamAtEquiv (params := params) t) M

end AxisParallelLine

namespace DiagonalLine

/-- Transport a diagonal-line measurement along rebasing of the line question by
translating its polynomial outcomes. -/
noncomputable def transportMeasurement {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (DiagonalLinePolynomial params) ι) (t : Fq params) :
    ProjMeas (DiagonalLinePolynomial params) ι :=
  ProjMeas.transport (DiagonalLinePolynomial.reparamAtEquiv (params := params) t) M

end DiagonalLine

/-- Stronger rebasing compatibility for axis-parallel-line measurements: the
measurement indexed by the rebased line is equal to the transport of the
original measurement along the answer reparametrization equivalence. -/
def AxisParallelMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t : Fq params),
    M (AxisParallelLine.rebaseAt ℓ t) =
      AxisParallelLine.transportMeasurement (params := params) (M ℓ) t

/-- Stronger rebasing compatibility for diagonal-line measurements: the
measurement indexed by the rebased line is equal to the transport of the
original measurement along the answer reparametrization equivalence. -/
def DiagonalMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params),
    M (DiagonalLine.rebaseAt ℓ t) =
      DiagonalLine.transportMeasurement (params := params) (M ℓ) t

/-- Axis-parallel line measurements bundled with the stronger transport-level
rebasing covariance. -/
structure AxisParallelCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toIdxProjMeas :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  transportInvariant :
    AxisParallelMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    CoeFun (AxisParallelCovariantMeasurement params ι)
      (fun _ => AxisParallelLine params → ProjMeas (AxisLinePolynomial params) ι) where
  coe M := M.toIdxProjMeas

namespace AxisParallelCovariantMeasurement

end AxisParallelCovariantMeasurement

/-- Diagonal line measurements bundled with the stronger transport-level
rebasing covariance. -/
structure DiagonalCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toIdxProjMeas :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι
  transportInvariant :
    DiagonalMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    CoeFun (DiagonalCovariantMeasurement params ι)
      (fun _ => DiagonalLine params → ProjMeas (DiagonalLinePolynomial params) ι) where
  coe M := M.toIdxProjMeas

namespace DiagonalCovariantMeasurement

end DiagonalCovariantMeasurement

/-- Transport covariance for diagonal-line measurements whose answers are the
paper-level line functions. -/
def DiagonalAnswerMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params),
    M (DiagonalLine.rebaseAt ℓ t) =
      ProjMeas.transport (DiagonalLineAnswer.reparamAtEquiv t) (M ℓ)

/-- Diagonal-line measurements with paper-level function answers, bundled with
transport-level rebasing covariance.

This parallel API is intended for the paper-faithful restriction redesign: unlike
`DiagonalLinePolynomial`, the function-answer alphabet admits a total slice
append/restrict equivalence. -/
structure DiagonalAnswerCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toIdxProjMeas :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι
  transportInvariant :
    DiagonalAnswerMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    CoeFun (DiagonalAnswerCovariantMeasurement params ι)
      (fun _ => DiagonalLine params → ProjMeas (DiagonalLineAnswer params) ι) where
  coe M := M.toIdxProjMeas

/-- Paper-level symmetric strategy data whose diagonal-line answers are functions.

This parallel structure is the target shape for the restriction redesign in
Section 6: restricting an ambient diagonal line to a slice is total for function
answers, unlike the current degree-bounded `DiagonalLinePolynomial` alphabet. -/
structure AnswerSymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)
  permInvState : PermInvState state
  densityFixed : swapDensity state.density = state.density
  isNormalized : state.IsNormalized
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement : AxisParallelCovariantMeasurement params ι
  diagonalMeasurement : DiagonalAnswerCovariantMeasurement params ι

/-- Paper-local symmetric strategy data.

The line-measurement fields are bundled as transport-covariant wrappers:
rebasing the question index is required to agree with transporting the
projective measurement along the corresponding answer reparametrization
equivalence. This is stronger than the older evaluation-level formulas
at `zeroCoord`, but those formulas remain available as derived lemmas via
`AxisParallelCovariantMeasurement.reparamInvariant` and
`DiagonalCovariantMeasurement.reparamInvariant`.

The `isNormalized` field records that the bipartite state's density
operator has normalized trace `1`. For pure states, this coincides
with the usual unit-vector condition (`⟨ψ|ψ⟩ = 1`) used in the paper.
Bundling normalization with the strategy avoids threading a
`state.IsNormalized` hypothesis through every downstream consumer
(pasting cascade, `triangleSub` users, self-improvement helpers). -/
structure SymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)  -- bipartite state on ℋ ⊗ ℋ
  permInvState : PermInvState state
  densityFixed : swapDensity state.density = state.density
  isNormalized : state.IsNormalized
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement : AxisParallelCovariantMeasurement params ι
  diagonalMeasurement : DiagonalCovariantMeasurement params ι

-- NOTE: no global `Inhabited` instance for `SymStrat`; constructing default
-- projective measurement families is non-canonical and requires additional
-- assumptions on outcome types.

/-- Encoded samples `(u, i)` for the axis-parallel lines test.
The paper samples a random point `u ∈ F_q^m` and a coordinate
`i ∈ {1, …, m}`. In Lean, `Fin params.m` represents the 0-indexed
coordinates `{0, …, m - 1}`, corresponding to the paper's 1-indexed
choice. The sample forms the axis-parallel line through `u` in that
coordinate direction. -/
abbrev AxisParallelTestSample (params : Parameters) :=
  Point params × Fin params.m

/-- Extend restricted direction coordinates to a full direction vector.
For restriction index `j` (0-indexed), the first `j + 1` coordinates
are the given free coordinates and the remaining are zero.
This matches the paper's convention that `v` has its last `m − i`
coordinates zero, where `i = j + 1`. -/
def extendRestrictedDirection {params : Parameters}
    [FieldModel params.q] (j : Fin params.m)
    (freeCoords : Fin (j.val + 1) → Fq params) :
    Point params :=
  fun k =>
    if h : k.val ≤ j.val then
      freeCoords ⟨k.val, Nat.lt_succ_of_le h⟩
    else zeroCoord

/-- Encoded samples `(u, freeCoords)` for the `j`-restricted diagonal
lines test. The base point `u ∈ F_q^m` and the free coordinates of
the restricted direction (first `j + 1` coordinates; rest are zero).
The full diagonal test averages over `j ∈ {0, …, m − 1}`. -/
abbrev RestrictedDiagonalSample (params : Parameters)
    (j : Fin params.m) :=
  Point params × (Fin (j.val + 1) → Fq params)

/-- The restricted diagonal sample space is nonempty. -/
instance restrictedDiagonalSampleNonempty (params : Parameters) (j : Fin params.m) :
    Nonempty (RestrictedDiagonalSample params j) :=
  inferInstance

/-- Sampled point answers in the axis-parallel lines test, obtained from a
point measurement. -/
noncomputable abbrev axisParallelPointAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pointMeasurement : IdxProjMeas (Point params) (Fq params) ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s => (pointMeasurement s.1).toSubMeas

/-- Sampled line answers in the axis-parallel lines test, obtained from an
axis-parallel measurement and evaluated at the base point. -/
noncomputable abbrev axisParallelLineAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (axisParallelMeasurement :
      AxisParallelLine params → ProjMeas (AxisLinePolynomial params) ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((axisParallelMeasurement ℓ).toSubMeas)
      (· zeroCoord)

/-- Sampled point answers in the restricted diagonal test, obtained from a
point measurement. -/
noncomputable abbrev diagonalPointAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pointMeasurement : IdxProjMeas (Point params) (Fq params) ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s => (pointMeasurement s.1).toSubMeas

/-- Sampled diagonal-line answers in the restricted diagonal test, obtained from
a diagonal-line measurement and evaluated at the base point. -/
noncomputable abbrev diagonalLineAnswerFamilyOf
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Answer : Type*} [Fintype Answer]
    (diagonalMeasurement : DiagonalLine params → ProjMeas Answer ι)
    (evalAtBase : Answer → Fq params)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((diagonalMeasurement ℓ).toSubMeas)
      evalAtBase

/-- Sampled point answers in the axis-parallel lines test.
The point player receives `u` (the base point) and answers with
their measurement at `u`. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  axisParallelPointAnswerFamilyOf strategy.pointMeasurement

/-- Sampled line answers in the axis-parallel lines test,
evaluated at the base point `u`.
The line player receives `ℓ` and returns a polynomial `f`.
The verifier checks `f(u) = a`; since `u = ℓ.pointAt zeroCoord`,
we evaluate `f` at `zeroCoord`. -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  axisParallelLineAnswerFamilyOf strategy.axisParallelMeasurement

-- Paper: `not:conditioned-on-last-direction` abbreviates the axis-parallel
-- line in the last coordinate direction of `F_q^(m+1)` by its base point `u`.

-- Paper: `not:conditioned-on-last-direction` writes `B^u` for the axis-parallel
-- line measurement conditioned on the last direction choice.

/-- Sampled point answers in the `j`-restricted diagonal test.
The point player receives `u` and answers at `u`. -/
noncomputable def diagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  diagonalPointAnswerFamilyOf strategy.pointMeasurement j

/-- Sampled diagonal-line answers in the `j`-restricted diagonal
test, evaluated at the base point `u`.
Since `u = ℓ.pointAt zeroCoord`, we evaluate `f` at
`zeroCoord`. -/
noncomputable def diagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  diagonalLineAnswerFamilyOf strategy.diagonalMeasurement (· zeroCoord) j

namespace AnswerSymStrat

/-- Sampled point answers in the axis-parallel lines test for an answer-valued
symmetric strategy. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  axisParallelPointAnswerFamilyOf strategy.pointMeasurement

/-- Sampled line answers in the axis-parallel lines test for an answer-valued
symmetric strategy, evaluated at the base point. -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  axisParallelLineAnswerFamilyOf strategy.axisParallelMeasurement

/-- Sampled point answers in the restricted diagonal test for an answer-valued
symmetric strategy. -/
noncomputable def diagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  diagonalPointAnswerFamilyOf strategy.pointMeasurement j

/-- Sampled diagonal-line answers in the restricted diagonal test for an
answer-valued symmetric strategy, evaluated at the base point. -/
noncomputable def diagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  diagonalLineAnswerFamilyOf strategy.diagonalMeasurement (· zeroCoord) j

/-- Axis-parallel failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Self-consistency failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Diagonal-line failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy j)
        (diagonalLineAnswerFamily strategy j)

/-- Goodness data for an answer-valued symmetric strategy. -/
structure IsGood {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error) : Prop where
  /-- The axis-parallel test fails with probability at most `eps`. -/
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  /-- The self-consistency test fails with probability at most `delta`. -/
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  /-- The diagonal-line test fails with probability at most `gamma`. -/
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end AnswerSymStrat

/-- Paper-faithful two-space projective strategy data.

This matches the paper's `def:general-projective-strategy`
(`test_definition.tex`, lines 98--115): Alice's and Bob's measurements act on
separate local carriers `ιA` and `ιB`, and the bipartite state lives on
`ιA × ιB` without a built-in swap symmetry.

The `isNormalized` field records that the bipartite state's density operator
has normalized trace `1`.

The four covariance conditions express that the line-indexed projectors
descend from chosen affine parametrizations to geometric lines; transport and
zero-coordinate evaluation are equivalent consequences. -/
structure ProjStrat (params : Parameters) [FieldModel params.q]
    (ιA : Type*) [Fintype ιA] [DecidableEq ιA]
    (ιB : Type*) [Fintype ιB] [DecidableEq ιB] where
  /-- Bipartite state on the tensor product of Alice's and Bob's local carriers. -/
  state : QuantumState (ιA × ιB)
  /-- The bipartite state's density operator is trace-normalized. -/
  isNormalized : state.IsNormalized
  /-- Alice's point-measurement family, acting on `ιA`. -/
  pointMeasurementA : IdxProjMeas (Point params) (Fq params) ιA
  /-- Alice's axis-parallel-line measurement family, acting on `ιA`. -/
  axisParallelMeasurementA :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ιA
  /-- Alice's axis-parallel measurement is covariant under line rebasing. -/
  axisParallelReparamInvariantA :
    AxisParallelMeasurementReparamInvariant params axisParallelMeasurementA
  /-- Alice's diagonal-line measurement family, acting on `ιA`. -/
  diagonalMeasurementA :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ιA
  /-- Alice's diagonal measurement is covariant under line rebasing. -/
  diagonalReparamInvariantA :
    DiagonalMeasurementReparamInvariant params diagonalMeasurementA
  /-- Bob's point-measurement family, acting on `ιB`. -/
  pointMeasurementB : IdxProjMeas (Point params) (Fq params) ιB
  /-- Bob's axis-parallel-line measurement family, acting on `ιB`. -/
  axisParallelMeasurementB :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ιB
  /-- Bob's axis-parallel measurement is covariant under line rebasing. -/
  axisParallelReparamInvariantB :
    AxisParallelMeasurementReparamInvariant params axisParallelMeasurementB
  /-- Bob's diagonal-line measurement family, acting on `ιB`. -/
  diagonalMeasurementB :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ιB
  /-- Bob's diagonal measurement is covariant under line rebasing. -/
  diagonalReparamInvariantB :
    DiagonalMeasurementReparamInvariant params diagonalMeasurementB

end MIPStarRE.LDT


