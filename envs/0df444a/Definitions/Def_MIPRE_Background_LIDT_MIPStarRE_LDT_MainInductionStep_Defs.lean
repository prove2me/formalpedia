-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:20:54.884706+00:00
-- url     : https://prove2.me/theorems/11bc3e6d-1176-4e07-af24-8b72ff800e4b
-- title:
--   Definitions of Defs: Section 6 — Definitions This file contains restriction/lifting maps, section-local error terms, averaging operators,…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Defs` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 6 — Definitions. This file contains restriction/lifting maps, section-local error terms, averaging operators, and tensor-placement bookkeeping for the induction step.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (25): `MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat` (Restricted slice data keeps the point and axis-parallel measurements complete, and packages a genuine projective measurement on the slice's…); `MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat.IsGood` (Goodness data for a restricted strategy.); `MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat.axisParallelFailureProbability` (Failure surrogate for the axis-parallel lines test.); `MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat.axisParallelLineAnswerFamily` (Sampled line answers in the axis-parallel lines test, evaluated at the base point `u` (parameter `zeroCoord`).); `MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat.axisParallelPointAnswerFamily` (Sampled point answers in the axis-parallel lines test.); `MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat.diagonalFailureProbability` (Failure surrogate for the diagonal lines test.); `MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat.restrictedDiagonalLineAnswerFamily` (Sampled diagonal-line answers in the `j`-restricted diagonal test, evaluated at the base point (parameter `zeroCoord`).); `MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat.restrictedDiagonalPointAnswerFamily` (Sampled point answers in the `j`-restricted diagonal test.); `MIPStarRE.LDT.MainInductionStep.RestrictedSymStrat.selfConsistencyFailureProbability` (Failure surrogate for the self-consistency test.); and 11 more.
--
--   **Embedded lemmas** (12): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `restrictAxisParallelMeasurement_outcome`, `restrictDiagonalAnswerMeasurement_postprocess_zero`, `restrictDiagonalMeasurement_postprocess_zero`, `xRestrictedAnswerSymStrat_diagonalMeasurement_apply`, `xRestrictedAnswerSymStrat_isNormalized`, `xRestrictedAnswerSymStrat_pointMeasurement_apply`, `xRestrictedAnswerSymStrat_state`, `xRestrictedStrategy_isNormalized`, `xRestrictedStrategy_pointMeasurement_apply`, `xRestrictedStrategy_state`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Defs` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Defs.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 20 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Defs.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MainInductionStep/Defs.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Defs.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Analysis.Complex.Exponential
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Theorems.Thm_MIPStarRE_LDT_AxisParallelLine_appendAtHeight_rebaseAt
import Theorems.Thm_MIPStarRE_LDT_DiagonalLine_appendAtHeight_rebaseAt
import Theorems.Thm_MIPStarRE_LDT_ProjMeas_ext
import Theorems.Thm_MIPStarRE_LDT_SubMeas_postprocess_comp
import Theorems.Thm_MIPStarRE_LDT_SubMeas_postprocess_transport_equiv

attribute [simp] MIPStarRE.LDT.AxisParallelLine.appendAtHeight_rebaseAt
attribute [simp] MIPStarRE.LDT.DiagonalLine.appendAtHeight_rebaseAt
attribute [ext] MIPStarRE.LDT.ProjMeas.ext
attribute [simp] MIPStarRE.LDT.SubMeas.postprocess_comp

set_option backward.isDefEq.respectTransparency false

/-!
# Section 6 — Definitions

This file contains restriction/lifting maps, section-local error terms,
averaging operators, and tensor-placement bookkeeping for the induction step.

## References

- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lift an axis-line answer from the restricted slice back to the ambient space. -/
def liftAxisAnswer (params : Parameters) [FieldModel params.q] (x : Fq params) :
    AxisLinePolynomial params → AxisLinePolynomial params.next :=
  fun f => AxisLinePolynomial.appendAtHeight params f x

/-- Restricted slice data keeps the point and axis-parallel measurements
complete, and packages a genuine projective measurement on the slice's diagonal
answer space.

The paper's outcome-level formula would send a slice polynomial `f` to the
ambient outcome `append_x(f)`. With the current ambient diagonal answer
encoding, that map is not total on all ambient outcomes, so here we preserve the
verifier-visible base-point readout used in Chapter 10 instead: first
postprocess the ambient slice-preserving diagonal measurement to its value at
`zeroCoord` in `F_q`, then re-embed that `F_q`-valued projective measurement
into the honest slice answer space `DiagonalLinePolynomial params` using
canonical representatives.

This yields a complete projective measurement on the `(m,q,d)` diagonal answer
space whose base-point evaluation agrees with the ambient slice-preserving
branch, eliminating the earlier lossy submeasurement while remaining faithful
to the restricted diagonal test actually formalized here. -/
structure RestrictedSymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The bipartite state carried by the restricted strategy. -/
  state : QuantumState (ι × ι)
  /-- The restricted strategy reuses the ambient state's normalization witness. -/
  isNormalized : state.IsNormalized
  /-- The restricted point measurement. -/
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  /-- The restricted axis-parallel line measurement, packaged with transport covariance. -/
  axisParallelMeasurement : MIPStarRE.LDT.AxisParallelCovariantMeasurement params ι
  /-- The restricted diagonal-line measurement on the honest slice answer space. -/
  diagonalMeasurement :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι

namespace RestrictedSymStrat

/-- Sampled point answers in the axis-parallel lines test.
Point player receives `u` (base point) and answers at `u`. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  MIPStarRE.LDT.axisParallelPointAnswerFamilyOf strategy.pointMeasurement

/-- Sampled line answers in the axis-parallel lines test,
evaluated at the base point `u` (parameter `zeroCoord`). -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  MIPStarRE.LDT.axisParallelLineAnswerFamilyOf strategy.axisParallelMeasurement

/-- Sampled point answers in the `j`-restricted diagonal test.
Point player receives `u` and answers at `u`. -/
noncomputable def restrictedDiagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  MIPStarRE.LDT.diagonalPointAnswerFamilyOf strategy.pointMeasurement j

/-- Sampled diagonal-line answers in the `j`-restricted diagonal
test, evaluated at the base point (parameter `zeroCoord`). -/
noncomputable def restrictedDiagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  MIPStarRE.LDT.diagonalLineAnswerFamilyOf strategy.diagonalMeasurement (· zeroCoord) j

/-- Failure surrogate for the axis-parallel lines test. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Failure surrogate for the self-consistency test. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Failure surrogate for the diagonal lines test.
Averages over restriction index `j`, then the
`j`-restricted diagonal test. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : RestrictedSymStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (restrictedDiagonalPointAnswerFamily strategy j)
        (restrictedDiagonalLineAnswerFamily strategy j)

/-- Goodness data for a restricted strategy. -/
structure IsGood {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FieldModel params.q]
    (strategy : RestrictedSymStrat params ι)
    (eps delta gamma : Error) : Prop where
  /-- The restricted axis-parallel test fails with probability at most `eps`. -/
  axisParallelTest :
    strategy.axisParallelFailureProbability ≤ eps
  /-- The restricted self-consistency test fails with probability at most `delta`. -/
  selfConsistencyTest :
    strategy.selfConsistencyFailureProbability ≤ delta
  /-- The restricted diagonal-line test fails with probability at most `gamma`. -/
  diagonalLineTest :
    strategy.diagonalFailureProbability ≤ gamma

end RestrictedSymStrat

/-- Equivalence between slice and ambient axis-line polynomials at a fixed height `x`:
`liftAxisAnswer` sends a slice polynomial to its ambient lift, with
`AxisLinePolynomial.restrictAtHeight` as inverse. -/
def axisLinePolynomialEquiv (params : Parameters) [FieldModel params.q] (x : Fq params) :
    AxisLinePolynomial params ≃ AxisLinePolynomial params.next where
  toFun := liftAxisAnswer params x
  invFun := fun f => AxisLinePolynomial.restrictAtHeight params f x
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- Restrict an axis-parallel line measurement to the slice at height `x`. -/
noncomputable def restrictAxisParallelMeasurement (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι :=
  fun ℓ =>
    let lifted := strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)
    let restrictedTotal : MIPStarRE.Quantum.Op ι :=
      ∑ f : AxisLinePolynomial params,
        lifted.toSubMeas.outcome (liftAxisAnswer params x f)
    have hrestrictedTotal :
        restrictedTotal = 1 := by
      calc
        restrictedTotal
          = ∑ g : AxisLinePolynomial params.next, lifted.toSubMeas.outcome g := by
              simpa [restrictedTotal] using
                (Fintype.sum_equiv (axisLinePolynomialEquiv params x)
                  (fun f => lifted.toSubMeas.outcome (liftAxisAnswer params x f))
                  (fun g => lifted.toSubMeas.outcome g)
                  (by intro f; rfl))
        _ = 1 := by
            rw [lifted.toSubMeas.sum_eq_total, lifted.total_eq_one]
    { toMeasurement := {
        toSubMeas := {
          outcome := fun f =>
            lifted.toSubMeas.outcome (liftAxisAnswer params x f)
          total := 1
          outcome_pos := fun f => lifted.outcome_pos (liftAxisAnswer params x f)
          sum_eq_total := hrestrictedTotal
          total_le_one := le_rfl
        }
        total_eq_one := rfl }
      proj := fun f => lifted.proj (liftAxisAnswer params x f) }

theorem restrictAxisParallelMeasurement_transportInvariant
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    MIPStarRE.LDT.AxisParallelMeasurementTransportInvariant params
      (restrictAxisParallelMeasurement params strategy x) := by
  intro ℓ t
  have htransport :=
    MIPStarRE.LDT.AxisParallelCovariantMeasurement.transportInvariant
      strategy.axisParallelMeasurement
      (AxisParallelLine.appendAtHeight params ℓ x) t
  apply ProjMeas.ext
  intro a
  calc
    (restrictAxisParallelMeasurement params strategy x
        (AxisParallelLine.rebaseAt ℓ t)).outcome a
      = (strategy.axisParallelMeasurement
          (AxisParallelLine.appendAtHeight params (AxisParallelLine.rebaseAt ℓ t) x)).outcome
          (liftAxisAnswer params x a) := by
            try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ = (strategy.axisParallelMeasurement
          (AxisParallelLine.rebaseAt (AxisParallelLine.appendAtHeight params ℓ x) t)).outcome
          (liftAxisAnswer params x a) := by
            simp
    _ = (AxisParallelLine.transportMeasurement (params := params.next)
          (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)) t).outcome
          (liftAxisAnswer params x a) := by
            simp [htransport]
    _ = (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).outcome
          (((AxisLinePolynomial.reparamAtEquiv (params := params.next) t).symm)
            (liftAxisAnswer params x a)) := by
            simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
              Measurement.transport, SubMeas.transport]
    _ = (strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).outcome
          (liftAxisAnswer params x
            (((AxisLinePolynomial.reparamAtEquiv (params := params) t).symm) a)) := by
            simp [liftAxisAnswer]
    _ = (restrictAxisParallelMeasurement params strategy x ℓ).outcome
          (((AxisLinePolynomial.reparamAtEquiv (params := params) t).symm) a) := by
            try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ = (AxisParallelLine.transportMeasurement (params := params)
          (restrictAxisParallelMeasurement params strategy x ℓ) t).outcome a := by
            simp [AxisParallelLine.transportMeasurement, ProjMeas.transport,
              Measurement.transport, SubMeas.transport]

/-- Canonical honest slice answer with prescribed value at the base point.

We use the constant polynomial because the restricted diagonal branch only reads
line answers at `zeroCoord`. -/
noncomputable def diagonalValueRepresentative (params : Parameters)
    [FieldModel params.q] (a : Fq params) :
    DiagonalLinePolynomial params where
  poly := _root_.Polynomial.C (decodeScalar a)
  degreeBounded := (_root_.Polynomial.natDegree_C (decodeScalar a)).trans_le (Nat.zero_le _)

/-- Restrict a diagonal-line measurement to the slice at height `x`.

This is not literally the paper's outcome reindexing
`f ↦ DiagonalLinePolynomial.appendAtHeight params f x`; that map only covers the
degree-`params.m * params.d` ambient outcomes. Instead we preserve the only
statistic used by the restricted diagonal test formalized here, namely the
base-point answer at `zeroCoord`.

Concretely we:
1. restrict the ambient line question to the slice-preserving line,
2. postprocess the ambient projective measurement to its `zeroCoord` value in
   `F_q`, and
3. re-embed that `F_q`-valued projective measurement into the honest slice
   answer space via `diagonalValueRepresentative`.

This produces a complete projective measurement on
`DiagonalLinePolynomial params` whose induced base-point answer distribution is
exactly the same as the ambient slice-preserving diagonal measurement. -/
noncomputable def restrictDiagonalMeasurement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι :=
  fun ℓ =>
    ProjMeas.postprocess
      (ProjMeas.postprocess
        (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
        (fun f : DiagonalLinePolynomial params.next => f zeroCoord))
      (diagonalValueRepresentative params)

/-- Restrict a diagonal-line measurement to the slice at height `x`, using the
paper-level function-answer alphabet.

Unlike `restrictDiagonalMeasurement`, this keeps the whole line answer function
rather than only the value at `zeroCoord`.  The map is total because
`DiagonalLineAnswer` has no degree-bound subtype proof to preserve. -/
noncomputable def restrictDiagonalAnswerMeasurement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι :=
  fun ℓ =>
    ProjMeas.postprocess
      (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x))
      (fun f : DiagonalLinePolynomial params.next =>
        DiagonalLineAnswer.restrictAtHeight params f.toAnswer x)

/-- Transport covariance for the function-valued restricted diagonal-line
measurement. -/
theorem restrictDiagonalAnswerMeasurement_transportInvariant (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    DiagonalAnswerMeasurementTransportInvariant params
      (restrictDiagonalAnswerMeasurement params strategy x) := by
  intro ℓ t
  apply ProjMeas.ext
  intro a
  have htransport :=
    MIPStarRE.LDT.DiagonalCovariantMeasurement.transportInvariant
      strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x) t
  let A := (strategy.diagonalMeasurement (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas
  let ePoly := DiagonalLinePolynomial.reparamAtEquiv (params := params.next) t
  let eAns := DiagonalLineAnswer.reparamAtEquiv (params := params) t
  let f : DiagonalLinePolynomial params.next → DiagonalLineAnswer params :=
    fun g => DiagonalLineAnswer.restrictAtHeight params g.toAnswer x
  have hcomm : ∀ g, f (ePoly g) = eAns (f g) := by
    intro g
    funext s
    dsimp [f, ePoly, eAns, DiagonalLinePolynomial.reparamAtEquiv,
      DiagonalLineAnswer.reparamAtEquiv, DiagonalLinePolynomial.toAnswer,
      DiagonalLineAnswer.restrictAtHeight, DiagonalLineAnswer.reparamAt]
    exact DiagonalLinePolynomial.reparamAt_apply g t s
  have hpost : postprocess (SubMeas.transport ePoly A) f =
      SubMeas.transport eAns (postprocess A f) :=
    SubMeas.postprocess_transport_equiv ePoly eAns A f f hcomm
  exact congrArg (fun M : SubMeas (DiagonalLineAnswer params) ι => M.outcome a) <| by
    simpa [restrictDiagonalAnswerMeasurement, DiagonalLine.transportMeasurement,
      ProjMeas.transport, Measurement.transport, A, ePoly, eAns, f,
      DiagonalLine.appendAtHeight_rebaseAt, htransport] using hpost

/-- The `x`-restricted strategy with function-valued diagonal-line
answers.

This matches the slice-restriction interface in `inductive_step.tex`, lines
436--455. It is
kept parallel to the current `xRestrictedStrategy`, whose diagonal field uses the
legacy degree-bounded answer alphabet and therefore only preserves the sampled
base-point readout. -/
noncomputable def xRestrictedAnswerSymStrat (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) : AnswerSymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  densityFixed := strategy.densityFixed
  isNormalized := strategy.isNormalized
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    { toIdxProjMeas := restrictAxisParallelMeasurement params strategy x
      transportInvariant :=
        restrictAxisParallelMeasurement_transportInvariant params strategy x }
  diagonalMeasurement :=
    { toIdxProjMeas := restrictDiagonalAnswerMeasurement params strategy x
      transportInvariant :=
        restrictDiagonalAnswerMeasurement_transportInvariant params strategy x }

/-- The function-answer restricted strategy reuses the ambient bipartite state. -/
@[simp] theorem xRestrictedAnswerSymStrat_state (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).state = strategy.state :=
  rfl

/-- The function-answer restricted strategy reindexes point questions by appending
the slice height. -/
@[simp] theorem xRestrictedAnswerSymStrat_pointMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) (u : Point params) :
    (xRestrictedAnswerSymStrat params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- The function-answer restricted strategy reuses the parent normalization witness. -/
@[simp] theorem xRestrictedAnswerSymStrat_isNormalized (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).isNormalized = strategy.isNormalized :=
  rfl

/-- The function-answer restricted diagonal measurement is the answer-valued
restriction of the ambient diagonal measurement. -/
@[simp] theorem xRestrictedAnswerSymStrat_diagonalMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) (ℓ : DiagonalLine params) :
    (xRestrictedAnswerSymStrat params strategy x).diagonalMeasurement ℓ =
      restrictDiagonalAnswerMeasurement params strategy x ℓ :=
  rfl

/-- Evaluating the answer-valued restricted diagonal measurement at the base point
recovers the ambient slice-preserving diagonal readout. -/
@[simp] theorem restrictDiagonalAnswerMeasurement_postprocess_zero (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : DiagonalLine params) :
    postprocess ((restrictDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess
        ((strategy.diagonalMeasurement
          (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : DiagonalLinePolynomial params.next => f zeroCoord) := by
  simp [restrictDiagonalAnswerMeasurement, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_comp, DiagonalLinePolynomial.toAnswer,
    DiagonalLineAnswer.restrictAtHeight]
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The `x`-restricted strategy from the proof of the main induction theorem. -/
noncomputable def xRestrictedStrategy (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) : RestrictedSymStrat params ι where
  state := strategy.state
  isNormalized := strategy.isNormalized
  pointMeasurement := fun u => strategy.pointMeasurement (appendPoint params u x)
  axisParallelMeasurement :=
    { toIdxProjMeas := restrictAxisParallelMeasurement params strategy x
      transportInvariant :=
        restrictAxisParallelMeasurement_transportInvariant params strategy x }
  diagonalMeasurement := restrictDiagonalMeasurement params strategy x

/-- Restricting a strategy does not change its bipartite state. -/
@[simp] theorem xRestrictedStrategy_state (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedStrategy params strategy x).state = strategy.state :=
  rfl

/-- Restricting a strategy reuses the parent strategy's normalization witness. -/
@[simp] theorem xRestrictedStrategy_isNormalized (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedStrategy params strategy x).isNormalized = strategy.isNormalized :=
  rfl

/-- Restricting a strategy reindexes point questions by appending the slice height. -/
@[simp] theorem xRestrictedStrategy_pointMeasurement_apply (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) (u : Point params) :
    (xRestrictedStrategy params strategy x).pointMeasurement u =
      strategy.pointMeasurement (appendPoint params u x) :=
  rfl

/-- Restricting an axis-parallel measurement reindexes outcomes by slice extension. -/
@[simp] theorem restrictAxisParallelMeasurement_outcome (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    (restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas.outcome f =
      (strategy.axisParallelMeasurement
        (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas.outcome
        (liftAxisAnswer params x f) :=
  rfl

/-- Postprocessing the restricted diagonal measurement at the base point recovers
exactly the ambient slice-preserving diagonal answer distribution at the base
point. -/
@[simp] theorem restrictDiagonalMeasurement_postprocess_zero (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params)
    (ℓ : DiagonalLine params) :
    postprocess ((restrictDiagonalMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLinePolynomial params => f zeroCoord) =
      postprocess
        ((strategy.diagonalMeasurement
          (DiagonalLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : DiagonalLinePolynomial params.next => f zeroCoord) := by
  classical
  let evalNext : DiagonalLinePolynomial params.next → Fq params := fun f => f zeroCoord
  let evalSlice : DiagonalLinePolynomial params → Fq params := fun f => f zeroCoord
  simp only [restrictDiagonalMeasurement, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_comp]
  simp [diagonalValueRepresentative, DiagonalLinePolynomial.toFun, evalLinePolynomialModel]
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The intermediate `ν` from `thm:main-induction`. -/
noncomputable def mainInductionNu (params : Parameters) (k : ℕ)
    (eps delta gamma : Error) : Error :=
  1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
    (Real.rpow eps (1 / (1024 : Error)) +
      Real.rpow delta (1 / (1024 : Error)) +
      Real.rpow gamma (1 / (1024 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (1024 : Error)))

/-- The explicit `σ` of `thm:main-induction`. -/
noncomputable def mainInductionError (params : Parameters) (k : ℕ)
    (eps delta gamma : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (mainInductionNu params k eps delta gamma +
      Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))

/-- The section-local self-improvement error. -/
noncomputable def selfImprovementInInductionError (params : Parameters)
    (eps delta _gamma : Error) : Error :=
  3000 * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- The intermediate `ν` from the section-local pasting theorem. -/
noncomputable def ldPastingInInductionNu (params : Parameters) (k : ℕ)
    (eps delta gamma zeta : Error) : Error :=
  100 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
    (Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)))

/-- The section-local pasting consistency error. -/
noncomputable def ldPastingInInductionError (params : Parameters) (k : ℕ)
    (eps delta gamma kappa zeta : Error) : Error :=
  kappa * (1 + 1 / (100 * (params.m : Error))) +
    2 * ldPastingInInductionNu params k eps delta gamma zeta +
    Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))

/-- Tensor-failure expectation on a bipartite space.

Computes `⟨ψ| (Z ⊗ I)(I ⊗ (I - Σ H_a)) |ψ⟩` where `Z` acts on the left register
and `H` acts on the right register. -/
noncomputable def tensorFailureExpectation {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (Z : MIPStarRE.Quantum.Op ιA) (H : SubMeas Outcome ιB) :
    Error :=
  ev ψ <|
    leftTensor (ι₂ := ιB) Z *
      rightTensor (ι₁ := ιA) (1 - H.total)

/-- Probability that a sampled test line in `F_q^{m+1}` is not parallel to the new axis. -/
noncomputable def sliceTransverseDirectionWeight (params : Parameters) : Error :=
  (params.m : Error) / (((params.m + 1 : ℕ) : Error))

/-- Reciprocal loss incurred when conditioning away the new axis direction.

In `lem:restricted-probabilities`, the axis-parallel and diagonal branches use
this same conditioning step, so both averaged slice bounds carry the paper's
common factor `((m + 1) / m)`. -/
noncomputable def sliceConditioningLoss (params : Parameters) : Error :=
  (((params.m + 1 : ℕ) : Error) / (params.m : Error))

end MIPStarRE.LDT.MainInductionStep


