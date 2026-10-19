-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:22:23.737018+00:00
-- url     : https://prove2.me/theorems/df1599d6-1174-4971-8a3f-eaa8219a9daa
-- title:
--   Definitions of Statements: Section 6 — Induction Step Data This file records the intermediate conclusion structures and bookkeeping statements…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Statements` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 6 — Induction Step Data. This file records the intermediate conclusion structures and bookkeeping statements used in the induction step. It contains the conclusions of the induction-level self-improvement and pasting theorems, together with restricted failure profiles and the stage data for the paper's slice restriction, slice-wise induction, self-improvement, and pasting assembly.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (24): `MIPStarRE.LDT.MainInductionStep.AnswerMainInductionConclusion` (Paper origin: `references/ldt-paper/inductive_step.tex:7-18` (`\label{thm:main-induction}`); answer-valued analogue.); `MIPStarRE.LDT.MainInductionStep.AnswerMainInductionHypothesis` (Predicate form of the answer-valued predecessor main-induction hypothesis.); `MIPStarRE.LDT.MainInductionStep.AnswerPerSliceInductionData` (Explicit per-slice output of the inductive hypothesis for answer-valued slices.); `MIPStarRE.LDT.MainInductionStep.AnswerRestrictedFailureProfile` (Bookkeeping data for answer-valued restricted strategies.); `MIPStarRE.LDT.MainInductionStep.AnswerRestrictedProbabilitiesStatement` (Paper origin: `references/ldt-paper/inductive_step.tex:374-412` (`\label{lem:restricted-probabilities}`); answer-valued variant carrying…); `MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData` (Slice-wise output of the induction-level self-improvement stage for answer-valued restricted strategies.); `MIPStarRE.LDT.MainInductionStep.AnswerSelfImprovementData.family` (The slice-indexed polynomial family obtained from answer-valued restricted self-improvement outputs.); `MIPStarRE.LDT.MainInductionStep.AnswerSliceRestrictionData` (Answer-valued slice-restriction data record for the Section 6 induction step.); `MIPStarRE.LDT.MainInductionStep.AveragedPastingData` (Paper origin: `references/ldt-paper/ld-pasting.tex:12-50` (`\label{thm:ld-pasting}`) and `references/ldt-paper/inductive_step.tex:239-342`.); and 8 more.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `family_dominationTarget`, `family_meas`, `family_witness`, `family_dominationTarget`, `family_meas`, `family_witness`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MainInductionStep.Statements` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Statements.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 22 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Statements.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MainInductionStep/Statements.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MainInductionStep/Statements.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies

set_option backward.isDefEq.respectTransparency false

/-!
# Section 6 — Induction Step Data

This file records the intermediate conclusion structures and bookkeeping
statements used in the induction step. It contains the conclusions of the
induction-level self-improvement and pasting theorems, together with restricted
failure profiles and the stage data for the paper's slice restriction,
slice-wise induction, self-improvement, and pasting assembly.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Paper origin: `references/ldt-paper/inductive_step.tex:249-286`
(`\label{thm:self-improvement-in-induction-section}`).

Conclusion of the induction-level self-improvement theorem.

The strategy's state is bipartite (`QuantumState (ι × ι)`). Fields that
involve bipartite-lifted operators use `leftPlacedSubMeas` /
`rightPlacedSubMeas` / `tensorFailureExpectation` with honest bipartite
structure. -/
structure SelfImprovementInInductionSectionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (_G : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
  /-- The projective submeasurement remains almost complete. -/
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementInInductionError params eps delta gamma)
  /-- The projective submeasurement stays point-consistent with the original strategy. -/
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementInInductionError params eps delta gamma)
  /-- The output family is strongly self-consistent in the bipartite sense. -/
  strongSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily H.toSubMeas)
      (selfImprovementInInductionError params eps delta gamma)
  /-- The left and right placements of the output family stay close in squared distance. -/
  selfCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementInInductionError params eps delta gamma)
  /-- The dual witness `Z` controls the tensor failure expectation of `H`. -/
  bounded :
    tensorFailureExpectation strategy.state Z H.toSubMeas
      ≤ selfImprovementInInductionError params eps delta gamma
  /-- Every averaged point-evaluation operator is dominated by the dual witness `Z`. -/
  dominatesAveragePointOperator :
    ∀ h : Polynomial params,
      IdxPolyFamily.averagedPointEvaluationOperator strategy h ≤ Z

/-- Paper origin: `references/ldt-paper/inductive_step.tex:299-338`
(`\label{thm:ld-pasting-in-induction-section}`).

Conclusion of the section-local pasting theorem. -/
structure LdPastingInInductionSectionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (_family : IdxPolyFamily params ι)
    (H : Measurement (Polynomial params.next) ι)
    (eps delta gamma kappa zeta : Error) (k : ℕ) : Prop where
  /-- The pasted measurement is point-consistent with the ambient strategy. -/
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H.toSubMeas)
      (ldPastingInInductionError params k eps delta gamma kappa zeta)

/-- Bookkeeping data `x ↦ (ε_x, δ_x, γ_x)` for the restricted strategies. -/
structure RestrictedFailureProfile (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) : Type where
  /-- The axis-parallel failure bound attached to each slice height. -/
  axisParallel : Fq params → Error
  /-- The self-consistency failure bound attached to each slice height. -/
  selfConsistency : Fq params → Error
  /-- The diagonal-line failure bound attached to each slice height. -/
  diagonal : Fq params → Error
  /-- Each slice-restricted strategy is good with the recorded parameters. -/
  restrictedGood :
    ∀ x,
      (xRestrictedStrategy params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Bookkeeping data for answer-valued restricted strategies.

This is the function-answer analogue of `RestrictedFailureProfile`: each slice is
the restricted strategy interface from `inductive_step.tex`, lines 436--455. -/
structure AnswerRestrictedFailureProfile (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) : Type where
  /-- The axis-parallel failure bound attached to each slice height. -/
  axisParallel : Fq params → Error
  /-- The self-consistency failure bound attached to each slice height. -/
  selfConsistency : Fq params → Error
  /-- The diagonal-line failure bound attached to each slice height. -/
  diagonal : Fq params → Error
  /-- Each answer-valued slice-restricted strategy is good with the recorded parameters. -/
  restrictedGood :
    ∀ x,
      (xRestrictedAnswerSymStrat params strategy x).IsGood
        (axisParallel x)
        (selfConsistency x)
        (diagonal x)

/-- Average restricted axis-parallel error over slices. -/
noncomputable def averageRestrictedAxisParallelError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over slices. -/
noncomputable def averageRestrictedSelfConsistencyError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over slices. -/
noncomputable def averageRestrictedDiagonalError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : RestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Average restricted axis-parallel error over answer-valued slices. -/
noncomputable def averageAnswerRestrictedAxisParallelError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : AnswerRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.axisParallel

/-- Average restricted self-consistency error over answer-valued slices. -/
noncomputable def averageAnswerRestrictedSelfConsistencyError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : AnswerRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.selfConsistency

/-- Average restricted diagonal-line error over answer-valued slices. -/
noncomputable def averageAnswerRestrictedDiagonalError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    (profile : AnswerRestrictedFailureProfile params strategy) : Error :=
  avgOver (uniformDistribution (Fq params)) profile.diagonal

/-- Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`); answer-valued variant carrying the
same axis-parallel/self-consistency/diagonal restriction bounds for the
answer-restricted slice profile.  This is an answer-valued variant of
`RestrictedProbabilitiesStatement` against `xRestrictedAnswerSymStrat` rather
than `xRestrictedStrategy`; no separate paper anchor exists for the
answer-valued variant.

Bookkeeping data for the answer-valued restricted-probabilities lemma. -/
structure AnswerRestrictedProbabilitiesStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) : Prop where
  /-- There is a slice-wise answer-valued error profile realizing the three averaged bounds. -/
  profileExists :
    ∃ profile : AnswerRestrictedFailureProfile params strategy,
      averageAnswerRestrictedAxisParallelError params profile ≤
          sliceConditioningLoss params * eps ∧
        averageAnswerRestrictedSelfConsistencyError params profile ≤ delta ∧
        averageAnswerRestrictedDiagonalError params profile ≤
          sliceConditioningLoss params * gamma

/-- Bookkeeping data for the slice-restriction step of `thm:main-induction`.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`) and
`references/ldt-paper/inductive_step.tex:441-454`.

This records an explicit restricted failure profile together with the averaged
bounds extracted from `lem:restricted-probabilities`. -/
structure SliceRestrictionData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) where
  /-- Slice-wise failure profile `x ↦ (ε_x, δ_x, γ_x)`. -/
  profile : RestrictedFailureProfile params strategy
  /-- Averaged axis-parallel slice error bound. -/
  axisAverageBound :
    averageRestrictedAxisParallelError params profile ≤
      sliceConditioningLoss params * eps
  /-- Averaged self-consistency slice error bound. -/
  selfAverageBound :
    averageRestrictedSelfConsistencyError params profile ≤ delta
  /-- Averaged diagonal slice error bound. -/
  diagonalAverageBound :
    averageRestrictedDiagonalError params profile ≤
      sliceConditioningLoss params * gamma

/-- Answer-valued slice-restriction data record for the Section 6 induction step.

Paper origin: `references/ldt-paper/inductive_step.tex:374-412`
(`\label{lem:restricted-probabilities}`) and the recursive slice application in
`references/ldt-paper/inductive_step.tex:441-454`. -/
structure AnswerSliceRestrictionData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) where
  /-- Slice-wise failure profile for the answer-valued restricted strategies. -/
  profile : AnswerRestrictedFailureProfile params strategy
  /-- Averaged axis-parallel slice error bound. -/
  axisAverageBound :
    averageAnswerRestrictedAxisParallelError params profile ≤
      sliceConditioningLoss params * eps
  /-- Averaged self-consistency slice error bound. -/
  selfAverageBound :
    averageAnswerRestrictedSelfConsistencyError params profile ≤ delta
  /-- Averaged diagonal slice error bound. -/
  diagonalAverageBound :
    averageAnswerRestrictedDiagonalError params profile ≤
      sliceConditioningLoss params * gamma

/-- Explicit per-slice output of the inductive hypothesis.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`.

This is the recursion-entry data: given slice-restriction data, a proof of
`thm:main-induction` in dimension `m` is expected to produce a measurement `G^x`
for every slice height `x`. -/
structure PerSliceInductionData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (k : ℕ) where
  /-- Slice-wise inductive error `σ_x`. -/
  sliceError : Fq params → Error
  /-- Slice-wise inductive measurement `G^x`. -/
  sliceMeasurement : Fq params → Measurement (Polynomial params) ι
  /-- Each `G^x` satisfies the dimension-`m` point-consistency conclusion. -/
  pointConsistency :
    ∀ x,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
        (sliceError x)
  /-- The slice-wise error is bounded by the dimension-`m` induction target. -/
  error_le :
    ∀ x,
      sliceError x ≤
        mainInductionError params k
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)

/-- Explicit per-slice output of the inductive hypothesis for answer-valued slices.

Paper origin: `references/ldt-paper/inductive_step.tex:441-454`; answer-valued
restriction interface for the same recursive call.

This is the function-answer recursion-entry data record: the recursive call is made on
`xRestrictedAnswerSymStrat`, whose diagonal answers retain the whole restricted
function instead of only its value at the base point. -/
structure AnswerPerSliceInductionData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (k : ℕ) where
  /-- Slice-wise inductive error `σ_x`. -/
  sliceError : Fq params → Error
  /-- Slice-wise inductive measurement `G^x`. -/
  sliceMeasurement : Fq params → Measurement (Polynomial params) ι
  /-- Each `G^x` satisfies the dimension-`m` point-consistency conclusion. -/
  pointConsistency :
    ∀ x,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceMeasurement x).toSubMeas)
        (sliceError x)
  /-- The slice-wise error is bounded by the dimension-`m` induction target. -/
  error_le :
    ∀ x,
      sliceError x ≤
        mainInductionError params k
          (restrictionPkg.profile.axisParallel x)
          (restrictionPkg.profile.selfConsistency x)
          (restrictionPkg.profile.diagonal x)

/-- Paper origin: `references/ldt-paper/inductive_step.tex:7-18`
(`\label{thm:main-induction}`); answer-valued analogue.

Main-induction conclusion for a function-answer symmetric strategy.

This is the answer-valued analogue of the conclusion of `thm:main-induction`.
It is used as the explicit predecessor induction hypothesis for the
paper-faithful answer-valued restriction route: for a strategy in dimension `m`,
it supplies a global polynomial measurement consistent with the point
measurement at the Section 6 error `mainInductionError`. -/
def AnswerMainInductionConclusion (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error) (k : ℕ) : Prop :=
  ∃ G : Measurement (Polynomial params) ι,
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas)
      (mainInductionError params k eps delta gamma)

/-- Predicate form of the answer-valued predecessor main-induction hypothesis.

This is a Lean-only interface for the induction step in
`references/ldt-paper/inductive_step.tex:441-454`.  It is deliberately stated at
`mainInductionError` strength and for `AnswerSymStrat`, so callers can instantiate
the paper-faithful `xRestrictedAnswerSymStrat` slices without appealing to the
public `Test.mainFormal` theorem.

The explicit `.{u,v}` universe binder decouples the universe of `FieldModel`'s
carrier `K : Type u` from the universe of the dimension index `ι : Type v`.
Without this separation, a proof that instantiates `FieldModel.{0}` (as many
`Test.MainTheorem` applications do) would also force `ι` to `Type 0`,
making it impossible to apply the hypothesis to the role-register space
`Role × ι` when the index universe exceeds `0`. -/
def AnswerMainInductionHypothesis.{u,v} (params : Parameters)
    [FieldModel.{u} params.q] : Prop :=
  ∀ (ι : Type v) [Fintype ι] [DecidableEq ι],
    ∀ (strategy : AnswerSymStrat params ι) (eps delta gamma : Error) (k : ℕ),
      strategy.IsGood eps delta gamma →
        1 ≤ k →
          400 * params.m * params.d ≤ k →
            AnswerMainInductionConclusion params strategy eps delta gamma k

/-- The slice-local self-improvement error `ζ_x`. -/
noncomputable def sliceSelfImprovementError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (x : Fq params) : Error :=
  selfImprovementInInductionError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)
    (restrictionPkg.profile.diagonal x)

/-- The slice-local self-improvement error `ζ_x` for answer-valued slices. -/
noncomputable def answerSliceSelfImprovementError (params : Parameters)
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error}
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (x : Fq params) : Error :=
  selfImprovementInInductionError params
    (restrictionPkg.profile.axisParallel x)
    (restrictionPkg.profile.selfConsistency x)
    (restrictionPkg.profile.diagonal x)

/-- Slice-wise output of the induction-level self-improvement stage.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`
(`\label{thm:self-improvement-in-induction-section}` in use inside the proof of
`\label{thm:main-induction}`).

Because `xRestrictedStrategy` is a section-local restricted strategy rather than
literally a `SymStrat params` interface—it does not carry the ambient
`permInvState` witness, the diagonal reparametrization-invariance field, or the
downstream role-symmetrization API—this data records directly the four
paper-faithful
properties that will later be averaged into the pasting inputs. -/
structure SelfImprovementData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) (k : ℕ)
    (restrictionPkg : SliceRestrictionData params strategy eps delta gamma)
    (inductionPkg : PerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    where
  /-- Slice-wise projective submeasurement `Ĝ^x`. -/
  sliceProj : Fq params → ProjSubMeas (Polynomial params) ι
  /-- Slice-wise PSD witness `Z^x`. -/
  sliceWitness : Fq params → MIPStarRE.Quantum.Op ι
  /-- Slice-wise completeness bound. -/
  completeness :
    ∀ x,
      CompletenessAtLeast strategy.state (sliceProj x).toSubMeas.liftLeft
        ((1 - inductionPkg.sliceError x) -
          sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise consistency with the restricted point measurement. -/
  pointConsistency :
    ∀ x,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (xRestrictedStrategy params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
        (sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise strong self-consistency. -/
  strongSelfConsistency :
    ∀ x,
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (sliceProj x).toSubMeas)
        (sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise left/right closeness needed for the averaged self-consistency input. -/
  selfCloseness :
    ∀ x,
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
        (sliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise boundedness residual. -/
  bounded :
    ∀ x,
      tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas
        ≤ sliceSelfImprovementError params restrictionPkg x
  /-- Slice-wise domination of the averaged point operator. -/
  dominatesAveragePointOperator :
    ∀ x, ∀ h : Polynomial params,
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x

namespace SelfImprovementData

/-- The slice-indexed polynomial family obtained by collecting the improved
slice measurements `Ĝ^x` together with the slice-wise witnesses `Z^x`. -/
noncomputable def family {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg) :
    IdxPolyFamily params ι where
  meas := pkg.sliceProj
  witness := pkg.sliceWitness
  dominationTarget := fun x g =>
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g

@[simp] theorem family_meas {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg) :
    pkg.family.meas = pkg.sliceProj :=
  rfl

@[simp] theorem family_witness {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) :
    pkg.family.witness x = pkg.sliceWitness x :=
  rfl

@[simp] theorem family_dominationTarget {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) (g : Polynomial params) :
    pkg.family.dominationTarget x g =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g :=
  rfl

end SelfImprovementData

/-- Slice-wise output of the induction-level self-improvement stage for
answer-valued restricted strategies.

Paper origin: `references/ldt-paper/inductive_step.tex:461-551`;
answer-valued restriction interface for the same self-improvement stage.

This mirrors `SelfImprovementData`, but its point-consistency field is stated
against `xRestrictedAnswerSymStrat`, the function-answer restricted strategy. -/
structure AnswerSelfImprovementData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) (k : ℕ)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k)
    where
  /-- Slice-wise projective submeasurement `Ĝ^x`. -/
  sliceProj : Fq params → ProjSubMeas (Polynomial params) ι
  /-- Slice-wise PSD witness `Z^x`. -/
  sliceWitness : Fq params → MIPStarRE.Quantum.Op ι
  /-- Slice-wise completeness bound. -/
  completeness :
    ∀ x,
      CompletenessAtLeast strategy.state (sliceProj x).toSubMeas.liftLeft
        ((1 - inductionPkg.sliceError x) -
          answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise consistency with the answer-valued restricted point measurement. -/
  pointConsistency :
    ∀ x,
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (xRestrictedAnswerSymStrat params strategy x).pointMeasurement)
        (polynomialEvaluationFamily params (sliceProj x).toSubMeas)
        (answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise strong self-consistency. -/
  strongSelfConsistency :
    ∀ x,
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (sliceProj x).toSubMeas)
        (answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise left/right closeness needed for the averaged self-consistency data record. -/
  selfCloseness :
    ∀ x,
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) (sliceProj x).toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) (sliceProj x).toSubMeas))
        (answerSliceSelfImprovementError params restrictionPkg x)
  /-- Slice-wise boundedness residual. -/
  bounded :
    ∀ x,
      tensorFailureExpectation strategy.state (sliceWitness x) (sliceProj x).toSubMeas
        ≤ answerSliceSelfImprovementError params restrictionPkg x
  /-- Slice-wise domination of the averaged point operator. -/
  dominatesAveragePointOperator :
    ∀ x, ∀ h : Polynomial params,
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x h ≤ sliceWitness x

namespace AnswerSelfImprovementData

/-- The slice-indexed polynomial family obtained from answer-valued restricted
self-improvement outputs. -/
noncomputable def family {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg) :
    IdxPolyFamily params ι where
  meas := pkg.sliceProj
  witness := pkg.sliceWitness
  dominationTarget := fun x g =>
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g

@[simp] theorem family_meas {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg) :
    pkg.family.meas = pkg.sliceProj :=
  rfl

@[simp] theorem family_witness {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) :
    pkg.family.witness x = pkg.sliceWitness x :=
  rfl

@[simp] theorem family_dominationTarget {params : Parameters}
    [FieldModel params.q]
    {strategy : SymStrat params.next ι}
    {eps delta gamma : Error} {k : ℕ}
    {restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      AnswerPerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (pkg :
      AnswerSelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    (x : Fq params) (g : Polynomial params) :
    pkg.family.dominationTarget x g =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g :=
  rfl

end AnswerSelfImprovementData

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:12-50`
(`\label{thm:ld-pasting}`) and
`references/ldt-paper/inductive_step.tex:239-342`.

Averaged pasting inputs distilled from the per-slice self-improvement data.

This records exactly the hypotheses needed to invoke
`thm:ld-pasting-in-induction-section` after the slice-wise self-improvement
outputs have been averaged. -/
structure AveragedPastingData (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error) (k : ℕ)
    {restrictionPkg : SliceRestrictionData params strategy eps delta gamma}
    {inductionPkg :
      PerSliceInductionData params strategy eps delta gamma restrictionPkg k}
    (selfPkg : SelfImprovementData params strategy eps delta gamma k restrictionPkg inductionPkg)
    where
  /-- Averaged completeness parameter `κ`. -/
  kappa : Error
  /-- Averaged self-improvement / pasting interface parameter `ζ`. -/
  zeta : Error
  /-- Averaged completeness of the slice family. -/
  complete : selfPkg.family.Complete strategy.state kappa
  /-- Averaged point-consistency of the slice family. -/
  consistent : selfPkg.family.ConsistentWithPoints strategy zeta
  /-- Averaged strong self-consistency of the slice family. -/
  selfConsistent : selfPkg.family.StronglySelfConsistent strategy.state zeta
  /-- Averaged boundedness input for the pasting theorem. -/
  bounded : IdxPolyFamily.SliceBoundednessInput strategy selfPkg.family zeta
  /-- Error telescoping from the induction-section pasting bound to the next-stage target. -/
  error_le :
    ldPastingInInductionError params k eps delta gamma kappa zeta ≤
      mainInductionError params.next k eps delta gamma

end MIPStarRE.LDT.MainInductionStep


