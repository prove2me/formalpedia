-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:16:30.791989+00:00
-- url     : https://prove2.me/theorems/ebb6d82a-ab32-4d55-b6ad-90311c31238f
-- title:
--   Definitions of Statements: Section 9 self-improvement statements This file records the SDP, `addInU`, and orthonormalization interfaces used in…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Statements` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 9 self-improvement statements. This file records the SDP, `addInU`, and orthonormalization interfaces used in the current formalization of the self-improvement theorem.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (21): `MIPStarRE.LDT.SelfImprovement.AddInUStatement` (Paper origin: `references/ldt-paper/self_improvement.tex:238-455` (`\label{lem:add-in-u}`).); `MIPStarRE.LDT.SelfImprovement.SdpOptimalPair` (Lean-only reduced SDP data for the currently formalized fragment of the self-improvement argument.); `MIPStarRE.LDT.SelfImprovement.SdpOptimalPairWithSlackness` (SDP optimal-pair data strengthened by complementary slackness.); `MIPStarRE.LDT.SelfImprovement.SdpOptimalPairWithSlackness.primalMeasurement` (The primal submeasurement in a slackness-carrying SDP pair is a measurement.); `MIPStarRE.LDT.SelfImprovement.SdpStatementWithSlackness` (Paper origin: `references/ldt-paper/self_improvement.tex:82-181` (`\label{lem:sdp}`); the complementary-slackness equation `T_g · Z = T_g ·…); `MIPStarRE.LDT.SelfImprovement.SelfImprovementConclusion` (Paper origin: `references/ldt-paper/self_improvement.tex:635-671` (`\label{thm:self-improvement}`).); `MIPStarRE.LDT.SelfImprovement.SelfImprovementFinalFields` (Final fields for the Section 9 transport stage.); `MIPStarRE.LDT.SelfImprovement.SelfImprovementHelperConclusion` (Paper origin: `references/ldt-paper/self_improvement.tex:24-60` (`\label{lem:self-improvement-helper}`);…); `MIPStarRE.LDT.SelfImprovement.SelfImprovementHelperConclusionWithSlackness` (Internal helper conclusion strengthened by the SDP complementary-slackness equation.); and 4 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `primalMeasurement_toSubMeas`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Statements` (`MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 39 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Statements.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Basic
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
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
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
import Mathlib.Algebra.Order.Group.Abs
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
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
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
import Mathlib.Analysis.Real.Spectrum
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
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
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
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
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
import Mathlib.Order.Hom.Basic
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
import Mathlib.Tactic.NormNum.Eq
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
import Mathlib.Topology.ContinuousOn
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs

set_option backward.isDefEq.respectTransparency false

/-!
# Section 9 self-improvement statements

This file records the SDP, `addInU`, and orthonormalization interfaces used in
the current formalization of the self-improvement theorem.

## References

- `blueprint/src/chapter/ch07_self_improvement.tex`
- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Operators and conclusions -/

/-- Lean-only reduced SDP data for the currently formalized fragment of the
self-improvement argument.

Paper-gap note: `docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

The paper's `lem:sdp` eventually supplies strong duality, complementary
slackness, and a concrete matrix-level optimal witness. The current Lean
development only consumes the weaker facts recorded here: the primal witness is
a full measurement (`T.total = 1`), and the dual witness dominates every
averaged point operator. Positivity of the dual witness is derivable from dual
feasibility and positivity of the averaged point operators. Despite the
historical name, this reduced record does not assert SDP optimality. -/
structure SdpOptimalPair (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (Z : MIPStarRE.Quantum.Op ι) : Prop where
  primalTotalOperator :
    T.total = 1
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g

namespace SdpOptimalPair

end SdpOptimalPair

/-- SDP optimal-pair data strengthened by complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`); paper-gap note:
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

The reduced `SdpOptimalPair` interface above contains only the feasibility and
normalization facts already produced by the current Lean theorem for `lem:sdp`.
The paper's strong-duality argument also gives complementary slackness.  This
successor interface records that additional conclusion without claiming that
the reduced theorem has already proved it. -/
structure SdpOptimalPairWithSlackness (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (Z : MIPStarRE.Quantum.Op ι) : Prop where
  toSdpOptimalPair :
    SdpOptimalPair params strategy T Z
  complementarySlackness :
    ∀ g : Polynomial params,
      sdpComplementarySlacknessEquation params strategy T Z g

/-- Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`); the complementary-slackness equation `T_g · Z = T_g · A_g`
is `eq:complementary-slackness` at line 179.

SDP conclusion strengthened by complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 62--88
introduce the Section 9 primal/dual SDP pair and state `\label{lem:sdp}`:
there is an optimal pair `{T_g}`, `Z` with `∑ g, T_g = I` and
`T_g Z = T_g A_g` for every polynomial `g`.  Lines 168--190 then invoke
Slater's condition, strong duality, and complementary slackness to derive these
same measurement-total and slackness conclusions from the canonical SDP.

This is the statement shape expected from that paper argument: it records the
complete primal measurement, the dual-feasible operator, and the
complementary-slackness equations. -/
structure SdpStatementWithSlackness (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) : Prop where
  witness :
    ∃ T : Measurement (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SdpOptimalPairWithSlackness params strategy T.toSubMeas Z

namespace SdpOptimalPairWithSlackness

/-- The primal submeasurement in a slackness-carrying SDP pair is a
measurement. -/
def primalMeasurement {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    {T : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    Measurement (Polynomial params) ι where
  toSubMeas := T
  total_eq_one := h.toSdpOptimalPair.primalTotalOperator

@[simp] theorem primalMeasurement_toSubMeas {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    {T : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : SdpOptimalPairWithSlackness params strategy T Z) :
    h.primalMeasurement.toSubMeas = T :=
  rfl

end SdpOptimalPairWithSlackness

namespace SdpStatementWithSlackness

end SdpStatementWithSlackness

/-- The operator inside the left-hand side of `lem:add-in-u` at a fixed point `u`.
Returns a bipartite operator `(M u).outcome o ⊗ H.outcome h`. -/
noncomputable def addInULeftOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (_strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (H : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    opTensor ((M u).outcome ah.1) (H.outcome ah.2)

/-- The operator inside the right-hand side of `lem:add-in-u` at a fixed point `u`.
Returns a bipartite operator `(Au * (M u).outcome o * Au) ⊗ T.outcome h`. -/
noncomputable def addInURightOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
    opTensor (Au * (M u).outcome ah.1 * Au) (T.outcome ah.2)

noncomputable def addInUPointAverage (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (f : Point params → MIPStarRE.Quantum.Op (ι × ι)) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u => ev strategy.state (f u))

/-- The left-hand expectation in `lem:add-in-u`. -/
noncomputable def addInULeftQuantity {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (H : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  addInUPointAverage params strategy (addInULeftOperatorAtPoint params strategy M H S)

/-- The right-hand expectation in `lem:add-in-u`. -/
noncomputable def addInURightQuantity {Outcome : Type*} [Fintype Outcome] (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) : Error :=
  addInUPointAverage params strategy (addInURightOperatorAtPoint params strategy M T S)

/-- The pointwise matched operator `Σ_a A^u_a ⊗ H_[h(u)=a]`
on the bipartite space `ι × ι`. -/
noncomputable def helperAgreementOperatorAtPoint (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  let Hu := evaluateAt params u H
  ∑ a : Fq params, opTensor ((strategy.pointMeasurement u).outcome a) (Hu.outcome a)

/-- The average operator `E_u Σ_a A^u_a ⊗ H_[h(u)=a]`
on the bipartite space `ι × ι`. -/
noncomputable def helperAgreementAverageOperator (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (helperAgreementOperatorAtPoint params strategy H)

/-- The helper-stage upper operator `Z ⊗ I`
on the bipartite space `ι × ι`. -/
noncomputable def helperUpperOperator (_params : Parameters)
    (Z : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι) Z

/-- The operator measuring the helper-stage boundedness defect
on the bipartite space `ι × ι`. -/
noncomputable def helperBoundednessOperator (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  helperUpperOperator params Z -
    helperAgreementAverageOperator params strategy H

/-- The helper-stage boundedness defect. -/
noncomputable def helperBoundednessGap (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) : Error :=
  ev strategy.state
    (helperBoundednessOperator params strategy H Z)

/-- The projective-stage residual operator `Z ⊗ (I - H)`
on the bipartite space `ι × ι`. -/
noncomputable def projectiveResidualOperator (params : Parameters)
    [FieldModel params.q]
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι) Z *
    rightTensor (ι₁ := ι) (1 - H.toSubMeas.total)

/-- The projective-stage boundedness defect. -/
noncomputable def projectiveBoundednessGap (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) : Error :=
  ev strategy.state
    (projectiveResidualOperator params H Z)

/-- Paper origin: `references/ldt-paper/self_improvement.tex:238-455`
(`\label{lem:add-in-u}`).

Reduced conclusion for the currently formalized fragment of `lem:add-in-u`.

The paper statement quantifies over an auxiliary submeasurement `M`, the
averaged family `H`, and a selection rule `S`, and proves a transfer inequality
between two expectations. The current Lean development only uses the downstream
global-variance corollary, which depends only on the SDP measurement `T` and
the error parameters, so those unused inputs are omitted here. -/
structure AddInUStatement (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (eps delta : Error) : Prop where
  varianceBound :
    pointConditionedGlobalVariance params strategy T.toSubMeas ≤
      selfImprovementVarianceError params eps delta

/-- Paper origin: `references/ldt-paper/self_improvement.tex:24-60`
(`\label{lem:self-improvement-helper}`);
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex` (SDP gap).

Reduced conclusion for the SDP and `addInU` stage of
`lem:self-improvement-helper`.

This structure intentionally records only the guarantees produced directly by
the current slackness-carrying SDP route and the `addInU` argument: the SDP
witness, the averaged construction of `H`, and the reduced `addInU` variance
bound. Positivity and pointwise dual feasibility of `Z` are read from the
bundled SDP witness rather than repeated as helper fields.

The paper and blueprint state four additional helper-lemma guarantees
(`completeness`, `pointConsistency`, strong self-consistency, and boundedness).
Those do not yet come from these arguments alone, so they are not fields here;
they should be proved as separate estimates that consume this SDP-witness
conclusion together with the paper hypotheses. -/
structure SelfImprovementHelperConclusion (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta : Error) : Prop where
  sdpWitness : SdpOptimalPair params strategy T.toSubMeas Z
  averagedConstruction :
    H = averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  addInUVarianceBound :
    AddInUStatement params strategy T eps delta

/-- Internal helper conclusion strengthened by the SDP complementary-slackness
equation.

Paper origin: `references/ldt-paper/self_improvement.tex:82-181`
(`\label{lem:sdp}`) and `references/ldt-paper/self_improvement.tex:635-671`
(`\label{thm:self-improvement}`); paper-gap note:
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

This is not an additional source-theorem hypothesis.  It is the internal
helper-output record produced after the SDP theorem
`sdp_statement_with_slackness` supplies strong duality.  It keeps all fields of
the reduced helper conclusion and additionally records the consequence
`T_g Z = T_g A_g`. -/
structure SelfImprovementHelperConclusionWithSlackness (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta : Error) : Prop where
  toHelperConclusion :
    SelfImprovementHelperConclusion params strategy T H Z eps delta
  complementarySlackness :
    ∀ g : Polynomial params,
      sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g

/-- Paper origin: `references/ldt-paper/self_improvement.tex:635-671`
(`\label{thm:self-improvement}`).

Conclusion of `thm:self-improvement`.

The paper's boundedness output is the projective residual estimate
`⟨ψ, Z ⊗ (I - H)⟩ ≤ ζ`, recorded here as `projectiveResidualBound`.  This
structure is the conjunction of the paper's displayed conclusions for the
already-quantified witnesses `H` and `Z`; it does not store an internal helper
form or an SDP connection input. -/
structure SelfImprovementConclusion (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta gamma nu : Error) : Prop where
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementError params eps delta)
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta)
  selfCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementError params eps delta)
  positiveSemidefiniteWitness :
    0 ≤ Z
  dualDominatesAveragedPoint :
    ∀ g : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z g
  projectiveResidualBound :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta

/-- Final fields for the Section 9 transport stage.

The final fields are the Section 9 outputs that remain after combining:
`SelfImprovementHelper`, orthonormalization, data-processing, and the
monotone-total transport used in the projective-output step.

This record contains completeness, point-consistency, self-closeness, and the
projective-residual estimate. This projective residual is already the
paper-facing boundedness quantity carried into `SelfImprovementConclusion`. -/
structure SelfImprovementFinalFields (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta nu : Error) : Prop where
  completeness :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementError params eps delta)
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta)
  selfCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (selfImprovementError params eps delta)
  projectiveResidualBound :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta

end MIPStarRE.LDT.SelfImprovement


