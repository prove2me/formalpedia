-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:14:54.171953+00:00
-- url     : https://prove2.me/theorems/97cfcd8c-2b83-4503-a632-30f8e2c9b53f
-- title:
--   Definitions of Defs: Section 9 — Definitions This file exposes the paper's SDP witnesses, the `add-in-u` transfer identity, and the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Defs` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 9 — Definitions. This file exposes the paper's SDP witnesses, the `add-in-u` transfer identity, and the non-projective/projective self-improvement outputs through explicit named constructions and error terms.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (18): `MIPStarRE.LDT.SelfImprovement.AddInUSelection` (A point-indexed selection of outcome/polynomial pairs used in `lem:add-in-u`.); `MIPStarRE.LDT.SelfImprovement.addInUError` (The error term in `lem:add-in-u`.); `MIPStarRE.LDT.SelfImprovement.addInUSelectionPairs` (The finite set of selected outcome/polynomial pairs at a point `u`.); `MIPStarRE.LDT.SelfImprovement.averagedPointOperator` (The averaged point operator `A_g = E_u A^u_{g(u)}`.); `MIPStarRE.LDT.SelfImprovement.averagedSandwichedPolynomialSubMeas` (The averaged sandwiched submeasurement `H_h = E_u H^u_h`.); `MIPStarRE.LDT.SelfImprovement.sandwichedPolynomialOutcomeOperatorAt` (The pointwise sandwiched operator `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`.); `MIPStarRE.LDT.SelfImprovement.sandwichedPolynomialSubMeasAt` (The pointwise sandwiched submeasurement `H^u = {H^u_h}`.); `MIPStarRE.LDT.SelfImprovement.sdpComplementarySlacknessEquation` (The complementary-slackness equation `T_g Z = T_g A_g`.); `MIPStarRE.LDT.SelfImprovement.sdpDistinguishedPolynomial` (The zero polynomial used as the distinguished polynomial block in canonical SDP completion arguments.); `MIPStarRE.LDT.SelfImprovement.sdpDualSlackOperator` (The dual slack operator `Z - A_g`.); `MIPStarRE.LDT.SelfImprovement.sdpStrictDualWitness` (Paper origin: `references/ldt-paper/self_improvement.tex:168-176` (`\label{lem:sdp}` strict feasible dual witness `Z = 2I`); blueprint…); and -5 more.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `sdpStrictDualWitness_nonneg`, `sdpStrictPrimalConstantSum`, `sdpStrictPrimalSubMeas_total`, `averagedSandwichedPolynomialSubMeas_total_le_one`, `sandwichedPolynomialOutcomeOperatorAt_sum_le_one`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Defs` (`MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Defs.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 38 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Defs.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Defs.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Defs.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPStarRE_LDT_ProjMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_congr
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_nonneg
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_sum
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_uniform_le_one
import Theorems.Thm_MIPStarRE_LDT_polynomial_sum_fiberwise

set_option backward.isDefEq.respectTransparency false

/-!
# Section 9 — Definitions

This file exposes the paper's SDP witnesses, the `add-in-u` transfer identity,
and the non-projective/projective self-improvement outputs through explicit named
constructions and error terms.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The zero polynomial used as the distinguished polynomial block in canonical
SDP completion arguments. -/
noncomputable def sdpDistinguishedPolynomial (params : Parameters) [FieldModel params.q] :
    Polynomial params :=
  ⟨0, by
    intro i
    simp [MvPolynomial.degreeOf_zero]⟩

/-- The paper's strict-feasibility weight `1 / (2 |\polyfunc{m}{q}{d}|)`. -/
noncomputable def sdpStrictPrimalWeight (params : Parameters)
    [FieldModel params.q] : Error :=
  1 / (2 * (Fintype.card (Polynomial params) : Error))

omit [Fintype ι] in
/-- Paper origin: `references/ldt-paper/self_improvement.tex:168-176`
(`\label{lem:sdp}` strict feasible primal witness
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`).

The constant strict primal effects have total mass `(1/2)I`.  This is the
scalar identity behind the paper's strict feasible primal witness. -/
theorem sdpStrictPrimalConstantSum (params : Parameters)
    [FieldModel params.q] :
    ∑ _ : Polynomial params, sdpStrictPrimalWeight params •
        (1 : MIPStarRE.Quantum.Op ι) =
      ((1 / 2 : Error) • (1 : MIPStarRE.Quantum.Op ι)) := by
  have hdenom : (2 * (Fintype.card (Polynomial params) : Error)) ≠ 0 := by
    positivity
  calc
    ∑ g : Polynomial params, sdpStrictPrimalWeight params •
        (1 : MIPStarRE.Quantum.Op ι)
        = ((∑ g : Polynomial params, sdpStrictPrimalWeight params) : Error) •
            (1 : MIPStarRE.Quantum.Op ι) := by
              simpa using
                (Finset.sum_smul (s := Finset.univ)
                  (f := fun _ : Polynomial params => sdpStrictPrimalWeight params)
                  (x := (1 : MIPStarRE.Quantum.Op ι))).symm
    _ = ((Fintype.card (Polynomial params) : Error) *
          sdpStrictPrimalWeight params) •
          (1 : MIPStarRE.Quantum.Op ι) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = ((1 / 2 : Error) • (1 : MIPStarRE.Quantum.Op ι)) := by
          congr 1
          unfold sdpStrictPrimalWeight
          field_simp [hdenom]

/-- The paper's strict-feasible primal SDP witness
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`. -/
noncomputable def sdpStrictPrimalSubMeas (params : Parameters)
    [FieldModel params.q] : SubMeas (Polynomial params) ι :=
  { outcome := fun _ => sdpStrictPrimalWeight params • (1 : MIPStarRE.Quantum.Op ι)
    total := ∑ g : Polynomial params,
      sdpStrictPrimalWeight params • (1 : MIPStarRE.Quantum.Op ι)
    outcome_pos := fun _ => smul_nonneg (by
      unfold sdpStrictPrimalWeight
      positivity) (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))
    sum_eq_total := rfl
    total_le_one := (le_of_eq (sdpStrictPrimalConstantSum (ι := ι) params)).trans (by
      simpa using smul_le_smul_of_nonneg_right
        (show (1 / 2 : Error) ≤ 1 by norm_num)
        (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))) }

/-- The paper's uniform strict-feasible primal witness has total mass
`(1 / 2) • I`. -/
@[simp] theorem sdpStrictPrimalSubMeas_total (params : Parameters)
    [FieldModel params.q] :
    (sdpStrictPrimalSubMeas (ι := ι) params).total =
      ((1 / 2 : Error) • (1 : MIPStarRE.Quantum.Op ι)) := by
  simpa [sdpStrictPrimalSubMeas] using
    sdpStrictPrimalConstantSum (ι := ι) params

/-- Paper origin: `references/ldt-paper/self_improvement.tex:168-176`
(`\label{lem:sdp}` strict feasible dual witness `Z = 2I`);
blueprint `\label{lem:sdp-uniform-feasible-witness}`.

The paper's strict-feasible dual SDP witness `Z = 2I`. -/
noncomputable def sdpStrictDualWitness : MIPStarRE.Quantum.Op ι :=
  (2 : Error) • (1 : MIPStarRE.Quantum.Op ι)

/-- The paper's strict-feasible dual witness `2I` is positive semidefinite. -/
@[simp] theorem sdpStrictDualWitness_nonneg {ι : Type*} [Finite ι] [DecidableEq ι] :
    0 ≤ (sdpStrictDualWitness (ι := ι)) := by
  letI := Fintype.ofFinite ι
  unfold sdpStrictDualWitness
  exact smul_nonneg (by norm_num)
    (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))

/-- The averaged point operator `A_g = E_u A^u_{g(u)}`. -/
noncomputable def averagedPointOperator (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g)

/-- The dual slack operator `Z - A_g`. -/
noncomputable def sdpDualSlackOperator (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  Z - averagedPointOperator params strategy g

/-- The complementary-slackness equation `T_g Z = T_g A_g`. -/
def sdpComplementarySlacknessEquation (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) : Prop :=
  T.outcome g * Z =
    T.outcome g * averagedPointOperator params strategy g

/-- A point-indexed selection of outcome/polynomial pairs used in `lem:add-in-u`. -/
abbrev AddInUSelection (params : Parameters) [FieldModel params.q] (Outcome : Type*) :=
  Point params → Set (Outcome × Polynomial params)

/-- The finite set of selected outcome/polynomial pairs at a point `u`. -/
noncomputable def addInUSelectionPairs {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : AddInUSelection params Outcome) (u : Point params) :
    Finset (Outcome × Polynomial params) :=
  open Classical in
    Finset.univ.filter (fun ah : Outcome × Polynomial params => ah ∈ S u)

/-- The pointwise sandwiched operator `H^u_h = A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def sandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (h : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
  Au * (T.outcome h) * Au

/-- The sum of the pointwise sandwiched operators is bounded above by the identity. -/
theorem sandwichedPolynomialOutcomeOperatorAt_sum_le_one (params : Parameters)
    [FieldModel params.q] (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (u : Point params) :
    ∑ h : Polynomial params, sandwichedPolynomialOutcomeOperatorAt params strategy T u h ≤ 1 := by
  let Au := strategy.pointMeasurement u
  -- Regroup by evaluation value a = h(u).
  calc
    ∑ h : Polynomial params, sandwichedPolynomialOutcomeOperatorAt params strategy T u h
      = ∑ a : Fq params,
          ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
            Au.toSubMeas.outcome a * T.outcome h * Au.toSubMeas.outcome a := by
          rw [show ∑ h : Polynomial params,
                sandwichedPolynomialOutcomeOperatorAt params strategy T u h =
              ∑ a : Fq params,
                ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                  sandwichedPolynomialOutcomeOperatorAt params strategy T u h from by
            exact polynomial_sum_fiberwise params u
              (sandwichedPolynomialOutcomeOperatorAt params strategy T u)]
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro h hh
          simp only [sandwichedPolynomialOutcomeOperatorAt,
            pointConditionedOutcomeOperatorAtPolynomial]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
          simp [Au, hh]
    _ = ∑ a : Fq params,
          Au.toSubMeas.outcome a *
            (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
              T.outcome h) *
            Au.toSubMeas.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← Matrix.sum_mul, ← Matrix.mul_sum]
    _ ≤ ∑ a : Fq params, Au.toSubMeas.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          have hfilt_le_one : ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a), T.outcome h ≤ 1 :=
            calc
              ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a), T.outcome h
                ≤ ∑ h : Polynomial params, T.outcome h :=
                  Finset.sum_le_sum_of_subset_of_nonneg
                    (Finset.filter_subset _ _) (fun h _ _ => T.outcome_pos h)
              _ = T.total := T.sum_eq_total
              _ ≤ 1 := T.total_le_one
          simpa [Au.proj a] using
            IsSelfAdjoint.conjugate_le_conjugate
              (c := Au.toSubMeas.outcome a) hfilt_le_one (Au.outcome_hermitian a)
    _ = Au.toSubMeas.total := by
          rw [Au.toSubMeas.sum_eq_total]
    _ = 1 := by
          simpa using Au.total_eq_one

/-- The pointwise sandwiched submeasurement `H^u = {H^u_h}`. -/
noncomputable def sandwichedPolynomialSubMeasAt (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (u : Point params) :
    SubMeas (Polynomial params) ι :=
  { outcome := sandwichedPolynomialOutcomeOperatorAt params strategy T u
    total := ∑ h : Polynomial params,
      sandwichedPolynomialOutcomeOperatorAt params strategy T u h
    outcome_pos := fun h => by
      simp only [sandwichedPolynomialOutcomeOperatorAt, pointConditionedOutcomeOperatorAtPolynomial]
      exact IsSelfAdjoint.conjugate_nonneg (T.outcome_pos h)
        (SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas (h u))
    sum_eq_total := rfl
    total_le_one := sandwichedPolynomialOutcomeOperatorAt_sum_le_one params strategy T u }

/-- The average of the total pointwise sandwiched operators is bounded by the identity. -/
theorem averagedSandwichedPolynomialSubMeas_total_le_one (params : Parameters)
    [FieldModel params.q] (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    ∑ h : Polynomial params,
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h) ≤ 1 := by
  let 𝒟 := uniformDistribution (Point params)
  calc
    ∑ h : Polynomial params,
        averageOperatorOverDistribution 𝒟
          (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
      = averageOperatorOverDistribution 𝒟
          (fun u => ∑ h : Polynomial params,
            sandwichedPolynomialOutcomeOperatorAt params strategy T u h) := by
            exact (averageOperatorOverDistribution_sum 𝒟
              (fun u h => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)).symm
    _ = averageOperatorOverDistribution 𝒟
          (fun u => (sandwichedPolynomialSubMeasAt params strategy T u).total) := by
            exact averageOperatorOverDistribution_congr 𝒟 _ _ fun u => by
              simp [sandwichedPolynomialSubMeasAt]
    _ ≤ 1 := by
          simpa [𝒟] using
            averageOperatorOverDistribution_uniform_le_one
              (fun u => (sandwichedPolynomialSubMeasAt params strategy T u).total)
              (fun u => (sandwichedPolynomialSubMeasAt params strategy T u).total_le_one)

/-- The averaged sandwiched submeasurement `H_h = E_u H^u_h`. -/
noncomputable def averagedSandwichedPolynomialSubMeas (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : SubMeas (Polynomial params) ι :=
  { outcome := fun h =>
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    total := ∑ h : Polynomial params,
      averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
    outcome_pos := fun h => averageOperatorOverDistribution_nonneg
      (uniformDistribution (Point params))
      (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
      (fun u => (sandwichedPolynomialSubMeasAt params strategy T u).outcome_pos h)
    sum_eq_total := rfl
    total_le_one := averagedSandwichedPolynomialSubMeas_total_le_one params strategy T }

/-- The variance error entering `lem:add-in-u`. -/
noncomputable def selfImprovementVarianceError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  globalVarianceOfPointsError params eps delta

/-- The error term in `lem:add-in-u`. -/
noncomputable def addInUError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  4 * Real.rpow (selfImprovementVarianceError params eps delta) (1 / (2 : Error))

/-- The quantitative error from `lem:self-improvement-helper`. -/
noncomputable def selfImprovementHelperError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  100 * (params.m : Error) *
    (Real.rpow eps (1 / (2 : Error)) +
      Real.rpow delta (1 / (2 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (2 : Error)))

/-- The orthogonalization error applied to the helper output. -/
noncomputable def selfImprovementOrthogonalizationError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  orthonormalizationError (selfImprovementHelperError params eps delta)

/-- The postprocessed error after projecting the helper output. -/
noncomputable def selfImprovementDataProcessingError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  8 * selfImprovementHelperError params eps delta +
    8 * Real.rpow (selfImprovementOrthogonalizationError params eps delta)
      (1 / (2 : Error))

/-- The quantitative error from `thm:self-improvement`. -/
noncomputable def selfImprovementError (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error) : Error :=
  MainInductionStep.selfImprovementInInductionError params eps delta 0

end MIPStarRE.LDT.SelfImprovement


