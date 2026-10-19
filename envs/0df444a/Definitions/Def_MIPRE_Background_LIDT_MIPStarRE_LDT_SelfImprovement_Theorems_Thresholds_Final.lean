-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:04:09.045246+00:00
-- url     : https://prove2.me/theorems/c10687c6-29df-4627-8933-0f0698d164ec
-- title:
--   Definitions of Final: Section 9 — final-stage numerical threshold absorptions This module contains the final-stage arithmetic comparisons…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 9 — final-stage numerical threshold absorptions. This module contains the final-stage arithmetic comparisons which absorb the natural projective-output error terms into the literal `selfImprovementError` threshold. The estimates formalize the exponent-monotonicity bookkeeping in `references/ldt-paper/self_improvement.tex`, lines 803--810, and are used by the final-field construction theorems in the self-improvement theorem. The helper-stage estimates, including the square-root bound on the global-variance error, are in `Thresholds.Helper`.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (1): `MIPStarRE.LDT.SelfImprovement.finalStagePowerSum` (The three-term power sum used in the final-stage self-improvement threshold bookkeeping.).
--
--   **Embedded lemmas** (12): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `finalStagePowerSum_le_of_exponent_ge`, `selfImprovementDataProcessingError_eq`, `selfImprovementHelperError_eq_finalStagePowerSum`, `selfImprovementOrthogonalizationError_eq`, `sqrt_finalStagePowerSum_le`, `final_fields_projective_residual_error_le_131_times_finalStagePowerSum`, `selfImprovementDataProcessingError_le_nine_sixty_m_powerSum_sixteenth`, `selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth`, `sqrt_rpow_eq_rpow_half`, `sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Final` (`MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 39 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Thresholds/Final.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Tactic.Linarith.Preprocessing
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
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_d_q_ratio_le_one_of_d_le_q
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_d_q_ratio_nonneg
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_selfImprovementHelperError_nonneg
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_sqrt_100m_le_10m
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_sqrt_10m_le_4m
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_sqrt_400m_le_20m
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_sqrt_960m_le_31m
import Theorems.Thm_MIPStarRE_LDT_sqrt_add3_le_add3_sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Section 9 — final-stage numerical threshold absorptions

This module contains the final-stage arithmetic comparisons which absorb the natural
projective-output error terms into the literal `selfImprovementError` threshold.
The estimates formalize the exponent-monotonicity bookkeeping in
`references/ldt-paper/self_improvement.tex`, lines 803--810, and are used by the
final-field construction theorems in the self-improvement theorem.

The helper-stage estimates, including the square-root bound on the global-variance
error, are in `Thresholds.Helper`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective

/-! ## Final-stage threshold: `30 ζ̂ ≤ ζ`

For `ε, δ, d/q ∈ [0, 1]`, the helper-stage error is dominated by
`selfImprovementError / 30`. This is the exponent-monotonicity step in the
paper's chained absorption (`self_improvement.tex`, lines 803--810): for
unit-interval `x` and `0 ≤ z ≤ y`, `x^y ≤ x^z`. -/

/-- The three-term power sum used in the final-stage self-improvement threshold
bookkeeping.

For exponent `p`, this is the Lean counterpart of
`ε^p + δ^p + (d/q)^p`. Keeping this expression named makes the nested
absorptions in `self_improvement.tex`, lines 772--810, insensitive to future
constant adjustments. -/
noncomputable def finalStagePowerSum (params : Parameters)
    (eps delta p : Error) : Error :=
  Real.rpow eps p + Real.rpow delta p +
    Real.rpow ((params.d : Error) / (params.q : Error)) p

/-- Exponent monotonicity for the final-stage power sum on the unit interval.

If `ε`, `δ`, and `d/q` all lie in `[0, 1]`, then increasing the exponent
decreases each term of the power sum. This is the formal arithmetic step behind
the final threshold comparison in `self_improvement.tex`, lines 803--810. -/
theorem finalStagePowerSum_le_of_exponent_ge
    (params : Parameters) (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1)
    {pLarge pSmall : Error} (hpSmall_nonneg : 0 ≤ pSmall)
    (hpSmall_le_pLarge : pSmall ≤ pLarge) :
    finalStagePowerSum params eps delta pLarge ≤
      finalStagePowerSum params eps delta pSmall := by
  unfold finalStagePowerSum
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact Real.rpow_le_rpow_of_exponent_ge' heps heps_le_one hpSmall_nonneg
      hpSmall_le_pLarge
  · exact Real.rpow_le_rpow_of_exponent_ge' hdelta hdelta_le_one hpSmall_nonneg
      hpSmall_le_pLarge
  · exact Real.rpow_le_rpow_of_exponent_ge' hdq_nonneg hdq_le_one hpSmall_nonneg
      hpSmall_le_pLarge

theorem sqrt_rpow_eq_rpow_half {x p : Error} (hx : 0 ≤ x) :
    Real.sqrt (Real.rpow x p) = Real.rpow x (p / 2) := by
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (Real.rpow x p) (1 / (2 : Error)) = Real.rpow x (p * (1 / 2)) := by
      exact (Real.rpow_mul hx p (1 / (2 : Error))).symm
    _ = Real.rpow x (p / 2) := by ring_nf

/-- The square root of a final-stage power sum is bounded by the power sum with
half the exponent.

The proof is the elementary estimate
`sqrt (x + y + z) ≤ sqrt x + sqrt y + sqrt z`, applied to the three powers
`ε^p`, `δ^p`, and `(d/q)^p`. -/
theorem sqrt_finalStagePowerSum_le
    (params : Parameters) (eps delta p : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (finalStagePowerSum params eps delta p) ≤
      finalStagePowerSum params eps delta (p / 2) := by
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  unfold finalStagePowerSum
  calc
    Real.sqrt (Real.rpow eps p + Real.rpow delta p +
        Real.rpow ((params.d : Error) / (params.q : Error)) p)
        ≤ Real.sqrt (Real.rpow eps p) + Real.sqrt (Real.rpow delta p) +
          Real.sqrt (Real.rpow ((params.d : Error) / (params.q : Error)) p) :=
      sqrt_add3_le_add3_sqrt (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdelta _)
        (Real.rpow_nonneg hdq_nonneg _)
    _ = Real.rpow eps (p / 2) + Real.rpow delta (p / 2) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (p / 2) := by
      rw [sqrt_rpow_eq_rpow_half heps, sqrt_rpow_eq_rpow_half hdelta,
        sqrt_rpow_eq_rpow_half hdq_nonneg]

/-- The helper-stage threshold as the final-stage power sum with exponent
`1/2`.

This is definitionally equal to `selfImprovementHelperError`; the named lemma is
used to avoid unfolding the error definition inside later absorptions. -/
theorem selfImprovementHelperError_eq_finalStagePowerSum
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementHelperError params eps delta =
      100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (2 : Error)) := by
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

theorem sqrt_selfImprovementHelperError_le_ten_m_powerSum_quarter
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (selfImprovementHelperError params eps delta) ≤
      10 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (4 : Error)) := by
  have h100m_nn : (0 : Error) ≤ 100 * (params.m : Error) := by positivity
  have hsqrt100m := sqrt_100m_le_10m params
  have hsqrt_sum :=
    sqrt_finalStagePowerSum_le params eps delta (1 / (2 : Error)) heps hdelta
  have h10m_nn : (0 : Error) ≤ 10 * (params.m : Error) := by positivity
  rw [selfImprovementHelperError_eq_finalStagePowerSum]
  calc
    Real.sqrt (100 * (params.m : Error) *
        finalStagePowerSum params eps delta (1 / (2 : Error)))
        = Real.sqrt (100 * (params.m : Error)) *
          Real.sqrt (finalStagePowerSum params eps delta (1 / (2 : Error))) := by
          rw [Real.sqrt_mul h100m_nn]
    _ ≤ (10 * (params.m : Error)) *
          finalStagePowerSum params eps delta (1 / (4 : Error)) := by
          calc
            Real.sqrt (100 * (params.m : Error)) *
                Real.sqrt (finalStagePowerSum params eps delta (1 / (2 : Error)))
                ≤ (10 * (params.m : Error)) *
                    Real.sqrt (finalStagePowerSum params eps delta (1 / (2 : Error))) :=
                  mul_le_mul_of_nonneg_right hsqrt100m (Real.sqrt_nonneg _)
            _ ≤ (10 * (params.m : Error)) *
                  finalStagePowerSum params eps delta (1 / (4 : Error)) := by
                  rw [show (1 / (4 : Error)) = (1 / (2 : Error)) / 2 by norm_num]
                  exact mul_le_mul_of_nonneg_left hsqrt_sum h10m_nn

/-- The orthogonalization threshold written as an iterated square root of the
helper threshold.

The paper writes the corresponding quantity as
`100 * \widehat{\zeta}^{1/4}`. This lemma gives the equivalent square-root
form used by the estimates which follow orthonormalization. -/
theorem selfImprovementOrthogonalizationError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementOrthogonalizationError params eps delta =
      100 * Real.sqrt (Real.sqrt (selfImprovementHelperError params eps delta)) := by
  unfold selfImprovementOrthogonalizationError orthonormalizationError
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  congr 1
  calc
    Real.rpow (selfImprovementHelperError params eps delta) (1 / (4 : Error)) =
        Real.rpow (selfImprovementHelperError params eps delta)
          ((1 / (2 : Error)) * (1 / 2)) := by
      congr 1
      ring
    _ = Real.rpow
          (Real.rpow (selfImprovementHelperError params eps delta) (1 / (2 : Error)))
          (1 / (2 : Error)) := by
      exact Real.rpow_mul (selfImprovementHelperError_nonneg params eps delta)
        (1 / (2 : Error)) (1 / (2 : Error))

theorem selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    selfImprovementOrthogonalizationError params eps delta ≤
      400 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (8 : Error)) := by
  have hsqrt_helper :=
    sqrt_selfImprovementHelperError_le_ten_m_powerSum_quarter params eps delta heps hdelta
  have hsqrt_mS :
      Real.sqrt (10 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (4 : Error))) ≤
        4 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (8 : Error)) := by
    have h10m_nn : (0 : Error) ≤ 10 * (params.m : Error) := by positivity
    have hsqrt10m := sqrt_10m_le_4m params
    have hsqrt_sum :=
      sqrt_finalStagePowerSum_le params eps delta (1 / (4 : Error)) heps hdelta
    have h4m_nn : (0 : Error) ≤ 4 * (params.m : Error) := by positivity
    calc
      Real.sqrt (10 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (4 : Error)))
          = Real.sqrt (10 * (params.m : Error)) *
            Real.sqrt (finalStagePowerSum params eps delta (1 / (4 : Error))) := by
            rw [Real.sqrt_mul h10m_nn]
      _ ≤ (4 * (params.m : Error)) *
            finalStagePowerSum params eps delta (1 / (8 : Error)) := by
            calc
              Real.sqrt (10 * (params.m : Error)) *
                  Real.sqrt (finalStagePowerSum params eps delta (1 / (4 : Error)))
                  ≤ (4 * (params.m : Error)) *
                      Real.sqrt (finalStagePowerSum params eps delta (1 / (4 : Error))) :=
                    mul_le_mul_of_nonneg_right hsqrt10m (Real.sqrt_nonneg _)
              _ ≤ (4 * (params.m : Error)) *
                    finalStagePowerSum params eps delta (1 / (8 : Error)) := by
                    rw [show (1 / (8 : Error)) = (1 / (4 : Error)) / 2 by norm_num]
                    exact mul_le_mul_of_nonneg_left hsqrt_sum h4m_nn
  rw [selfImprovementOrthogonalizationError_eq]
  calc
    100 * Real.sqrt (Real.sqrt (selfImprovementHelperError params eps delta))
        ≤ 100 * Real.sqrt
            (10 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (4 : Error))) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsqrt_helper) (by norm_num)
    _ ≤ 100 * (4 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (8 : Error))) :=
        mul_le_mul_of_nonneg_left hsqrt_mS (by norm_num)
    _ = 400 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (8 : Error)) := by ring

theorem sqrt_selfImprovementOrthogonalizationError_le_twenty_m_powerSum_sixteenth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
      20 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (16 : Error)) := by
  have horth :=
    selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth
      params eps delta heps hdelta
  have h400m_nn : (0 : Error) ≤ 400 * (params.m : Error) := by positivity
  have hsqrt400m := sqrt_400m_le_20m params
  have hsqrt_sum :=
    sqrt_finalStagePowerSum_le params eps delta (1 / (8 : Error)) heps hdelta
  have h20m_nn : (0 : Error) ≤ 20 * (params.m : Error) := by positivity
  calc
    Real.sqrt (selfImprovementOrthogonalizationError params eps delta)
        ≤ Real.sqrt (400 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (8 : Error))) :=
          Real.sqrt_le_sqrt horth
    _ = Real.sqrt (400 * (params.m : Error)) *
          Real.sqrt (finalStagePowerSum params eps delta (1 / (8 : Error))) := by
          rw [Real.sqrt_mul h400m_nn]
    _ ≤ (20 * (params.m : Error)) *
          finalStagePowerSum params eps delta (1 / (16 : Error)) := by
          calc
            Real.sqrt (400 * (params.m : Error)) *
                Real.sqrt (finalStagePowerSum params eps delta (1 / (8 : Error)))
                ≤ (20 * (params.m : Error)) *
                    Real.sqrt (finalStagePowerSum params eps delta (1 / (8 : Error))) :=
                  mul_le_mul_of_nonneg_right hsqrt400m (Real.sqrt_nonneg _)
            _ ≤ (20 * (params.m : Error)) *
                  finalStagePowerSum params eps delta (1 / (16 : Error)) := by
                  rw [show (1 / (16 : Error)) = (1 / (8 : Error)) / 2 by norm_num]
                  exact mul_le_mul_of_nonneg_left hsqrt_sum h20m_nn

/-- The data-processing threshold written with an ordinary square root.

This is the displayed expression used after projecting the helper output:
`8\widehat{\zeta} + 8\sqrt{\widehat{\zeta}_{\mathrm{ortho}}}`. -/
theorem selfImprovementDataProcessingError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementDataProcessingError params eps delta =
      8 * selfImprovementHelperError params eps delta +
        8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
  unfold selfImprovementDataProcessingError
  simp [Real.sqrt_eq_rpow, Real.rpow_eq_pow]

theorem selfImprovementDataProcessingError_le_nine_sixty_m_powerSum_sixteenth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    selfImprovementDataProcessingError params eps delta ≤
      960 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (16 : Error)) := by
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (16 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (16 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hsqrt_orth :=
    sqrt_selfImprovementOrthogonalizationError_le_twenty_m_powerSum_sixteenth
      params eps delta heps hdelta
  rw [selfImprovementDataProcessingError_eq]
  calc
    8 * selfImprovementHelperError params eps delta +
        8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)
        ≤ 8 * (100 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (16 : Error))) +
          8 * (20 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (16 : Error))) := by
          gcongr
    _ = 960 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (16 : Error)) := by ring

theorem sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
      31 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
  have hdata :=
    selfImprovementDataProcessingError_le_nine_sixty_m_powerSum_sixteenth
      params eps delta heps heps_le_one hdelta hdelta_le_one hdq_le_one
  have h960m_nn : (0 : Error) ≤ 960 * (params.m : Error) := by positivity
  have hsqrt960m := sqrt_960m_le_31m params
  have hsqrt_sum :=
    sqrt_finalStagePowerSum_le params eps delta (1 / (16 : Error)) heps hdelta
  have h31m_nn : (0 : Error) ≤ 31 * (params.m : Error) := by positivity
  calc
    Real.sqrt (selfImprovementDataProcessingError params eps delta)
        ≤ Real.sqrt (960 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (16 : Error))) :=
          Real.sqrt_le_sqrt hdata
    _ = Real.sqrt (960 * (params.m : Error)) *
          Real.sqrt (finalStagePowerSum params eps delta (1 / (16 : Error))) := by
          rw [Real.sqrt_mul h960m_nn]
    _ ≤ (31 * (params.m : Error)) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
          calc
            Real.sqrt (960 * (params.m : Error)) *
                Real.sqrt (finalStagePowerSum params eps delta (1 / (16 : Error)))
                ≤ (31 * (params.m : Error)) *
                    Real.sqrt (finalStagePowerSum params eps delta (1 / (16 : Error))) :=
                  mul_le_mul_of_nonneg_right hsqrt960m (Real.sqrt_nonneg _)
            _ ≤ (31 * (params.m : Error)) *
                  finalStagePowerSum params eps delta (1 / (32 : Error)) := by
                  rw [show (1 / (32 : Error)) = (1 / (16 : Error)) / 2 by norm_num]
                  exact mul_le_mul_of_nonneg_left hsqrt_sum h31m_nn

theorem final_fields_projective_residual_error_le_131_times_finalStagePowerSum
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
      131 * (params.m : Error) *
        finalStagePowerSum params eps delta (1 / (32 : Error)) := by
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hdata_sqrt :
      Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        31 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    exact sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond
      params eps delta heps heps_le_one hdelta hdelta_le_one hdq_le_one
  nlinarith

end MIPStarRE.LDT.SelfImprovement


