-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:14:54.95139+00:00
-- url     : https://prove2.me/theorems/c1415203-30fd-45a7-a0a2-4b6237d02926
-- title:
--   Definitions of Selected: Selected add-in-u Step 1/2 Cauchy--Schwarz bounds Selected-family contraction inputs and raw `√(2δ)` estimates for the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep12.Selected` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Selected add-in-u Step 1/2 Cauchy--Schwarz bounds. Selected-family contraction inputs and raw `√(2δ)` estimates for the first two add-in-u moves in the self-improvement chain.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `addInU_selected_filtered_tensor_sum_le_one`, `addInU_selected_step1_C_contraction`, `addInU_selected_step2_C_contraction`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep12.Selected` (`MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 52 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep12/Selected.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Field.Rat
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
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
import Mathlib.Algebra.Polynomial.Roots
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
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
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
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.NNRat.Defs
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
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Init
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_one
import Theorems.Thm_MIPStarRE_LDT_opTensor_le_leftTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_left_univ
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_right_univ
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_rightTensor_mul_rightTensor
import Theorems.Thm_MIPStarRE_LDT_rightTensor_one
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

set_option backward.isDefEq.respectTransparency false

/-!
# Selected add-in-u Step 1/2 Cauchy--Schwarz bounds

Selected-family contraction inputs and raw `√(2δ)` estimates for the first
two add-in-u moves in the self-improvement chain.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The selected fiber tensor mass is a contraction.

For fixed points `u, v` and a value `a`, the selected sum over pairs
`(o,h) ∈ S_u` with `h(v)=a` is bounded by the full product
`M^u_{\mathrm{tot}} ⊗ T_{\mathrm{tot}}`, hence by the identity. -/
lemma addInU_selected_filtered_tensor_sum_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u v : Point params)
    (a : Fq params) :
    ∑ ah ∈ (addInUSelectionPairs params S u).filter (fun ah => ah.2 v = a),
        opTensor ((M u).outcome ah.1) (T.outcome ah.2) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  calc
    ∑ ah ∈ (addInUSelectionPairs params S u).filter (fun ah => ah.2 v = a),
        opTensor ((M u).outcome ah.1) (T.outcome ah.2)
        ≤ ∑ ah : Outcome × Polynomial params,
            opTensor ((M u).outcome ah.1) (T.outcome ah.2) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro ah hah
              exact Finset.mem_univ ah)
            (by
              intro ah _ _
              exact opTensor_nonneg ((M u).outcome_pos ah.1) (T.outcome_pos ah.2))
    _ = opTensor (M u).total T.total := by
          change (∑ oh ∈ (Finset.univ : Finset Outcome).product
                (Finset.univ : Finset (Polynomial params)),
              opTensor ((M u).outcome oh.1) (T.outcome oh.2)) =
            opTensor (M u).total T.total
          have hprod :
              (∑ oh ∈ (Finset.univ : Finset Outcome).product
                  (Finset.univ : Finset (Polynomial params)),
                opTensor ((M u).outcome oh.1) (T.outcome oh.2)) =
                ∑ o ∈ (Finset.univ : Finset Outcome),
                  ∑ h ∈ (Finset.univ : Finset (Polynomial params)),
                    opTensor ((M u).outcome o) (T.outcome h) := by
            simpa using
              (Finset.sum_product
                (s := (Finset.univ : Finset Outcome))
                (t := (Finset.univ : Finset (Polynomial params)))
                (f := fun oh : Outcome × Polynomial params =>
                  opTensor ((M u).outcome oh.1) (T.outcome oh.2)))
          rw [hprod]
          calc
            ∑ o : Outcome, ∑ h : Polynomial params,
                opTensor ((M u).outcome o) (T.outcome h)
                = ∑ o : Outcome, opTensor ((M u).outcome o) T.total := by
                  refine Finset.sum_congr rfl ?_
                  intro o _
                  rw [← T.sum_eq_total, opTensor_sum_right_univ]
            _ = opTensor (M u).total T.total := by
                  rw [← (M u).sum_eq_total, opTensor_sum_left_univ]
    _ ≤ leftTensor (ι₂ := ι) (M u).total := by
          exact opTensor_le_leftTensor (SubMeas.total_nonneg (M u)) T.total_le_one
    _ ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact leftTensor_le_one (ι₂ := ι) (M u).total_le_one

/-- Cauchy--Schwarz contraction side condition for selected Step 1.

For a fixed `(u, v)`, the selected fiber sum
`K_a = ∑_{(o,h) ∈ S_u, h(v)=a} M^u_o ⊗ T_h` is a contraction.  Sandwiching
by the right-register point projector `A^v_a` and summing over `a` is therefore
bounded by the identity. -/
lemma addInU_selected_step1_C_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
      opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
  let Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    rightTensor (ι₁ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hsum_eq : ∀ a : Fq params,
      (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
          (fun ah => ah.2 uv.2 = a),
        opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)) =
        K a * Pa a := by
    intro a
    rw [← Finset.sum_mul]
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hM_herm : ∀ o : Outcome, ((M uv.1).outcome o)ᴴ = (M uv.1).outcome o :=
      fun o =>
        (Matrix.nonneg_iff_posSemidef.mp ((M uv.1).outcome_pos o)).isHermitian.eq
    have hT_herm : ∀ h : Polynomial params, (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hM_herm, hT_herm]
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, rightTensor_conjTranspose, hOutcome_herm]
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_mul_rightTensor, hproj]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro ah _
    exact opTensor_nonneg ((M uv.1).outcome_pos ah.1) (T.outcome_pos ah.2)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_selected_filtered_tensor_sum_le_one params M T S uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  have hterm_le : ∀ a : Fq params, (K a * Pa a)ᴴ * (K a * Pa a) ≤ Pa a := by
    intro a
    have hexpand : (K a * Pa a)ᴴ * (K a * Pa a) = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := IsSelfAdjoint.conjugate_le_conjugate (hK_sq_le_one a) (hPa_herm a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [rightTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, rightTensor_one]
  calc
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))
        = ∑ a : Fq params, (K a * Pa a)ᴴ * (K a * Pa a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

/-- Cauchy--Schwarz contraction side condition for selected Step 2.

This is the left-register analogue of `addInU_selected_step1_C_contraction`:
for each fixed `(u,v)`, the operators
`C_a = A^v_a \otimes I · K_a`, with `K_a` the selected fiber tensor mass,
have `∑_a C_a C_aᴴ ≤ I`. -/
lemma addInU_selected_step2_C_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2))ᴴ ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
      opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
  let Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    leftTensor (ι₂ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hsum_eq : ∀ a : Fq params,
      (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
          (fun ah => ah.2 uv.2 = a),
        leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) =
        Pa a * K a := by
    intro a
    rw [← Finset.mul_sum]
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hM_herm : ∀ o : Outcome, ((M uv.1).outcome o)ᴴ = (M uv.1).outcome o :=
      fun o =>
        (Matrix.nonneg_iff_posSemidef.mp ((M uv.1).outcome_pos o)).isHermitian.eq
    have hT_herm : ∀ h : Polynomial params, (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hM_herm, hT_herm]
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, leftTensor_conjTranspose, hOutcome_herm]
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_mul_leftTensor, hproj]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro ah _
    exact opTensor_nonneg ((M uv.1).outcome_pos ah.1) (T.outcome_pos ah.2)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_selected_filtered_tensor_sum_le_one params M T S uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  have hterm_le : ∀ a : Fq params, (Pa a * K a) * (Pa a * K a)ᴴ ≤ Pa a := by
    intro a
    have hexpand : (Pa a * K a) * (Pa a * K a)ᴴ = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := IsSelfAdjoint.conjugate_le_conjugate (hK_sq_le_one a) (hPa_herm a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [leftTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, leftTensor_one]
  calc
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2))ᴴ
        = ∑ a : Fq params, (Pa a * K a) * (Pa a * K a)ᴴ := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

end MIPStarRE.LDT.SelfImprovement


