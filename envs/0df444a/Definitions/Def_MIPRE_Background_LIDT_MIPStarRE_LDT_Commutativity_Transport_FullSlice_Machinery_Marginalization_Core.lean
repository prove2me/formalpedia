-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:19:15.501256+00:00
-- url     : https://prove2.me/theorems/5f721b34-702f-4307-84ed-d92594b47cb0
-- title:
--   Definitions of Core: Full-slice tensor marginalization core Collision residuals, postprocessing expansions, and tensor marginalization core…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Marginalization.Core` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Full-slice tensor marginalization core. Collision residuals, postprocessing expansions, and tensor marginalization core bounds for the `BABA` and `ABAB` full-slice tensor averages. Ex-private definitions are tensor-form machinery per architecture decision #713; downstream code should use the scalar public API exposed by the full-slice transport theorems.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (2): `MIPStarRE.LDT.Commutativity.fullSliceABAByCollisionFactored` (Factored collision residual for the y-marginalization tensor step.); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Marginalization.Core.0.MIPStarRE.LDT.Commutativity.fullSliceBABAxCollisionFactored` (Factored collision residual for the x-marginalization tensor step.).
--
--   **Embedded lemmas** (9): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `avg_postprocess_sandwichTensor_eq_diag_add_collision`, `diagonal_pair_sum`, `ev_sandwichTensor_indicator_expand`, `fullSliceABAByCollisionFactored_le_mdq`, `fullSliceBABAtensor_xEvaluation_eq_full_add_collision`, `fullSliceBABAxCollisionFactored_le_mdq`, `fullSliceBABAxCollisionFactored_nonneg`, `postprocess_collision_coeff_sum`, `postprocess_sandwichTensor_expand`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Marginalization.Core` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 52 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Transport/FullSlice/Machinery/Marginalization/Core.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Tactic.NormNum.Basic
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceCommutation_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_EvaluationSpecialization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_polynomialCollision_sandwichTensor_le_mdq
import Theorems.Thm_MIPStarRE_LDT_avgOver_add
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_mul_const
import Theorems.Thm_MIPStarRE_LDT_avgOver_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_sum
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_const
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_ev_zero
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_sandwichTensorSummand_nonneg

set_option backward.isDefEq.respectTransparency false

/-!
# Full-slice tensor marginalization core

Collision residuals, postprocessing expansions, and tensor marginalization
core bounds for the `BABA` and `ABAB` full-slice tensor averages.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by the
full-slice transport theorems.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Factored collision residual for the x-marginalization tensor step.

After expanding the first evaluated family in paper `eq:gcom4-diff`, the remaining
error is this nonnegative sum over pairs of distinct polynomial outcomes whose
values collide at the sampled point `u`. -/
noncomputable def fullSliceBABAxCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (xy : FullSliceQuestion params) : Error :=
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  ∑ gg : Polynomial params × Polynomial params, ∑ h : Polynomial params,
    (if gg.1 = gg.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
      ev strategy.state
        (leftTensor (ι₂ := ι) (B.outcome h * A.outcome gg.1 * B.outcome h) *
          rightTensor (ι₁ := ι) (A.outcome gg.2))

/-- The Schwartz-Zippel/PSD bound for the x-marginalization collision residual.

This is the proved hard estimate used by the staged x-marginalization tensor
lemma below.  The algebraic expansion identifies the x-evaluated tensor-average
difference with this residual averaged over `x,y`. -/
lemma fullSliceBABAxCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (xy : FullSliceQuestion params) :
    fullSliceBABAxCollisionFactored params strategy family xy ≤
      (params.m * params.d : Error) / params.q := by
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  simpa [fullSliceBABAxCollisionFactored, A, B] using
    MIPStarRE.LDT.Preliminaries.polynomialCollision_sandwichTensor_le_mdq
      params strategy.state hnorm B A A

/-- Factored collision residual for the y-marginalization tensor step.

Here the outer sandwich is the already x-evaluated family
`G^x_[g(u)=a]`, while the colliding polynomial pair is on the `y` side. -/
noncomputable def fullSliceABAByCollisionFactored
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (u : Point params) (xy : FullSliceQuestion params) : Error :=
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  ∑ hh : Polynomial params × Polynomial params, ∑ a : Fq params,
    (if hh.1 = hh.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun v => if hh.1 v = hh.2 v then (1 : Error) else 0)) *
      ev strategy.state
        (leftTensor (ι₂ := ι) (A.outcome a * B.outcome hh.1 * A.outcome a) *
          rightTensor (ι₁ := ι) (B.outcome hh.2))

/-- The Schwartz-Zippel/PSD bound for the y-marginalization collision residual.

This is the proved hard estimate used by the staged y-marginalization tensor
lemma below; the postprocessing expansion identifies the data-ordered evaluated
tensor-average difference with `fullSliceABAByCollisionFactored`. -/
lemma fullSliceABAByCollisionFactored_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (hnorm : strategy.state.IsNormalized)
    (u : Point params) (xy : FullSliceQuestion params) :
    fullSliceABAByCollisionFactored params strategy family u xy ≤
      (params.m * params.d : Error) / params.q := by
  let A : SubMeas (Fq params) ι :=
    evaluateAt params u ((family.meas xy.1).toSubMeas)
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  simpa [fullSliceABAByCollisionFactored, A, B] using
    MIPStarRE.LDT.Preliminaries.polynomialCollision_sandwichTensor_le_mdq
      params strategy.state hnorm A B B

/-- Expand the expectation of a tensor sandwich whose inner/right family is an
indicator-restricted finite sum. -/
lemma ev_sandwichTensor_indicator_expand
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (B : MIPStarRE.Quantum.Op ι) (A : α → MIPStarRE.Quantum.Op ι)
    (p : α → Prop) [DecidablePred p] :
    ev ψ
      (leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) *
        rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0)) =
      ∑ aa : α × α,
        (if p aa.1 then if p aa.2 then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A aa.1 * B) *
              rightTensor (ι₁ := ι) (A aa.2)) := by
  classical
  let S : MIPStarRE.Quantum.Op ι := ∑ a : α, if p a then A a else 0
  have hleft :
      leftTensor (ι₂ := ι) (B * S * B) =
        ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
    calc
      leftTensor (ι₂ := ι) (B * S * B)
        = leftTensor (ι₂ := ι) (∑ a : α, if p a then B * A a * B else 0) := by
            congr 1
            simp [S, Matrix.mul_sum, Matrix.sum_mul, mul_assoc]
      _ = ∑ a : α, leftTensor (ι₂ := ι) (if p a then B * A a * B else 0) := by
            exact (leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun a : α => if p a then B * A a * B else 0)).symm
      _ = ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp, leftTensor]
  have hright :
      rightTensor (ι₁ := ι) S =
        ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
    calc
      rightTensor (ι₁ := ι) S
        = ∑ a : α, rightTensor (ι₁ := ι) (if p a then A a else 0) := by
            exact (rightTensor_finset_sum (ι₁ := ι) Finset.univ
              (fun a : α => if p a then A a else 0)).symm
      _ = ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp, rightTensor]
  calc
    ev ψ
      (leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) *
        rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0))
      = ev ψ ((∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0) *
          (∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0)) := by
          have hleft' :
              leftTensor (ι₂ := ι) (B * (∑ a : α, if p a then A a else 0) * B) =
                ∑ a : α, if p a then leftTensor (ι₂ := ι) (B * A a * B) else 0 := by
            simpa [S] using hleft
          have hright' :
              rightTensor (ι₁ := ι) (∑ a : α, if p a then A a else 0) =
                ∑ a : α, if p a then rightTensor (ι₁ := ι) (A a) else 0 := by
            simpa [S] using hright
          rw [hleft', hright']
    _ = ev ψ (∑ a₁ : α, ∑ a₂ : α,
          (if p a₁ then leftTensor (ι₂ := ι) (B * A a₁ * B) else 0) *
            (if p a₂ then rightTensor (ι₁ := ι) (A a₂) else 0)) := by
          congr 1
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          rw [Finset.mul_sum]
    _ = ∑ a₁ : α, ∑ a₂ : α,
          ev ψ ((if p a₁ then leftTensor (ι₂ := ι) (B * A a₁ * B) else 0) *
            (if p a₂ then rightTensor (ι₁ := ι) (A a₂) else 0)) := by
          rw [ev_sum]
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          rw [ev_sum]
    _ = ∑ a₁ : α, ∑ a₂ : α,
          (if p a₁ then if p a₂ then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A a₁ * B) *
              rightTensor (ι₁ := ι) (A a₂)) := by
          refine Finset.sum_congr rfl ?_
          intro a₁ _
          refine Finset.sum_congr rfl ?_
          intro a₂ _
          by_cases h₁ : p a₁ <;> by_cases h₂ : p a₂ <;> simp [h₁, h₂, ev_zero]
    _ = ∑ aa : α × α,
        (if p aa.1 then if p aa.2 then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B * A aa.1 * B) *
              rightTensor (ι₁ := ι) (A aa.2)) := by
          exact (Fintype.sum_prod_type' (f := fun a₁ : α => fun a₂ : α =>
            (if p a₁ then if p a₂ then (1 : Error) else 0 else 0) *
              ev ψ
                (leftTensor (ι₂ := ι) (B * A a₁ * B) *
                  rightTensor (ι₁ := ι) (A a₂)))).symm

/-- Sum over the postprocessed outcome label of two matching indicators. -/
lemma postprocess_collision_coeff_sum
    {α κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : α → κ) (a₁ a₂ : α) :
    (∑ k : κ,
        if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) =
      (if f a₁ = f a₂ then (1 : Error) else 0) := by
  classical
  by_cases h : f a₁ = f a₂
  · calc
      (∑ k : κ,
          if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0)
        = ∑ k : κ, if f a₁ = k then (1 : Error) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro k _
            by_cases hk : f a₁ = k
            · have hk₂ : f a₂ = k := h.symm.trans hk
              simp [hk, hk₂]
            · simp [hk]
      _ = (1 : Error) := by
            rw [Fintype.sum_ite_eq]
      _ = if f a₁ = f a₂ then (1 : Error) else 0 := by simp [h]
  · have hzero :
        ∀ k : κ,
          (if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) = 0 := by
      intro k
      by_cases h₁ : f a₁ = k
      · by_cases h₂ : f a₂ = k
        · exact (h (h₁.trans h₂.symm)).elim
        · simp [h₁, h₂]
      · simp [h₁]
    calc
      (∑ k : κ,
          if f a₁ = k then if f a₂ = k then (1 : Error) else 0 else 0) = 0 := by
            exact Finset.sum_eq_zero (fun k _ => hzero k)
      _ = if f a₁ = f a₂ then (1 : Error) else 0 := by simp [h]

/-- Expand a postprocessed tensor sandwich into the pair-collision expression for
one fixed sample. -/
lemma postprocess_sandwichTensor_expand
    {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι) (B : SubMeas β ι) (f : α → κ) :
    (∑ k : κ, ∑ b : β,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k))) =
    (∑ aa : α × α, ∑ b : β,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2))) := by
  classical
  calc
    (∑ k : κ, ∑ b : β,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k)))
      = ∑ b : β, ∑ k : κ,
      ev ψ
        (leftTensor (ι₂ := ι)
            (B.outcome b * (postprocess A f).outcome k * B.outcome b) *
          rightTensor (ι₁ := ι) ((postprocess A f).outcome k)) := by
          rw [Finset.sum_comm]
    _ = ∑ b : β, ∑ k : κ, ∑ aa : α × α,
        (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro k _
          have hpost :
              (postprocess A f).outcome k =
                ∑ a : α, if f a = k then A.outcome a else 0 := by
            unfold postprocess
            dsimp
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases ha : f a = k <;> simp [ha]
          rw [hpost]
          simpa [mul_assoc] using ev_sandwichTensor_indicator_expand (ψ := ψ) (B := B.outcome b)
            (A := A.outcome) (p := fun a : α => f a = k)
    _ = ∑ b : β, ∑ aa : α × α, ∑ k : κ,
        (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_comm]
    _ = ∑ b : β, ∑ aa : α × α,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          refine Finset.sum_congr rfl ?_
          intro aa _
          calc
            (∑ k : κ,
                (if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
                  ev ψ
                    (leftTensor (ι₂ := ι)
                        (B.outcome b * A.outcome aa.1 * B.outcome b) *
                      rightTensor (ι₁ := ι) (A.outcome aa.2)))
              = (∑ k : κ,
                  if f aa.1 = k then if f aa.2 = k then (1 : Error) else 0 else 0) *
                    ev ψ
                      (leftTensor (ι₂ := ι)
                          (B.outcome b * A.outcome aa.1 * B.outcome b) *
                        rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
                  rw [Finset.sum_mul]
            _ = (if f aa.1 = f aa.2 then (1 : Error) else 0) *
                    ev ψ
                      (leftTensor (ι₂ := ι)
                          (B.outcome b * A.outcome aa.1 * B.outcome b) *
                        rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
                  rw [postprocess_collision_coeff_sum f aa.1 aa.2]
    _ = ∑ aa : α × α, ∑ b : β,
      (if f aa.1 = f aa.2 then (1 : Error) else 0) *
        ev ψ
          (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
            rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          rw [Finset.sum_comm]

/-- Summing a pair-indexed expression against the diagonal indicator leaves the
ordinary diagonal sum. -/
lemma diagonal_pair_sum
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (T : α × α → β → Error) :
    (∑ aa : α × α, ∑ b : β,
        (if aa.1 = aa.2 then (1 : Error) else 0) * T aa b) =
      ∑ a : α, ∑ b : β, T (a, a) b := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a₁ _
  calc
    (∑ a₂ : α, ∑ b : β,
        (if a₁ = a₂ then (1 : Error) else 0) * T (a₁, a₂) b)
      = ∑ a₂ : α, if a₁ = a₂ then (∑ b : β, T (a₁, a₂) b) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a₂ _
          by_cases h : a₁ = a₂ <;> simp [h]
    _ = ∑ b : β, T (a₁, a₁) b := by
          rw [Fintype.sum_ite_eq]

/-- Expand one postprocessed tensor sandwich and split the resulting pair sum into
its diagonal part and off-diagonal collision residual.

This is the common finite-sum identity behind both tensor marginalization steps.
The outcome family `A` is postprocessed by the sample-dependent map `eval s`; the
outer sandwich family `B` is not postprocessed. -/
lemma avg_postprocess_sandwichTensor_eq_diag_add_collision
    {α β σ κ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β]
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι) (B : SubMeas β ι) (eval : σ → α → κ) :
    avgOver (uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι)
                (B.outcome b * (postprocess A (eval s)).outcome k * B.outcome b) *
              rightTensor (ι₁ := ι) ((postprocess A (eval s)).outcome k))) =
      (∑ a : α, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            avgOver (uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0)) *
            ev ψ
              (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
                rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
  classical
  let 𝒟 : Distribution σ := uniformDistribution σ
  let T : α × α → β → Error := fun aa b =>
    ev ψ
      (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
        rightTensor (ι₁ := ι) (A.outcome aa.2))
  let c : α × α → Error := fun aa =>
    avgOver 𝒟 (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0)
  have hc_diag (a : α) : c (a, a) = 1 := by
    simp [c, 𝒟, avgOver_uniform_const]
  calc
    avgOver (uniformDistribution σ)
        (fun s => ∑ k : κ, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι)
                (B.outcome b * (postprocess A (eval s)).outcome k * B.outcome b) *
              rightTensor (ι₁ := ι) ((postprocess A (eval s)).outcome k)))
      = avgOver 𝒟 (fun s => ∑ aa : α × α, ∑ b : β,
          (if eval s aa.1 = eval s aa.2 then (1 : Error) else 0) * T aa b) := by
          apply avgOver_congr
          intro s
          simpa [T] using
            postprocess_sandwichTensor_expand (ψ := ψ) (A := A) (B := B)
              (f := eval s)
    _ = ∑ aa : α × α, ∑ b : β,
          avgOver 𝒟
            (fun s =>
              (if eval s aa.1 = eval s aa.2 then (1 : Error) else 0) * T aa b) := by
          rw [avgOver_sum]
          refine Finset.sum_congr rfl ?_
          intro aa _
          rw [avgOver_sum]
    _ = ∑ aa : α × α, ∑ b : β, c aa * T aa b := by
          refine Finset.sum_congr rfl ?_
          intro aa _
          refine Finset.sum_congr rfl ?_
          intro b _
          exact avgOver_mul_const 𝒟
            (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0) (T aa b)
    _ = (∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then (1 : Error) else 0) * T aa b) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else c aa) * T aa b := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro aa _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro b _
          by_cases h : aa.1 = aa.2
          · have hc : c aa = 1 := by
              rcases aa with ⟨a₁, a₂⟩
              dsimp at h ⊢
              subst a₂
              exact hc_diag a₁
            simp [h, hc]
          · simp [h]
    _ = (∑ a : α, ∑ b : β, T (a, a) b) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else c aa) * T aa b := by
          rw [diagonal_pair_sum]
    _ = (∑ a : α, ∑ b : β,
          ev ψ
            (leftTensor (ι₂ := ι) (B.outcome b * A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (A.outcome a))) +
        ∑ aa : α × α, ∑ b : β,
          (if aa.1 = aa.2 then 0 else
            avgOver (uniformDistribution σ)
              (fun s => if eval s aa.1 = eval s aa.2 then (1 : Error) else 0)) *
            ev ψ
              (leftTensor (ι₂ := ι) (B.outcome b * A.outcome aa.1 * B.outcome b) *
                rightTensor (ι₁ := ι) (A.outcome aa.2)) := by
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The x-collision residual is nonnegative term-by-term. -/
lemma fullSliceBABAxCollisionFactored_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (xy : FullSliceQuestion params) :
    0 ≤ fullSliceBABAxCollisionFactored params strategy family xy := by
  classical
  let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
  let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
  have hcoef_nonneg (gg : Polynomial params × Polynomial params) :
      0 ≤ (if gg.1 = gg.2 then 0 else
        avgOver (uniformDistribution (Point params))
          (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) := by
    by_cases hEq : gg.1 = gg.2
    · simp [hEq]
    · have hnonneg :
          0 ≤ avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0) := by
        exact avgOver_nonneg _ _ (by
          intro u
          by_cases hu : gg.1 u = gg.2 u <;> simp [hu])
      simpa [hEq] using hnonneg
  have hsum :
      0 ≤ ∑ gg : Polynomial params × Polynomial params, ∑ h : Polynomial params,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
          ev strategy.state
            (leftTensor (ι₂ := ι) (B.outcome h * A.outcome gg.1 * B.outcome h) *
              rightTensor (ι₁ := ι) (A.outcome gg.2)) := by
    refine Finset.sum_nonneg ?_
    intro gg _
    refine Finset.sum_nonneg ?_
    intro h _
    exact mul_nonneg (hcoef_nonneg gg)
      (sandwichTensorSummand_nonneg strategy.state B A A h gg.1 gg.2)
  simpa [fullSliceBABAxCollisionFactored, A, B] using hsum

/-- Exact x-side postprocessing identity: the x-evaluated `BAB ⊗ A` tensor
average is the full tensor average plus the x-collision residual. -/
lemma fullSliceBABAtensor_xEvaluation_eq_full_add_collision
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    xEvaluatedSliceBABAtensorAvg params strategy family =
      fullSliceBABAtensorAvg params strategy family +
        avgOver (uniformDistribution (FullSliceQuestion params))
          (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
  classical
  let 𝒟 : Distribution (FullSliceQuestion params) :=
    uniformDistribution (FullSliceQuestion params)
  let diag : FullSliceQuestion params → Error := fun xy =>
    ∑ g : Polynomial params, ∑ h : Polynomial params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
            ((family.meas xy.2).toSubMeas.outcome h *
              (family.meas xy.1).toSubMeas.outcome g *
              (family.meas xy.2).toSubMeas.outcome h) *
          rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g))
  have hpoint (xy : FullSliceQuestion params) :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let A : SubMeas (Fq params) ι :=
            evaluateAt params u ((family.meas xy.1).toSubMeas)
          let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
          ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                rightTensor (ι₁ := ι) (A.outcome a))) =
        diag xy + fullSliceBABAxCollisionFactored params strategy family xy := by
    let A : SubMeas (Polynomial params) ι := (family.meas xy.1).toSubMeas
    let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
    simpa [diag, fullSliceBABAxCollisionFactored, A, B, evaluateAt] using
      (avg_postprocess_sandwichTensor_eq_diag_add_collision
        (ψ := strategy.state) (A := A) (B := B)
        (eval := fun u : Point params => fun g : Polynomial params => g u))
  have hdiag : avgOver 𝒟 diag = fullSliceBABAtensorAvg params strategy family := by
    unfold fullSliceBABAtensorAvg
    apply avgOver_congr
    intro xy
    dsimp [diag]
    simpa using
      (Fintype.sum_prod_type' (f := fun g : Polynomial params => fun h : Polynomial params =>
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((family.meas xy.2).toSubMeas.outcome h *
                (family.meas xy.1).toSubMeas.outcome g *
                (family.meas xy.2).toSubMeas.outcome h) *
            rightTensor (ι₁ := ι)
              ((family.meas xy.1).toSubMeas.outcome g)))).symm
  unfold xEvaluatedSliceBABAtensorAvg
  calc
    avgOver 𝒟
        (fun xy =>
          avgOver (uniformDistribution (Point params))
            (fun u =>
              let A : SubMeas (Fq params) ι :=
                evaluateAt params u ((family.meas xy.1).toSubMeas)
              let B : SubMeas (Polynomial params) ι := (family.meas xy.2).toSubMeas
              ∑ a : Fq params, ∑ h : Polynomial params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) (B.outcome h * A.outcome a * B.outcome h) *
                    rightTensor (ι₁ := ι) (A.outcome a))))
      = avgOver 𝒟
          (fun xy => diag xy + fullSliceBABAxCollisionFactored params strategy family xy) := by
          exact avgOver_congr 𝒟 _ _ hpoint
    _ = avgOver 𝒟 diag +
          avgOver 𝒟 (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
          rw [avgOver_add]
    _ = fullSliceBABAtensorAvg params strategy family +
          avgOver (uniformDistribution (FullSliceQuestion params))
            (fun xy => fullSliceBABAxCollisionFactored params strategy family xy) := by
          rw [hdiag]

end MIPStarRE.LDT.Commutativity


