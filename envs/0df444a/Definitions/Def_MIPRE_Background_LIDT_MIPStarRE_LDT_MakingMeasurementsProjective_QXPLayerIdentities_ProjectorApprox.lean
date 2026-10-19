-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:37:58.883522+00:00
-- url     : https://prove2.me/theorems/c6684680-a387-4abd-9f42-a358c88e8f61
-- title:
--   Definitions of ProjectorApprox: Section 5 — P-Q approximation for QXP layers The final comparison estimates between the projective family `P` produced…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.ProjectorApprox` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — P-Q approximation for QXP layers. The final comparison estimates between the projective family `P` produced from `XHat` and the original projective `Q` layer.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `pa_hermitian`, `pa_idempotent`, `pa_mass_le_one`, `pa_nonneg`, `q_p_cross_close`, `xHat_cross_sum_eq_sqrt`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.ProjectorApprox` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/ProjectorApprox.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 42 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/ProjectorApprox.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/ProjectorApprox.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayerIdentities/ProjectorApprox.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
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
import Mathlib.Algebra.Module.Equiv.Defs
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
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
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
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
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
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.ULift
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
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
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NoncommRing
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_qAlmostProjective
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_qaRestated
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_squaredDifference
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_xExpressionToQExpression
import Theorems.Thm_MIPStarRE_LDT_Measurement_sum_eq
import Theorems.Thm_MIPStarRE_LDT_ProjMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_ev_abs_mul_le_sqrt
import Theorems.Thm_MIPStarRE_LDT_ev_adjoint_self_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_scale
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_ev_sum

set_option backward.isDefEq.respectTransparency false

/-!
# Section 5 — P-Q approximation for QXP layers

The final comparison estimates between the projective family `P` produced
from `XHat` and the original projective `Q` layer.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

lemma pa_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    0 ≤ Pa data a := by
  rcases pProjectivity data with ⟨P, hP⟩
  simpa [hP a] using P.outcome_pos a

lemma pa_hermitian {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (Pa data a)ᴴ = Pa data a :=
  (Matrix.nonneg_iff_posSemidef.mp (pa_nonneg data a)).isHermitian.eq

lemma pa_idempotent {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Pa data a * Pa data a = Pa data a := by
  rcases pProjectivity data with ⟨P, hP⟩
  simpa [hP a] using P.proj a

lemma pa_mass_le_one {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (ψ : QuantumState ι)
    (hψ : ψ.IsNormalized) :
    (∑ a : Outcome, ev ψ (Pa data a)) ≤ 1 := by
  rcases pProjectivity data with ⟨P, hP⟩
  calc
    (∑ a : Outcome, ev ψ (Pa data a))
        = ∑ a : Outcome, ev ψ (P.outcome a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hP a]
    _ = ev ψ (∑ a : Outcome, P.outcome a) := by
          exact (ev_sum ψ P.outcome).symm
    _ = ev ψ P.total := by rw [P.sum_eq_total]
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op ι) := ev_mono ψ _ _ P.total_le_one
    _ = 1 := ev_one_of_isNormalized ψ hψ

lemma xHat_cross_sum_eq_sqrt {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a) =
      CFC.sqrt (QTotal data.qLayer) := by
  have hterm : ∀ a : Outcome,
      (Xa data a)ᴴ * data.xHat * Pa data a =
        data.xᴴ * Ta data.qLayer a * data.xHat := by
    intro a
    have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
      simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
    calc
      (Xa data a)ᴴ * data.xHat * Pa data a
          = (data.xᴴ * Ta data.qLayer a) * data.xHat *
              (data.xHatᴴ * Ta data.qLayer a * data.xHat) := by
              simp [Xa, Pa, Matrix.conjTranspose_mul, hTa, Matrix.mul_assoc]
      _ = data.xᴴ * Ta data.qLayer a * (data.xHat * data.xHatᴴ) *
              Ta data.qLayer a * data.xHat := by
              simp [Matrix.mul_assoc]
      _ = data.xᴴ * Ta data.qLayer a * Ta data.qLayer a * data.xHat := by
              simp [data.xHat_coisometry, Matrix.mul_assoc]
      _ = data.xᴴ * Ta data.qLayer a * data.xHat := by
              simp [Ta, data.qLayer.t.proj a, Matrix.mul_assoc]
  calc
    (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a)
        = ∑ a : Outcome, data.xᴴ * Ta data.qLayer a * data.xHat := by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact hterm a
    _ = (∑ a : Outcome, data.xᴴ * Ta data.qLayer a) * data.xHat := by
          simpa using
            (Matrix.sum_mul (s := Finset.univ)
              (f := fun a : Outcome => data.xᴴ * Ta data.qLayer a)
              (M := data.xHat)).symm
    _ = data.xᴴ * (∑ a : Outcome, Ta data.qLayer a) * data.xHat := by
          have hsum : (∑ a : Outcome, data.xᴴ * Ta data.qLayer a) =
              data.xᴴ * (∑ a : Outcome, Ta data.qLayer a) := by
            simpa using
              (Matrix.mul_sum (s := Finset.univ)
                (f := fun a : Outcome => Ta data.qLayer a)
                (M := data.xᴴ)).symm
          rw [hsum]
    _ = data.xᴴ * data.xHat := by
          simpa [Ta] using
            congrArg (fun M => data.xᴴ * M * data.xHat) data.qLayer.t.sum_eq
    _ = CFC.sqrt (QTotal data.qLayer) := data.xHat_mixed

lemma q_p_cross_close {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QXPLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error))
    (hRank : RankReductionWitness ψ A ζ data.qLayer) :
    |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
        ev ψ (CFC.sqrt (QTotal data.qLayer))| ≤
      2 * zetaQuarterRoot ζ := by
  let D : Matrix data.qLayer.auxSpace.carrier ι ℂ := data.x - data.xHat
  let first : Outcome → Error := fun a =>
    ev ψ ((Xa data a)ᴴ * (D * Dᴴ) * Xa data a)
  let second : Outcome → Error := fun a =>
    ev ψ ((Pa data a)ᴴ * Pa data a)
  have hfirst_nonneg : ∀ a : Outcome, 0 ≤ first a := by
    intro a
    dsimp [first, D]
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      ev_adjoint_self_nonneg ψ ((data.x - data.xHat)ᴴ * Xa data a)
  have hsecond_nonneg : ∀ a : Outcome, 0 ≤ second a := by
    intro a
    dsimp [second]
    exact ev_adjoint_self_nonneg ψ (Pa data a)
  have hfirst_le : (∑ a : Outcome, first a) ≤
      4 * spectralTruncationError ζ := by
    have hpoint : ∀ a : Outcome,
        first a ≤ ev ψ (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
          Qa data.qLayer a) := by
      intro a
      have hrect :
          (Xa data a)ᴴ * (D * Dᴴ) * Xa data a ≤
            (Xa data a)ᴴ *
              ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
              Xa data a := by
        apply sub_nonneg.mp
        have hpsd :
            0 ≤ (Xa data a)ᴴ *
              (((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) - D * Dᴴ) *
              Xa data a := by
          exact
            (Matrix.PosSemidef.conjTranspose_mul_mul_same
              (Matrix.nonneg_iff_posSemidef.mp <|
                sub_nonneg.mpr (by simpa [D] using squaredDifference data))
              (Xa data a)).nonneg
        simpa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] using hpsd
      calc
        first a ≤ ev ψ ((Xa data a)ᴴ *
              ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
              Xa data a) := by
            dsimp [first]
            exact ev_mono ψ _ _ hrect
        _ = ev ψ (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
              Qa data.qLayer a) := by
            rw [xExpressionToQExpression data a]
    calc
      (∑ a : Outcome, first a)
          ≤ ∑ a : Outcome,
              ev ψ (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
                Qa data.qLayer a) := by
              exact Finset.sum_le_sum fun a _ => hpoint a
      _ = ev ψ (∑ a : Outcome,
              (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
                Qa data.qLayer a)) := by
            exact (ev_sum ψ (fun a : Outcome =>
              Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
                Qa data.qLayer a)).symm
      _ ≤ ev ψ ((((4 : Error) * spectralTruncationError ζ) : ℂ) •
              (1 : MIPStarRE.Quantum.Op ι)) := by
            exact ev_mono ψ _ _ (qAlmostProjective ψ A ζ data.qLayer hζ hζ_small hRank)
      _ = 4 * spectralTruncationError ζ := by
            simpa [Complex.ofReal_mul, ev_one_of_isNormalized ψ hψ] using
              ev_scale ψ (4 * spectralTruncationError ζ)
                (1 : MIPStarRE.Quantum.Op ι)
  have hsecond_le : (∑ a : Outcome, second a) ≤ 1 := by
    calc
      (∑ a : Outcome, second a)
          = ∑ a : Outcome, ev ψ (Pa data a) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simp [second, pa_hermitian data a, pa_idempotent data a]
      _ ≤ 1 := pa_mass_le_one data ψ hψ
  have hhat_ev :
      (∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)) =
        ev ψ (CFC.sqrt (QTotal data.qLayer)) := by
    calc
      (∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a))
          = ev ψ (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a) := by
              exact (ev_sum ψ (fun a : Outcome =>
                (Xa data a)ᴴ * data.xHat * Pa data a)).symm
      _ = ev ψ (CFC.sqrt (QTotal data.qLayer)) := by
            rw [xHat_cross_sum_eq_sqrt data]
  have hdiff_sum :
      ((∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
        ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)) =
        ∑ a : Outcome, ev ψ (((Xa data a)ᴴ * D) * Pa data a) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    calc
      ev ψ (Qa data.qLayer a * Pa data a) -
          ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)
          = ev ψ (Qa data.qLayer a * Pa data a -
              (Xa data a)ᴴ * data.xHat * Pa data a) := by
              rw [← ev_sub]
      _ = ev ψ (((Xa data a)ᴴ * D) * Pa data a) := by
            congr 1
            rw [(qaRestated data a).2.2]
            dsimp [D]
            rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  have hdiff_abs :
      |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
          ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)| ≤
        Real.sqrt (∑ a : Outcome, first a) * Real.sqrt (∑ a : Outcome, second a) := by
    calc
      |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
          ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)|
          = |∑ a : Outcome, ev ψ (((Xa data a)ᴴ * D) * Pa data a)| := by
              rw [hdiff_sum]
      _ ≤ ∑ a : Outcome, |ev ψ (((Xa data a)ᴴ * D) * Pa data a)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome, Real.sqrt (first a) * Real.sqrt (second a) := by
            refine Finset.sum_le_sum ?_
            intro a _
            dsimp [first, second]
            simpa [D, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
              ev_abs_mul_le_sqrt ψ ((Xa data a)ᴴ * D) (Pa data a)
      _ ≤ Real.sqrt (∑ a : Outcome, first a) *
            Real.sqrt (∑ a : Outcome, second a) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a : Outcome => first a)
              (g := fun a : Outcome => second a)
              (fun a => hfirst_nonneg a) (fun a => hsecond_nonneg a)
  have hsqrt_first : Real.sqrt (∑ a : Outcome, first a) ≤
      Real.sqrt (4 * spectralTruncationError ζ) := by
    exact Real.sqrt_le_sqrt hfirst_le
  have hsqrt_second : Real.sqrt (∑ a : Outcome, second a) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hsecond_le
    simpa using h
  calc
    |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
        ev ψ (CFC.sqrt (QTotal data.qLayer))|
        = |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
            ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)| := by
            rw [hhat_ev]
    _ ≤ Real.sqrt (∑ a : Outcome, first a) *
          Real.sqrt (∑ a : Outcome, second a) := hdiff_abs
    _ ≤ Real.sqrt (4 * spectralTruncationError ζ) * 1 := by
          exact mul_le_mul hsqrt_first hsqrt_second
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * zetaQuarterRoot ζ := by
          have hsqrt_rpow :
              Real.sqrt (ζ ^ (1 / (2 : Error))) = zetaQuarterRoot ζ := by
            rw [Real.sqrt_eq_rpow, zetaQuarterRoot, ← Real.rpow_mul hζ]
            congr 1
            ring
          dsimp [spectralTruncationError]
          rw [Real.sqrt_mul (by positivity : 0 ≤ (4 : Error)), hsqrt_rpow]
          ring

end

end MIPStarRE.LDT.MakingMeasurementsProjective


