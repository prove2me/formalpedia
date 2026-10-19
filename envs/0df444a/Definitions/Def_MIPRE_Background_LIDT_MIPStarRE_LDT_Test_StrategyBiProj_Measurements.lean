-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:07:30.713722+00:00
-- url     : https://prove2.me/theorems/3127e4cb-5913-4c91-a43e-f19b6009f73c
-- title:
--   Definitions of Measurements: Two-Space Projective Strategies: Role-Register Measurements This module contains the direct-sum measurement…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProj.Measurements` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Two-Space Projective Strategies: Role-Register Measurements. This module contains the direct-sum measurement constructors and the role-register symmetric strategy associated to a heterogeneous projective strategy.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (26): `MIPStarRE.LDT.ProjStrat.PassesLowIndividualDegreeTest` (Passing the full low-individual-degree test with error `ε`, for the paper-faithful two-space strategy container.); `MIPStarRE.LDT.ProjStrat.axisParallelLineAnswerFamilyA` (Alice's axis-parallel-line answers: Alice receives `ℓ`, answers with `B^{A,ℓ}`, and the verifier postprocesses to the value at the sampled…); `MIPStarRE.LDT.ProjStrat.axisParallelLineAnswerFamilyB` (Bob's axis-parallel-line answers: Bob receives `ℓ`, answers with `B^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base…); `MIPStarRE.LDT.ProjStrat.axisParallelLineLeftPointRightFailureProbability` (Axis-parallel branch component where Alice receives the sampled line and Bob receives its base point.); `MIPStarRE.LDT.ProjStrat.axisParallelPointAnswerFamilyA` (Alice's point answers in the axis-parallel branch: Alice receives `u`, the base point of the sampled line, and answers with `A^{A,u}`.); `MIPStarRE.LDT.ProjStrat.axisParallelPointAnswerFamilyB` (Bob's point answers in the axis-parallel branch: Bob receives `u`, the base point of the sampled line, and answers with `A^{B,u}`.); `MIPStarRE.LDT.ProjStrat.axisParallelPointLeftLineRightFailureProbability` (Axis-parallel branch component where Alice receives the sampled base point and Bob receives the sampled line.); `MIPStarRE.LDT.ProjStrat.axisParallelRoleAverage` (The paper's axis-parallel branch for a two-space general strategy, averaged over the two role choices.); and 9 more.
--
--   **Embedded lemmas** (12): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `localDirectSumMeasurement_outcome`, `localDirectSumMeasurement_total`, `localDirectSumProjMeas_outcome`, `roleBlockMeasurement_outcome`, `roleBlockMeasurement_total`, `roleBlockProjMeas_outcome`, `roleRegisterAxisParallelTransportInvariant`, `roleRegisterDiagonalTransportInvariant`, `roleRegisterProjMeas_A_B`, `roleRegisterProjMeas_A_inl_inl`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProj.Measurements` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProj/Measurements.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 22 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProj/Measurements.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/StrategyBiProj/Measurements.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProj/Measurements.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
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
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Pi
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
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum
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
import Mathlib.Data.Fintype.Sum
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Theorems.Thm_MIPStarRE_LDT_AxisParallelMeasurementReparamInvariant_toTransportInvariant
import Theorems.Thm_MIPStarRE_LDT_DiagonalMeasurementReparamInvariant_toTransportInvariant
import Theorems.Thm_MIPStarRE_LDT_ProjMeas_ext
import Theorems.Thm_MIPStarRE_LDT_ProjMeas_transport_trivialDistinguishedOutcome
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_localDirectSumBlock_finset_sum
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_localDirectSumBlock_nonneg
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_roleBlock_finset_sum
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_roleBlock_nonneg
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_roleRegisterSymmState_density_fixed
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_roleRegisterSymmState_isNormalized
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_roleRegisterSymmState_permInvState
import Theorems.Thm_MIPStarRE_LDT_QuantumState_IsNormalized_nonempty

attribute [ext] MIPStarRE.LDT.ProjMeas.ext
attribute [simp] MIPStarRE.LDT.ProjMeas.transport_trivialDistinguishedOutcome
attribute [simp] MIPStarRE.LDT.ProjStrat.roleRegisterSymmState_density_fixed

set_option backward.isDefEq.respectTransparency false

/-!
# Two-Space Projective Strategies: Role-Register Measurements

This module contains the direct-sum measurement constructors and the
role-register symmetric strategy associated to a heterogeneous projective
strategy.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat

/-! ### Complete block-measurement constructors -/

/-- Direct-sum measurement obtained by placing Alice's and Bob's complete
measurements on the `Sum.inl` and `Sum.inr` sectors respectively. -/
noncomputable def localDirectSumMeasurement {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : Measurement Outcome ιA) (MB : Measurement Outcome ιB) :
    Measurement Outcome (LocalCarrierSum ιA ιB) :=
  ({ outcome := fun a => localDirectSumBlock (MA.outcome a) (MB.outcome a)
     total := localDirectSumBlock MA.total MB.total
     outcome_pos := fun a => localDirectSumBlock_nonneg (MA.outcome_pos a) (MB.outcome_pos a)
     sum_eq_total :=
       (localDirectSumBlock_finset_sum Finset.univ MA.outcome MB.outcome).trans
         (congrArg₂ localDirectSumBlock MA.sum_eq_total MB.sum_eq_total)
     total_le_one :=
       ((congrArg₂ localDirectSumBlock MA.total_eq_one MB.total_eq_one).trans
         localDirectSumBlock_one).le } :
    SubMeas Outcome (LocalCarrierSum ιA ιB)).toMeasurement
    ((congrArg₂ localDirectSumBlock MA.total_eq_one MB.total_eq_one).trans
      localDirectSumBlock_one)

@[simp] theorem localDirectSumMeasurement_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : Measurement Outcome ιA) (MB : Measurement Outcome ιB) (a : Outcome) :
    (localDirectSumMeasurement MA MB).outcome a =
      localDirectSumBlock (MA.outcome a) (MB.outcome a) :=
  rfl

@[simp] theorem localDirectSumMeasurement_total {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : Measurement Outcome ιA) (MB : Measurement Outcome ιB) :
    (localDirectSumMeasurement MA MB).total = 1 := by
  simp [localDirectSumMeasurement, MA.total_eq_one, MB.total_eq_one]

/-- Direct-sum projective measurement obtained by block-diagonalizing two
projective measurements with the same outcome type. -/
noncomputable def localDirectSumProjMeas {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    ProjMeas Outcome (LocalCarrierSum ιA ιB) where
  toMeasurement := localDirectSumMeasurement MA.toMeasurement MB.toMeasurement
  proj := fun a =>
    (localDirectSumBlock_mul _ _ _ _).trans
      (congrArg₂ localDirectSumBlock (MA.proj a) (MB.proj a))

@[simp] theorem localDirectSumProjMeas_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) (a : Outcome) :
    (localDirectSumProjMeas MA MB).outcome a =
      localDirectSumBlock (MA.outcome a) (MB.outcome a) :=
  rfl

/-- Role-register measurement obtained by placing two complete direct-sum
measurements in the `Role.A` and `Role.B` sectors. -/
noncomputable def roleBlockMeasurement {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : Measurement Outcome (LocalCarrierSum ιA ιB)) :
    Measurement Outcome (RoleRegisterLocal ιA ιB) :=
  ({ outcome := fun a => roleBlock (MA.outcome a) (MB.outcome a)
     total := roleBlock MA.total MB.total
     outcome_pos := fun a => roleBlock_nonneg (MA.outcome_pos a) (MB.outcome_pos a)
     sum_eq_total :=
       (roleBlock_finset_sum Finset.univ MA.outcome MB.outcome).trans
         (congrArg₂ roleBlock MA.sum_eq_total MB.sum_eq_total)
     total_le_one :=
       ((congrArg₂ roleBlock MA.total_eq_one MB.total_eq_one).trans roleBlock_one).le } :
    SubMeas Outcome (RoleRegisterLocal ιA ιB)).toMeasurement
    ((congrArg₂ roleBlock MA.total_eq_one MB.total_eq_one).trans roleBlock_one)

@[simp] theorem roleBlockMeasurement_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : Measurement Outcome (LocalCarrierSum ιA ιB)) (a : Outcome) :
    (roleBlockMeasurement MA MB).outcome a = roleBlock (MA.outcome a) (MB.outcome a) :=
  rfl

@[simp] theorem roleBlockMeasurement_total {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : Measurement Outcome (LocalCarrierSum ιA ιB)) :
    (roleBlockMeasurement MA MB).total = 1 := by
  simp [roleBlockMeasurement, MA.total_eq_one, MB.total_eq_one]

/-- Role-register projective measurement obtained by block-diagonalizing two
complete direct-sum projective measurements. -/
noncomputable def roleBlockProjMeas {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : ProjMeas Outcome (LocalCarrierSum ιA ιB)) :
    ProjMeas Outcome (RoleRegisterLocal ιA ιB) where
  toMeasurement := roleBlockMeasurement MA.toMeasurement MB.toMeasurement
  proj := fun a =>
    (roleBlock_mul _ _ _ _).trans (congrArg₂ roleBlock (MA.proj a) (MB.proj a))

@[simp] theorem roleBlockProjMeas_outcome {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA MB : ProjMeas Outcome (LocalCarrierSum ιA ιB)) (a : Outcome) :
    (roleBlockProjMeas MA MB).outcome a = roleBlock (MA.outcome a) (MB.outcome a) :=
  rfl

/--
Heterogeneous role-register projective measurement for a two-space strategy.

The `Role.A` sector acts on Alice's original summand and the `Role.B` sector
acts on Bob's original summand, as in the role-register symmetrization in
`references/ldt-paper/inductive_step.tex:40-59`.  The complementary direct-sum
sectors are filled by the canonical distinguished-outcome projective
measurement.  Those sectors are auxiliary: in the eventual heterogeneous
symmetrized state, the occupied sectors are `(Role.A, Sum.inl _)` on the left
and `(Role.B, Sum.inr _)` on the right, together with their swapped copy. -/
noncomputable def roleRegisterProjMeas {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    ProjMeas Outcome (RoleRegisterLocal ιA ιB) :=
  let fillerA : ProjMeas Outcome ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerB : ProjMeas Outcome ιB := ProjMeas.trivialDistinguishedOutcome default
  roleBlockProjMeas
    (localDirectSumProjMeas MA fillerB)
    (localDirectSumProjMeas fillerA MB)

@[simp] theorem roleRegisterProjMeas_A_inl_inl {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (a : Outcome) (i j : ιA) :
    (roleRegisterProjMeas MA MB).outcome a (Role.A, Sum.inl i) (Role.A, Sum.inl j) =
      MA.outcome a i j :=
  rfl

@[simp] theorem roleRegisterProjMeas_B_inr_inr {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (a : Outcome) (i j : ιB) :
    (roleRegisterProjMeas MA MB).outcome a (Role.B, Sum.inr i) (Role.B, Sum.inr j) =
      MB.outcome a i j :=
  rfl

@[simp] theorem roleRegisterProjMeas_A_B {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (a : Outcome) (i j : LocalCarrierSum ιA ιB) :
    (roleRegisterProjMeas MA MB).outcome a (Role.A, i) (Role.B, j) = 0 :=
  rfl

@[simp] theorem roleRegisterProjMeas_B_A {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (a : Outcome) (i j : LocalCarrierSum ιA ιB) :
    (roleRegisterProjMeas MA MB).outcome a (Role.B, i) (Role.A, j) = 0 :=
  rfl

variable {params : Parameters} [FieldModel params.q]
variable {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
variable {ιB : Type*} [Fintype ιB] [DecidableEq ιB]

/-! ### Heterogeneous role-register measurement families -/

/-- Point measurements of the heterogeneous role-register strategy associated to
a two-space projective strategy. -/
noncomputable def roleRegisterPointMeasurement
    (strategy : ProjStrat params ιA ιB) :
    IdxProjMeas (Point params) (Fq params) (RoleRegisterLocal ιA ιB) :=
  fun u => roleRegisterProjMeas (strategy.pointMeasurementA u)
    (strategy.pointMeasurementB u)

/-- Axis-parallel-line measurements of the heterogeneous role-register strategy
associated to a two-space projective strategy. -/
noncomputable def roleRegisterAxisParallelMeasurement
    (strategy : ProjStrat params ιA ιB) :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params)
      (RoleRegisterLocal ιA ιB) :=
  fun ℓ => roleRegisterProjMeas (strategy.axisParallelMeasurementA ℓ)
    (strategy.axisParallelMeasurementB ℓ)

/-- Diagonal-line measurements of the heterogeneous role-register strategy
associated to a two-space projective strategy. -/
noncomputable def roleRegisterDiagonalMeasurement
    (strategy : ProjStrat params ιA ιB) :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params)
      (RoleRegisterLocal ιA ιB) :=
  fun ℓ => roleRegisterProjMeas (strategy.diagonalMeasurementA ℓ)
    (strategy.diagonalMeasurementB ℓ)

theorem roleRegisterAxisParallelTransportInvariant
    (strategy : ProjStrat params ιA ιB) :
    AxisParallelMeasurementTransportInvariant params
      (roleRegisterAxisParallelMeasurement strategy) := by
  intro ℓ t
  ext a
  have hA := congrArg (fun N => N.outcome a)
    (strategy.axisParallelReparamInvariantA.toTransportInvariant ℓ t)
  have hB := congrArg (fun N => N.outcome a)
    (strategy.axisParallelReparamInvariantB.toTransportInvariant ℓ t)
  have hFillA :
      (ProjMeas.trivialDistinguishedOutcome (ι := ιA)
          (default : AxisLinePolynomial params)).outcome a =
        (ProjMeas.trivialDistinguishedOutcome (ι := ιA)
          (default : AxisLinePolynomial params)).outcome
            ((AxisLinePolynomial.reparamAtEquiv (params := params) t).symm a) := by
    have h := congrArg
      (fun M : ProjMeas (AxisLinePolynomial params) ιA => M.outcome a)
      (ProjMeas.transport_trivialDistinguishedOutcome
        (ι := ιA) (e := AxisLinePolynomial.reparamAtEquiv (params := params) t)
        (a₀ := (default : AxisLinePolynomial params)))
    simpa [ProjMeas.transport, Measurement.transport, SubMeas.transport,
      AxisLinePolynomial.reparamAtEquiv] using h.symm
  have hFillB :
      (ProjMeas.trivialDistinguishedOutcome (ι := ιB)
          (default : AxisLinePolynomial params)).outcome a =
        (ProjMeas.trivialDistinguishedOutcome (ι := ιB)
          (default : AxisLinePolynomial params)).outcome
            ((AxisLinePolynomial.reparamAtEquiv (params := params) t).symm a) := by
    have h := congrArg
      (fun M : ProjMeas (AxisLinePolynomial params) ιB => M.outcome a)
      (ProjMeas.transport_trivialDistinguishedOutcome
        (ι := ιB) (e := AxisLinePolynomial.reparamAtEquiv (params := params) t)
        (a₀ := (default : AxisLinePolynomial params)))
    simpa [ProjMeas.transport, Measurement.transport, SubMeas.transport,
      AxisLinePolynomial.reparamAtEquiv] using h.symm
  simp [roleRegisterAxisParallelMeasurement, roleRegisterProjMeas,
    AxisParallelLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, hA, hB, hFillA, hFillB]

theorem roleRegisterDiagonalTransportInvariant
    (strategy : ProjStrat params ιA ιB) :
    DiagonalMeasurementTransportInvariant params
      (roleRegisterDiagonalMeasurement strategy) := by
  intro ℓ t
  ext a
  have hA := congrArg (fun N => N.outcome a)
    (strategy.diagonalReparamInvariantA.toTransportInvariant ℓ t)
  have hB := congrArg (fun N => N.outcome a)
    (strategy.diagonalReparamInvariantB.toTransportInvariant ℓ t)
  have hFillA :
      (ProjMeas.trivialDistinguishedOutcome (ι := ιA)
          (default : DiagonalLinePolynomial params)).outcome a =
        (ProjMeas.trivialDistinguishedOutcome (ι := ιA)
          (default : DiagonalLinePolynomial params)).outcome
            ((DiagonalLinePolynomial.reparamAtEquiv (params := params) t).symm a) := by
    have h := congrArg
      (fun M : ProjMeas (DiagonalLinePolynomial params) ιA => M.outcome a)
      (ProjMeas.transport_trivialDistinguishedOutcome
        (ι := ιA) (e := DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
        (a₀ := (default : DiagonalLinePolynomial params)))
    simpa [ProjMeas.transport, Measurement.transport, SubMeas.transport,
      DiagonalLinePolynomial.reparamAtEquiv] using h.symm
  have hFillB :
      (ProjMeas.trivialDistinguishedOutcome (ι := ιB)
          (default : DiagonalLinePolynomial params)).outcome a =
        (ProjMeas.trivialDistinguishedOutcome (ι := ιB)
          (default : DiagonalLinePolynomial params)).outcome
            ((DiagonalLinePolynomial.reparamAtEquiv (params := params) t).symm a) := by
    have h := congrArg
      (fun M : ProjMeas (DiagonalLinePolynomial params) ιB => M.outcome a)
      (ProjMeas.transport_trivialDistinguishedOutcome
        (ι := ιB) (e := DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
        (a₀ := (default : DiagonalLinePolynomial params)))
    simpa [ProjMeas.transport, Measurement.transport, SubMeas.transport,
      DiagonalLinePolynomial.reparamAtEquiv] using h.symm
  simp [roleRegisterDiagonalMeasurement, roleRegisterProjMeas,
    DiagonalLine.transportMeasurement, ProjMeas.transport,
    Measurement.transport, SubMeas.transport, hA, hB, hFillA, hFillB]

/-- The heterogeneous role-register symmetrization of a two-space projective
strategy as a symmetric strategy on the common local space `Role × (ιA ⊕ ιB)`.

This construction proves the structural part of the paper's symmetrization
step: the state is exchange-invariant, normalized, and equipped with the
role-blocked point, axis-parallel, and diagonal projective measurements.  The
branch-probability comparison giving `(3ε,3ε,3ε)` goodness is a separate
theorem. -/
noncomputable def roleRegisterSymmStrategy
    (strategy : ProjStrat params ιA ιB) :
    SymStrat params (RoleRegisterLocal ιA ιB) :=
  haveI : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  haveI : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  { state := roleRegisterSymmState strategy.state
    permInvState := roleRegisterSymmState_permInvState strategy.state
    densityFixed := roleRegisterSymmState_density_fixed strategy.state
    isNormalized := roleRegisterSymmState_isNormalized strategy.state strategy.isNormalized
    pointMeasurement := roleRegisterPointMeasurement strategy
    axisParallelMeasurement :=
      { toIdxProjMeas := roleRegisterAxisParallelMeasurement strategy
        transportInvariant := roleRegisterAxisParallelTransportInvariant strategy }
    diagonalMeasurement :=
      { toIdxProjMeas := roleRegisterDiagonalMeasurement strategy
        transportInvariant := roleRegisterDiagonalTransportInvariant strategy } }

/-! ### Paper test branches for two-space strategies -/

/-- Alice's point answers in the axis-parallel branch: Alice receives `u`,
the base point of the sampled line, and answers with `A^{A,u}`. -/
noncomputable def axisParallelPointAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιA :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the axis-parallel branch: Bob receives `u`,
the base point of the sampled line, and answers with `A^{B,u}`. -/
noncomputable def axisParallelPointAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιB :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's axis-parallel-line answers: Alice receives `ℓ`, answers with
`B^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιA :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's axis-parallel-line answers: Bob receives `ℓ`, answers with
`B^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιB :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-- Alice's point answers in the restricted diagonal branch: Alice receives the
sampled base point `u` and answers with `A^{A,u}`. -/
noncomputable def diagonalPointAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιA :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the restricted diagonal branch: Bob receives the
sampled base point `u` and answers with `A^{B,u}`. -/
noncomputable def diagonalPointAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιB :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's restricted diagonal-line answers: Alice receives `ℓ`, answers with
`L^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyA
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιA :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's restricted diagonal-line answers: Bob receives `ℓ`, answers with
`L^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyB
    (strategy : ProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιB :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-- Axis-parallel branch component where Alice receives the sampled line and Bob
receives its base point. -/
noncomputable def axisParallelLineLeftPointRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelLineAnswerFamilyA strategy)
    (axisParallelPointAnswerFamilyB strategy)

/-- Axis-parallel branch component where Alice receives the sampled base point
and Bob receives the sampled line. -/
noncomputable def axisParallelPointLeftLineRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamilyA strategy)
    (axisParallelLineAnswerFamilyB strategy)

/-- The paper's axis-parallel branch for a two-space general strategy, averaged
over the two role choices. -/
noncomputable def axisParallelRoleAverage
    (strategy : ProjStrat params ιA ιB) : Error :=
  (axisParallelLineLeftPointRightFailureProbability strategy +
    axisParallelPointLeftLineRightFailureProbability strategy) / 2

/-- Point-agreement branch: both provers receive the same point and the verifier
checks equality of their field answers. -/
noncomputable def pointAgreementFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)

/-- Diagonal branch component where Alice receives the sampled diagonal line and
Bob receives its base point. -/
noncomputable def diagonalLineLeftPointRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalLineAnswerFamilyA strategy j)
        (diagonalPointAnswerFamilyB strategy j)

/-- Diagonal branch component where Alice receives the sampled base point and
Bob receives the sampled diagonal line. -/
noncomputable def diagonalPointLeftLineRightFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamilyA strategy j)
        (diagonalLineAnswerFamilyB strategy j)

/-- The paper's diagonal branch for a two-space general strategy, averaged over
the two role choices and the restricted diagonal samples. -/
noncomputable def diagonalRoleAverage
    (strategy : ProjStrat params ιA ιB) : Error :=
  (diagonalLineLeftPointRightFailureProbability strategy +
    diagonalPointLeftLineRightFailureProbability strategy) / 2

/-- Trace-based failure surrogate for the full low-individual-degree test for a
paper-faithful two-space projective strategy.

The three outer summands are respectively axis-parallel consistency, point
agreement, and restricted-diagonal consistency, with outer weight `1 / 3`.
Each line branch averages the two prover-role orderings with weight `1 / 2`, and
the restricted-diagonal branch also averages its restriction index with weight
`1 / m`.  Line answers are evaluated at `zeroCoord`, the parameter value of the
sampled base point. -/
noncomputable def lowIndividualDegreeFailureProbability
    (strategy : ProjStrat params ιA ιB) : Error :=
  let axisPointA : IdxSubMeas (Point params × Fin params.m) (Fq params) ιA :=
    fun s => (strategy.pointMeasurementA s.1).toSubMeas
  let axisPointB : IdxSubMeas (Point params × Fin params.m) (Fq params) ιB :=
    fun s => (strategy.pointMeasurementB s.1).toSubMeas
  let axisLineA : IdxSubMeas (Point params × Fin params.m) (Fq params) ιA :=
    fun s =>
      let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
      postprocess ((strategy.axisParallelMeasurementA ℓ).toSubMeas) (· zeroCoord)
  let axisLineB : IdxSubMeas (Point params × Fin params.m) (Fq params) ιB :=
    fun s =>
      let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
      postprocess ((strategy.axisParallelMeasurementB ℓ).toSubMeas) (· zeroCoord)
  let extendDirection (j : Fin params.m)
      (freeCoords : Fin (j.val + 1) → Fq params) : Point params :=
    fun k =>
      if h : k.val ≤ j.val then
        freeCoords ⟨k.val, Nat.lt_succ_of_le h⟩
      else zeroCoord
  let diagonalPointA (j : Fin params.m) :
      IdxSubMeas (Point params × (Fin (j.val + 1) → Fq params)) (Fq params) ιA :=
    fun s => (strategy.pointMeasurementA s.1).toSubMeas
  let diagonalPointB (j : Fin params.m) :
      IdxSubMeas (Point params × (Fin (j.val + 1) → Fq params)) (Fq params) ιB :=
    fun s => (strategy.pointMeasurementB s.1).toSubMeas
  let diagonalLineA (j : Fin params.m) :
      IdxSubMeas (Point params × (Fin (j.val + 1) → Fq params)) (Fq params) ιA :=
    fun s =>
      let ℓ : DiagonalLine params := { base := s.1, direction := extendDirection j s.2 }
      postprocess ((strategy.diagonalMeasurementA ℓ).toSubMeas) (· zeroCoord)
  let diagonalLineB (j : Fin params.m) :
      IdxSubMeas (Point params × (Fin (j.val + 1) → Fq params)) (Fq params) ιB :=
    fun s =>
      let ℓ : DiagonalLine params := { base := s.1, direction := extendDirection j s.2 }
      postprocess ((strategy.diagonalMeasurementB ℓ).toSubMeas) (· zeroCoord)
  ((bipartiteConsError strategy.state
        (@uniformDistribution (Point params × Fin params.m) _ _
          ⟨(fun _ => zeroCoord, default)⟩) axisLineA axisPointB +
      bipartiteConsError strategy.state
        (@uniformDistribution (Point params × Fin params.m) _ _
          ⟨(fun _ => zeroCoord, default)⟩) axisPointA axisLineB) / ((2 : ℕ) : Error) +
    bipartiteConsError strategy.state
      (@uniformDistribution (Point params) _ _ ⟨fun _ => zeroCoord⟩)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) +
    ((1 / (params.m : Error)) * ∑ j : Fin params.m,
        bipartiteConsError strategy.state
          (@uniformDistribution (Point params × (Fin (j.val + 1) → Fq params)) _ _
            ⟨(fun _ => zeroCoord, fun _ => zeroCoord)⟩)
          (diagonalLineA j) (diagonalPointB j) +
      (1 / (params.m : Error)) * ∑ j : Fin params.m,
        bipartiteConsError strategy.state
          (@uniformDistribution (Point params × (Fin (j.val + 1) → Fq params)) _ _
            ⟨(fun _ => zeroCoord, fun _ => zeroCoord)⟩)
          (diagonalPointA j) (diagonalLineB j)) / ((2 : ℕ) : Error)) / 3

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- Passing the full low-individual-degree test with error `ε`, for the
paper-faithful two-space strategy container. -/
structure PassesLowIndividualDegreeTest
    (strategy : ProjStrat params ιA ιB) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end ProjStrat

end MIPStarRE.LDT


