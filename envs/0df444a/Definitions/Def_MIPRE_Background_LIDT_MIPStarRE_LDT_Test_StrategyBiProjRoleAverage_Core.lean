-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProjRoleAverage_Core
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProjRoleAverage_Core
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:08:49.180549+00:00
-- url     : https://prove2.me/theorems/f508dc32-2838-489b-a8e2-6cdc38eef1c5
-- title:
--   Definitions of Core: Role-Register Averaging: Branch Equalities This module proves the role-register branch equalities for heterogeneous…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProjRoleAverage.Core` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Role-Register Averaging: Branch Equalities. This module proves the role-register branch equalities for heterogeneous projective strategies.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (18): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ev_roleRegisterSymmState_rolePairDirectSumCond_AA`, `ev_roleRegisterSymmState_rolePairDirectSumCond_BB`, `axisParallel_roleRegister_sample_eq_average`, `diagonal_roleRegister_sample_eq_average`, `ev_roleRegisterSymmState_point_postprocessedLine_outcome`, `ev_roleRegisterSymmState_roleBlock_localDirectSumBlocks`, `ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks`, `ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks`, `ev_roleRegisterSymmState_roleRegisterProjMeas_outcome`, `localPairABBlock_mul_opTensor_localDirectSumBlocks`, ….
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProjRoleAverage.Core` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Core.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 25 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Core.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Core.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Core.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_localDirectSumBlock_finset_sum
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_normalizedTrace_heterogeneousSwapDensity
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_normalizedTrace_localPairABBlock
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_normalizedTrace_localPairBABlock
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_normalizedTrace_rolePairDirectSumCond
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_roleBlock_finset_sum
import Theorems.Thm_MIPStarRE_LDT_ProjStrat_roleRegisterSymmState_isNormalized
import Theorems.Thm_MIPStarRE_LDT_ev_add
import Theorems.Thm_MIPStarRE_LDT_qBipartiteConsDefect_of_measurements
import Theorems.Thm_MIPStarRE_Quantum_normalizedTrace_add
import Theorems.Thm_MIPStarRE_Quantum_normalizedTrace_smul

set_option backward.isDefEq.respectTransparency false

/-!
# Role-Register Averaging: Branch Equalities

This module proves the role-register branch equalities for heterogeneous
projective strategies.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat

theorem ev_roleRegisterSymmState_rolePairDirectSumCond_AA {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    ev (roleRegisterSymmState ψ) (rolePairDirectSumCond Role.A Role.A X) = 0 := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.A Role.A X)) = 0
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.A Role.B Role.A Role.A
      (localPairABBlock ψ.density) X (by decide)]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.B Role.A Role.A Role.A
      (localPairBABlock (heterogeneousSwapDensity ψ.density)) X (by decide)]
  simp

theorem ev_roleRegisterSymmState_rolePairDirectSumCond_BB {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    ev (roleRegisterSymmState ψ) (rolePairDirectSumCond Role.B Role.B X) = 0 := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.B Role.B X)) = 0
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.A Role.B Role.B Role.B
      (localPairABBlock ψ.density) X (by decide)]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.B Role.A Role.B Role.B
      (localPairBABlock (heterogeneousSwapDensity ψ.density)) X (by decide)]
  simp

lemma opTensor_roleBlock_eq_rolePairDirectSumCond_sum {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A B C D : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    opTensor (roleBlock A B) (roleBlock C D) =
      rolePairDirectSumCond Role.A Role.A (opTensor A C) +
        rolePairDirectSumCond Role.A Role.B (opTensor A D) +
          (rolePairDirectSumCond Role.B Role.A (opTensor B C) +
            rolePairDirectSumCond Role.B Role.B (opTensor B D)) := by
  ext x y
  rcases x with ⟨⟨rx, ix⟩, ⟨sx, jx⟩⟩
  rcases y with ⟨⟨ry, iy⟩, ⟨sy, jy⟩⟩
  cases rx <;> cases sx <;> cases ry <;> cases sy <;>
    simp [opTensor, rolePairDirectSumCond, rolePairProj, roleProj,
      roleRegisterPairLocalEquiv]

lemma localPairABBlock_mul_opTensor_localDirectSumBlocks {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Afill : MIPStarRE.Quantum.Op ιA) (D : MIPStarRE.Quantum.Op ιB) :
    localPairABBlock X *
        opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Afill D) =
      localPairABBlock (X * opTensor A D) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ with
      | inl j =>
          cases y₁ <;> cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]
      | inr j =>
          cases y₁ with
          | inl i' =>
              cases y₂ with
              | inl j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp [localPairABBlock, opTensor]
              | inr j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairABBlock, opTensor,
                    localDirectSumBlock, Matrix.of_apply, zero_mul, Finset.sum_const_zero,
                    zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιA => fun y : ιB =>
                      X (i, j) (x, y) * (A x i' * D y j'))).symm
          | inr i' =>
              cases y₂ <;>
                rw [Matrix.mul_apply, Fintype.sum_prod_type] <;>
                simp [localPairABBlock, opTensor]
  | inr i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;>
        simp [localPairABBlock, Matrix.mul_apply]

lemma localPairBABlock_mul_opTensor_localDirectSumBlocks {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA))
    (B : MIPStarRE.Quantum.Op ιB) (Afill : MIPStarRE.Quantum.Op ιA)
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB) :
    localPairBABlock X *
        opTensor (localDirectSumBlock Afill B) (localDirectSumBlock A Bfill) =
      localPairBABlock (X * opTensor B A) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;>
        simp [localPairBABlock, Matrix.mul_apply]
  | inr i =>
      cases x₂ with
      | inl j =>
          cases y₁ with
          | inl i' =>
              cases y₂ <;>
                rw [Matrix.mul_apply, Fintype.sum_prod_type] <;>
                simp [localPairBABlock, opTensor]
          | inr i' =>
              cases y₂ with
              | inl j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairBABlock, opTensor,
                    localDirectSumBlock, Matrix.of_apply, zero_mul, Finset.sum_const_zero,
                    zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιB => fun y : ιA =>
                      X (i, j) (x, y) * (B x i' * A y j'))).symm
              | inr j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp [localPairBABlock, opTensor]
      | inr j =>
          cases y₁ <;> cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]

lemma ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Afill : MIPStarRE.Quantum.Op ιA) (D : MIPStarRE.Quantum.Op ιB) :
    ev (roleRegisterSymmState ψ)
        (rolePairDirectSumCond Role.A Role.B
          (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Afill D))) =
      (1 / 2 : Error) * ev ψ (opTensor A D) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.A Role.B
          (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Afill D)))) =
    (1 / 2 : Error) * ev ψ (opTensor A D)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_same, rolePairDirectSumCond_BA_mul_AB]
  rw [localPairABBlock_mul_opTensor_localDirectSumBlocks]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, add_zero]
  rw [normalizedTrace_rolePairDirectSumCond, normalizedTrace_localPairABBlock]
  let T := MIPStarRE.Quantum.normalizedTrace (ψ.density * opTensor A D)
  let R : ℂ :=
    (Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
      ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscalar :
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R) = (1 / 2 : ℂ) := by
    subst R
    unfold roleRegisterDensityScale
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
    ring_nf
  change Complex.re ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T))) =
    (1 / 2 : Error) * ev ψ (opTensor A D)
  rw [show ev ψ (opTensor A D) = Complex.re T by rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

lemma ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (B : MIPStarRE.Quantum.Op ιB) (Afill : MIPStarRE.Quantum.Op ιA)
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB) :
    ev (roleRegisterSymmState ψ)
        (rolePairDirectSumCond Role.B Role.A
          (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock A Bfill))) =
      (1 / 2 : Error) * ev ψ (opTensor A B) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.B Role.A
          (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock A Bfill)))) =
    (1 / 2 : Error) * ev ψ (opTensor A B)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_AB_mul_BA, rolePairDirectSumCond_mul_same]
  rw [localPairBABlock_mul_opTensor_localDirectSumBlocks]
  rw [← heterogeneousSwapDensity_opTensor]
  rw [← heterogeneousSwapDensity_mul]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, zero_add]
  rw [normalizedTrace_rolePairDirectSumCond, normalizedTrace_localPairBABlock,
    normalizedTrace_heterogeneousSwapDensity]
  let T := MIPStarRE.Quantum.normalizedTrace (ψ.density * opTensor A B)
  let R : ℂ :=
    (Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
      ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscalar :
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R) = (1 / 2 : ℂ) := by
    subst R
    unfold roleRegisterDensityScale
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
    ring_nf
  change Complex.re ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T))) =
    (1 / 2 : Error) * ev ψ (opTensor A B)
  rw [show ev ψ (opTensor A B) = Complex.re T by rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

lemma ev_roleRegisterSymmState_roleBlock_localDirectSumBlocks
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A C Afill Cfill : MIPStarRE.Quantum.Op ιA)
    (B D Bfill Dfill : MIPStarRE.Quantum.Op ιB) :
    ev (roleRegisterSymmState ψ)
        (opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          (roleBlock (localDirectSumBlock C Dfill) (localDirectSumBlock Cfill D))) =
      (1 / 2 : Error) * ev ψ (opTensor A D) +
        (1 / 2 : Error) * ev ψ (opTensor C B) := by
  calc
    ev (roleRegisterSymmState ψ)
        (opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          (roleBlock (localDirectSumBlock C Dfill) (localDirectSumBlock Cfill D)))
      = ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock C Dfill)) +
            rolePairDirectSumCond Role.A Role.B
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Cfill D)) +
              (rolePairDirectSumCond Role.B Role.A
                (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock C Dfill)) +
                rolePairDirectSumCond Role.B Role.B
                  (opTensor (localDirectSumBlock Afill B)
                    (localDirectSumBlock Cfill D)))) := by
          rw [opTensor_roleBlock_eq_rolePairDirectSumCond_sum]
    _ =
        ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock C Dfill))) +
          ev (roleRegisterSymmState ψ)
            (rolePairDirectSumCond Role.A Role.B
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Cfill D))) +
            (ev (roleRegisterSymmState ψ)
              (rolePairDirectSumCond Role.B Role.A
                (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock C Dfill))) +
              ev (roleRegisterSymmState ψ)
                (rolePairDirectSumCond Role.B Role.B
                  (opTensor (localDirectSumBlock Afill B)
                    (localDirectSumBlock Cfill D)))) := by
          repeat rw [ev_add]
    _ = 0 + (1 / 2 : Error) * ev ψ (opTensor A D) +
            ((1 / 2 : Error) * ev ψ (opTensor C B) + 0) := by
          rw [ev_roleRegisterSymmState_rolePairDirectSumCond_AA,
            ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePairDirectSumCond_BB]
    _ = (1 / 2 : Error) * ev ψ (opTensor A D) +
        (1 / 2 : Error) * ev ψ (opTensor C B) := by
          ring

lemma ev_roleRegisterSymmState_roleRegisterProjMeas_outcome
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA NA : ProjMeas Outcome ιA) (MB NB : ProjMeas Outcome ιB)
    (a : Outcome) :
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas MA MB).outcome a)
          ((roleRegisterProjMeas NA NB).outcome a)) =
      (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
        (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
  let fillerA : ProjMeas Outcome ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerB : ProjMeas Outcome ιB := ProjMeas.trivialDistinguishedOutcome default
  calc
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas MA MB).outcome a)
          ((roleRegisterProjMeas NA NB).outcome a))
      = ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (NA.outcome a) (fillerB.outcome a))) +
            rolePairDirectSumCond Role.A Role.B
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (fillerA.outcome a) (NB.outcome a))) +
              (rolePairDirectSumCond Role.B Role.A
                (opTensor
                  (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                  (localDirectSumBlock (NA.outcome a) (fillerB.outcome a))) +
                rolePairDirectSumCond Role.B Role.B
                  (opTensor
                    (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                    (localDirectSumBlock (fillerA.outcome a) (NB.outcome a))))) := by
          congr 1
          simp [roleRegisterProjMeas, opTensor_roleBlock_eq_rolePairDirectSumCond_sum,
            fillerA, fillerB]
    _ =
        ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (NA.outcome a) (fillerB.outcome a)))) +
          ev (roleRegisterSymmState ψ)
            (rolePairDirectSumCond Role.A Role.B
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (fillerA.outcome a) (NB.outcome a)))) +
            (ev (roleRegisterSymmState ψ)
              (rolePairDirectSumCond Role.B Role.A
                (opTensor
                  (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                  (localDirectSumBlock (NA.outcome a) (fillerB.outcome a)))) +
              ev (roleRegisterSymmState ψ)
                (rolePairDirectSumCond Role.B Role.B
                  (opTensor
                    (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                    (localDirectSumBlock (fillerA.outcome a) (NB.outcome a))))) := by
          repeat rw [ev_add]
    _ = 0 +
          (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            ((1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) +
              0) := by
          rw [ev_roleRegisterSymmState_rolePairDirectSumCond_AA,
            ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePairDirectSumCond_BB]
    _ = (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
        (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
          ring

lemma postprocess_roleRegisterProjMeas_outcome
    {α β ιA ιB : Type*}
    [Inhabited α] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas α ιA) (MB : ProjMeas α ιB) (f : α → β) (b : β) :
    (postprocess ((roleRegisterProjMeas MA MB).toSubMeas) f).outcome b =
      roleBlock
        (localDirectSumBlock ((ProjMeas.postprocess MA f).outcome b)
          ((ProjMeas.postprocess
            (ProjMeas.trivialDistinguishedOutcome (ι := ιB) (default : α)) f).outcome b))
        (localDirectSumBlock
          ((ProjMeas.postprocess
            (ProjMeas.trivialDistinguishedOutcome (ι := ιA) (default : α)) f).outcome b)
          ((ProjMeas.postprocess MB f).outcome b)) := by
  classical
  rw [SubMeas.postprocess_outcome]
  simp only [roleRegisterProjMeas, roleBlockProjMeas_outcome,
    localDirectSumProjMeas_outcome, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_outcome]
  rw [roleBlock_finset_sum]
  rw [localDirectSumBlock_finset_sum, localDirectSumBlock_finset_sum]

lemma ev_roleRegisterSymmState_point_postprocessedLine_outcome
    {α β ιA ιB : Type*}
    [Inhabited α] [Inhabited β] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (PA : ProjMeas β ιA) (PB : ProjMeas β ιB)
    (LA : ProjMeas α ιA) (LB : ProjMeas α ιB)
    (f : α → β) (b : β) :
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas PA PB).outcome b)
          ((postprocess ((roleRegisterProjMeas LA LB).toSubMeas) f).outcome b)) =
      (1 / 2 : Error) *
          ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
        (1 / 2 : Error) *
          ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b)) := by
  let fillerAβ : ProjMeas β ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerBβ : ProjMeas β ιB := ProjMeas.trivialDistinguishedOutcome default
  rw [postprocess_roleRegisterProjMeas_outcome]
  change ev (roleRegisterSymmState ψ)
      (opTensor
        (roleBlock (localDirectSumBlock (PA.outcome b) (fillerBβ.outcome b))
          (localDirectSumBlock (fillerAβ.outcome b) (PB.outcome b)))
        (roleBlock
          (localDirectSumBlock ((ProjMeas.postprocess LA f).outcome b)
            ((ProjMeas.postprocess
              (ProjMeas.trivialDistinguishedOutcome (ι := ιB) (default : α)) f).outcome b))
          (localDirectSumBlock
            ((ProjMeas.postprocess
              (ProjMeas.trivialDistinguishedOutcome (ι := ιA) (default : α)) f).outcome b)
            ((ProjMeas.postprocess LB f).outcome b)))) =
    (1 / 2 : Error) *
        ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
      (1 / 2 : Error) *
        ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b))
  exact ev_roleRegisterSymmState_roleBlock_localDirectSumBlocks ψ
    (PA.outcome b) ((ProjMeas.postprocess LA f).outcome b)
    (fillerAβ.outcome b)
    ((ProjMeas.postprocess
      (ProjMeas.trivialDistinguishedOutcome (ι := ιA) (default : α)) f).outcome b)
    (PB.outcome b) ((ProjMeas.postprocess LB f).outcome b)
    (fillerBβ.outcome b)
    ((ProjMeas.postprocess
      (ProjMeas.trivialDistinguishedOutcome (ι := ιB) (default : α)) f).outcome b)

lemma qBipartiteMatchMass_roleRegister_point_postprocessedLine_eq_average
    {α β ιA ιB : Type*}
    [Inhabited α] [Inhabited β] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (PA : ProjMeas β ιA) (PB : ProjMeas β ιB)
    (LA : ProjMeas α ιA) (LB : ProjMeas α ιB) (f : α → β) :
    qBipartiteMatchMass (roleRegisterSymmState ψ)
        (roleRegisterProjMeas PA PB).toSubMeas
        ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) =
      (qBipartiteMatchMass ψ PA.toSubMeas (ProjMeas.postprocess LB f).toSubMeas +
        qBipartiteMatchMass ψ (ProjMeas.postprocess LA f).toSubMeas PB.toSubMeas) / 2 := by
  unfold qBipartiteMatchMass
  calc
    ∑ b : β,
        ev (roleRegisterSymmState ψ)
          (opTensor ((roleRegisterProjMeas PA PB).outcome b)
            (((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas).outcome b))
      = ∑ b : β,
          ((1 / 2 : Error) *
              ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
            (1 / 2 : Error) *
              ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b))) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            exact ev_roleRegisterSymmState_point_postprocessedLine_outcome
              ψ PA PB LA LB f b
    _ = (1 / 2 : Error) *
          ∑ b : β, ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
        (1 / 2 : Error) *
          ∑ b : β, ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ =
        (∑ b : β, ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
          ∑ b : β, ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b)
            (PB.outcome b))) / 2 := by
          ring

lemma qBipartiteConsDefect_roleRegister_point_postprocessedLine_eq_average
    {α β ιA ιB : Type*}
    [Inhabited α] [Inhabited β] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (PA : ProjMeas β ιA) (PB : ProjMeas β ιB)
    (LA : ProjMeas α ιA) (LB : ProjMeas α ιB) (f : α → β) :
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas PA PB).toSubMeas
        ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) =
      (qBipartiteConsDefect ψ PA.toSubMeas (ProjMeas.postprocess LB f).toSubMeas +
        qBipartiteConsDefect ψ (ProjMeas.postprocess LA f).toSubMeas PB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas PA PB).toSubMeas
        ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas)
      = ev (roleRegisterSymmState ψ)
          (1 : MIPStarRE.Quantum.Op
            (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas PA PB).toSubMeas
            ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) := by
            exact qBipartiteConsDefect_of_measurements (roleRegisterSymmState ψ)
              (roleRegisterProjMeas PA PB).toMeasurement
              (ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toMeasurement
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas PA PB).toSubMeas
            ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) := by
            rw [ev_one_of_isNormalized (roleRegisterSymmState ψ)
              (roleRegisterSymmState_isNormalized ψ hψ), ev_one_of_isNormalized ψ hψ]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          ((qBipartiteMatchMass ψ PA.toSubMeas
              (ProjMeas.postprocess LB f).toSubMeas +
            qBipartiteMatchMass ψ (ProjMeas.postprocess LA f).toSubMeas
              PB.toSubMeas) / 2) := by
            rw [qBipartiteMatchMass_roleRegister_point_postprocessedLine_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ PA.toSubMeas
              (ProjMeas.postprocess LB f).toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ (ProjMeas.postprocess LA f).toSubMeas
              PB.toSubMeas)) / 2 := by
            ring
    _ = (qBipartiteConsDefect ψ PA.toSubMeas
            (ProjMeas.postprocess LB f).toSubMeas +
          qBipartiteConsDefect ψ (ProjMeas.postprocess LA f).toSubMeas
            PB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ PA.toMeasurement
              (ProjMeas.postprocess LB f).toMeasurement]
            rw [← qBipartiteConsDefect_of_measurements ψ
              (ProjMeas.postprocess LA f).toMeasurement PB.toMeasurement]

lemma qBipartiteMatchMass_roleRegisterProjMeas_eq_average
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA NA : ProjMeas Outcome ιA) (MB NB : ProjMeas Outcome ιB) :
    qBipartiteMatchMass (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
        (roleRegisterProjMeas NA NB).toSubMeas =
      (qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome,
        ev (roleRegisterSymmState ψ)
          (opTensor ((roleRegisterProjMeas MA MB).outcome a)
            ((roleRegisterProjMeas NA NB).outcome a))
      = ∑ a : Outcome,
          ((1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact ev_roleRegisterSymmState_roleRegisterProjMeas_outcome ψ MA NA MB NB a
    _ = (1 / 2 : Error) *
          ∑ a : Outcome, ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
        (1 / 2 : Error) *
          ∑ a : Outcome, ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ =
        (∑ a : Outcome, ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
          ∑ a : Outcome, ev ψ (opTensor (NA.outcome a) (MB.outcome a))) / 2 := by
          ring

lemma qBipartiteConsDefect_roleRegisterProjMeas_eq_average
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA NA : ProjMeas Outcome ιA) (MB NB : ProjMeas Outcome ιB) :
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
        (roleRegisterProjMeas NA NB).toSubMeas =
      (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
        (roleRegisterProjMeas NA NB).toSubMeas
      = ev (roleRegisterSymmState ψ)
          (1 : MIPStarRE.Quantum.Op
            (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas MA MB).toSubMeas
            (roleRegisterProjMeas NA NB).toSubMeas := by
            exact qBipartiteConsDefect_of_measurements (roleRegisterSymmState ψ)
              (roleRegisterProjMeas MA MB).toMeasurement
              (roleRegisterProjMeas NA NB).toMeasurement
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas MA MB).toSubMeas
            (roleRegisterProjMeas NA NB).toSubMeas := by
            rw [ev_one_of_isNormalized (roleRegisterSymmState ψ)
              (roleRegisterSymmState_isNormalized ψ hψ), ev_one_of_isNormalized ψ hψ]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          ((qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2) := by
            rw [qBipartiteMatchMass_roleRegisterProjMeas_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas)) / 2 := by
            ring
    _ = (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
          qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ MA.toMeasurement NB.toMeasurement]
            rw [← qBipartiteConsDefect_of_measurements ψ NA.toMeasurement MB.toMeasurement]

lemma qBipartiteSSCDefect_roleRegisterProjMeas_eq_cons
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    qBipartiteSSCDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas =
      qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas := by
  calc
    qBipartiteSSCDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
      = qBipartiteConsDefect (roleRegisterSymmState ψ)
          (roleRegisterProjMeas MA MB).toSubMeas
          (roleRegisterProjMeas MA MB).toSubMeas := by
          simp [qBipartiteSSCDefect, qBipartiteConsDefect, qBipartiteMatchMass,
            (roleRegisterProjMeas MA MB).total_eq_one, leftTensor, opTensor]
    _ = (qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas +
          qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas) / 2 := by
          rw [qBipartiteConsDefect_roleRegisterProjMeas_eq_average ψ hψ MA MA MB MB]
    _ = qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas := by
          ring

lemma axisParallel_roleRegister_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (strategy : ProjStrat params ιA ιB) (s : AxisParallelTestSample params) :
    qBipartiteConsDefect (strategy.roleRegisterSymmStrategy.state)
        (axisParallelPointAnswerFamily strategy.roleRegisterSymmStrategy s)
        (axisParallelLineAnswerFamily strategy.roleRegisterSymmStrategy s) =
      (qBipartiteConsDefect strategy.state
          (axisParallelPointAnswerFamilyA strategy s)
          (axisParallelLineAnswerFamilyB strategy s) +
        qBipartiteConsDefect strategy.state
          (axisParallelLineAnswerFamilyA strategy s)
          (axisParallelPointAnswerFamilyB strategy s)) / 2 := by
  let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
  have h := qBipartiteConsDefect_roleRegister_point_postprocessedLine_eq_average
    strategy.state strategy.isNormalized
    (strategy.pointMeasurementA s.1) (strategy.pointMeasurementB s.1)
    (strategy.axisParallelMeasurementA ℓ) (strategy.axisParallelMeasurementB ℓ)
    (fun p : AxisLinePolynomial params => p zeroCoord)
  simpa [SymStrat.axisParallelFailureProbability, roleRegisterSymmStrategy,
    axisParallelPointAnswerFamily, axisParallelLineAnswerFamily,
    axisParallelPointAnswerFamilyOf, axisParallelLineAnswerFamilyOf,
    roleRegisterPointMeasurement, roleRegisterAxisParallelMeasurement,
    axisParallelPointAnswerFamilyA, axisParallelPointAnswerFamilyB,
    axisParallelLineAnswerFamilyA, axisParallelLineAnswerFamilyB, ℓ,
    ProjMeas.postprocess_toSubMeas, add_comm] using h

lemma diagonal_roleRegister_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (strategy : ProjStrat params ιA ιB)
    (j : Fin params.m) (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect (strategy.roleRegisterSymmStrategy.state)
        (diagonalPointAnswerFamily strategy.roleRegisterSymmStrategy j s)
        (diagonalLineAnswerFamily strategy.roleRegisterSymmStrategy j s) =
      (qBipartiteConsDefect strategy.state
          (diagonalPointAnswerFamilyA strategy j s)
          (diagonalLineAnswerFamilyB strategy j s) +
        qBipartiteConsDefect strategy.state
          (diagonalLineAnswerFamilyA strategy j s)
          (diagonalPointAnswerFamilyB strategy j s)) / 2 := by
  let v := extendRestrictedDirection j s.2
  let ℓ : DiagonalLine params := { base := s.1, direction := v }
  have h := qBipartiteConsDefect_roleRegister_point_postprocessedLine_eq_average
    strategy.state strategy.isNormalized
    (strategy.pointMeasurementA s.1) (strategy.pointMeasurementB s.1)
    (strategy.diagonalMeasurementA ℓ) (strategy.diagonalMeasurementB ℓ)
    (fun p : DiagonalLinePolynomial params => p zeroCoord)
  simpa [roleRegisterSymmStrategy, diagonalPointAnswerFamily, diagonalLineAnswerFamily,
    diagonalPointAnswerFamilyOf, diagonalLineAnswerFamilyOf,
    roleRegisterPointMeasurement, roleRegisterDiagonalMeasurement,
    diagonalPointAnswerFamilyA, diagonalPointAnswerFamilyB,
    diagonalLineAnswerFamilyA, diagonalLineAnswerFamilyB, v, ℓ,
    ProjMeas.postprocess_toSubMeas, add_comm] using h

end ProjStrat

end MIPStarRE.LDT


