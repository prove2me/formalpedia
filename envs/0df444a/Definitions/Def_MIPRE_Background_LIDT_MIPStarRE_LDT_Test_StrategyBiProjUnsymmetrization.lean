-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:10:52.144881+00:00
-- url     : https://prove2.me/theorems/ac0899c0-16b6-4c9b-914c-c39cc1f91995
-- title:
--   Definitions of StrategyBiProjUnsymmetrization: Heterogeneous role-register measurement extraction This file contains the principal-block extraction used to…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Heterogeneous role-register measurement extraction. This file contains the principal-block extraction used to unsymmetrize a measurement on the heterogeneous role-register space `Role × (ιA ⊕ ιB)`. The Alice extraction is the block indexed by `(Role.A, Sum.inl _)`; the Bob extraction is the block indexed by `(Role.B, Sum.inr _)`. These are the two-space analogues of the same-space extractions in `MIPStarRE.LDT.Test.Unsymmetrization`. They preserve POVM completeness, but they do not assert that arbitrary principal blocks of a projective measurement remain projective. As in the paper proof,…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (10): `MIPStarRE.LDT.Measurement.extractRoleRegisterAlice` (Extract Alice's original local block from a measurement on the heterogeneous role-register space.); `MIPStarRE.LDT.Measurement.extractRoleRegisterBob` (Extract Bob's original local block from a measurement on the heterogeneous role-register space.); `MIPStarRE.LDT.ProjStrat.extractRoleRegisterAliceBlock` (Alice's principal block of an operator on the heterogeneous role-register space, indexed by `(Role.A, Sum.inl _)`.); `MIPStarRE.LDT.ProjStrat.extractRoleRegisterBobBlock` (Bob's principal block of an operator on the heterogeneous role-register space, indexed by `(Role.B, Sum.inr _)`.); `MIPStarRE.LDT.SubMeas.extractRoleRegisterAlice` (Extract Alice's original local block from a submeasurement on the heterogeneous role-register space.); `MIPStarRE.LDT.SubMeas.extractRoleRegisterBob` (Extract Bob's original local block from a submeasurement on the heterogeneous role-register space.); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization.0.MIPStarRE.LDT.ProjStrat.localPairABEmbedding` (The local-sector embedding selecting the Alice--Bob tensor summand.); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization.0.MIPStarRE.LDT.ProjStrat.localPairBAEmbedding` (The local-sector embedding selecting the Bob--Alice tensor summand.); and 0 more.
--
--   **Embedded lemmas** (40): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `extractRoleRegisterAlice_outcome`, `extractRoleRegisterAlice_toSubMeas`, `extractRoleRegisterBob_outcome`, `extractRoleRegisterBob_toSubMeas`, `extractRoleRegisterAliceBlock_add`, `extractRoleRegisterAliceBlock_apply`, `extractRoleRegisterAliceBlock_finset_sum`, `extractRoleRegisterAliceBlock_le`, `extractRoleRegisterAliceBlock_nonneg`, `extractRoleRegisterAliceBlock_one`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProjRoleAverage_Core
import Theorems.Thm_MIPStarRE_Quantum_normalizedTrace_add
import Theorems.Thm_MIPStarRE_Quantum_normalizedTrace_smul
import Theorems.Thm_Matrix_trace_reindex

set_option backward.isDefEq.respectTransparency false

/-!
# Heterogeneous role-register measurement extraction

This file contains the principal-block extraction used to unsymmetrize a
measurement on the heterogeneous role-register space
`Role × (ιA ⊕ ιB)`.  The Alice extraction is the block indexed by
`(Role.A, Sum.inl _)`; the Bob extraction is the block indexed by
`(Role.B, Sum.inr _)`.

These are the two-space analogues of the same-space extractions in
`MIPStarRE.LDT.Test.Unsymmetrization`.  They preserve POVM completeness, but
they do not assert that arbitrary principal blocks of a projective measurement
remain projective.  As in the paper proof, projectivity is restored later by
the projectivization step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 84--109.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace ProjStrat

/-! ### Principal blocks of heterogeneous role-register operators -/

/-- Alice's principal block of an operator on the heterogeneous role-register
space, indexed by `(Role.A, Sum.inl _)`. -/
noncomputable def extractRoleRegisterAliceBlock {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    MIPStarRE.Quantum.Op ιA :=
  Y.submatrix (fun i => (Role.A, Sum.inl i)) (fun i => (Role.A, Sum.inl i))

/-- Bob's principal block of an operator on the heterogeneous role-register
space, indexed by `(Role.B, Sum.inr _)`. -/
noncomputable def extractRoleRegisterBobBlock {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    MIPStarRE.Quantum.Op ιB :=
  Y.submatrix (fun i => (Role.B, Sum.inr i)) (fun i => (Role.B, Sum.inr i))

@[simp] theorem extractRoleRegisterAliceBlock_apply {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) (i j : ιA) :
    extractRoleRegisterAliceBlock Y i j = Y (Role.A, Sum.inl i) (Role.A, Sum.inl j) :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_apply {ιA ιB : Type*}
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) (i j : ιB) :
    extractRoleRegisterBobBlock Y i j = Y (Role.B, Sum.inr i) (Role.B, Sum.inr j) :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_zero {ιA ιB : Type*} :
    extractRoleRegisterAliceBlock (ιA := ιA) (ιB := ιB) 0 = 0 :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_zero {ιA ιB : Type*} :
    extractRoleRegisterBobBlock (ιA := ιA) (ιB := ιB) 0 = 0 :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_add {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (X + Y) =
      extractRoleRegisterAliceBlock X + extractRoleRegisterAliceBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_add {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (X + Y) =
      extractRoleRegisterBobBlock X + extractRoleRegisterBobBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_sub {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (X - Y) =
      extractRoleRegisterAliceBlock X - extractRoleRegisterAliceBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_sub {ιA ιB : Type*}
    (X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (X - Y) =
      extractRoleRegisterBobBlock X - extractRoleRegisterBobBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_smul {ιA ιB : Type*}
    (c : ℂ) (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (c • Y) = c • extractRoleRegisterAliceBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterBobBlock_smul {ιA ιB : Type*}
    (c : ℂ) (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (c • Y) = c • extractRoleRegisterBobBlock Y :=
  rfl

@[simp] theorem extractRoleRegisterAliceBlock_finset_sum {α ιA ιB : Type*}
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (∑ a ∈ s, f a) =
      ∑ a ∈ s, extractRoleRegisterAliceBlock (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

@[simp] theorem extractRoleRegisterBobBlock_finset_sum {α ιA ιB : Type*}
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (∑ a ∈ s, f a) =
      ∑ a ∈ s, extractRoleRegisterBobBlock (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

@[simp] theorem extractRoleRegisterAliceBlock_univ_sum {α ιA ιB : Type*}
    [Fintype α] (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterAliceBlock (∑ a, f a) =
      ∑ a, extractRoleRegisterAliceBlock (f a) := by
  exact extractRoleRegisterAliceBlock_finset_sum Finset.univ f

@[simp] theorem extractRoleRegisterBobBlock_univ_sum {α ιA ιB : Type*}
    [Fintype α] (f : α → MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    extractRoleRegisterBobBlock (∑ a, f a) =
      ∑ a, extractRoleRegisterBobBlock (f a) := by
  exact extractRoleRegisterBobBlock_finset_sum Finset.univ f

@[simp] theorem extractRoleRegisterAliceBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    extractRoleRegisterAliceBlock
      (1 : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

@[simp] theorem extractRoleRegisterBobBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    extractRoleRegisterBobBlock
      (1 : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- Alice principal blocks preserve positive semidefiniteness. -/
theorem extractRoleRegisterAliceBlock_nonneg {ιA ιB : Type*}
    {Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hY : 0 ≤ Y) :
    0 ≤ extractRoleRegisterAliceBlock Y := by
  exact Matrix.nonneg_iff_posSemidef.mpr <|
    (Matrix.nonneg_iff_posSemidef.mp hY).submatrix (fun i => (Role.A, Sum.inl i))

/-- Bob principal blocks preserve positive semidefiniteness. -/
theorem extractRoleRegisterBobBlock_nonneg {ιA ιB : Type*}
    {Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hY : 0 ≤ Y) :
    0 ≤ extractRoleRegisterBobBlock Y := by
  exact Matrix.nonneg_iff_posSemidef.mpr <|
    (Matrix.nonneg_iff_posSemidef.mp hY).submatrix (fun i => (Role.B, Sum.inr i))

/-- Alice principal blocks are monotone for the matrix order. -/
theorem extractRoleRegisterAliceBlock_le {ιA ιB : Type*}
    {X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hXY : X ≤ Y) :
    extractRoleRegisterAliceBlock X ≤ extractRoleRegisterAliceBlock Y := by
  rw [Matrix.le_iff] at hXY ⊢
  simpa [extractRoleRegisterAliceBlock, extractRoleRegisterAliceBlock_sub,
    Matrix.submatrix_sub] using
    hXY.submatrix (fun i : ιA => (Role.A, Sum.inl i))

/-- Bob principal blocks are monotone for the matrix order. -/
theorem extractRoleRegisterBobBlock_le {ιA ιB : Type*}
    {X Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)} (hXY : X ≤ Y) :
    extractRoleRegisterBobBlock X ≤ extractRoleRegisterBobBlock Y := by
  rw [Matrix.le_iff] at hXY ⊢
  simpa [extractRoleRegisterBobBlock, extractRoleRegisterBobBlock_sub,
    Matrix.submatrix_sub] using
    hXY.submatrix (fun i : ιB => (Role.B, Sum.inr i))

end ProjStrat

namespace SubMeas

/-- Extract Alice's original local block from a submeasurement on the
heterogeneous role-register space. -/
noncomputable def extractRoleRegisterAlice {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) : SubMeas α ιA where
  outcome := fun a => ProjStrat.extractRoleRegisterAliceBlock (A.outcome a)
  total := ProjStrat.extractRoleRegisterAliceBlock A.total
  outcome_pos := fun a => ProjStrat.extractRoleRegisterAliceBlock_nonneg (A.outcome_pos a)
  sum_eq_total := (ProjStrat.extractRoleRegisterAliceBlock_univ_sum A.outcome).symm.trans
      (congrArg ProjStrat.extractRoleRegisterAliceBlock A.sum_eq_total)
  total_le_one := (ProjStrat.extractRoleRegisterAliceBlock_le A.total_le_one).trans_eq
      ProjStrat.extractRoleRegisterAliceBlock_one

/-- Extract Bob's original local block from a submeasurement on the
heterogeneous role-register space. -/
noncomputable def extractRoleRegisterBob {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) : SubMeas α ιB where
  outcome := fun a => ProjStrat.extractRoleRegisterBobBlock (A.outcome a)
  total := ProjStrat.extractRoleRegisterBobBlock A.total
  outcome_pos := fun a => ProjStrat.extractRoleRegisterBobBlock_nonneg (A.outcome_pos a)
  sum_eq_total := (ProjStrat.extractRoleRegisterBobBlock_univ_sum A.outcome).symm.trans
      (congrArg ProjStrat.extractRoleRegisterBobBlock A.sum_eq_total)
  total_le_one := (ProjStrat.extractRoleRegisterBobBlock_le A.total_le_one).trans_eq
      ProjStrat.extractRoleRegisterBobBlock_one

@[simp] theorem extractRoleRegisterAlice_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterAlice).outcome a =
      ProjStrat.extractRoleRegisterAliceBlock (A.outcome a) :=
  rfl

@[simp] theorem extractRoleRegisterBob_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterBob).outcome a =
      ProjStrat.extractRoleRegisterBobBlock (A.outcome a) :=
  rfl

@[simp] theorem extractRoleRegisterAlice_total {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterAlice).total = ProjStrat.extractRoleRegisterAliceBlock A.total :=
  rfl

@[simp] theorem extractRoleRegisterBob_total {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterBob).total = ProjStrat.extractRoleRegisterBobBlock A.total :=
  rfl

end SubMeas

namespace Measurement

/-- Extract Alice's original local block from a measurement on the heterogeneous
role-register space. -/
noncomputable def extractRoleRegisterAlice {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) : Measurement α ιA where
  toSubMeas := A.toSubMeas.extractRoleRegisterAlice
  total_eq_one := (congrArg ProjStrat.extractRoleRegisterAliceBlock A.total_eq_one).trans
      ProjStrat.extractRoleRegisterAliceBlock_one

/-- Extract Bob's original local block from a measurement on the heterogeneous
role-register space. -/
noncomputable def extractRoleRegisterBob {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) : Measurement α ιB where
  toSubMeas := A.toSubMeas.extractRoleRegisterBob
  total_eq_one := (congrArg ProjStrat.extractRoleRegisterBobBlock A.total_eq_one).trans
      ProjStrat.extractRoleRegisterBobBlock_one

@[simp] theorem extractRoleRegisterAlice_toSubMeas {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterAlice).toSubMeas = A.toSubMeas.extractRoleRegisterAlice :=
  rfl

@[simp] theorem extractRoleRegisterBob_toSubMeas {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) :
    (A.extractRoleRegisterBob).toSubMeas = A.toSubMeas.extractRoleRegisterBob :=
  rfl

@[simp] theorem extractRoleRegisterAlice_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterAlice).outcome a =
      ProjStrat.extractRoleRegisterAliceBlock (A.outcome a) :=
  rfl

@[simp] theorem extractRoleRegisterBob_outcome {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Measurement α (ProjStrat.RoleRegisterLocal ιA ιB)) (a : α) :
    (A.extractRoleRegisterBob).outcome a =
      ProjStrat.extractRoleRegisterBobBlock (A.outcome a) :=
  rfl

end Measurement

namespace ProjStrat

/-! ### Extraction on the constructed role-register measurements -/

/-! ### Trace compression for occupied role-register sectors -/

lemma trace_single_tensor_mul_eq_trace_submatrix {β α : Type*}
    [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α]
    (b : β) (X : MIPStarRE.Quantum.Op α)
    (Y : MIPStarRE.Quantum.Op (β × α)) :
    Matrix.trace (opTensor (Matrix.single b b (1 : ℂ)) X * Y) =
      Matrix.trace (X * Y.submatrix (fun i : α => (b, i)) (fun i : α => (b, i))) := by
  classical
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  calc
    ∑ x : β, ∑ y : α, ∑ x_1 : β, ∑ y_1 : α,
        Matrix.single b b (1 : ℂ) x x_1 * X y y_1 * Y (x_1, y_1) (x, y)
      = ∑ x : β, ∑ y : α, ∑ y_1 : α,
        Matrix.single b b (1 : ℂ) x b * X y y_1 * Y (b, y_1) (x, y) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [Fintype.sum_eq_single b (by
            intro x_1 hx
            have hx' : b ≠ x_1 := fun h => hx h.symm
            simp [Matrix.single, hx'])]
    _ = ∑ y : α, ∑ y_1 : α, X y y_1 * Y (b, y_1) (b, y) := by
          rw [Fintype.sum_eq_single b (by
            intro x hx
            have hx' : b ≠ x := fun h => hx h.symm
            simp [Matrix.single, hx'])]
          simp [Matrix.single]
    _ = ∑ y : α, ∑ y_1 : α, X y y_1 * Y (b, y_1) (b, y) := rfl

lemma rolePairProj_eq_single_pair (rL rR : Role) :
    rolePairProj rL rR = Matrix.single (rL, rR) (rL, rR) (1 : ℂ) := by
  ext p q
  rcases p with ⟨pL, pR⟩
  rcases q with ⟨qL, qR⟩
  cases rL <;> cases rR <;> cases pL <;> cases pR <;> cases qL <;> cases qR <;>
    simp [rolePairProj, roleProj, opTensor]

/-- The local-sector embedding selecting the Alice--Bob tensor summand. -/
def localPairABEmbedding {ιA ιB : Type*} :
    ιA × ιB → LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB :=
  fun z => (Sum.inl z.1, Sum.inr z.2)

/-- The local-sector embedding selecting the Bob--Alice tensor summand. -/
def localPairBAEmbedding {ιA ιB : Type*} :
    ιB × ιA → LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB :=
  fun z => (Sum.inr z.1, Sum.inl z.2)

/-- The role-sector embedding selecting the `rL,rR` block. -/
def rolePairSectorEmbedding {ιA ιB : Type*} (rL rR : Role) :
    LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB →
      RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB :=
  fun z => ((rL, z.1), (rR, z.2))

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

lemma trace_rolePairDirectSumCond_mul {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB))
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) :
    Matrix.trace (rolePairDirectSumCond rL rR X * Y) =
      Matrix.trace (X * Y.submatrix
        (rolePairSectorEmbedding rL rR) (rolePairSectorEmbedding rL rR)) := by
  classical
  let e := roleRegisterPairLocalEquiv ιA ιB
  let Y' : MIPStarRE.Quantum.Op
      ((Role × Role) × (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :=
    Matrix.reindex e.symm e.symm Y
  have hY : Y = Matrix.reindex e e Y' := by
    ext x y
    simp [Y', e]
  rw [hY]
  unfold rolePairDirectSumCond
  change Matrix.trace ((Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) Y') = _
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)]
  simp only [Matrix.coe_reindexAlgEquiv]
  rw [Matrix.trace_reindex]
  rw [rolePairProj_eq_single_pair]
  rw [trace_single_tensor_mul_eq_trace_submatrix]
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

lemma trace_localPairABBlock_mul_arbitrary {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB))
    (Y : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    Matrix.trace (localPairABBlock X * Y) =
      Matrix.trace (X * Y.submatrix
        localPairABEmbedding localPairABEmbedding) := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [localPairABBlock, localPairABEmbedding]

lemma trace_localPairBABlock_mul_arbitrary {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA))
    (Y : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    Matrix.trace (localPairBABlock X * Y) =
      Matrix.trace (X * Y.submatrix
        localPairBAEmbedding localPairBAEmbedding) := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [localPairBABlock, localPairBAEmbedding]

noncomputable def roleRegisterRoleLocalBlock {ιA ιB : Type*}
    (r : Role) (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB) :=
  Y.submatrix (fun i => (r, i)) (fun i => (r, i))

lemma opTensor_localDirectSum_roleLocalBlock_AB_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor (localDirectSumBlock A Bfill) (roleRegisterRoleLocalBlock Role.B Y)).submatrix
      localPairABEmbedding localPairABEmbedding =
    opTensor A (extractRoleRegisterBobBlock Y) := by
  ext z w
  simp [localPairABEmbedding, roleRegisterRoleLocalBlock,
    extractRoleRegisterBobBlock, opTensor]

lemma opTensor_localDirectSum_roleLocalBlock_BA_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (Afill : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor (localDirectSumBlock Afill B) (roleRegisterRoleLocalBlock Role.A Y)).submatrix
      localPairBAEmbedding localPairBAEmbedding =
    opTensor B (extractRoleRegisterAliceBlock Y) := by
  ext z w
  simp [localPairBAEmbedding, roleRegisterRoleLocalBlock,
    extractRoleRegisterAliceBlock, opTensor]

lemma opTensor_roleBlock_roleRegister_AB_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A Afill : MIPStarRE.Quantum.Op ιA) (B Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor
        (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
        Y).submatrix
      (rolePairSectorEmbedding Role.A Role.B) (rolePairSectorEmbedding Role.A Role.B) =
      opTensor (localDirectSumBlock A Bfill) (roleRegisterRoleLocalBlock Role.B Y) := by
  ext z w
  simp [rolePairSectorEmbedding, roleRegisterRoleLocalBlock, opTensor]

lemma opTensor_roleBlock_roleRegister_BA_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A Afill : MIPStarRE.Quantum.Op ιA) (B Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor
        (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
        Y).submatrix
      (rolePairSectorEmbedding Role.B Role.A) (rolePairSectorEmbedding Role.B Role.A) =
      opTensor (localDirectSumBlock Afill B) (roleRegisterRoleLocalBlock Role.A Y) := by
  ext z w
  simp [rolePairSectorEmbedding, roleRegisterRoleLocalBlock, opTensor]

lemma trace_heterogeneousSwapDensity_mul_opTensor {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    Matrix.trace (heterogeneousSwapDensity X * opTensor B A) =
      Matrix.trace (X * opTensor A B) := by
  rw [← heterogeneousSwapDensity_opTensor]
  rw [← heterogeneousSwapDensity_mul]
  unfold heterogeneousSwapDensity
  rw [Matrix.trace_reindex]

lemma ev_roleRegisterSymmState_roleBlock_arbitrary
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A Afill : MIPStarRE.Quantum.Op ιA) (B Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    ev (roleRegisterSymmState ψ)
        (opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          Y) =
      (1 / 2 : Error) * ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) +
        (1 / 2 : Error) * ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace
      (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          Y)) =
    (1 / 2 : Error) * ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) +
      (1 / 2 : Error) * ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [trace_rolePairDirectSumCond_mul]
  rw [opTensor_roleBlock_roleRegister_AB_submatrix]
  rw [trace_localPairABBlock_mul_arbitrary]
  rw [opTensor_localDirectSum_roleLocalBlock_AB_submatrix]
  rw [trace_rolePairDirectSumCond_mul]
  rw [opTensor_roleBlock_roleRegister_BA_submatrix]
  rw [trace_localPairBABlock_mul_arbitrary]
  rw [opTensor_localDirectSum_roleLocalBlock_BA_submatrix]
  rw [trace_heterogeneousSwapDensity_mul_opTensor]
  let T₁ : ℂ :=
    Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)) /
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))
  let T₂ : ℂ :=
    Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B) /
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscale (T : ℂ) :
      (roleRegisterDensityScale ιA ιB : ℂ) *
          (T / (Fintype.card (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) : ℂ)) =
        (1 / 2 : ℂ) *
          (T / ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))) := by
    unfold roleRegisterDensityScale RoleRegisterLocal
    rw [Fintype.card_prod, Fintype.card_prod]
    have hRole : Fintype.card Role = 2 := by decide
    rw [hRole]
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
  rw [show ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) = Complex.re T₁ by
    unfold ev MIPStarRE.Quantum.normalizedTrace
    rw [Fintype.card_prod]
    norm_num [Nat.cast_mul]
    rfl]
  rw [show ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B) = Complex.re T₂ by
    unfold ev MIPStarRE.Quantum.normalizedTrace
    rw [Fintype.card_prod]
    norm_num [Nat.cast_mul]
    rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) *
        (Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)) /
          (Fintype.card (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) : ℂ)) =
      (1 / 2 : ℂ) * T₁ by
    subst T₁
    exact hscale (Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)))]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) *
        (Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B) /
          (Fintype.card (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) : ℂ)) =
      (1 / 2 : ℂ) * T₂ by
    subst T₂
    exact hscale (Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B))]
  norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

lemma ev_roleRegisterSymmState_roleRegisterProjMeas_arbitrary_outcome
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (G : Measurement Outcome (RoleRegisterLocal ιA ιB)) (a : Outcome) :
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas MA MB).outcome a) (G.outcome a)) =
      (1 / 2 : Error) *
          ev ψ (opTensor (MA.outcome a) ((G.extractRoleRegisterBob).outcome a)) +
        (1 / 2 : Error) *
          ev ψ (opTensor ((G.extractRoleRegisterAlice).outcome a) (MB.outcome a)) := by
  let fillerA : ProjMeas Outcome ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerB : ProjMeas Outcome ιB := ProjMeas.trivialDistinguishedOutcome default
  change ev (roleRegisterSymmState ψ)
      (opTensor
        (roleBlock
          (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
          (localDirectSumBlock (fillerA.outcome a) (MB.outcome a)))
        (G.outcome a)) =
    (1 / 2 : Error) *
        ev ψ (opTensor (MA.outcome a) (extractRoleRegisterBobBlock (G.outcome a))) +
      (1 / 2 : Error) *
        ev ψ (opTensor (extractRoleRegisterAliceBlock (G.outcome a)) (MB.outcome a))
  exact ev_roleRegisterSymmState_roleBlock_arbitrary ψ
    (MA.outcome a) (fillerA.outcome a) (MB.outcome a) (fillerB.outcome a) (G.outcome a)

end ProjStrat

end MIPStarRE.LDT


