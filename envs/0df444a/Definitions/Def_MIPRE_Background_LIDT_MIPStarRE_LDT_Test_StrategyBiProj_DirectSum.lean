-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:05:48.492991+00:00
-- url     : https://prove2.me/theorems/29b266d0-c967-41b9-9fee-2362badc8c2c
-- title:
--   Definitions of DirectSum: Two-Space Projective Strategies: Direct-Sum State Blocks This module contains the role-register direct-sum carriers and…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProj.DirectSum` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Two-Space Projective Strategies: Direct-Sum State Blocks. This module contains the role-register direct-sum carriers and block-state construction used to symmetrize a heterogeneous projective strategy.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (13): `MIPStarRE.LDT.ProjStrat.LocalCarrierSum` (Direct-sum carrier for the future heterogeneous role symmetrization.); `MIPStarRE.LDT.ProjStrat.RoleRegisterLocal` (Local carrier planned for the heterogeneous symmetrization bridge: a role bit and a direct-sum carrier.); `MIPStarRE.LDT.ProjStrat.heterogeneousSwapDensity` (Swap an operator on `ιA × ιB` to one on `ιB × ιA`.); `MIPStarRE.LDT.ProjStrat.localDirectSumBlock` (Block-diagonal operator on `ιA ⊕ ιB`, with Alice's block in the `Sum.inl` sector and Bob's block in the `Sum.inr` sector.); `MIPStarRE.LDT.ProjStrat.localPairABBlock` (Embed an operator on Alice's and Bob's original tensor product into the `(Sum.inl _) × (Sum.inr _)` block of the direct-sum tensor product.); `MIPStarRE.LDT.ProjStrat.localPairBABlock` (Embed an operator on Bob's and Alice's original tensor product into the `(Sum.inr _) × (Sum.inl _)` block of the direct-sum tensor product.); `MIPStarRE.LDT.ProjStrat.roleBlock` (Role-blocked operator on `Role × (ιA ⊕ ιB)`.); `MIPStarRE.LDT.ProjStrat.rolePairDirectSumCond` (Place a direct-sum bipartite operator in a chosen pair of role sectors.); `MIPStarRE.LDT.ProjStrat.roleRegisterDensityScale` (Normalizing scalar for the direct-sum heterogeneous role-register state.); `MIPStarRE.LDT.ProjStrat.roleRegisterPairLocalEquiv` (Reassociate role bits and direct-sum carriers.); `MIPStarRE.LDT.ProjStrat.roleRegisterSymmState` (Heterogeneous role-register symmetrization of a two-space bipartite state.); and -6 more.
--
--   **Embedded lemmas** (40): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `heterogeneousSwapDensity_mul`, `heterogeneousSwapDensity_nonneg`, `heterogeneousSwapDensity_opTensor`, `localDirectSumBlock_add`, `localDirectSumBlock_conjTranspose`, `localDirectSumBlock_inl_inl`, `localDirectSumBlock_inl_inr`, `localDirectSumBlock_inr_inl`, `localDirectSumBlock_inr_inr`, `localDirectSumBlock_mul`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProj.DirectSum` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProj/DirectSum.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 21 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProj/DirectSum.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/StrategyBiProj/DirectSum.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/StrategyBiProj/DirectSum.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPStarRE_LDT_opTensor_mul
import Theorems.Thm_MIPStarRE_LDT_rolePairProj_nonneg
import Theorems.Thm_MIPStarRE_Quantum_reindex_nonneg

set_option backward.isDefEq.respectTransparency false

/-!
# Two-Space Projective Strategies: Direct-Sum State Blocks

This module contains the role-register direct-sum carriers and block-state
construction used to symmetrize a heterogeneous projective strategy.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat

/-! ### Direct-sum role-register helpers -/

/-- Direct-sum carrier for the future heterogeneous role symmetrization.

For a two-space strategy with Alice carrier `ιA` and Bob carrier `ιB`, the later
symmetrized local space will use this tagged direct sum so that Alice's operators
occupy the `Sum.inl` block and Bob's operators occupy the `Sum.inr` block. -/
abbrev LocalCarrierSum (ιA ιB : Type*) := Sum ιA ιB

/-- Local carrier planned for the heterogeneous symmetrization bridge: a role bit
and a direct-sum carrier. This is the direct-sum analogue of the current
same-space target `Role × ι` in `StrategyRole.lean`. -/
abbrev RoleRegisterLocal (ιA ιB : Type*) := Role × LocalCarrierSum ιA ιB

/-- Reassociate role bits and direct-sum carriers.

This is the public heterogeneous analogue of the same-space role-register
reassociation used internally by `StrategyRole.lean`. It prepares the target
shape for reindexing block states on
`(Role × (ιA ⊕ ιB)) × (Role × (ιA ⊕ ιB))`. -/
def roleRegisterPairLocalEquiv (ιA ιB : Type*) :
    ((Role × Role) × (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) ≃
      (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl

/-! ### Direct-sum block states for heterogeneous role symmetrization -/

/-- Embed an operator on Alice's and Bob's original tensor product into the
`(Sum.inl _) × (Sum.inr _)` block of the direct-sum tensor product. -/
noncomputable def localPairABBlock {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB) :=
  Matrix.of fun x y =>
    match x, y with
    | (Sum.inl i, Sum.inr j), (Sum.inl i', Sum.inr j') => X (i, j) (i', j')
    | _, _ => 0

/-- Embed an operator on Bob's and Alice's original tensor product into the
`(Sum.inr _) × (Sum.inl _)` block of the direct-sum tensor product. -/
noncomputable def localPairBABlock {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB) :=
  Matrix.of fun x y =>
    match x, y with
    | (Sum.inr i, Sum.inl j), (Sum.inr i', Sum.inl j') => X (i, j) (i', j')
    | _, _ => 0

@[simp] theorem localPairABBlock_AB_AB {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) (i i' : ιA) (j j' : ιB) :
    localPairABBlock X (Sum.inl i, Sum.inr j) (Sum.inl i', Sum.inr j') =
      X (i, j) (i', j') :=
  rfl

@[simp] theorem localPairBABlock_BA_BA {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) (i i' : ιB) (j j' : ιA) :
    localPairBABlock X (Sum.inr i, Sum.inl j) (Sum.inr i', Sum.inl j') =
      X (i, j) (i', j') :=
  rfl

@[simp] theorem localPairABBlock_conjTranspose {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    (localPairABBlock X)ᴴ = localPairABBlock Xᴴ := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [localPairABBlock]

@[simp] theorem localPairBABlock_conjTranspose {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιB × ιA)) :
    (localPairBABlock X)ᴴ = localPairBABlock Xᴴ := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [localPairBABlock]

@[simp] theorem localPairABBlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X Y : MIPStarRE.Quantum.Op (ιA × ιB)) :
    localPairABBlock X * localPairABBlock Y = localPairABBlock (X * Y) := by
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
              | inl j' => simp [localPairABBlock, Matrix.mul_apply]
              | inr j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairABBlock, Matrix.of_apply,
                    zero_mul, Finset.sum_const_zero, zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιA => fun y : ιB =>
                      X (i, j) (x, y) * Y (x, y) (i', j'))).symm
          | inr i' =>
              cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]
  | inr i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]

@[simp] theorem localPairBABlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (X Y : MIPStarRE.Quantum.Op (ιB × ιA)) :
    localPairBABlock X * localPairBABlock Y = localPairBABlock (X * Y) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]
  | inr i =>
      cases x₂ with
      | inl j =>
          cases y₁ with
          | inl i' =>
              cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]
          | inr i' =>
              cases y₂ with
              | inl j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairBABlock, Matrix.of_apply,
                    zero_mul, Finset.sum_const_zero, zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιB => fun y : ιA =>
                      X (i, j) (x, y) * Y (x, y) (i', j'))).symm
              | inr j' => simp [localPairBABlock, Matrix.mul_apply]
      | inr j =>
          cases y₁ <;> cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]

theorem localPairABBlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {X : MIPStarRE.Quantum.Op (ιA × ιB)} (hX : 0 ≤ X) :
    0 ≤ localPairABBlock X := by
  classical
  letI := Fintype.ofFinite ιA
  letI := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hX ⊢
  rcases hX with ⟨C, hC⟩
  refine ⟨localPairABBlock C, ?_⟩
  change localPairABBlock X = (localPairABBlock C)ᴴ * localPairABBlock C
  rw [localPairABBlock_conjTranspose, localPairABBlock_mul]
  exact congrArg localPairABBlock hC

theorem localPairBABlock_nonneg {ιA ιB : Type*} [Finite ιA] [Finite ιB]
    {X : MIPStarRE.Quantum.Op (ιB × ιA)} (hX : 0 ≤ X) :
    0 ≤ localPairBABlock X := by
  classical
  letI := Fintype.ofFinite ιA
  letI := Fintype.ofFinite ιB
  rw [CStarAlgebra.nonneg_iff_eq_star_mul_self] at hX ⊢
  rcases hX with ⟨C, hC⟩
  refine ⟨localPairBABlock C, ?_⟩
  change localPairBABlock X = (localPairBABlock C)ᴴ * localPairBABlock C
  rw [localPairBABlock_conjTranspose, localPairBABlock_mul]
  exact congrArg localPairBABlock hC

/-- Swap an operator on `ιA × ιB` to one on `ιB × ιA`. -/
noncomputable def heterogeneousSwapDensity {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    MIPStarRE.Quantum.Op (ιB × ιA) :=
  Matrix.reindex (Equiv.prodComm ιA ιB) (Equiv.prodComm ιA ιB) X

/-- **Lean-only:** Tensor products commute with the heterogeneous swap map.

Paper origin: `references/ldt-paper/inductive_step.tex:40-66`; this is the
matrix-index identity used to identify the two role-register sectors in the
heterogeneous symmetrization. -/
@[simp] theorem heterogeneousSwapDensity_opTensor {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    heterogeneousSwapDensity (opTensor A B) = opTensor B A := by
  ext i j
  rcases i with ⟨iB, iA⟩
  rcases j with ⟨jB, jA⟩
  simp [heterogeneousSwapDensity, opTensor]
  ring

theorem heterogeneousSwapDensity_nonneg {ιA ιB : Type*}
    [Finite ιA] [Finite ιB] {X : MIPStarRE.Quantum.Op (ιA × ιB)}
    (hX : 0 ≤ X) : 0 ≤ heterogeneousSwapDensity X :=
  MIPStarRE.Quantum.reindex_nonneg (Equiv.prodComm ιA ιB) hX

@[simp] theorem heterogeneousSwapDensity_mul {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (X Y : MIPStarRE.Quantum.Op (ιA × ιB)) :
    heterogeneousSwapDensity (X * Y) =
      heterogeneousSwapDensity X * heterogeneousSwapDensity Y := by
  classical
  unfold heterogeneousSwapDensity
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodComm ιA ιB)) X Y

@[simp] theorem swapDensity_localPairABBlock {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    swapDensity (localPairABBlock X) =
      localPairBABlock (heterogeneousSwapDensity X) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [swapDensity, localPairABBlock, localPairBABlock, heterogeneousSwapDensity]

@[simp] theorem swapDensity_localPairBABlock_heterogeneousSwapDensity {ιA ιB : Type*}
    (X : MIPStarRE.Quantum.Op (ιA × ιB)) :
    swapDensity (localPairBABlock (heterogeneousSwapDensity X)) =
      localPairABBlock X := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp [swapDensity, localPairABBlock, localPairBABlock, heterogeneousSwapDensity]

@[simp] theorem rolePairProj_AB_mul_BA :
    rolePairProj Role.A Role.B * rolePairProj Role.B Role.A = 0 :=
  MIPStarRE.LDT.rolePairProj_AB_mul_BA

@[simp] theorem rolePairProj_BA_mul_AB :
    rolePairProj Role.B Role.A * rolePairProj Role.A Role.B = 0 :=
  MIPStarRE.LDT.rolePairProj_BA_mul_AB

/-- Place a direct-sum bipartite operator in a chosen pair of role sectors. -/
noncomputable def rolePairDirectSumCond {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) :=
  Matrix.reindex (roleRegisterPairLocalEquiv ιA ιB)
    (roleRegisterPairLocalEquiv ιA ιB)
    (opTensor (rolePairProj rL rR) X)

theorem rolePairDirectSumCond_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    {X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)}
    (hX : 0 ≤ X) : 0 ≤ rolePairDirectSumCond rL rR X :=
  MIPStarRE.Quantum.reindex_nonneg (roleRegisterPairLocalEquiv ιA ιB)
    (opTensor_nonneg (MIPStarRE.LDT.rolePairProj_nonneg rL rR) hX)

@[simp] theorem rolePairDirectSumCond_mul_same {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    rolePairDirectSumCond rL rR X * rolePairDirectSumCond rL rR Y =
      rolePairDirectSumCond rL rR (X * Y) := by
  unfold rolePairDirectSumCond
  let e := roleRegisterPairLocalEquiv ιA ιB
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) Y) =
    (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) (X * Y))
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)]
  congr 1
  simp [opTensor_mul, rolePairProj, roleProj_mul_self]

/-- Distinct role-pair sectors of the direct-sum role register are orthogonal. -/
theorem rolePairDirectSumCond_mul_eq_zero_of_ne {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR sL sR : Role)
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB))
    (h : (rL, rR) ≠ (sL, sR)) :
    rolePairDirectSumCond rL rR X * rolePairDirectSumCond sL sR Y = 0 := by
  unfold rolePairDirectSumCond
  let e := roleRegisterPairLocalEquiv ιA ιB
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj sL sR) Y) = 0
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)]
  rw [opTensor_mul, rolePairProj_mul_eq_zero_of_ne rL rR sL sR h]
  simp [opTensor]

@[simp] theorem rolePairDirectSumCond_AB_mul_BA {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    rolePairDirectSumCond Role.A Role.B X * rolePairDirectSumCond Role.B Role.A Y = 0 := by
  exact rolePairDirectSumCond_mul_eq_zero_of_ne Role.A Role.B Role.B Role.A X Y (by decide)

@[simp] theorem rolePairDirectSumCond_BA_mul_AB {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    rolePairDirectSumCond Role.B Role.A X * rolePairDirectSumCond Role.A Role.B Y = 0 := by
  exact rolePairDirectSumCond_mul_eq_zero_of_ne Role.B Role.A Role.A Role.B X Y (by decide)

@[simp] theorem swapDensity_rolePairDirectSumCond {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    swapDensity (rolePairDirectSumCond rL rR X) =
      rolePairDirectSumCond rR rL (swapDensity X) := by
  ext x y
  rcases x with ⟨⟨sL, iL⟩, ⟨sR, iR⟩⟩
  rcases y with ⟨⟨tL, jL⟩, ⟨tR, jR⟩⟩
  cases rL <;> cases rR <;> cases sL <;> cases sR <;> cases tL <;> cases tR <;>
    simp [swapDensity, rolePairDirectSumCond, rolePairProj, roleProj, opTensor,
      roleRegisterPairLocalEquiv]

/-- Normalizing scalar for the direct-sum heterogeneous role-register state. -/
noncomputable def roleRegisterDensityScale (ιA ιB : Type*) [Fintype ιA] [Fintype ιB] :
    Error :=
  2 * ((Fintype.card (LocalCarrierSum ιA ιB) : Error) ^ (2 : ℕ)) /
    ((Fintype.card ιA : Error) * (Fintype.card ιB : Error))

theorem roleRegisterDensityScale_nonneg (ιA ιB : Type*) [Fintype ιA] [Fintype ιB] :
    0 ≤ roleRegisterDensityScale ιA ιB := by
  unfold roleRegisterDensityScale
  positivity

/-- Heterogeneous role-register symmetrization of a two-space bipartite state.

The state lives on `Role × (ιA ⊕ ιB)` on each side.  Its occupied sectors are
`A/B`, carrying the original density in the `Sum.inl × Sum.inr` direct-sum
block, and `B/A`, carrying the swapped density in the `Sum.inr × Sum.inl` block.
The scalar compensates for normalized trace on the enlarged direct-sum carrier.
Normalization and the LDT goodness comparison are separate lemmas. -/
noncomputable def roleRegisterSymmState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) :
    QuantumState (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) where
  density :=
    roleRegisterDensityScale ιA ιB •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
    roleRegisterDensityScale ιA ιB •
      rolePairDirectSumCond Role.B Role.A
        (localPairBABlock (heterogeneousSwapDensity ψ.density))
  density_psd := add_nonneg
    (smul_nonneg (roleRegisterDensityScale_nonneg ιA ιB)
      (rolePairDirectSumCond_nonneg Role.A Role.B
        (localPairABBlock_nonneg ψ.density_psd)))
    (smul_nonneg (roleRegisterDensityScale_nonneg ιA ιB)
      (rolePairDirectSumCond_nonneg Role.B Role.A
        (localPairBABlock_nonneg (heterogeneousSwapDensity_nonneg ψ.density_psd))))

/-- Block-diagonal operator on `ιA ⊕ ιB`, with Alice's block in the
`Sum.inl` sector and Bob's block in the `Sum.inr` sector.

This is the matrix-level direct sum that will underlie symmetrized measurements
such as
`|0⟩⟨0| ⊗ A^A + |1⟩⟨1| ⊗ A^B` from
`references/ldt-paper/inductive_step.tex:55-59`. -/
noncomputable def localDirectSumBlock {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB) :=
  Matrix.fromBlocks A 0 0 B

@[simp] theorem localDirectSumBlock_inl_inl {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i j : ιA) : localDirectSumBlock A B (Sum.inl i) (Sum.inl j) = A i j :=
  rfl

@[simp] theorem localDirectSumBlock_inl_inr {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i : ιA) (j : ιB) : localDirectSumBlock A B (Sum.inl i) (Sum.inr j) = 0 :=
  rfl

@[simp] theorem localDirectSumBlock_inr_inl {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i : ιB) (j : ιA) : localDirectSumBlock A B (Sum.inr i) (Sum.inl j) = 0 :=
  rfl

@[simp] theorem localDirectSumBlock_inr_inr {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (i j : ιB) : localDirectSumBlock A B (Sum.inr i) (Sum.inr j) = B i j :=
  rfl

@[simp] theorem localDirectSumBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    localDirectSumBlock (1 : MIPStarRE.Quantum.Op ιA) (1 : MIPStarRE.Quantum.Op ιB) = 1 := by
  simp [localDirectSumBlock]

@[simp] theorem localDirectSumBlock_zero {ιA ιB : Type*} :
    localDirectSumBlock (0 : MIPStarRE.Quantum.Op ιA) (0 : MIPStarRE.Quantum.Op ιB) = 0 := by
  simp [localDirectSumBlock]

/-- Direct-sum blocks are additive in the two diagonal blocks. -/
@[simp] theorem localDirectSumBlock_add {ιA ιB : Type*}
    (A₁ A₂ : MIPStarRE.Quantum.Op ιA) (B₁ B₂ : MIPStarRE.Quantum.Op ιB) :
    localDirectSumBlock A₁ B₁ + localDirectSumBlock A₂ B₂ =
      localDirectSumBlock (A₁ + A₂) (B₁ + B₂) := by
  simp [localDirectSumBlock, Matrix.fromBlocks_add]

@[simp] theorem localDirectSumBlock_conjTranspose {ιA ιB : Type*}
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    (localDirectSumBlock A B)ᴴ = localDirectSumBlock Aᴴ Bᴴ := by
  simp [localDirectSumBlock, Matrix.fromBlocks_conjTranspose]

@[simp] theorem localDirectSumBlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (A₁ A₂ : MIPStarRE.Quantum.Op ιA) (B₁ B₂ : MIPStarRE.Quantum.Op ιB) :
    localDirectSumBlock A₁ B₁ * localDirectSumBlock A₂ B₂ =
      localDirectSumBlock (A₁ * A₂) (B₁ * B₂) := by
  simp [localDirectSumBlock, Matrix.fromBlocks_multiply]

def roleBlockFamily {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    Role → MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)
  | Role.A => A
  | Role.B => B

/-- The role-register block diagonal as a ring homomorphism. -/
noncomputable def roleBlockRingHom {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB] [DecidableEq ιA] [DecidableEq ιB] :
    (Role → MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) →+*
      MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB) := by
  classical
  exact
    (Matrix.reindexAlgEquiv ℂ ℂ
      (Equiv.prodComm (LocalCarrierSum ιA ιB) Role)).toRingHom.comp
        (Matrix.blockDiagonalRingHom (LocalCarrierSum ιA ιB) Role ℂ)

/-- Role-blocked operator on `Role × (ιA ⊕ ιB)`.

The first block is used when the role register is `Role.A`; the second block is
used when the role register is `Role.B`. This is the direct-sum scaffold for the
paper's symmetrized measurements in `inductive_step.tex:55-59`. -/
noncomputable def roleBlock {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB) :=
  Matrix.reindex (Equiv.prodComm (LocalCarrierSum ιA ιB) Role)
    (Equiv.prodComm (LocalCarrierSum ιA ιB) Role)
    (Matrix.blockDiagonal (roleBlockFamily A B))

@[simp] theorem roleBlock_A {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.A, i) (Role.A, j) = A i j :=
  rfl

@[simp] theorem roleBlock_B {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.B, i) (Role.B, j) = B i j :=
  rfl

@[simp] theorem roleBlock_AB {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.A, i) (Role.B, j) = 0 :=
  rfl

@[simp] theorem roleBlock_BA {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB))
    (i j : LocalCarrierSum ιA ιB) :
    roleBlock A B (Role.B, i) (Role.A, j) = 0 :=
  rfl

@[simp] theorem roleBlock_one {ιA ιB : Type*}
    [DecidableEq ιA] [DecidableEq ιB] :
    roleBlock (1 : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) 1 = 1 := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp [Matrix.one_apply]

@[simp] theorem roleBlock_zero {ιA ιB : Type*} :
    roleBlock (0 : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) 0 = 0 := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp

/-- Role-register blocks are additive in their two role sectors. -/
@[simp] theorem roleBlock_add {ιA ιB : Type*}
    (A₁ A₂ B₁ B₂ : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    roleBlock A₁ B₁ + roleBlock A₂ B₂ = roleBlock (A₁ + A₂) (B₁ + B₂) := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp

@[simp] theorem roleBlock_conjTranspose {ιA ιB : Type*}
    (A B : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    (roleBlock A B)ᴴ = roleBlock Aᴴ Bᴴ := by
  ext x y
  rcases x with ⟨rx, ix⟩
  rcases y with ⟨ry, iy⟩
  cases rx <;> cases ry <;> simp

@[simp] theorem roleBlock_mul {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (A₁ A₂ B₁ B₂ : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    roleBlock A₁ B₁ * roleBlock A₂ B₂ = roleBlock (A₁ * A₂) (B₁ * B₂) := by
  classical
  change roleBlockRingHom (roleBlockFamily A₁ B₁) *
      roleBlockRingHom (roleBlockFamily A₂ B₂) =
    roleBlockRingHom (roleBlockFamily (A₁ * A₂) (B₁ * B₂))
  rw [← map_mul (roleBlockRingHom :
    (Role → MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) →+*
      MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB))]
  congr
  ext r
  cases r <;> rfl

end ProjStrat

end MIPStarRE.LDT


