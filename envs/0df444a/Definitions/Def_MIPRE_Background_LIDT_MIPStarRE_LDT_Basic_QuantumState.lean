-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:40.515973+00:00
-- url     : https://prove2.me/theorems/f1ff4307-7545-4517-a8eb-2dd1d2f5f732
-- title:
--   Definitions of QuantumState: Quantum states and tensor placement for the low individual degree test Core quantum-state definitions together with…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.QuantumState` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Quantum states and tensor placement for the low individual degree test. Core quantum-state definitions together with tensor-placement operators.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (13): `MIPStarRE.LDT.PureState` (A pure-state witness as a unit vector in the ambient finite Hilbert space.); `MIPStarRE.LDT.PureState.density` (The density matrix represented by a pure-state witness.); `MIPStarRE.LDT.PureState.instCoeQuantumState`; `MIPStarRE.LDT.PureState.toQuantumState`; `MIPStarRE.LDT.QuantumState` (A PSD density matrix indexed by `ι`.); `MIPStarRE.LDT.QuantumState.IsNormalized` (Unit normalized trace for the concrete matrix carried by a state.); `MIPStarRE.LDT.QuantumState.tensor` (Tensor product of two quantum states.); `MIPStarRE.LDT.ev` (The expectation `Re τ(ψ X)`.); `MIPStarRE.LDT.leftTensor` (Left placement `A ⊗ I` on a bipartite space `ι₁ × ι₂`.); `MIPStarRE.LDT.opTensor` (Tensor product of two operators via Kronecker product.); `MIPStarRE.LDT.pureDensity` (The scaled rank-one density matrix attached to a state vector.); `MIPStarRE.LDT.rightTensor` (Right placement `I ⊗ B` on a bipartite space `ι₁ × ι₂`.); `MIPStarRE.LDT.swapVector` (Swap the two tensor coordinates of a bipartite state vector.).
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coe_density`, `density_psd`, `tensor_density`, `conjTranspose_opTensor`, `leftTensor_conjTranspose`, `opTensor_nonneg`, `rightTensor_conjTranspose`, `swapVector_swapVector`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.QuantumState` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/QuantumState.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 6 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/QuantumState.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/QuantumState.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/QuantumState.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
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
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
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
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
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
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
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
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Theorems.Thm_MIPStarRE_Quantum_kronecker_nonneg

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum states and tensor placement for the low individual degree test

Core quantum-state definitions together with tensor-placement operators.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A PSD density matrix indexed by `ι`.

There is intentionally no global `Inhabited` instance: the zero matrix is PSD but
not a physical state of unit trace, so an ambient default would silently
trivialize later statements. Use `IsNormalized` to additionally require
`τ(ρ) = 1`.

This remains the ambient state space for the current LDT development: strategy
packages in `LDT/Test/StrategyCore.lean`, the SWAP-symmetry API `PermInvState`,
and the expectation-value lemmas in `LDT/Basic/OperatorExpectations.lean` are all
stated for arbitrary density matrices, not only pure states. -/
structure QuantumState (ι : Type*) [Fintype ι] [DecidableEq ι] where
  density : MIPStarRE.Quantum.Op ι := 0
  density_psd : 0 ≤ density := by positivity

/-- Unit normalized trace for the concrete matrix carried by a state. -/
def QuantumState.IsNormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) : Prop :=
  MIPStarRE.Quantum.normalizedTrace ψ.density = 1

/-- The scaled rank-one density matrix attached to a state vector.

Because this development uses the normalized trace `τ(A) = tr(A) / dim`, the
quantum state represented by a unit vector `ψ` is `dim · |ψ⟩⟨ψ|` rather than the
raw projector `|ψ⟩⟨ψ|`. This scaling makes `τ(ρ) = 1` and keeps `ev` aligned
with the paper's bra-ket expectations. -/
noncomputable def pureDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → ℂ) : MIPStarRE.Quantum.Op ι :=
  (Fintype.card ι : ℂ) • Matrix.vecMulVec ψ (star ψ)

/-- Swap the two tensor coordinates of a bipartite state vector. -/
def swapVector {ι : Type*} (ψ : ι × ι → ℂ) : ι × ι → ℂ :=
  fun ij => ψ (ij.2, ij.1)

/-- A pure-state witness as a unit vector in the ambient finite Hilbert space.

The associated density matrix is `pureDensity ψ.vector = dim · |ψ⟩⟨ψ|`, so that
coercing to `QuantumState` preserves the paper's scalar `⟨ψ|X|ψ⟩` formulas
despite our use of the normalized trace. -/
structure PureState (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] where
  vector : ι → ℂ
  unit : star vector ⬝ᵥ vector = 1

namespace PureState

/-- The density matrix represented by a pure-state witness. -/
noncomputable def density {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) : MIPStarRE.Quantum.Op ι :=
  pureDensity ψ.vector

theorem density_psd {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) :
    0 ≤ ψ.density := by
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  exact (Matrix.posSemidef_vecMulVec_self_star ψ.vector).smul
    (by positivity : 0 ≤ (Fintype.card ι : ℂ))

noncomputable def toQuantumState {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) : QuantumState ι where
  density := ψ.density
  density_psd := ψ.density_psd

noncomputable instance {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Coe (PureState ι) (QuantumState ι) where
  coe := toQuantumState

@[simp] theorem coe_density {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : PureState ι) :
    (ψ : QuantumState ι).density = ψ.density := rfl

end PureState

@[simp] theorem swapVector_swapVector {ι : Type*} (ψ : ι × ι → ℂ) :
    swapVector (swapVector ψ) = ψ := by
  funext ij
  rcases ij with ⟨i, j⟩
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The expectation `Re τ(ψ X)`. Dimensions match by construction. -/
noncomputable def ev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X : MIPStarRE.Quantum.Op ι) : Error :=
  Complex.re <| MIPStarRE.Quantum.normalizedTrace (ψ.density * X)

/-- Tensor product of two operators via Kronecker product. -/
abbrev opTensor {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
  Matrix.kronecker A B

/-- Left placement `A ⊗ I` on a bipartite space `ι₁ × ι₂`. -/
abbrev leftTensor {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) : MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
  Matrix.kronecker A 1

/-- Right placement `I ⊗ B` on a bipartite space `ι₁ × ι₂`. -/
abbrev rightTensor {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : MIPStarRE.Quantum.Op ι₂) : MIPStarRE.Quantum.Op (ι₁ × ι₂) :=
  Matrix.kronecker 1 B

/-- Positivity is preserved by `opTensor`. -/
theorem opTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} {B : MIPStarRE.Quantum.Op ι₂}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ opTensor A B := by
  simpa [opTensor] using MIPStarRE.Quantum.kronecker_nonneg hA hB

namespace QuantumState

/-- Tensor product of two quantum states. -/
noncomputable def tensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState ι₁) (φ : QuantumState ι₂) : QuantumState (ι₁ × ι₂) where
  density := opTensor ψ.density φ.density
  density_psd := opTensor_nonneg ψ.density_psd φ.density_psd

@[simp] theorem tensor_density
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : QuantumState ι₁) (φ : QuantumState ι₂) :
    (ψ.tensor φ).density = opTensor ψ.density φ.density := rfl

end QuantumState

/-- Conjugate transpose distributes over `opTensor`. -/
theorem conjTranspose_opTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    (opTensor A B)ᴴ = opTensor Aᴴ Bᴴ :=
  Matrix.conjTranspose_kronecker A B

/-- Conjugate transpose commutes with left tensor placement. -/
@[simp]
theorem leftTensor_conjTranspose
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) :
    (leftTensor (ι₂ := ι₂) A)ᴴ = leftTensor (ι₂ := ι₂) Aᴴ := by
  simpa [leftTensor, opTensor] using
    (conjTranspose_opTensor (ι₁ := ι₁) (ι₂ := ι₂) A (1 : MIPStarRE.Quantum.Op ι₂))

/-- Conjugate transpose commutes with right tensor placement. -/
@[simp]
theorem rightTensor_conjTranspose
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : MIPStarRE.Quantum.Op ι₂) :
    (rightTensor (ι₁ := ι₁) B)ᴴ = rightTensor (ι₁ := ι₁) Bᴴ := by
  simpa [rightTensor, opTensor] using
    (conjTranspose_opTensor (ι₁ := ι₁) (ι₂ := ι₂) (1 : MIPStarRE.Quantum.Op ι₁) B)

end MIPStarRE.LDT


