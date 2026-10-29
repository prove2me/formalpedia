-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
-- name    : LIDT_MIPStarRE_LDT_Basic_QuantumState
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:48:59.222191+00:00
-- url     : https://prove2.me/theorems/5425db01-3269-4101-8e85-8756e8ed0762
-- title:
--   LIDT definitions: LDT / Basic / QuantumState
-- statement:
--   This bundle defines the finite-dimensional quantum state and operator language used throughout the LDT formalization. It includes positive states, normalization, pure-state density matrices, tensor-coordinate swaps, expectation values, tensor products, and the pure-state witness structures used by later arguments.
--
--   Principal definitions:
--   - `QuantumState`: a positive semidefinite matrix state on a finite index type.
--   - `QuantumState.IsNormalized`: the unit normalized-trace condition.
--   - `pureDensity`: the scaled rank-one density matrix of a state vector.
--   - `swapVector`: swaps the two tensor coordinates of a bipartite vector.
--   - `PureState`: a unit-vector witness for a pure state.
--   - `density`: the density matrix represented by a pure-state witness.
--   - `ev`: the real part of the normalized expectation of an operator.
--   - `opTensor`: the Kronecker tensor product of two operators.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/QuantumState.lean#L18-L574

-- Generated from MIPStarRE/LDT/Basic/QuantumState.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

open scoped _root_.Matrix

namespace LIDT

/-!
# Quantum states and tensor placement for the low individual degree test

Core quantum-state definitions together with tensor-placement operators.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

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

/-- A normalized state has a nonempty carrier: if the carrier were empty, the
trace would vanish and `normalizedTrace = 0 / 0 = 0`, contradicting `= 1`. -/
theorem QuantumState.IsNormalized.nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} (hψ : ψ.IsNormalized) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  let := h
  rw [QuantumState.IsNormalized] at hψ
  have hzero : MIPStarRE.Quantum.normalizedTrace ψ.density = 0 := by
    simp [MIPStarRE.Quantum.normalizedTrace]
  exact zero_ne_one (hzero.symm.trans hψ)

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
  rfl

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

/-- Left placement of the identity is the identity on the product space. -/
theorem leftTensor_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] :
    leftTensor (ι₂ := ι₂) (1 : MIPStarRE.Quantum.Op ι₁) =
      (1 : MIPStarRE.Quantum.Op (ι₁ × ι₂)) := by
  simpa only [leftTensor, Matrix.kronecker] using
    (Matrix.one_kronecker_one (m := ι₁) (n := ι₂) (α := ℂ))

/-- Right placement of the identity is the identity on the product space. -/
theorem rightTensor_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] :
    rightTensor (ι₁ := ι₁) (1 : MIPStarRE.Quantum.Op ι₂) =
      (1 : MIPStarRE.Quantum.Op (ι₁ × ι₂)) := by
  simpa only [rightTensor, Matrix.kronecker] using
    (Matrix.one_kronecker_one (m := ι₁) (n := ι₂) (α := ℂ))

/-- Local tensor placements multiply to the full Kronecker product. -/
theorem leftTensor_mul_rightTensor_eq_opTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B = opTensor A B := by
  simpa [leftTensor, rightTensor, opTensor] using
    (Matrix.mul_kronecker_mul
      A (1 : MIPStarRE.Quantum.Op ι₁) (1 : MIPStarRE.Quantum.Op ι₂) B).symm

/-- Positivity is preserved by `opTensor`. -/
theorem opTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} {B : MIPStarRE.Quantum.Op ι₂}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ opTensor A B := by
  simpa [opTensor] using MIPStarRE.Quantum.kronecker_nonneg hA hB

/-- The normalized trace of a tensor product is the product of the normalized traces. -/
theorem normalizedTrace_opTensor
    {ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Nonempty ι₁]
    [Fintype ι₂] [DecidableEq ι₂] [Nonempty ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    MIPStarRE.Quantum.normalizedTrace (opTensor A B) =
      MIPStarRE.Quantum.normalizedTrace A * MIPStarRE.Quantum.normalizedTrace B := by
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [show Matrix.trace (opTensor A B) = Matrix.trace A * Matrix.trace B by
    simpa [opTensor] using Matrix.trace_kronecker A B]
  have hι₁ : ((Fintype.card ι₁ : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hι₂ : ((Fintype.card ι₂ : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.card_prod, Nat.cast_mul]
  field_simp [hι₁, hι₂]

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

/-- If `0 ≤ A` and `B ≤ 1`, then `A ⊗ B ≤ A ⊗ I`. -/
theorem opTensor_le_leftTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} {B : MIPStarRE.Quantum.Op ι₂}
    (hA : 0 ≤ A) (hB : B ≤ 1) :
    opTensor A B ≤ leftTensor (ι₂ := ι₂) A := by
  simpa [leftTensor, opTensor] using
    MIPStarRE.Quantum.kronecker_le_kronecker_right_one hA hB

/-- `opTensor` is monotone in the left factor against a PSD right factor. -/
theorem opTensor_mono_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A₁ A₂ : MIPStarRE.Quantum.Op ι₁} {B : MIPStarRE.Quantum.Op ι₂}
    (hA : A₁ ≤ A₂) (hB : 0 ≤ B) :
    opTensor A₁ B ≤ opTensor A₂ B := by
  simpa [opTensor] using MIPStarRE.Quantum.kronecker_mono_left hA hB

/-- Left tensor placement is monotone. -/
theorem leftTensor_mono
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A₁ A₂ : MIPStarRE.Quantum.Op ι₁} (hA : A₁ ≤ A₂) :
    leftTensor (ι₂ := ι₂) A₁ ≤ leftTensor (ι₂ := ι₂) A₂ :=
  opTensor_mono_left hA zero_le_one

/-- `opTensor` is monotone in the right factor against a PSD left factor. -/
theorem opTensor_mono_right
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} {B₁ B₂ : MIPStarRE.Quantum.Op ι₂}
    (hA : 0 ≤ A) (hB : B₁ ≤ B₂) :
    opTensor A B₁ ≤ opTensor A B₂ := by
  change (opTensor A B₂ - opTensor A B₁).PosSemidef
  have hpsd :
      (Matrix.kronecker A (B₂ - B₁)).PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp <|
      MIPStarRE.Quantum.kronecker_nonneg hA (sub_nonneg.mpr hB)
  rw [opTensor, opTensor, MIPStarRE.Quantum.kronecker_sub_right]
  exact hpsd




/-- `rightTensor B * leftTensor A = opTensor A B`. -/
theorem rightTensor_mul_leftTensor_eq_opTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    rightTensor (ι₁ := ι₁) B * leftTensor (ι₂ := ι₂) A = opTensor A B := by
  simpa [leftTensor, rightTensor, opTensor] using
    (Matrix.mul_kronecker_mul
      (1 : MIPStarRE.Quantum.Op ι₁) A B (1 : MIPStarRE.Quantum.Op ι₂)).symm

/-- `leftTensor A * leftTensor B = leftTensor (A * B)`. -/
theorem leftTensor_mul_leftTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) :
    leftTensor (ι₂ := ι₂) A * leftTensor (ι₂ := ι₂) B =
      leftTensor (ι₂ := ι₂) (A * B) := by
  simpa [leftTensor, opTensor] using
    (Matrix.mul_kronecker_mul
      A B (1 : MIPStarRE.Quantum.Op ι₂) (1 : MIPStarRE.Quantum.Op ι₂)).symm

/-- Multiplying a left tensor into a full tensor only affects the left factor. -/
theorem leftTensor_mul_opTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) (C : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) A * opTensor B C = opTensor (A * B) C := by
  calc
    leftTensor (ι₂ := ι₂) A * opTensor B C
        = leftTensor (ι₂ := ι₂) A *
            (leftTensor (ι₂ := ι₂) B * rightTensor (ι₁ := ι₁) C) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]
    _ = (leftTensor (ι₂ := ι₂) A * leftTensor (ι₂ := ι₂) B) *
          rightTensor (ι₁ := ι₁) C := by
          rw [Matrix.mul_assoc]
    _ = leftTensor (ι₂ := ι₂) (A * B) * rightTensor (ι₁ := ι₁) C := by
          rw [leftTensor_mul_leftTensor]
    _ = opTensor (A * B) C := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]







/-- `rightTensor A * rightTensor B = rightTensor (A * B)`. -/
theorem rightTensor_mul_rightTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₂) :
    rightTensor (ι₁ := ι₁) A * rightTensor (ι₁ := ι₁) B =
      rightTensor (ι₁ := ι₁) (A * B) := by
  simpa [rightTensor, opTensor] using
    (Matrix.mul_kronecker_mul
      (1 : MIPStarRE.Quantum.Op ι₁) (1 : MIPStarRE.Quantum.Op ι₁) A B).symm

/-- Multiplying a right tensor into a full tensor only affects the right factor. -/
theorem rightTensor_mul_opTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₂) (B : MIPStarRE.Quantum.Op ι₁)
    (C : MIPStarRE.Quantum.Op ι₂) :
    rightTensor (ι₁ := ι₁) A * opTensor B C = opTensor B (A * C) := by
  calc
    rightTensor (ι₁ := ι₁) A * opTensor B C
        = rightTensor (ι₁ := ι₁) A *
            (leftTensor (ι₂ := ι₂) B * rightTensor (ι₁ := ι₁) C) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]
    _ = (rightTensor (ι₁ := ι₁) A * leftTensor (ι₂ := ι₂) B) *
          rightTensor (ι₁ := ι₁) C := by
          rw [Matrix.mul_assoc]
    _ = opTensor B A * rightTensor (ι₁ := ι₁) C := by
          rw [rightTensor_mul_leftTensor_eq_opTensor]
    _ = (leftTensor (ι₂ := ι₂) B * rightTensor (ι₁ := ι₁) A) *
          rightTensor (ι₁ := ι₁) C := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]
    _ = leftTensor (ι₂ := ι₂) B *
          (rightTensor (ι₁ := ι₁) A * rightTensor (ι₁ := ι₁) C) := by
          rw [Matrix.mul_assoc]
    _ = leftTensor (ι₂ := ι₂) B * rightTensor (ι₁ := ι₁) (A * C) := by
          rw [rightTensor_mul_rightTensor]
    _ = opTensor B (A * C) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]

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

/-- `opTensor` distributes over multiplication. -/
theorem opTensor_mul
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A₁ A₂ : MIPStarRE.Quantum.Op ι₁) (B₁ B₂ : MIPStarRE.Quantum.Op ι₂) :
    opTensor A₁ B₁ * opTensor A₂ B₂ = opTensor (A₁ * A₂) (B₁ * B₂) :=
  (Matrix.mul_kronecker_mul A₁ A₂ B₁ B₂).symm

/-- `opTensor` is linear in the left factor: subtraction. -/
theorem opTensor_sub_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) (C : MIPStarRE.Quantum.Op ι₂) :
    opTensor A C - opTensor B C = opTensor (A - B) C := by
  simpa [opTensor] using
    MIPStarRE.Quantum.kronecker_sub_left (A₁ := A) (A₂ := B) (B := C)

/-- Left tensor placement commutes with subtraction. -/
theorem leftTensor_sub
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) :
    leftTensor (ι₂ := ι₂) A - leftTensor (ι₂ := ι₂) B =
      leftTensor (ι₂ := ι₂) (A - B) := by
  simpa [leftTensor, opTensor, Matrix.kronecker] using
    (opTensor_sub_left (ι₁ := ι₁) (ι₂ := ι₂) A B (1 : MIPStarRE.Quantum.Op ι₂))



/-- `opTensor` is linear in the left factor: real scalar multiplication. -/
theorem opTensor_smul_left_error
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (c • A) B = c • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm]

/-- `opTensor` is linear in the right factor: real scalar multiplication. -/
theorem opTensor_smul_right_error
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor A (c • B) = c • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm]

/-- `opTensor` is additive in the left factor. -/
theorem opTensor_add_left_local
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : MIPStarRE.Quantum.Op ι₁) (C : MIPStarRE.Quantum.Op ι₂) :
    opTensor (A + B) C = opTensor A C + opTensor B C := by
  ext x y
  simp [opTensor, add_mul]

/-- `opTensor` is additive in the right factor. -/
theorem opTensor_add_right_local
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (B C : MIPStarRE.Quantum.Op ι₂) :
    opTensor A (B + C) = opTensor A B + opTensor A C := by
  ext x y
  simp [opTensor, mul_add]

/-- Pull a finite sum out of the left factor of `opTensor`. -/
theorem opTensor_sum_left_finset
    {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (∑ a ∈ s, f a) B = ∑ a ∈ s, opTensor (f a) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_left_local, ih]

/-- Pull a finite sum out of the right factor of `opTensor`. -/
theorem opTensor_sum_right_finset
    {α ι₁ ι₂ : Type*}
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₂) :
    opTensor A (∑ a ∈ s, f a) = ∑ a ∈ s, opTensor A (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_right_local, ih]

/-- Pull an unindexed finite-type sum out of the left factor of `opTensor`. -/
theorem opTensor_sum_left_univ
    {α ι₁ ι₂ : Type*} [Fintype α]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (f : α → MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (∑ a : α, f a) B = ∑ a : α, opTensor (f a) B := by
  classical
  simpa using opTensor_sum_left_finset (s := (Finset.univ : Finset α)) (f := f) (B := B)

/-- Pull an unindexed finite-type sum out of the right factor of `opTensor`. -/
theorem opTensor_sum_right_univ
    {α ι₁ ι₂ : Type*} [Fintype α]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A : MIPStarRE.Quantum.Op ι₁) (f : α → MIPStarRE.Quantum.Op ι₂) :
    opTensor A (∑ a : α, f a) = ∑ a : α, opTensor A (f a) := by
  classical
  simpa using opTensor_sum_right_finset (A := A) (s := (Finset.univ : Finset α)) (f := f)


end MIPStarRE.LDT

end

end LIDT


