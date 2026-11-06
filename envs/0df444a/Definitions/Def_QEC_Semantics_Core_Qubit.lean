-- Prove2me | Definitions.Def_QEC_Semantics_Core_Qubit
-- name    : QEC_Semantics_Core_Qubit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:04:37.521037+00:00
-- url     : https://prove2.me/theorems/e1450a4f-dfb8-4a56-93a2-b6051c18fae1
-- title:
--   Qubit
-- statement:
--   Definitions and structural lemmas for Qubit, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Qubit.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Semantics
namespace Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
abbrev QubitSpace : Type :=
  EuclideanSpace Complex (Fin 2)
abbrev Bitstring (ι : Type u) : Type u :=
  ι → Fin 2
abbrev QubitRegister (ι : Type u) [Fintype ι] : Type u :=
  EuclideanSpace Complex (Bitstring ι)
@[simp]
theorem card_bitstring (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Fintype.card (Bitstring ι) = 2 ^ Fintype.card ι := by
  change Fintype.card (ι → Fin 2) = 2 ^ Fintype.card ι
  rw [Fintype.card_fun]
  simp
@[simp]
theorem natCard_bitstring (ι : Type u) [Fintype ι] :
    Nat.card (Bitstring ι) = 2 ^ Fintype.card ι := by
  change Nat.card (ι → Fin 2) = 2 ^ Fintype.card ι
  rw [Nat.card_fun]
  simp
@[simp]
theorem finrank_qubitRegister (ι : Type u) [Fintype ι] :
    Module.finrank Complex (QubitRegister ι) = 2 ^ Fintype.card ι := by
  classical
  change Module.finrank Complex (EuclideanSpace Complex (Bitstring ι)) =
    2 ^ Fintype.card ι
  rw [finrank_euclideanSpace]
  exact card_bitstring ι
def flipBit (b : Fin 2) : Fin 2 :=
  if b = 0 then 1 else 0
@[simp] theorem flipBit_zero : flipBit 0 = 1 := by
  simp [flipBit]
@[simp] theorem flipBit_one : flipBit 1 = 0 := by
  simp [flipBit]
@[simp] theorem flipBit_flip (b : Fin 2) : flipBit (flipBit b) = b := by
  fin_cases b <;> simp
def zPhase (b : Fin 2) : Complex :=
  if b = 0 then 1 else -1
@[simp] theorem zPhase_zero : zPhase 0 = 1 := by
  simp [zPhase]
@[simp] theorem zPhase_one : zPhase 1 = -1 := by
  simp [zPhase]
@[simp] theorem zPhase_flipBit (b : Fin 2) : zPhase (flipBit b) = -zPhase b := by
  fin_cases b <;> simp [zPhase]
@[simp] theorem zPhase_sq (b : Fin 2) : zPhase b * zPhase b = 1 := by
  fin_cases b <;> simp [zPhase]
@[simp] theorem zPhase_star (b : Fin 2) : star (zPhase b) = zPhase b := by
  fin_cases b <;> simp [zPhase]
def flipAt {ι : Type u} [DecidableEq ι] (i : ι) (bits : Bitstring ι) :
    Bitstring ι :=
  Function.update bits i (flipBit (bits i))
@[simp] theorem flipAt_apply_self {ι : Type u} [DecidableEq ι]
    (i : ι) (bits : Bitstring ι) :
    flipAt i bits i = flipBit (bits i) := by
  simp [flipAt]
@[simp] theorem flipAt_flipAt {ι : Type u} [DecidableEq ι]
    (i : ι) (bits : Bitstring ι) :
    flipAt i (flipAt i bits) = bits := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]
def pauliXMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  fun row col => if row = flipBit col then 1 else 0
def pauliYMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  fun row col =>
    if row = 0 ∧ col = 1 then -Complex.I
    else if row = 1 ∧ col = 0 then Complex.I
    else 0
def pauliZMatrix : Matrix (Fin 2) (Fin 2) Complex :=
  fun row col => if row = col then zPhase col else 0
def pauliI : Operator QubitSpace :=
  1
def pauliX : Operator QubitSpace :=
  Matrix.toEuclideanLin pauliXMatrix
def pauliY : Operator QubitSpace :=
  Matrix.toEuclideanLin pauliYMatrix
def pauliZ : Operator QubitSpace :=
  Matrix.toEuclideanLin pauliZMatrix
@[simp] theorem pauliI_apply (ψ : QubitSpace) (b : Fin 2) :
    pauliI ψ b = ψ b :=
  rfl
@[simp] theorem pauliX_apply (ψ : QubitSpace) (b : Fin 2) :
    pauliX ψ b = ψ (flipBit b) := by
  fin_cases b <;> simp [pauliX, pauliXMatrix, Matrix.mulVec, dotProduct, flipBit]
@[simp] theorem pauliY_apply_zero (ψ : QubitSpace) :
    pauliY ψ 0 = -Complex.I * ψ 1 := by
  simp [pauliY, pauliYMatrix, Matrix.mulVec, dotProduct]
@[simp] theorem pauliY_apply_one (ψ : QubitSpace) :
    pauliY ψ 1 = Complex.I * ψ 0 := by
  simp [pauliY, pauliYMatrix, Matrix.mulVec, dotProduct]
@[simp] theorem pauliY_apply (ψ : QubitSpace) (b : Fin 2) :
    pauliY ψ b = if b = 0 then -Complex.I * ψ 1 else Complex.I * ψ 0 := by
  fin_cases b <;> simp
@[simp] theorem pauliZ_apply (ψ : QubitSpace) (b : Fin 2) :
    pauliZ ψ b = zPhase b * ψ b := by
  fin_cases b <;> simp [pauliZ, pauliZMatrix, Matrix.mulVec, dotProduct, zPhase]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def localXMatrix (i : ι) : Matrix (Bitstring ι) (Bitstring ι) Complex :=
  fun row col => if row = flipAt i col then 1 else 0
def localZMatrix (i : ι) : Matrix (Bitstring ι) (Bitstring ι) Complex :=
  fun row col => if row = col then zPhase (col i) else 0
def localX (i : ι) : Operator (QubitRegister ι) := by
  classical
  exact Matrix.toEuclideanLin (localXMatrix i)
def localZ (i : ι) : Operator (QubitRegister ι) := by
  classical
  exact Matrix.toEuclideanLin (localZMatrix i)
@[simp] theorem localX_apply (i : ι) (ψ : QubitRegister ι) (bits : Bitstring ι) :
    localX i ψ bits = ψ (flipAt i bits) := by
  classical
  simp only [localX, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  change (∑ x, (localXMatrix i bits x) * ψ.ofLp x) = ψ.ofLp (flipAt i bits)
  rw [Finset.sum_eq_single (flipAt i bits)]
  · simp [localXMatrix]
  · intro b _ hbne
    have hnot : ¬ bits = flipAt i b := by
      intro h
      have hb : flipAt i bits = b := by
        simp [h]
      exact hbne hb.symm
    simp [localXMatrix, hnot]
  · intro hnot
    simp at hnot
@[simp] theorem localZ_apply (i : ι) (ψ : QubitRegister ι) (bits : Bitstring ι) :
    localZ i ψ bits = zPhase (bits i) * ψ bits := by
  classical
  simp only [localZ, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  change (∑ x, (localZMatrix i bits x) * ψ.ofLp x) = zPhase (bits i) * ψ.ofLp bits
  rw [Finset.sum_eq_single bits]
  · simp [localZMatrix]
  · intro b _ hbne
    have hne : ¬ bits = b := fun h => hbne h.symm
    simp [localZMatrix, hne]
  · intro hnot
    simp at hnot
def flipSupport (s : Finset ι) (bits : Bitstring ι) : Bitstring ι :=
  fun i => if i ∈ s then flipBit (bits i) else bits i
omit [Fintype ι] in
@[simp] theorem flipSupport_empty (bits : Bitstring ι) :
    flipSupport (∅ : Finset ι) bits = bits := by
  funext i
  simp [flipSupport]
def zSupportPhase (s : Finset ι) (bits : Bitstring ι) : Complex :=
  ∏ i ∈ s, zPhase (bits i)
def supportPhaseSign (xSupport zSupport : Finset ι) : Complex :=
  ∏ i ∈ zSupport, if i ∈ xSupport then (-1 : Complex) else 1
def localXSupport (s : Finset ι) : Operator (QubitRegister ι) where
  toFun ψ := WithLp.toLp 2 (fun bits => ψ (flipSupport s bits))
  map_add' ψ φ := by
    ext bits
    simp
  map_smul' c ψ := by
    ext bits
    simp
def localZSupport (s : Finset ι) : Operator (QubitRegister ι) where
  toFun ψ := WithLp.toLp 2 (fun bits => zSupportPhase s bits * ψ bits)
  map_add' ψ φ := by
    ext bits
    simp [mul_add]
  map_smul' c ψ := by
    ext bits
    simp [smul_eq_mul, mul_left_comm]
end Qubit
end Semantics
end QEC


