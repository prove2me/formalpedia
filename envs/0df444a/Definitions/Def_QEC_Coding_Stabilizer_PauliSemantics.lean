-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
-- name    : QEC_Coding_Stabilizer_PauliSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:17:46.797446+00:00
-- url     : https://prove2.me/theorems/f959f67b-55e6-4b56-81c4-fa275280bc05
-- title:
--   Pauli Semantics
-- statement:
--   Definitions and structural lemmas for Pauli Semantics, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Coding_ChainComplexData_firstCoboundaryCheckCode_orthogonal_middleBoundaryCode
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LinearCode_symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Semantics
namespace Qubit
open Classical
open scoped BigOperators
universe u
variable {ι : Type u}
variable [Fintype ι] [DecidableEq ι]
@[simp] theorem localXSupport_empty :
    localXSupport (∅ : Finset ι) = 1 := by
  ext ψ bits
  simp
@[simp] theorem localZSupport_empty :
    localZSupport (∅ : Finset ι) = 1 := by
  ext ψ bits
  simp [localZSupport, zSupportPhase]
end Qubit
end Semantics
namespace Coding
open Classical
open scoped BigOperators
universe u w
namespace PauliSymplectic
variable {ι : Type u} [Fintype ι]
def binarySupport (x : Word (ZMod 2) ι) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ 0
@[simp] theorem mem_binarySupport (x : Word (ZMod 2) ι) (i : ι) :
    i ∈ binarySupport x ↔ x i ≠ 0 := by
  simp [binarySupport]
@[simp] theorem binarySupport_zero :
    binarySupport (0 : Word (ZMod 2) ι) = ∅ := by
  ext i
  simp [binarySupport]
def binaryPhaseScalar (p : ZMod 2) : Complex :=
  if p = 0 then 1 else -1
@[simp] theorem binaryPhaseScalar_zero : binaryPhaseScalar 0 = 1 := by
  simp [binaryPhaseScalar]
@[simp] theorem binaryPhaseScalar_one : binaryPhaseScalar 1 = -1 := by
  norm_num [binaryPhaseScalar]
theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · contradiction
  · rfl
theorem binaryPhaseScalar_add (a b : ZMod 2) :
    binaryPhaseScalar (a + b) = binaryPhaseScalar a * binaryPhaseScalar b := by
  by_cases ha : a = 0
  · subst a
    simp [binaryPhaseScalar]
  · have ha1 : a = 1 := zmod_two_eq_one_of_ne_zero ha
    subst a
    by_cases hb : b = 0
    · subst b
      simp [binaryPhaseScalar]
    · have hb1 : b = 1 := zmod_two_eq_one_of_ne_zero hb
      subst b
      have hone : (1 : ZMod 2) + 1 = 0 := by decide
      simp [binaryPhaseScalar, hone]
theorem binaryPhaseScalar_sum {α : Type u} (s : Finset α) (f : α → ZMod 2) :
    binaryPhaseScalar (Finset.sum s f) =
      Finset.prod s (fun i => binaryPhaseScalar (f i)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp [binaryPhaseScalar]
  · intro a s ha hs
    simp [ha, hs, binaryPhaseScalar_add]
theorem binaryPhaseScalar_eq_one_iff (p : ZMod 2) :
    binaryPhaseScalar p = 1 ↔ p = 0 := by
  fin_cases p <;> norm_num [binaryPhaseScalar]
theorem finTwo_to_zmodTwo_to_fin (b : Fin 2) :
    (if (b : ZMod 2) = 0 then (0 : Fin 2) else 1) = b := by
  fin_cases b
  · change (if (((0 : Fin 2) : ZMod 2) = 0) then (0 : Fin 2) else 1) = 0
    simp
  · have h : (((1 : Fin 2) : ZMod 2) ≠ 0) := by decide
    change (if (((1 : Fin 2) : ZMod 2) = 0) then (0 : Fin 2) else 1) = 1
    simp [h]
theorem zmodTwo_to_finTwo_to_zmod (a : ZMod 2) :
    (((if a = 0 then (0 : Fin 2) else 1) : Fin 2) : ZMod 2) = a := by
  fin_cases a
  · change (((if (0 : ZMod 2) = 0 then (0 : Fin 2) else 1) : Fin 2) : ZMod 2) = 0
    simp
  · have h : (1 : ZMod 2) ≠ 0 := by decide
    change (((if (1 : ZMod 2) = 0 then (0 : Fin 2) else 1) : Fin 2) : ZMod 2) = 1
    simp [h]
theorem finTwo_flipBit_to_zmodTwo (b : Fin 2) :
    ((Semantics.Qubit.flipBit b : Fin 2) : ZMod 2) = (b : ZMod 2) + 1 := by
  fin_cases b
  · change ((Semantics.Qubit.flipBit (0 : Fin 2) : Fin 2) : ZMod 2) =
      ((0 : Fin 2) : ZMod 2) + 1
    norm_num [Semantics.Qubit.flipBit]
  · have h : ((1 : Fin 2) : ZMod 2) + 1 = 0 := by decide
    change ((Semantics.Qubit.flipBit (1 : Fin 2) : Fin 2) : ZMod 2) =
      ((1 : Fin 2) : ZMod 2) + 1
    rw [h]
    norm_num [Semantics.Qubit.flipBit]
theorem zPhase_eq_binaryPhaseScalar_finTwo (b : Fin 2) :
    Semantics.Qubit.zPhase b = binaryPhaseScalar (b : ZMod 2) := by
  fin_cases b
  · change (1 : Complex) = binaryPhaseScalar (0 : ZMod 2)
    exact binaryPhaseScalar_zero.symm
  · change (-1 : Complex) = binaryPhaseScalar (1 : ZMod 2)
    exact binaryPhaseScalar_one.symm
noncomputable def bitstringWordEquiv (ι : Type u) [Fintype ι] :
    Semantics.Qubit.Bitstring ι ≃ Word (ZMod 2) ι where
  toFun bits := fun i => (bits i : ZMod 2)
  invFun x := fun i => if x i = 0 then 0 else 1
  left_inv := by
    intro bits
    funext i
    exact finTwo_to_zmodTwo_to_fin (bits i)
  right_inv := by
    intro x
    funext i
    exact zmodTwo_to_finTwo_to_zmod (x i)
@[simp] theorem bitstringWordEquiv_apply
    (bits : Semantics.Qubit.Bitstring ι) (i : ι) :
    bitstringWordEquiv ι bits i = (bits i : ZMod 2) :=
  rfl
theorem bitstringWordEquiv_flipSupport [DecidableEq ι]
    (x : Word (ZMod 2) ι) (bits : Semantics.Qubit.Bitstring ι) :
    bitstringWordEquiv ι (Semantics.Qubit.flipSupport (binarySupport x) bits) =
      bitstringWordEquiv ι bits + x := by
  funext i
  simp only [Pi.add_apply, bitstringWordEquiv_apply, Semantics.Qubit.flipSupport]
  by_cases hxi : x i = 0
  · have hi : i ∉ binarySupport x := by simp [binarySupport, hxi]
    rw [if_neg hi, hxi]
    exact (@add_zero (ZMod 2) _ (bits i)).symm
  · have hxi_one : x i = 1 := zmod_two_eq_one_of_ne_zero hxi
    have hi : i ∈ binarySupport x := by
      simp [binarySupport, hxi_one]
    rw [if_pos hi, hxi_one]
    exact finTwo_flipBit_to_zmodTwo (bits i)
theorem zSupportPhase_eq_binaryPhaseScalar_wordPairing
    (z : Word (ZMod 2) ι) (bits : Semantics.Qubit.Bitstring ι) :
    Semantics.Qubit.zSupportPhase (binarySupport z) bits =
      binaryPhaseScalar
        (wordPairing (F := ZMod 2) (ι := ι) z (bitstringWordEquiv ι bits)) := by
  rw [Semantics.Qubit.zSupportPhase, binarySupport, wordPairing_apply, dotProduct]
  rw [Finset.prod_filter, binaryPhaseScalar_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases hzi : z i = 0
  · rw [hzi, zero_mul, binaryPhaseScalar_zero]
    simp
  · have hzi_one : z i = 1 := zmod_two_eq_one_of_ne_zero hzi
    calc
      (if z i ≠ 0 then Semantics.Qubit.zPhase (bits i) else 1) =
          Semantics.Qubit.zPhase (bits i) := by
            simp [hzi]
      _ = binaryPhaseScalar (bitstringWordEquiv ι bits i) :=
            zPhase_eq_binaryPhaseScalar_finTwo (bits i)
      _ = binaryPhaseScalar (z i * bitstringWordEquiv ι bits i) := by
            rw [hzi_one, one_mul]
theorem zSupportPhase_eq_one_iff_wordPairing_eq_zero [DecidableEq ι]
    (z : Word (ZMod 2) ι) (bits : Semantics.Qubit.Bitstring ι) :
    Semantics.Qubit.zSupportPhase (binarySupport z) bits = 1 ↔
      wordPairing (F := ZMod 2) (ι := ι) z (bitstringWordEquiv ι bits) = 0 := by
  rw [zSupportPhase_eq_binaryPhaseScalar_wordPairing]
  exact binaryPhaseScalar_eq_one_iff _
variable [DecidableEq ι]
abbrev Binary (ι : Type u) [Fintype ι] :=
  PauliSymplectic (ZMod 2) ι
noncomputable def binaryEquivPhaseXPartZPart :
    Binary ι ≃ ZMod 2 × Word (ZMod 2) ι × Word (ZMod 2) ι where
  toFun P := (P.phase, P.vector.xPart, P.vector.zPart)
  invFun p := { phase := p.1, vector := { xPart := p.2.1, zPart := p.2.2 } }
  left_inv := by
    intro P
    rcases P with ⟨phase, vector⟩
    rcases vector with ⟨x, z⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨phase, x, z⟩
    rfl
noncomputable instance instFintypeBinary : Fintype (Binary ι) :=
  Fintype.ofEquiv (ZMod 2 × Word (ZMod 2) ι × Word (ZMod 2) ι)
    (binaryEquivPhaseXPartZPart (ι := ι)).symm
abbrev cssXCheck (x : Word (ZMod 2) ι) : Binary ι :=
  { phase := 0, vector := { xPart := x, zPart := 0 } }
abbrev cssZCheck (z : Word (ZMod 2) ι) : Binary ι :=
  { phase := 0, vector := { xPart := 0, zPart := z } }
def binaryCSSCheckSet (xCode zCode : LinearCode (ZMod 2) ι) : Set (Binary ι) :=
  {P | (∃ x, x ∈ xCode.carrier ∧ P = cssXCheck x) ∨
       (∃ z, z ∈ zCode.carrier ∧ P = cssZCheck z)}
def xSupport (P : Binary ι) : Finset ι :=
  binarySupport P.vector.xPart
def zSupport (P : Binary ι) : Finset ι :=
  binarySupport P.vector.zPart
def support (P : Binary ι) : Finset ι :=
  xSupport P ∪ zSupport P
@[simp] theorem mem_support (P : Binary ι) (i : ι) :
    i ∈ support P ↔ i ∈ xSupport P ∨ i ∈ zSupport P := by
  simp [support]
def weight (P : Binary ι) : Nat :=
  (support P).card
def binaryOne : Binary ι :=
  { phase := 0, vector := { xPart := 0, zPart := 0 } }
@[simp] theorem support_binaryOne :
    support (binaryOne (ι := ι)) = ∅ := by
  ext i
  simp [binaryOne, support, xSupport, zSupport, binarySupport]
@[simp] theorem weight_binaryOne :
    weight (binaryOne (ι := ι)) = 0 := by
  simp [weight]
def scopedByWeightFinset (B : Nat) : Finset (Binary ι) :=
  Finset.univ.filter fun P => weight P ≤ B
def scopedByWeight (B : Nat) : Set (Binary ι) :=
  {P | P ∈ scopedByWeightFinset (ι := ι) B}
@[simp] theorem mem_scopedByWeight (B : Nat) (P : Binary ι) :
    P ∈ scopedByWeight (ι := ι) B ↔ weight P ≤ B := by
  simp [scopedByWeight, scopedByWeightFinset]
@[simp] theorem support_cssXCheck (x : Word (ZMod 2) ι) :
    support (cssXCheck x) = hammingSupport x := by
  ext i
  simp [support, xSupport, zSupport, binarySupport, hammingSupport]
@[simp] theorem support_cssZCheck (z : Word (ZMod 2) ι) :
    support (cssZCheck z) = hammingSupport z := by
  ext i
  simp [support, xSupport, zSupport, binarySupport, hammingSupport]
@[simp] theorem weight_cssXCheck_eq_hammingWeight (x : Word (ZMod 2) ι) :
    weight (cssXCheck x) = HammingWeight x := by
  simp [weight, HammingWeight]
@[simp] theorem weight_cssZCheck_eq_hammingWeight (z : Word (ZMod 2) ι) :
    weight (cssZCheck z) = HammingWeight z := by
  simp [weight, HammingWeight]
def binarySwapPhase (x z : Word (ZMod 2) ι) : Complex :=
  Semantics.Qubit.supportPhaseSign (binarySupport x) (binarySupport z)
@[simp] theorem binaryPhaseScalar_star (p : ZMod 2) :
    star (binaryPhaseScalar p) = binaryPhaseScalar p := by
  by_cases hp : p = 0
  · simp [binaryPhaseScalar, hp]
  · have hp1 : p = 1 := zmod_two_eq_one_of_ne_zero hp
    subst p
    norm_num [binaryPhaseScalar]
def binaryMulPhase (P Q : Binary ι) : ZMod 2 :=
  P.phase + Q.phase + Finset.sum Finset.univ (fun i => Q.vector.xPart i * P.vector.zPart i)
def binaryMul (P Q : Binary ι) : Binary ι :=
  { phase := binaryMulPhase P Q
    vector := { xPart := P.vector.xPart + Q.vector.xPart
                zPart := P.vector.zPart + Q.vector.zPart } }
omit [DecidableEq ι] in
@[simp] theorem binaryMul_cssXCheck (x y : Word (ZMod 2) ι) :
    binaryMul (cssXCheck x) (cssXCheck y) = cssXCheck (x + y) := by
  simp [binaryMul, binaryMulPhase]
omit [DecidableEq ι] in
@[simp] theorem binaryMul_cssZCheck (z w : Word (ZMod 2) ι) :
    binaryMul (cssZCheck z) (cssZCheck w) = cssZCheck (z + w) := by
  simp [binaryMul, binaryMulPhase]
def binaryDaggerPhase (P : Binary ι) : ZMod 2 :=
  P.phase + Finset.sum Finset.univ (fun i => P.vector.xPart i * P.vector.zPart i)
def binaryDagger (P : Binary ι) : Binary ι :=
  { phase := binaryDaggerPhase P
    vector := P.vector }
omit [DecidableEq ι] in
@[simp] theorem binaryDagger_binaryOne :
    binaryDagger (binaryOne (ι := ι)) = binaryOne := by
  simp [binaryDagger, binaryDaggerPhase, binaryOne]
omit [DecidableEq ι] in
@[simp] theorem binaryDagger_cssXCheck (x : Word (ZMod 2) ι) :
    binaryDagger (cssXCheck x) = cssXCheck x := by
  simp [binaryDagger, binaryDaggerPhase, cssXCheck]
omit [DecidableEq ι] in
@[simp] theorem binaryDagger_cssZCheck (z : Word (ZMod 2) ι) :
    binaryDagger (cssZCheck z) = cssZCheck z := by
  simp [binaryDagger, binaryDaggerPhase, cssZCheck]
omit [DecidableEq ι] in
@[simp] theorem binaryMul_binaryOne_left (P : Binary ι) :
    binaryMul (binaryOne (ι := ι)) P = P := by
  rcases P with ⟨phase, vector⟩
  rcases vector with ⟨x, z⟩
  simp [binaryMul, binaryMulPhase, binaryOne]
omit [DecidableEq ι] in
@[simp] theorem binaryMul_binaryOne_right (P : Binary ι) :
    binaryMul P (binaryOne (ι := ι)) = P := by
  rcases P with ⟨phase, vector⟩
  rcases vector with ⟨x, z⟩
  simp [binaryMul, binaryMulPhase, binaryOne]
omit [DecidableEq ι] in
@[simp] theorem binaryMul_binaryDagger_left (P : Binary ι) :
    binaryMul (binaryDagger P) P = binaryOne := by
  rcases P with ⟨phase, vector⟩
  rcases vector with ⟨x, z⟩
  have hbit_add_self (a : ZMod 2) : a + a = 0 := by
    by_cases ha : a = 0
    · simp [ha]
    · have ha1 : a = 1 := zmod_two_eq_one_of_ne_zero ha
      subst a
      decide
  simp [binaryMul, binaryMulPhase, binaryDagger, binaryDaggerPhase, binaryOne]
  constructor
  · let s : ZMod 2 := ∑ i, x i * z i
    change phase + s + phase + s = 0
    calc
      phase + s + phase + s = (phase + phase) + (s + s) := by abel
      _ = 0 := by simp [hbit_add_self]
  constructor
  · funext i
    exact hbit_add_self (x i)
  · funext i
    exact hbit_add_self (z i)
@[simp] theorem support_binaryDagger (P : Binary ι) :
    support (binaryDagger P) = support P := by
  rfl
@[simp] theorem weight_binaryDagger (P : Binary ι) :
    weight (binaryDagger P) = weight P := by
  rfl
def toQubitOperator (P : Binary ι) :
    Semantics.Operator (Semantics.Qubit.QubitRegister ι) :=
  binaryPhaseScalar P.phase •
    (Semantics.Qubit.localXSupport (xSupport P) *
      Semantics.Qubit.localZSupport (zSupport P))
@[simp] theorem toQubitOperator_apply (P : Binary ι)
    (ψ : Semantics.Qubit.QubitRegister ι) (bits : Semantics.Qubit.Bitstring ι) :
    toQubitOperator P ψ bits =
      binaryPhaseScalar P.phase *
        (Semantics.Qubit.zSupportPhase (zSupport P)
          (Semantics.Qubit.flipSupport (xSupport P) bits) *
            ψ (Semantics.Qubit.flipSupport (xSupport P) bits)) := by
  simp [toQubitOperator, Module.End.mul_apply, smul_eq_mul]
def scopedErrorOperators (B : Nat) :
    Set (Semantics.Operator (Semantics.Qubit.QubitRegister ι)) :=
  Set.image toQubitOperator (scopedByWeight (ι := ι) B)
noncomputable def scopedErrorFamily (B : Nat) :
    Semantics.FiniteKrausFamily {P : Binary ι // P ∈ scopedByWeight (ι := ι) B}
      (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι) where
  operator P := toQubitOperator P.1
omit [DecidableEq ι] in
/-- Binary CSS X checks commute algebraically in Pauli-symplectic coordinates. -/
theorem cssXCheck_commutes_cssXCheck (x y : Word (ZMod 2) ι) :
    Commutes (cssXCheck x) (cssXCheck y) := by
  simp [Commutes, symplecticForm]
omit [DecidableEq ι] in
/-- Binary CSS Z checks commute algebraically in Pauli-symplectic coordinates. -/
theorem cssZCheck_commutes_cssZCheck (z w : Word (ZMod 2) ι) :
    Commutes (cssZCheck z) (cssZCheck w) := by
  simp [Commutes, symplecticForm]
omit [DecidableEq ι] in
/--
Binary CSS X/Z checks commute algebraically when the `Z` word lies in the dual
of the classical code containing the `X` word.
-/
theorem cssXCheck_commutes_cssZCheck_of_mem_dual
    (C : LinearCode (ZMod 2) ι) {x z : Word (ZMod 2) ι}
    (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    Commutes (cssXCheck x) (cssZCheck z) := by
  exact
    (by
      simpa [cssXCheck, cssZCheck, Commutes] using
        LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual C hx hz)
omit [DecidableEq ι] in
/-- Binary CSS X/Z checks commute algebraically under `zCode ≤ xCode.dual`. -/
theorem cssXCheck_commutes_cssZCheck_of_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {x z : Word (ZMod 2) ι}
    (hx : x ∈ xCode.carrier) (hz : z ∈ zCode.carrier) :
    Commutes (cssXCheck x) (cssZCheck z) :=
  cssXCheck_commutes_cssZCheck_of_mem_dual xCode hx (hdual hz)
omit [DecidableEq ι] in
/--
Binary CSS Z/X checks commute algebraically in the reverse orientation. The
proof explicitly reduces the reversed symplectic form to the negated X/Z form.
-/
theorem cssZCheck_commutes_cssXCheck_of_mem_dual
    (C : LinearCode (ZMod 2) ι) {x z : Word (ZMod 2) ι}
    (hx : x ∈ C.carrier) (hz : z ∈ C.dual.carrier) :
    Commutes (cssZCheck z) (cssXCheck x) := by
  have hXZ :
      symplecticForm ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
          ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) = 0 :=
    LinearCode.symplecticForm_x_zero_zero_z_eq_zero_of_mem_dual C hx hz
  rw [cssZCheck, cssXCheck, Commutes]
  calc
    symplecticForm ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι)
        ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
        = -symplecticForm
            ({ xPart := x, zPart := 0 } : SymplecticVector (ZMod 2) ι)
            ({ xPart := 0, zPart := z } : SymplecticVector (ZMod 2) ι) := by
          simp [symplecticForm, mul_comm]
    _ = 0 := by
          simp [hXZ]
omit [DecidableEq ι] in
/-- Binary CSS Z/X checks commute algebraically under `zCode ≤ xCode.dual`. -/
theorem cssZCheck_commutes_cssXCheck_of_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {x z : Word (ZMod 2) ι}
    (hz : z ∈ zCode.carrier) (hx : x ∈ xCode.carrier) :
    Commutes (cssZCheck z) (cssXCheck x) :=
  cssZCheck_commutes_cssXCheck_of_mem_dual xCode hx (hdual hz)
omit [DecidableEq ι] in
/-- If a word is not in a binary code dual, some codeword has nonzero pairing with it. -/
theorem exists_carrier_wordPairing_ne_zero_of_not_mem_dual
    (C : LinearCode (ZMod 2) ι) {x : Word (ZMod 2) ι}
    (hx : x ∉ C.dual.carrier) :
    ∃ c, c ∈ C.carrier ∧ wordPairing (F := ZMod 2) (ι := ι) x c ≠ 0 := by
  classical
  have hnotOrth :
      ¬ ∀ c : Word (ZMod 2) ι, c ∈ C.carrier →
        wordPairing (F := ZMod 2) (ι := ι) x c = 0 := by
    intro horth
    exact hx ((C.mem_dual x).2 horth)
  rcases not_forall.mp hnotOrth with ⟨c, hc⟩
  have hc' :
      c ∈ C.carrier ∧ wordPairing (F := ZMod 2) (ι := ι) x c ≠ 0 :=
    Classical.not_imp.mp hc
  exact ⟨c, hc'.1, hc'.2⟩
inductive GeneratedStabilizer {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) : Binary ι → Prop
  | one : GeneratedStabilizer generators (binaryOne (ι := ι))
  | generator (j : κ) : GeneratedStabilizer generators (generators j)
  | mul {P Q : Binary ι} : GeneratedStabilizer generators P →
      GeneratedStabilizer generators Q →
      GeneratedStabilizer generators (binaryMul P Q)
  | dagger {P : Binary ι} : GeneratedStabilizer generators P →
      GeneratedStabilizer generators (binaryDagger P)
def generatedStabilizerSet {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) : Set (Binary ι) :=
  {P | GeneratedStabilizer generators P}
omit [DecidableEq ι] in
@[simp] theorem commutes_binaryOne_right (E : Binary ι) :
    Commutes E (binaryOne (ι := ι)) := by
  simp [Commutes, binaryOne, symplecticForm]
def InStabilizerNormalizer {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E : Binary ι) : Prop :=
  ∀ S, GeneratedStabilizer generators S → Commutes E S
def stabilizerNormalizer {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) : Set (Binary ι) :=
  {E | InStabilizerNormalizer generators E}
def binarySign (phase : ZMod 2) : Binary ι :=
  { phase := phase, vector := { xPart := 0, zPart := 0 } }
def BinaryUpToSign (P Q : Binary ι) : Prop :=
  P.vector = Q.vector
omit [DecidableEq ι] in
@[refl] theorem binaryUpToSign_refl (P : Binary ι) : BinaryUpToSign P P := rfl
omit [DecidableEq ι] in
@[symm] theorem binaryUpToSign_symm {P Q : Binary ι} :
    BinaryUpToSign P Q → BinaryUpToSign Q P :=
  Eq.symm
omit [DecidableEq ι] in
@[trans] theorem binaryUpToSign_trans {P Q R : Binary ι} :
    BinaryUpToSign P Q → BinaryUpToSign Q R → BinaryUpToSign P R :=
  Eq.trans
omit [DecidableEq ι] in
@[simp] theorem binaryUpToSign_binaryDagger (P : Binary ι) :
    BinaryUpToSign (binaryDagger P) P := rfl
def InGeneratedStabilizerUpToSign {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E : Binary ι) : Prop :=
  ∃ S, GeneratedStabilizer generators S ∧ BinaryUpToSign E S
def StabilizerEquivalent {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E F : Binary ι) : Prop :=
  InGeneratedStabilizerUpToSign generators (binaryMul (binaryDagger E) F)
def DegenerateErrorPair {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E F : Binary ι) : Prop :=
  StabilizerEquivalent generators E F
def stabilizerSyndromeBit (M E : Binary ι) : ZMod 2 :=
  symplecticForm E.vector M.vector
def stabilizerSyndrome {κ : Type w} [Fintype κ]
    (generators : κ → Binary ι) (E : Binary ι) : κ → ZMod 2 :=
  fun j => stabilizerSyndromeBit (generators j) E
omit [DecidableEq ι] in
@[simp] theorem stabilizerSyndrome_apply
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    (E : Binary ι) (j : κ) :
    stabilizerSyndrome generators E j = stabilizerSyndromeBit (generators j) E := rfl
omit [DecidableEq ι] in
/-- A check set distinguishes a binary Pauli representative from identity. -/
def checkDistinguishes (checks : Set (Binary ι)) (E : Binary ι) : Prop :=
  ∃ S, S ∈ checks ∧ ¬ Commutes E S
omit [DecidableEq ι] in
/--
Pair-level check separation, phrased through the binary representative of
`E† * F`. This is internal vocabulary, not a public syndrome theorem.
-/
def syndromeSeparatedByCheckSet (checks : Set (Binary ι))
    (E F : Binary ι) : Prop :=
  checkDistinguishes checks (binaryMul (binaryDagger E) F)
omit [DecidableEq ι] in
/--
The scoped binary CSS check set is pairwise commuting from the explicit
dual-containment hypothesis `zCode ≤ xCode.dual`.
-/
theorem binaryCSSCheckSet_pairwise_commutes_of_dual_le
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode →
      ∀ Q : Binary ι, Q ∈ binaryCSSCheckSet xCode zCode → Commutes P Q := by
  intro P hP Q hQ
  rw [binaryCSSCheckSet] at hP hQ
  rcases hP with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
  · rcases hQ with ⟨y, _hy, rfl⟩ | ⟨w, hw, rfl⟩
    · exact cssXCheck_commutes_cssXCheck x y
    · exact cssXCheck_commutes_cssZCheck_of_dual_le xCode zCode hdual hx hw
  · rcases hQ with ⟨y, hy, rfl⟩ | ⟨w, _hw, rfl⟩
    · exact cssZCheck_commutes_cssXCheck_of_dual_le xCode zCode hdual hz hy
    · exact cssZCheck_commutes_cssZCheck z w
omit [DecidableEq ι] in
/--
The binary CSS `X` code, pulled back as a submodule of the `Z`-dual carrier.
Under dual containment it is equivalent to `xCode.carrier`; without that
hypothesis it is the actual intersection with `zCode.dual.carrier`.
-/
noncomputable def binaryCSSXCodeInZDual
    (xCode zCode : LinearCode (ZMod 2) ι) :
    Submodule (ZMod 2) zCode.dual.carrier :=
  xCode.carrier.comap zCode.dual.carrier.subtype
omit [DecidableEq ι] in
/--
Dual containment `zCode ≤ xCode.dual` places the `X` code inside the `Z` dual.
The inclusion is derived from `LinearCode.le_dual_of_le_dual`, not assumed.
-/
noncomputable def binaryCSSXCodeInZDualEquiv
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    binaryCSSXCodeInZDual xCode zCode ≃ₗ[ZMod 2] xCode.carrier :=
  Submodule.comapSubtypeEquivOfLe
    (LinearCode.le_dual_of_le_dual xCode zCode hdual)
omit [DecidableEq ι] in
/-- Algebraic binary CSS logical-basis quotient `zCode.dual / xCode`. -/
noncomputable abbrev binaryCSSLogicalBasisQuotient
    (xCode zCode : LinearCode (ZMod 2) ι) :=
  zCode.dual.carrier ⧸ binaryCSSXCodeInZDual xCode zCode
omit [DecidableEq ι] in
@[simp] theorem finrank_binaryCSSXCodeInZDual_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Module.finrank (ZMod 2) (binaryCSSXCodeInZDual xCode zCode) =
      Dimension xCode := by
  rw [Dimension_eq_finrank_carrier]
  exact (binaryCSSXCodeInZDualEquiv xCode zCode hdual).finrank_eq
def binaryStabilizerFixedSubmodule (S : Set (Binary ι)) :
    Submodule Complex (Semantics.Qubit.QubitRegister ι) where
  carrier := {ψ | ∀ P : Binary ι, P ∈ S → toQubitOperator P ψ = ψ}
  zero_mem' := by
    intro P _hP
    simp
  add_mem' := by
    intro ψ φ hψ hφ P hP
    rw [map_add, hψ P hP, hφ P hP]
  smul_mem' := by
    intro c ψ hψ P hP
    rw [map_smul, hψ P hP]
@[simp] theorem mem_binaryStabilizerFixedSubmodule
    (S : Set (Binary ι)) (ψ : Semantics.Qubit.QubitRegister ι) :
    ψ ∈ binaryStabilizerFixedSubmodule S ↔
      ∀ P : Binary ι, P ∈ S → toQubitOperator P ψ = ψ :=
  Iff.rfl
def binaryStabilizerCommonFixedQuantumCode (S : Set (Binary ι)) :
    Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι) where
  carrier := binaryStabilizerFixedSubmodule S
@[simp] theorem mem_binaryStabilizerCommonFixedQuantumCode_carrier
    (S : Set (Binary ι)) (ψ : Semantics.Qubit.QubitRegister ι) :
    ψ ∈ (binaryStabilizerCommonFixedQuantumCode S).carrier ↔
      ∀ P : Binary ι, P ∈ S → toQubitOperator P ψ = ψ :=
  Iff.rfl
def binaryCSSStabilizerCodeOfDualLe
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    StabilizerCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι) where
  stabilizers := binaryCSSCheckSet xCode zCode
  code := binaryStabilizerCommonFixedQuantumCode (binaryCSSCheckSet xCode zCode)
  isotropic := binaryCSSCheckSet_pairwise_commutes_of_dual_le xCode zCode hdual
noncomputable def binaryCSSQuantumCodeOfDualLe
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Semantics.QuantumCode (Semantics.Qubit.QubitRegister ι) :=
  (binaryCSSStabilizerCodeOfDualLe xCode zCode hdual).code
@[simp] theorem mem_binaryCSSQuantumCodeOfDualLe_carrier
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (ψ : Semantics.Qubit.QubitRegister ι) :
    ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier ↔
      ∀ P : Binary ι, P ∈ binaryCSSCheckSet xCode zCode → toQubitOperator P ψ = ψ := by
  simp [binaryCSSQuantumCodeOfDualLe, binaryCSSStabilizerCodeOfDualLe]
noncomputable def scopedErrorFamilyKLScalar (t : Nat)
    (E F : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t}) : Complex :=
  if (binaryMul (binaryDagger E.1) F.1).vector.xPart = 0 ∧
      (binaryMul (binaryDagger E.1) F.1).vector.zPart = 0 then
    binaryPhaseScalar (binaryMul (binaryDagger E.1) F.1).phase
  else
    0
theorem binaryCSSQuantumCodeOfDualLe_apply_flipSupport_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    {x : Word (ZMod 2) ι} (hx : x ∈ xCode.carrier)
    (bits : Semantics.Qubit.Bitstring ι) :
    ψ (Semantics.Qubit.flipSupport (binarySupport x) bits) = ψ bits := by
  have hfixed :
      toQubitOperator (cssXCheck x) ψ = ψ :=
    (mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual ψ).1 hψ
      (cssXCheck x) (Or.inl ⟨x, hx, rfl⟩)
  have hbits : toQubitOperator (cssXCheck x) ψ bits = ψ bits := by
    simpa using congrArg (fun φ : Semantics.Qubit.QubitRegister ι => φ bits) hfixed
  simpa [cssXCheck, xSupport, zSupport, Semantics.Qubit.zSupportPhase] using hbits
noncomputable def scopedAmplitudeErrorFamily (t : Nat)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex) :
    Semantics.FiniteKrausFamily {P : Binary ι // P ∈ scopedByWeight (ι := ι) t}
      (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι) :=
  (scopedErrorFamily (ι := ι) t).scale amp
@[simp]
theorem scopedAmplitudeErrorFamily_operator (t : Nat)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex)
    (P : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t}) :
    (scopedAmplitudeErrorFamily (ι := ι) t amp).operator P =
      amp P • toQubitOperator P.1 :=
  rfl
theorem binaryCSSQuantumCodeOfDualLe_apply_eq_zero_of_not_mem_zDual
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    {bits : Semantics.Qubit.Bitstring ι}
    (hbits : bitstringWordEquiv ι bits ∉ zCode.dual.carrier) :
    ψ bits = 0 := by
  rcases exists_carrier_wordPairing_ne_zero_of_not_mem_dual zCode hbits with
    ⟨z, hz, hpair⟩
  have hfixed :
      toQubitOperator (cssZCheck z) ψ = ψ :=
    (mem_binaryCSSQuantumCodeOfDualLe_carrier xCode zCode hdual ψ).1 hψ
      (cssZCheck z) (Or.inr ⟨z, hz, rfl⟩)
  have hbitsFixed : toQubitOperator (cssZCheck z) ψ bits = ψ bits := by
    simpa using congrArg (fun φ : Semantics.Qubit.QubitRegister ι => φ bits) hfixed
  have hphase_mul :
      Semantics.Qubit.zSupportPhase (binarySupport z) bits * ψ bits = ψ bits := by
    simpa [cssZCheck, xSupport, zSupport] using hbitsFixed
  have hpair' :
      wordPairing (F := ZMod 2) (ι := ι) z (bitstringWordEquiv ι bits) ≠ 0 := by
    intro hzero
    exact hpair (by simpa [wordPairing_apply, dotProduct_comm] using hzero)
  have hphase_ne_one :
      Semantics.Qubit.zSupportPhase (binarySupport z) bits ≠ 1 := by
    intro hphase
    exact hpair' ((zSupportPhase_eq_one_iff_wordPairing_eq_zero z bits).1 hphase)
  have hfactor_ne_zero :
      Semantics.Qubit.zSupportPhase (binarySupport z) bits - 1 ≠ 0 := by
    intro hzero
    exact hphase_ne_one (sub_eq_zero.mp hzero)
  have hmul_zero :
      (Semantics.Qubit.zSupportPhase (binarySupport z) bits - 1) * ψ bits = 0 := by
    rw [sub_mul, one_mul, hphase_mul, sub_self]
  exact (mul_eq_zero.mp hmul_zero).resolve_left hfactor_ne_zero
theorem binaryCSSQuantumCodeOfDualLe_apply_eq_of_quotient_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {ψ : Semantics.Qubit.QubitRegister ι}
    (hψ : ψ ∈ (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    {u v : zCode.dual.carrier}
    (h : Submodule.Quotient.mk u =
      (Submodule.Quotient.mk v : binaryCSSLogicalBasisQuotient xCode zCode)) :
    ψ ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) =
      ψ ((bitstringWordEquiv ι).symm (v : Word (ZMod 2) ι)) := by
  have hdiff :
      u - v ∈ binaryCSSXCodeInZDual xCode zCode :=
    (Submodule.Quotient.eq (binaryCSSXCodeInZDual xCode zCode)).1 h
  have hx : ((u : Word (ZMod 2) ι) - (v : Word (ZMod 2) ι)) ∈ xCode.carrier := by
    change ((u - v : zCode.dual.carrier) : Word (ZMod 2) ι) ∈ xCode.carrier at hdiff
    exact hdiff
  have hbits :
      Semantics.Qubit.flipSupport
          (binarySupport ((u : Word (ZMod 2) ι) - (v : Word (ZMod 2) ι)))
          ((bitstringWordEquiv ι).symm (v : Word (ZMod 2) ι)) =
        (bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι) := by
    apply (bitstringWordEquiv ι).injective
    rw [bitstringWordEquiv_flipSupport]
    simp [sub_eq_add_neg, add_left_comm]
  have hflip :=
    binaryCSSQuantumCodeOfDualLe_apply_flipSupport_eq
      xCode zCode hdual hψ hx ((bitstringWordEquiv ι).symm (v : Word (ZMod 2) ι))
  simpa [hbits] using hflip
noncomputable def binaryCSSLogicalBasisQuotientToQubitRegister
    (xCode zCode : LinearCode (ZMod 2) ι) :
    EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode) →ₗ[Complex]
      Semantics.Qubit.QubitRegister ι where
  toFun φ := WithLp.toLp 2 fun bits =>
    if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
      φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
    else
      0
  map_add' := by
    intro φ χ
    ext bits
    change
      (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
          (φ + χ) (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
        else
          0) =
        (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
          φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
        else
          0) +
        (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
          χ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
        else
          0)
    by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
    · rw [dif_pos hbits, dif_pos hbits, dif_pos hbits]
      rfl
    · rw [dif_neg hbits, dif_neg hbits, dif_neg hbits]
      simp
  map_smul' := by
    intro a φ
    ext bits
    change
      (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
          (a • φ) (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
        else
          0) =
        a *
          (if hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
            φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
          else
            0)
    by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
    · rw [dif_pos hbits, dif_pos hbits]
      rfl
    · rw [dif_neg hbits, dif_neg hbits]
      simp
omit [DecidableEq ι] in
@[simp] theorem binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem
    (xCode zCode : LinearCode (ZMod 2) ι)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode))
    {bits : Semantics.Qubit.Bitstring ι}
    (hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier) :
    binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits =
      φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩) := by
  change
    (if h : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
        φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, h⟩)
      else
        0) =
      φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, hbits⟩)
  rw [dif_pos hbits]
omit [DecidableEq ι] in
@[simp] theorem binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem
    (xCode zCode : LinearCode (ZMod 2) ι)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode))
    {bits : Semantics.Qubit.Bitstring ι}
    (hbits : bitstringWordEquiv ι bits ∉ zCode.dual.carrier) :
    binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits = 0 := by
  change
    (if h : bitstringWordEquiv ι bits ∈ zCode.dual.carrier then
        φ (Submodule.Quotient.mk ⟨bitstringWordEquiv ι bits, h⟩)
      else
        0) =
      0
  rw [dif_neg hbits]
theorem binaryCSSLogicalBasisQuotientToQubitRegister_apply_flipSupport_eq
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode))
    {x : Word (ZMod 2) ι} (hx : x ∈ xCode.carrier)
    (bits : Semantics.Qubit.Bitstring ι) :
    binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ
        (Semantics.Qubit.flipSupport (binarySupport x) bits) =
      binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits := by
  have hxDual : x ∈ zCode.dual.carrier :=
    LinearCode.le_dual_of_le_dual xCode zCode hdual hx
  by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
  · have hflip :
        bitstringWordEquiv ι (Semantics.Qubit.flipSupport (binarySupport x) bits) ∈
          zCode.dual.carrier := by
      rw [bitstringWordEquiv_flipSupport]
      exact zCode.dual.carrier.add_mem hbits hxDual
    rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem xCode zCode φ hflip,
      binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem xCode zCode φ hbits]
    apply congrArg φ
    rw [Submodule.Quotient.eq]
    change
      (bitstringWordEquiv ι (Semantics.Qubit.flipSupport (binarySupport x) bits) -
          bitstringWordEquiv ι bits) ∈ xCode.carrier
    simpa [bitstringWordEquiv_flipSupport, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hx
  · have hflip :
        bitstringWordEquiv ι (Semantics.Qubit.flipSupport (binarySupport x) bits) ∉
          zCode.dual.carrier := by
      intro hflipMem
      apply hbits
      have hsum : bitstringWordEquiv ι bits + x ∈ zCode.dual.carrier := by
        simpa [bitstringWordEquiv_flipSupport] using hflipMem
      have hsub : bitstringWordEquiv ι bits + x - x ∈ zCode.dual.carrier :=
        zCode.dual.carrier.sub_mem hsum hxDual
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
    rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem xCode zCode φ hflip,
      binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem xCode zCode φ hbits]
theorem zSupportPhase_mul_binaryCSSLogicalBasisQuotientToQubitRegister_apply
    (xCode zCode : LinearCode (ZMod 2) ι)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode))
    {z : Word (ZMod 2) ι} (hz : z ∈ zCode.carrier)
    (bits : Semantics.Qubit.Bitstring ι) :
    Semantics.Qubit.zSupportPhase (binarySupport z) bits *
        binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits =
      binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ bits := by
  by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
  · have hpair :
        wordPairing (F := ZMod 2) (ι := ι) z (bitstringWordEquiv ι bits) = 0 := by
      have horth := zCode.orthogonal_of_mem_dual hbits hz
      simpa [wordPairing_apply, dotProduct_comm] using horth
    have hphase : Semantics.Qubit.zSupportPhase (binarySupport z) bits = 1 :=
      (zSupportPhase_eq_one_iff_wordPairing_eq_zero z bits).2 hpair
    simp [hphase]
  · rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem xCode zCode φ hbits]
    simp
theorem binaryCSSLogicalBasisQuotientToQubitRegister_mem_carrier
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (φ : EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode)) :
    binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ ∈
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier := by
  rw [mem_binaryCSSQuantumCodeOfDualLe_carrier]
  intro P hP
  ext bits
  rcases hP with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
  · simpa [cssXCheck, xSupport, zSupport, Semantics.Qubit.zSupportPhase] using
      binaryCSSLogicalBasisQuotientToQubitRegister_apply_flipSupport_eq
        xCode zCode hdual φ hx bits
  · simpa [cssZCheck, xSupport, zSupport] using
      zSupportPhase_mul_binaryCSSLogicalBasisQuotientToQubitRegister_apply
        xCode zCode φ hz bits
noncomputable def binaryCSSLogicalBasisQuotientToCarrier
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode) →ₗ[Complex]
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier :=
  (binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode).codRestrict
    (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier
    (binaryCSSLogicalBasisQuotientToQubitRegister_mem_carrier xCode zCode hdual)
noncomputable def binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier →ₗ[Complex]
      EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode) where
  toFun ψ := WithLp.toLp 2 fun q =>
    Quotient.liftOn q
      (fun u : zCode.dual.carrier =>
        (ψ : Semantics.Qubit.QubitRegister ι)
          ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)))
      (fun u v h => by
        exact binaryCSSQuantumCodeOfDualLe_apply_eq_of_quotient_eq
          xCode zCode hdual ψ.2 (Quotient.sound h))
  map_add' := by
    intro ψ φ
    ext q
    refine Submodule.Quotient.induction_on
      (p := binaryCSSXCodeInZDual xCode zCode) q ?_
    intro u
    change
      (↑(ψ + φ) : Semantics.Qubit.QubitRegister ι)
          ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) =
        (ψ : Semantics.Qubit.QubitRegister ι)
            ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) +
          (φ : Semantics.Qubit.QubitRegister ι)
            ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι))
    rfl
  map_smul' := by
    intro a ψ
    ext q
    refine Submodule.Quotient.induction_on
      (p := binaryCSSXCodeInZDual xCode zCode) q ?_
    intro u
    change
      (↑(a • ψ) : Semantics.Qubit.QubitRegister ι)
          ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) =
        a *
          (ψ : Semantics.Qubit.QubitRegister ι)
            ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι))
    rfl
@[simp] theorem binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient_apply_mk
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    (ψ : (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier)
    (u : zCode.dual.carrier) :
    binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient xCode zCode hdual ψ
        (Submodule.Quotient.mk u : binaryCSSLogicalBasisQuotient xCode zCode) =
      (ψ : Semantics.Qubit.QubitRegister ι)
        ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) := by
  rfl
noncomputable def binaryCSSQuantumCodeOfDualLeCarrierEquivLogicalBasisQuotient
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    (binaryCSSQuantumCodeOfDualLe xCode zCode hdual).carrier ≃ₗ[Complex]
      EuclideanSpace Complex (binaryCSSLogicalBasisQuotient xCode zCode) where
  toFun ψ := binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
    xCode zCode hdual ψ
  invFun φ := binaryCSSLogicalBasisQuotientToCarrier xCode zCode hdual φ
  left_inv := by
    intro ψ
    ext bits
    by_cases hbits : bitstringWordEquiv ι bits ∈ zCode.dual.carrier
    · change
        binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode
            (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
              xCode zCode hdual ψ) bits =
          (ψ : Semantics.Qubit.QubitRegister ι) bits
      rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem xCode zCode
        (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient xCode zCode hdual ψ)
        hbits]
      rw [binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient_apply_mk]
      simp
    · have hzero :=
        binaryCSSQuantumCodeOfDualLe_apply_eq_zero_of_not_mem_zDual
          xCode zCode hdual ψ.2 hbits
      change
        binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode
            (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
              xCode zCode hdual ψ) bits =
          (ψ : Semantics.Qubit.QubitRegister ι) bits
      rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_not_mem xCode zCode
        (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient xCode zCode hdual ψ)
        hbits]
      simp [hzero]
  right_inv := by
    intro φ
    ext q
    refine Submodule.Quotient.induction_on
      (p := binaryCSSXCodeInZDual xCode zCode) q ?_
    intro u
    rw [binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient_apply_mk]
    have hu :
        bitstringWordEquiv ι ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) ∈
          zCode.dual.carrier := by
      rw [Equiv.apply_symm_apply]
      exact u.property
    change
      binaryCSSLogicalBasisQuotientToQubitRegister xCode zCode φ
          ((bitstringWordEquiv ι).symm (u : Word (ZMod 2) ι)) =
        φ (Submodule.Quotient.mk u)
    rw [binaryCSSLogicalBasisQuotientToQubitRegister_apply_of_mem xCode zCode φ hu]
    apply congrArg (fun q : binaryCSSLogicalBasisQuotient xCode zCode => φ q)
    congr 1
    apply Subtype.ext
    simp
  map_add' := by
    intro ψ φ
    exact (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
      xCode zCode hdual).map_add ψ φ
  map_smul' := by
    intro a ψ
    exact (binaryCSSQuantumCodeOfDualLeCarrierToLogicalBasisQuotient
      xCode zCode hdual).map_smul a ψ
end PauliSymplectic
namespace ChainComplexData
noncomputable def binaryCSSCode
    {ι κ C2 : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [AddCommGroup C2] [Module (ZMod 2) C2]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) κ) (Word (ZMod 2) ι) C2) :
    CSSCode (ZMod 2) ι (Semantics.Qubit.QubitRegister ι) where
  xCode := K.firstCoboundaryCheckCode
  zCode := K.middleBoundaryCode
  stabilizer :=
    PauliSymplectic.binaryCSSStabilizerCodeOfDualLe K.firstCoboundaryCheckCode
      K.middleBoundaryCode K.middleBoundaryCode_le_firstCoboundaryCheckCode_dual
  orthogonal := K.firstCoboundaryCheckCode_orthogonal_middleBoundaryCode
end ChainComplexData
end Coding
end QEC


