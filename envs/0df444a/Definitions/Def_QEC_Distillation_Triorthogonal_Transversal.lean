-- Prove2me | Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
-- name    : QEC_Distillation_Triorthogonal_Transversal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:26:59.709425+00:00
-- url     : https://prove2.me/theorems/2ae36a2a-32a8-4af7-8511-b102c1c5b90d
-- title:
--   Transversal
-- statement:
--   Definitions and structural lemmas for Transversal, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
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
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
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
namespace Distillation
namespace Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
def bitLift8 (x : ZMod 2) : ZMod 8 := x.val
def bitLift4 (x : ZMod 2) : ZMod 4 := x.val
@[simp] theorem bitLift4_mul (x y : ZMod 2) :
    bitLift4 (x * y) = bitLift4 x * bitLift4 y := by
  fin_cases x <;> fin_cases y <;> decide
@[simp] theorem bitLift8_mul_self (x : ZMod 2) :
    bitLift8 x * bitLift8 x = bitLift8 x := by
  fin_cases x <;> decide
def booleanElementaryOne : List (ZMod 2) → ZMod 8
  | [] => 0
  | x :: xs => bitLift8 x + booleanElementaryOne xs
def booleanElementaryTwo : List (ZMod 2) → ZMod 8
  | [] => 0
  | x :: xs => bitLift8 x * booleanElementaryOne xs + booleanElementaryTwo xs
def booleanElementaryThree : List (ZMod 2) → ZMod 8
  | [] => 0
  | x :: xs => bitLift8 x * booleanElementaryTwo xs + booleanElementaryThree xs
def booleanXor : List (ZMod 2) → ZMod 2
  | [] => 0
  | x :: xs => x + booleanXor xs
@[simp] theorem bitLift8_mul (x y : ZMod 2) :
    bitLift8 (x * y) = bitLift8 x * bitLift8 y := by
  fin_cases x <;> fin_cases y <;> decide
def wordListXor : List (Word (ZMod 2) Index) → Word (ZMod 2) Index
  | [] => 0
  | x :: xs => x + wordListXor xs
@[simp] theorem wordListXor_apply
    (xs : List (Word (ZMod 2) Index)) (p : Index) :
    wordListXor xs p = booleanXor (xs.map fun x => x p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [wordListXor, booleanXor, ih]
def wordWeightSum8 : List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | x :: xs => (HammingWeight x : ZMod 8) + wordWeightSum8 xs
def wordPairSum8 : List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | x :: xs =>
      (xs.map fun y => (BinaryRowFamily.pairOverlap x y : ZMod 8)).sum +
        wordPairSum8 xs
def fixedPairTripleSum8 (x y : Word (ZMod 2) Index) :
    List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | z :: zs =>
      (BinaryRowFamily.tripleOverlap x y z : ZMod 8) +
        fixedPairTripleSum8 x y zs
def fixedTripleSum8 (x : Word (ZMod 2) Index) :
    List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | y :: ys => fixedPairTripleSum8 x y ys + fixedTripleSum8 x ys
def wordTripleSum8 : List (Word (ZMod 2) Index) → ZMod 8
  | [] => 0
  | x :: xs => fixedTripleSum8 x xs + wordTripleSum8 xs
def wordElementaryOne8 (xs : List (Word (ZMod 2) Index)) : ZMod 8 :=
  ∑ p, booleanElementaryOne (xs.map fun x => x p)
def wordElementaryTwo8 (xs : List (Word (ZMod 2) Index)) : ZMod 8 :=
  ∑ p, booleanElementaryTwo (xs.map fun x => x p)
def wordElementaryThree8 (xs : List (Word (ZMod 2) Index)) : ZMod 8 :=
  ∑ p, booleanElementaryThree (xs.map fun x => x p)
noncomputable def diagonalPhaseLinearEquiv (angle : Qubit.Bitstring Index → Real) :
    Qubit.QubitRegister Index ≃ₗ[Complex] Qubit.QubitRegister Index where
  toFun psi := WithLp.toLp 2 fun bits =>
    OneQubitMagic.phaseAmplitude (angle bits) * psi bits
  invFun psi := WithLp.toLp 2 fun bits =>
    OneQubitMagic.phaseAmplitude (-angle bits) * psi bits
  left_inv := by
    intro psi
    ext bits
    change OneQubitMagic.phaseAmplitude (-angle bits) *
        (OneQubitMagic.phaseAmplitude (angle bits) * psi bits) = psi bits
    rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
    simp
  right_inv := by
    intro psi
    ext bits
    change OneQubitMagic.phaseAmplitude (angle bits) *
        (OneQubitMagic.phaseAmplitude (-angle bits) * psi bits) = psi bits
    rw [← mul_assoc, ← OneQubitMagic.phaseAmplitude_add]
    simp
  map_add' := by
    intro psi chi
    ext bits
    change OneQubitMagic.phaseAmplitude (angle bits) * (psi bits + chi bits) =
      OneQubitMagic.phaseAmplitude (angle bits) * psi bits +
        OneQubitMagic.phaseAmplitude (angle bits) * chi bits
    ring
  map_smul' := by
    intro scalar psi
    ext bits
    change OneQubitMagic.phaseAmplitude (angle bits) * (scalar * psi bits) =
      scalar * (OneQubitMagic.phaseAmplitude (angle bits) * psi bits)
    ring
@[simp] theorem diagonalPhaseLinearEquiv_apply
    (angle : Qubit.Bitstring Index → Real) (psi : Qubit.QubitRegister Index)
    (bits : Qubit.Bitstring Index) :
    diagonalPhaseLinearEquiv angle psi bits =
      OneQubitMagic.phaseAmplitude (angle bits) * psi bits :=
  rfl
noncomputable def diagonalPhaseTransport (angle : Qubit.Bitstring Index → Real) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) where
  toLinearEquiv := diagonalPhaseLinearEquiv angle
  map_inner := by
    intro psi chi
    rw [PiLp.inner_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro bits _hbits
    simp only [diagonalPhaseLinearEquiv_apply, RCLike.inner_apply, map_mul]
    calc
      (OneQubitMagic.phaseAmplitude (angle bits) * chi bits) *
          (starRingEnd Complex (OneQubitMagic.phaseAmplitude (angle bits)) *
            starRingEnd Complex (psi bits)) =
        (OneQubitMagic.phaseAmplitude (angle bits) *
            starRingEnd Complex (OneQubitMagic.phaseAmplitude (angle bits))) *
          (chi bits * starRingEnd Complex (psi bits)) := by ring
      _ = chi bits * starRingEnd Complex (psi bits) := by
        rw [starRingEnd_apply, OneQubitMagic.phaseAmplitude_mul_conj]
        simp
@[simp] theorem diagonalPhaseTransport_apply
    (angle : Qubit.Bitstring Index → Real) (psi : Qubit.QubitRegister Index)
    (bits : Qubit.Bitstring Index) :
    diagonalPhaseTransport angle psi bits =
      OneQubitMagic.phaseAmplitude (angle bits) * psi bits :=
  rfl
structure LocalDiagonalPhase (support : Finset Index) where
  angle : Qubit.Bitstring Index → Real
  depends_on_support : ∀ bits bits',
    (∀ j ∈ support, bits j = bits' j) → angle bits = angle bits'
noncomputable def diagonalPhaseGateModel :
    FinitePhysicalGateModel Index (Qubit.QubitRegister Index) where
  LocalGate := LocalDiagonalPhase
  realize gate := diagonalPhaseTransport gate.angle
def singleSiteLocalPhase (theta : Real) (j : Index) :
    LocalDiagonalPhase ({j} : Finset Index) where
  angle bits := theta * (bits j).val
  depends_on_support := by
    intro bits bits' h
    rw [h j (by simp)]
noncomputable def singleSitePhaseTransport (theta : Real) (j : Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  diagonalPhaseTransport (singleSiteLocalPhase theta j).angle
@[simp] theorem singleSitePhaseTransport_apply
    (theta : Real) (j : Index) (psi : Qubit.QubitRegister Index)
    (bits : Qubit.Bitstring Index) :
    singleSitePhaseTransport theta j psi bits =
      OneQubitMagic.phaseAmplitude (theta * (bits j).val) * psi bits :=
  rfl
noncomputable def physicalT (j : Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  singleSitePhaseTransport (Real.pi / 4) j
noncomputable def physicalInverseS (j : Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  singleSitePhaseTransport (-Real.pi / 2) j
def controlledZLocalPhase (p q : Index) :
    LocalDiagonalPhase ({p, q} : Finset Index) where
  angle bits := Real.pi * (bits p).val * (bits q).val
  depends_on_support := by
    intro bits bits' h
    rw [h p (by simp), h q (by simp)]
noncomputable def physicalControlledZ (p q : Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  diagonalPhaseTransport (controlledZLocalPhase p q).angle
@[simp] theorem physicalControlledZ_apply
    (p q : Index) (psi : Qubit.QubitRegister Index)
    (bits : Qubit.Bitstring Index) :
    physicalControlledZ p q psi bits =
      OneQubitMagic.phaseAmplitude
        (Real.pi * (bits p).val * (bits q).val) * psi bits :=
  rfl
noncomputable def siteEquivFin (Index : Type u) [Fintype Index] :
    Fin (Fintype.card Index) ≃ Index :=
  (Fintype.equivFin Index).symm
noncomputable def allSitePhase (theta : Real) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  UnitaryTransport.composeFamily fun j : Fin (Fintype.card Index) =>
    singleSitePhaseTransport theta (siteEquivFin Index j)
noncomputable def allSiteT :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  allSitePhase (Index := Index) (Real.pi / 4)
noncomputable def allSitePhaseTransversality (theta : Real) :
    SitewiseTransversalityData (diagonalPhaseGateModel (Index := Index))
      (allSitePhase (Index := Index) theta) where
  factorCount := Fintype.card Index
  support j := {siteEquivFin Index j}
  factor j := singleSiteLocalPhase theta (siteEquivFin Index j)
  pairwise_disjoint := by
    intro i j hij
    simp only [Finset.disjoint_singleton]
    exact (siteEquivFin Index).injective.ne hij
  realizes := rfl
  support_card_le_one := by
    intro j
    simp
noncomputable def allSiteTTransversality :
    SitewiseTransversalityData (diagonalPhaseGateModel (Index := Index))
      (allSiteT (Index := Index)) :=
  allSitePhaseTransversality (Index := Index) (Real.pi / 4)
inductive CliffordCorrectionAtom (Index : Type u)
  | inverseS (p : Index)
  | controlledZ (p q : Index)
namespace CliffordCorrectionAtom
def support : CliffordCorrectionAtom Index → Finset Index
  | .inverseS p => {p}
  | .controlledZ p q => {p, q}
def localGate (a : CliffordCorrectionAtom Index) : LocalDiagonalPhase a.support :=
  match a with
  | .inverseS p => singleSiteLocalPhase (-Real.pi / 2) p
  | .controlledZ p q => controlledZLocalPhase p q
noncomputable def realized (a : CliffordCorrectionAtom Index) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  (diagonalPhaseGateModel (Index := Index)).realize a.localGate
def angle (a : CliffordCorrectionAtom Index) (bits : Qubit.Bitstring Index) : Real :=
  match a with
  | .inverseS p => -Real.pi / 2 * (bits p).val
  | .controlledZ p q => Real.pi * (bits p).val * (bits q).val
end CliffordCorrectionAtom
def unorderedPairs : List Index → List (Index × Index)
  | [] => []
  | p :: ps => ps.map (p, ·) ++ unorderedPairs ps
def bitPairSum8 : List (ZMod 2) → ZMod 8
  | [] => 0
  | x :: xs => (xs.map fun y => bitLift8 x * bitLift8 y).sum + bitPairSum8 xs
def pairMulCrossSum {A R : Type*} [CommRing R]
    (f g : A → R) : List A → R
  | [] => 0
  | x :: xs =>
      (xs.map fun y => f x * g y + f y * g x).sum + pairMulCrossSum f g xs
noncomputable def siteList (Index : Type u) [Fintype Index] : List Index :=
  List.ofFn (siteEquivFin Index)
noncomputable def sitePairList (Index : Type u) [Fintype Index] :
    List (Index × Index) :=
  unorderedPairs (siteList Index)
def siteBitCount (bits : Qubit.Bitstring Index) : Nat :=
  ((siteList Index).map fun p => (bits p).val).sum
noncomputable def cliffordCorrectionAtoms
    (single : Index → ZMod 4) (pair : Index → Index → ZMod 2) :
    List (CliffordCorrectionAtom Index) :=
  ((siteList Index).flatMap fun p =>
      List.replicate (single p).val (.inverseS p)) ++
    ((sitePairList Index).flatMap fun pq =>
      List.replicate (pair pq.1 pq.2).val (.controlledZ pq.1 pq.2))
noncomputable def cliffordCorrection
    (single : Index → ZMod 4) (pair : Index → Index → ZMod 2) :
    UnitaryTransport (Qubit.QubitRegister Index) (Qubit.QubitRegister Index) :=
  UnitaryTransport.composeList
    ((cliffordCorrectionAtoms single pair).map CliffordCorrectionAtom.realized)
def atomAngleSum (atoms : List (CliffordCorrectionAtom Index))
    (bits : Qubit.Bitstring Index) : Real :=
  (atoms.map fun a => a.angle bits).sum
noncomputable def cliffordCorrectionAngle
    (single : Index → ZMod 4) (pair : Index → Index → ZMod 2)
    (bits : Qubit.Bitstring Index) : Real :=
  ((siteList Index).map fun p =>
      ((single p).val : Real) * (-Real.pi / 2 * (bits p).val)).sum +
    ((sitePairList Index).map fun pq =>
      ((pair pq.1 pq.2).val : Real) *
        (Real.pi * (bits pq.1).val * (bits pq.2).val)).sum
universe uO uE uC
namespace BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
abbrev EvenBasisIndex (R : BinaryRowFamily OddRow EvenRow Col) :=
  Fin (Module.finrank (ZMod 2) R.evenCode.carrier)
noncomputable def evenBasis (R : BinaryRowFamily OddRow EvenRow Col) :
    Module.Basis R.EvenBasisIndex (ZMod 2) R.evenCode.carrier :=
  Module.finBasis (ZMod 2) R.evenCode.carrier
noncomputable def reducedRow (R : BinaryRowFamily OddRow EvenRow Col) :
    Sum OddRow R.EvenBasisIndex → Word (ZMod 2) Col :=
  Sum.elim R.oddRow fun b => R.evenBasis b
noncomputable def reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) (Sum OddRow R.EvenBasisIndex) →ₗ[ZMod 2]
      Word (ZMod 2) Col :=
  Fintype.linearCombination (ZMod 2) R.reducedRow
@[simp] theorem reducedCombination_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    R.reducedCombination c = ∑ r, c r • R.reducedRow r :=
  Fintype.linearCombination_apply (ZMod 2) R.reducedRow c
noncomputable def rowCoefficientMap
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Word (ZMod 2) Col →ₗ[ZMod 2]
      Word (ZMod 2) (Sum OddRow R.EvenBasisIndex) :=
  R.reducedCombination.leftInverse
noncomputable def rowCoefficientEntry
    (R : BinaryRowFamily OddRow EvenRow Col)
    (r : Sum OddRow R.EvenBasisIndex) (p : Col) : ZMod 2 :=
  R.rowCoefficientMap (Pi.single p 1) r
noncomputable def coefficientBitList
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : Sum OddRow R.EvenBasisIndex) : List (ZMod 2) :=
  (siteList Col).map fun p => R.rowCoefficientEntry r p * f p
def wordTriplePairing (x y z : Word (ZMod 2) Col) : ZMod 2 :=
  ∑ p, x p * y p * z p
noncomputable def reducedRowEquivFin (R : BinaryRowFamily OddRow EvenRow Col) :
    Fin (Fintype.card (Sum OddRow R.EvenBasisIndex)) ≃ Sum OddRow R.EvenBasisIndex :=
  (Fintype.equivFin (Sum OddRow R.EvenBasisIndex)).symm
noncomputable def reducedRowIndexList
    (R : BinaryRowFamily OddRow EvenRow Col) : List (Sum OddRow R.EvenBasisIndex) :=
  List.ofFn R.reducedRowEquivFin
noncomputable def reducedWordList
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    List (Word (ZMod 2) Col) :=
  R.reducedRowIndexList.map fun r => c r • R.reducedRow r
abbrev ReducedRowIndex (R : BinaryRowFamily OddRow EvenRow Col) :=
  Sum OddRow R.EvenBasisIndex
def reducedRowParity (R : BinaryRowFamily OddRow EvenRow Col) :
    R.ReducedRowIndex → Nat
  | .inl _ => 1
  | .inr _ => 0
def rowGamma (R : BinaryRowFamily OddRow EvenRow Col)
    (r : R.ReducedRowIndex) : Nat :=
  (HammingWeight (R.reducedRow r) - R.reducedRowParity r) / 2
def rowPairGamma (R : BinaryRowFamily OddRow EvenRow Col)
    (r s : R.ReducedRowIndex) : Nat :=
  pairOverlap (R.reducedRow r) (R.reducedRow s) / 2
def logicalExponent8 (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) (rs : List R.ReducedRowIndex) : ZMod 8 :=
  (rs.map fun r => (R.reducedRowParity r : ZMod 8) * bitLift8 (c r)).sum
def rowGammaLinear8 (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) (rs : List R.ReducedRowIndex) : ZMod 8 :=
  (rs.map fun r => (R.rowGamma r : ZMod 8) * bitLift8 (c r)).sum
def rowGammaPair8 (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : List R.ReducedRowIndex → ZMod 8
  | [] => 0
  | r :: rs =>
      (rs.map fun s => (R.rowPairGamma r s : ZMod 8) *
        bitLift8 (c r) * bitLift8 (c s)).sum + R.rowGammaPair8 c rs
def rowCliffordExponent8 (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : ZMod 8 :=
  2 * R.rowGammaLinear8 c R.reducedRowIndexList -
    4 * R.rowGammaPair8 c R.reducedRowIndexList
noncomputable def lambdaSingle8
    (R : BinaryRowFamily OddRow EvenRow Col) (p : Col) : ZMod 8 :=
  (R.reducedRowIndexList.map fun r =>
      (R.rowGamma r : ZMod 8) * bitLift8 (R.rowCoefficientEntry r p)).sum -
    2 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        bitLift8 (R.rowCoefficientEntry rs.1 p) *
          bitLift8 (R.rowCoefficientEntry rs.2 p)).sum
noncomputable def lambdaPair8
    (R : BinaryRowFamily OddRow EvenRow Col) (p q : Col) : ZMod 8 :=
  (R.reducedRowIndexList.map fun r =>
      (R.rowGamma r : ZMod 8) *
        bitLift8 (R.rowCoefficientEntry r p) *
          bitLift8 (R.rowCoefficientEntry r q)).sum -
    ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      (R.rowPairGamma rs.1 rs.2 : ZMod 8) *
        (bitLift8 (R.rowCoefficientEntry rs.1 p) *
            bitLift8 (R.rowCoefficientEntry rs.2 q) +
          bitLift8 (R.rowCoefficientEntry rs.2 p) *
            bitLift8 (R.rowCoefficientEntry rs.1 q))).sum
noncomputable def lambdaSingle
    (R : BinaryRowFamily OddRow EvenRow Col) (p : Col) : ZMod 4 :=
  (R.reducedRowIndexList.map fun r =>
      (R.rowGamma r : ZMod 4) * bitLift4 (R.rowCoefficientEntry r p)).sum -
    2 * ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      (R.rowPairGamma rs.1 rs.2 : ZMod 4) *
        bitLift4 (R.rowCoefficientEntry rs.1 p) *
          bitLift4 (R.rowCoefficientEntry rs.2 p)).sum
noncomputable def lambdaPair
    (R : BinaryRowFamily OddRow EvenRow Col) (p q : Col) : ZMod 2 :=
  (R.reducedRowIndexList.map fun r =>
      (R.rowGamma r : ZMod 2) * R.rowCoefficientEntry r p *
        R.rowCoefficientEntry r q).sum -
    ((unorderedPairs R.reducedRowIndexList).map fun rs =>
      (R.rowPairGamma rs.1 rs.2 : ZMod 2) *
        (R.rowCoefficientEntry rs.1 p * R.rowCoefficientEntry rs.2 q +
          R.rowCoefficientEntry rs.2 p * R.rowCoefficientEntry rs.1 q)).sum
def correctionExponent8
    (R : BinaryRowFamily OddRow EvenRow Col)
    (f : Word (ZMod 2) Col) : ZMod 8 :=
  -2 * ((siteList Col).map fun p =>
      ((R.lambdaSingle p).val : ZMod 8) * bitLift8 (f p)).sum +
    4 * ((sitePairList Col).map fun pq =>
      ((R.lambdaPair pq.1 pq.2).val : ZMod 8) *
        bitLift8 (f pq.1) * bitLift8 (f pq.2)).sum
def correctionExponentInt
    (R : BinaryRowFamily OddRow EvenRow Col)
    (bits : Qubit.Bitstring Col) : Int :=
  -2 * ((siteList Col).map fun p =>
      ((R.lambdaSingle p).val : Int) * (bits p).val).sum +
    4 * ((sitePairList Col).map fun pq =>
      ((R.lambdaPair pq.1 pq.2).val : Int) *
        (bits pq.1).val * (bits pq.2).val).sum
noncomputable def physicalCliffordCorrection
    (R : BinaryRowFamily OddRow EvenRow Col) :
    UnitaryTransport (Qubit.QubitRegister Col) (Qubit.QubitRegister Col) :=
  cliffordCorrection R.lambdaSingle R.lambdaPair
noncomputable def correctedAllSiteT
    (R : BinaryRowFamily OddRow EvenRow Col) :
    UnitaryTransport (Qubit.QubitRegister Col) (Qubit.QubitRegister Col) :=
  (allSiteT (Index := Col)).trans R.physicalCliffordCorrection
def correctedExponentInt
    (R : BinaryRowFamily OddRow EvenRow Col)
    (bits : Qubit.Bitstring Col) : Int :=
  (HammingWeight (bitstringWordEquiv Col bits) : Int) +
    R.correctionExponentInt bits
theorem rowCode_le_dual_dual
    (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.carrier ≤ R.rowCode.dual.dual.carrier :=
  LinearCode.le_dual_of_le_dual R.rowCode R.rowCode.dual le_rfl
def oddCoefficients (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : Word (ZMod 2) OddRow :=
  fun a => c (.inl a)
def evenPart (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : Word (ZMod 2) Col :=
  ∑ b, c (.inr b) • (R.evenBasis b : Word (ZMod 2) Col)
theorem evenPart_mem_evenCode
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.evenPart c ∈ R.evenCode.carrier := by
  exact Submodule.sum_mem R.evenCode.carrier (fun b _ =>
    R.evenCode.carrier.smul_mem _ (R.evenBasis b).property)
theorem reducedCombination_eq_oddCombination_add_evenPart
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.reducedCombination c =
      R.oddCombination (R.oddCoefficients c) + R.evenPart c := by
  rw [R.reducedCombination_apply, Fintype.sum_sum_type,
    R.oddCombination_apply]
  rfl
theorem reducedCombination_mem_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.reducedCombination c ∈ R.rowCode.carrier := by
  rw [R.reducedCombination_eq_oddCombination_add_evenPart]
  rw [R.rowCode_eq_evenCode_sup_oddCode]
  exact Submodule.add_mem _
    (Submodule.mem_sup_right (R.oddCombination_mem_oddCode (R.oddCoefficients c)))
    (Submodule.mem_sup_left (R.evenPart_mem_evenCode c))
theorem reducedCombination_mem_dual_dual
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.reducedCombination c ∈ R.rowCode.dual.dual.carrier :=
  R.rowCode_le_dual_dual (R.reducedCombination_mem_rowCode c)
def reducedLogicalBits
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) : Qubit.Bitstring OddRow :=
  (bitstringWordEquiv OddRow).symm (R.oddCoefficients c)
universe v
end BinaryRowFamily
end Triorthogonal
end Distillation
end QEC


