-- Prove2me | Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
-- name    : QEC_Coding_Stabilizer_JointMeasurement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:48:38.386899+00:00
-- url     : https://prove2.me/theorems/d9a5dc61-d57f-431c-aefb-df3566bb39e7
-- title:
--   Joint Measurement
-- statement:
--   Definitions and structural lemmas for Joint Measurement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_commute_of_commutes
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
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
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
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
namespace Coding
namespace PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
abbrev JointSyndrome (κ : Type v) := κ → StabilizerOutcome
def jointStabilizerFactor (checks : κ → Binary ι)
    (syndrome : JointSyndrome κ) (check : κ) :
    Operator (Qubit.QubitRegister ι) :=
  stabilizerProjector (checks check) (syndrome check)
theorem jointStabilizerFactor_commute
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (left right : κ) (syndromeLeft syndromeRight : JointSyndrome κ) :
    Commute (jointStabilizerFactor checks syndromeLeft left)
      (jointStabilizerFactor checks syndromeRight right) := by
  unfold jointStabilizerFactor stabilizerProjector
  have hoperator :
      toHermitianQubitOperator (checks left) *
          toHermitianQubitOperator (checks right) =
        toHermitianQubitOperator (checks right) *
          toHermitianQubitOperator (checks left) :=
    toHermitianQubitOperator_commute_of_commutes
      (checks left) (checks right) (hcomm left right)
  change
    ((1 / 2 : Complex) •
        (1 + (syndromeLeft left).sign •
          toHermitianQubitOperator (checks left))) *
      ((1 / 2 : Complex) •
        (1 + (syndromeRight right).sign •
          toHermitianQubitOperator (checks right))) =
    ((1 / 2 : Complex) •
        (1 + (syndromeRight right).sign •
          toHermitianQubitOperator (checks right))) *
      ((1 / 2 : Complex) •
        (1 + (syndromeLeft left).sign •
          toHermitianQubitOperator (checks left)))
  rw [smul_mul_smul_comm, smul_mul_smul_comm]
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul_comm]
  rw [hoperator]
  module
theorem jointStabilizerFactor_adjoint
    (checks : κ → Binary ι) (syndrome : JointSyndrome κ) (check : κ) :
    LinearMap.adjoint (jointStabilizerFactor checks syndrome check) =
      jointStabilizerFactor checks syndrome check :=
  stabilizerProjector_adjoint (checks check) (syndrome check)
theorem jointStabilizerFactor_pairwise
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (selected : Finset κ) :
    (selected : Set κ).Pairwise
      (Function.onFun Commute (jointStabilizerFactor checks syndrome)) := by
  intro left _ right _ _
  exact jointStabilizerFactor_commute checks hcomm left right syndrome syndrome
noncomputable def jointStabilizerProjector
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    Operator (Qubit.QubitRegister ι) :=
  Finset.univ.noncommProd (jointStabilizerFactor checks syndrome)
    (jointStabilizerFactor_pairwise checks hcomm syndrome Finset.univ)
theorem jointStabilizerProjectorOn_adjoint
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (selected : Finset κ) :
    LinearMap.adjoint
        (selected.noncommProd (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome selected)) =
      selected.noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome selected) := by
  classical
  induction selected using Finset.induction_on with
  | empty =>
      simp [Finset.noncommProd_empty]
  | insert check selected hnotmem induction =>
      have hrest : (selected : Set κ).Pairwise
          (Function.onFun Commute (jointStabilizerFactor checks syndrome)) :=
        (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)).mono
          (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := selected.noncommProd (jointStabilizerFactor checks syndrome) hrest
      have hfactor : (insert check selected).noncommProd
          (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) =
          jointStabilizerFactor checks syndrome check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem selected check
          (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) hnotmem]
      have hcommRest : Commute (jointStabilizerFactor checks syndrome check) productRest := by
        dsimp [productRest]
        exact Finset.noncommProd_commute selected (jointStabilizerFactor checks syndrome) hrest
          (jointStabilizerFactor checks syndrome check)
          (fun other _ => jointStabilizerFactor_commute checks hcomm check other syndrome syndrome)
      calc
        LinearMap.adjoint ((insert check selected).noncommProd
            (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected))) =
            LinearMap.adjoint (jointStabilizerFactor checks syndrome check * productRest) := by
              rw [hfactor]
        _ = LinearMap.adjoint productRest *
            LinearMap.adjoint (jointStabilizerFactor checks syndrome check) := by
              rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, ← Module.End.mul_eq_comp]
        _ = productRest * jointStabilizerFactor checks syndrome check := by
              rw [show LinearMap.adjoint productRest = productRest by
                dsimp [productRest]
                exact induction, jointStabilizerFactor_adjoint]
        _ = jointStabilizerFactor checks syndrome check * productRest := hcommRest.eq.symm
        _ = (insert check selected).noncommProd (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) :=
              hfactor.symm
theorem jointStabilizerProjector_adjoint
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    LinearMap.adjoint (jointStabilizerProjector checks hcomm syndrome) =
      jointStabilizerProjector checks hcomm syndrome :=
  jointStabilizerProjectorOn_adjoint checks hcomm syndrome Finset.univ
theorem jointStabilizerFactor_idempotent
    (checks : κ → Binary ι) (syndrome : JointSyndrome κ) (check : κ) :
    jointStabilizerFactor checks syndrome check *
        jointStabilizerFactor checks syndrome check =
      jointStabilizerFactor checks syndrome check :=
  stabilizerProjector_idempotent (checks check) (syndrome check)
theorem jointStabilizerProjectorOn_idempotent
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (selected : Finset κ) :
    selected.noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome selected) *
      selected.noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome selected) =
      selected.noncommProd (jointStabilizerFactor checks syndrome)
        (jointStabilizerFactor_pairwise checks hcomm syndrome selected) := by
  classical
  induction selected using Finset.induction_on with
  | empty =>
      simp [Finset.noncommProd_empty]
  | insert check selected hnotmem induction =>
      have hrest : (selected : Set κ).Pairwise
          (Function.onFun Commute (jointStabilizerFactor checks syndrome)) :=
        (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)).mono
          (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := selected.noncommProd (jointStabilizerFactor checks syndrome) hrest
      have hfactor : (insert check selected).noncommProd
          (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) =
          jointStabilizerFactor checks syndrome check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem selected check
          (jointStabilizerFactor checks syndrome)
          (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) hnotmem]
      have hcommRest : Commute (jointStabilizerFactor checks syndrome check) productRest := by
        dsimp [productRest]
        exact Finset.noncommProd_commute selected (jointStabilizerFactor checks syndrome) hrest
          (jointStabilizerFactor checks syndrome check)
          (fun other _ => jointStabilizerFactor_commute checks hcomm check other syndrome syndrome)
      calc
        (insert check selected).noncommProd (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) *
          (insert check selected).noncommProd (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) =
            (jointStabilizerFactor checks syndrome check * productRest) *
              (jointStabilizerFactor checks syndrome check * productRest) := by rw [hfactor]
        _ = jointStabilizerFactor checks syndrome check *
              (productRest * jointStabilizerFactor checks syndrome check) * productRest := by
              simp only [mul_assoc]
        _ = jointStabilizerFactor checks syndrome check *
              (jointStabilizerFactor checks syndrome check * productRest) * productRest := by
              rw [hcommRest.eq]
        _ = (jointStabilizerFactor checks syndrome check *
              jointStabilizerFactor checks syndrome check) * (productRest * productRest) := by
              simp only [mul_assoc]
        _ = jointStabilizerFactor checks syndrome check * productRest := by
              rw [jointStabilizerFactor_idempotent]
              rw [show productRest * productRest = productRest by
                dsimp [productRest]
                exact induction]
        _ = (insert check selected).noncommProd (jointStabilizerFactor checks syndrome)
            (jointStabilizerFactor_pairwise checks hcomm syndrome (insert check selected)) :=
              hfactor.symm
theorem jointStabilizerProjector_idempotent
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector checks hcomm syndrome :=
  jointStabilizerProjectorOn_idempotent checks hcomm syndrome Finset.univ
def jointStabilizerPartialFactor (checks : κ → Binary ι)
    (selected : Finset κ) (syndrome : ∀ check, check ∈ selected → StabilizerOutcome)
    (check : κ) : Operator (Qubit.QubitRegister ι) :=
  if hmem : check ∈ selected then
    stabilizerProjector (checks check) (syndrome check hmem)
  else 1
noncomputable def jointStabilizerPartialProjector (checks : κ → Binary ι)
    (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (selected : Finset κ) (syndrome : ∀ check, check ∈ selected → StabilizerOutcome) :
    Operator (Qubit.QubitRegister ι) :=
  selected.noncommProd (jointStabilizerPartialFactor checks selected syndrome) (by
    intro left hleft right hright _
    change jointStabilizerPartialFactor checks selected syndrome left *
        jointStabilizerPartialFactor checks selected syndrome right =
      jointStabilizerPartialFactor checks selected syndrome right *
        jointStabilizerPartialFactor checks selected syndrome left
    let totalSyndrome : JointSyndrome κ :=
      fun check => if hmem : check ∈ selected then syndrome check hmem else .positive
    have hleft' : left ∈ selected := by simpa using hleft
    have hright' : right ∈ selected := by simpa using hright
    have hleftFactor : jointStabilizerPartialFactor checks selected syndrome left =
        jointStabilizerFactor checks totalSyndrome left := by
      unfold jointStabilizerPartialFactor jointStabilizerFactor
      rw [dif_pos hleft']
      simp only [totalSyndrome, dif_pos hleft']
    have hrightFactor : jointStabilizerPartialFactor checks selected syndrome right =
        jointStabilizerFactor checks totalSyndrome right := by
      unfold jointStabilizerPartialFactor jointStabilizerFactor
      rw [dif_pos hright']
      simp only [totalSyndrome, dif_pos hright']
    rw [hleftFactor, hrightFactor]
    exact jointStabilizerFactor_commute checks hcomm left right totalSyndrome totalSyndrome)
theorem jointStabilizerPartialProjector_insert
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (check : κ) (selected : Finset κ) (hnotmem : check ∉ selected)
    (outcome : StabilizerOutcome)
    (syndrome : ∀ other, other ∈ selected → StabilizerOutcome) :
    jointStabilizerPartialProjector checks hcomm (insert check selected)
        (Finset.prodPiInsert (s := selected) (a := check)
          (fun _ => StabilizerOutcome) (outcome, syndrome)) =
      stabilizerProjector (checks check) outcome *
        jointStabilizerPartialProjector checks hcomm selected syndrome := by
  classical
  let extended := Finset.prodPiInsert (s := selected) (a := check)
    (fun _ => StabilizerOutcome) (outcome, syndrome)
  let insertedFactor := jointStabilizerPartialFactor checks (insert check selected) extended
  let remainingFactor := jointStabilizerPartialFactor checks selected syndrome
  have hcheck : insertedFactor check = stabilizerProjector (checks check) outcome := by
    simp [insertedFactor, extended, jointStabilizerPartialFactor,
      Finset.prodPiInsert]
  have hremaining : ∀ other ∈ selected, insertedFactor other = remainingFactor other := by
    intro other hother
    have hne : other ≠ check := by
      intro heq
      subst other
      exact hnotmem hother
    simp only [insertedFactor, remainingFactor, extended, jointStabilizerPartialFactor,
      dif_pos (Finset.mem_insert_of_mem hother), dif_pos hother,
      Finset.prodPiInsert, dif_neg hne]
  change (insert check selected).noncommProd insertedFactor _ =
    stabilizerProjector (checks check) outcome * selected.noncommProd remainingFactor _
  have hpair : (↑(insert check selected) : Set κ).Pairwise
      (Function.onFun Commute insertedFactor) := by
    intro left hleft right hright _
    change left ∈ insert check selected at hleft
    change right ∈ insert check selected at hright
    simp only [Function.onFun, insertedFactor, jointStabilizerPartialFactor,
      dif_pos hleft, dif_pos hright]
    simpa only [jointStabilizerFactor] using
      jointStabilizerFactor_commute checks hcomm left right
        (fun _ => extended left hleft) (fun _ => extended right hright)
  have hrest := hpair.mono (fun _ => Finset.mem_insert_of_mem)
  trans insertedFactor check * selected.noncommProd insertedFactor hrest
  · exact Finset.noncommProd_insert_of_notMem selected check insertedFactor hpair hnotmem
  rw [hcheck]
  congr 1
  exact Finset.noncommProd_congr rfl hremaining hrest
theorem sum_stabilizerProjector_eq_one (P : Binary ι) :
    ∑ outcome : StabilizerOutcome, stabilizerProjector P outcome = 1 := by
  rw [show (Finset.univ : Finset StabilizerOutcome) = {.positive, .negative} by decide]
  simpa [StabilizerOutcome.opposite] using stabilizerProjector_add_opposite P .positive
theorem sum_jointStabilizerPartialProjector_eq_one
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (selected : Finset κ) :
    ∑ syndrome : (∀ check, check ∈ selected → StabilizerOutcome),
      jointStabilizerPartialProjector checks hcomm selected syndrome = 1 := by
  classical
  induction selected using Finset.induction_on with
  | empty =>
      let emptySyndrome : ∀ check, check ∈ (∅ : Finset κ) → StabilizerOutcome :=
        fun _ hmem => (by simpa using hmem : False).elim
      letI : Unique (∀ check, check ∈ (∅ : Finset κ) → StabilizerOutcome) :=
        { default := emptySyndrome
          uniq := by
            intro syndrome
            funext check hmem
            exact (by simpa using hmem : False).elim }
      rw [Fintype.sum_unique]
      exact Finset.noncommProd_empty _ _
  | insert check selected hnotmem induction =>
      let split := Finset.insertPiProdEquiv (fun _ : κ => StabilizerOutcome) hnotmem
      calc
        ∑ syndrome : (∀ other, other ∈ insert check selected → StabilizerOutcome),
            jointStabilizerPartialProjector checks hcomm (insert check selected) syndrome =
          ∑ data : StabilizerOutcome ×
              (∀ other, other ∈ selected → StabilizerOutcome),
            jointStabilizerPartialProjector checks hcomm (insert check selected)
              (split.symm data) := by
                simpa using split.sum_comp (fun data =>
                  jointStabilizerPartialProjector checks hcomm (insert check selected)
                    (split.symm data))
        _ = ∑ data : StabilizerOutcome ×
              (∀ other, other ∈ selected → StabilizerOutcome),
            stabilizerProjector (checks check) data.1 *
              jointStabilizerPartialProjector checks hcomm selected data.2 := by
                apply Fintype.sum_congr
                intro data
                exact jointStabilizerPartialProjector_insert
                  checks hcomm check selected hnotmem data.1 data.2
        _ = ∑ outcome : StabilizerOutcome,
              ∑ syndrome : (∀ other, other ∈ selected → StabilizerOutcome),
                stabilizerProjector (checks check) outcome *
                  jointStabilizerPartialProjector checks hcomm selected syndrome := by
                rw [Fintype.sum_prod_type]
        _ = (∑ outcome : StabilizerOutcome, stabilizerProjector (checks check) outcome) *
              ∑ syndrome : (∀ other, other ∈ selected → StabilizerOutcome),
                jointStabilizerPartialProjector checks hcomm selected syndrome := by
                rw [Fintype.sum_mul_sum]
        _ = 1 := by rw [sum_stabilizerProjector_eq_one, induction, one_mul]
theorem jointStabilizerPartialProjector_univ
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    jointStabilizerPartialProjector checks hcomm Finset.univ
        (fun check _ => syndrome check) =
      jointStabilizerProjector checks hcomm syndrome := by
  unfold jointStabilizerPartialProjector jointStabilizerProjector
  exact Finset.noncommProd_congr rfl (by
    intro check hmem
    simp [jointStabilizerPartialFactor, jointStabilizerFactor]) _
def jointSyndromeUnivEquiv :
    JointSyndrome κ ≃ (∀ check, check ∈ (Finset.univ : Finset κ) → StabilizerOutcome) where
  toFun syndrome check _ := syndrome check
  invFun syndrome check := syndrome check (Finset.mem_univ check)
  left_inv _ := rfl
  right_inv syndrome := by
    funext check hmem
    rfl
theorem sum_jointStabilizerProjector_eq_one
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    ∑ syndrome : JointSyndrome κ, jointStabilizerProjector checks hcomm syndrome = 1 := by
  classical
  let equiv := jointSyndromeUnivEquiv (κ := κ)
  calc
    ∑ syndrome : JointSyndrome κ, jointStabilizerProjector checks hcomm syndrome =
        ∑ restricted : (∀ check, check ∈ (Finset.univ : Finset κ) → StabilizerOutcome),
          jointStabilizerProjector checks hcomm (equiv.symm restricted) := by
            simpa using equiv.sum_comp (fun restricted =>
              jointStabilizerProjector checks hcomm (equiv.symm restricted))
    _ = ∑ restricted : (∀ check, check ∈ (Finset.univ : Finset κ) → StabilizerOutcome),
          jointStabilizerPartialProjector checks hcomm Finset.univ restricted := by
            apply Fintype.sum_congr
            intro restricted
            exact (jointStabilizerPartialProjector_univ
              checks hcomm (equiv.symm restricted)).symm
    _ = 1 := sum_jointStabilizerPartialProjector_eq_one checks hcomm Finset.univ
def jointStabilizerKrausFamily
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    FiniteKrausFamily (JointSyndrome κ)
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) where
  operator := jointStabilizerProjector checks hcomm
@[simp]
theorem jointStabilizerKrausFamily_operator
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    (jointStabilizerKrausFamily checks hcomm).operator syndrome =
      jointStabilizerProjector checks hcomm syndrome :=
  rfl
theorem jointStabilizerKrausFamily_complete
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    (jointStabilizerKrausFamily checks hcomm).Complete := by
  classical
  unfold FiniteKrausFamily.Complete
  simp only [jointStabilizerKrausFamily_operator, jointStabilizerProjector_adjoint]
  change
    (∑ syndrome : JointSyndrome κ,
      jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerProjector checks hcomm syndrome) = 1
  calc
    (∑ syndrome : JointSyndrome κ,
      jointStabilizerProjector checks hcomm syndrome *
        jointStabilizerProjector checks hcomm syndrome) =
        ∑ syndrome : JointSyndrome κ, jointStabilizerProjector checks hcomm syndrome := by
          apply Finset.sum_congr rfl
          intro syndrome _
          exact jointStabilizerProjector_idempotent checks hcomm syndrome
    _ = 1 := sum_jointStabilizerProjector_eq_one checks hcomm
def jointStabilizerInstrument
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    FiniteInstrument (JointSyndrome κ) (JointSyndrome κ)
      (Qubit.QubitRegister ι) (Qubit.QubitRegister ι) where
  kraus := jointStabilizerKrausFamily checks hcomm
  observe := fun syndrome => syndrome
def jointStabilizerConditionalDensity
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι))
    (hpos : 0 < (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho) :
    DensityOperator (Qubit.QubitRegister ι) :=
  (jointStabilizerInstrument checks hcomm).conditionalDensity syndrome rho hpos
end PauliSymplectic
end Coding
end QEC


