-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_Core
-- name    : QEC_Coding_FiberBundle_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:15:52.01055+00:00
-- url     : https://prove2.me/theorems/9d637d9e-7635-41d2-ab31-3d0fb86d264e
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
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
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
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
namespace QEC.Coding.FiberBundle
universe u
abbrev C0Index (baseZero fiberZero : Type*) := baseZero × fiberZero
abbrev QubitIndex
    (baseZero baseOne fiberZero fiberOne : Type*) :=
  Sum (baseOne × fiberZero) (baseZero × fiberOne)
abbrev C2Index (baseOne fiberOne : Type*) := baseOne × fiberOne
structure FiberAutomorphism
    (fiberZero fiberOne : Type*) [Fintype fiberZero] [Fintype fiberOne]
    (fiberBoundary : Matrix fiberZero fiberOne (ZMod 2)) where
  onZero : Equiv.Perm fiberZero
  onOne : Equiv.Perm fiberOne
  boundary_naturality :
    ∀ i j, fiberBoundary (onZero i) (onOne j) = fiberBoundary i j
structure Data
    (baseZero baseOne fiberZero fiberOne : Type*)
    [Fintype fiberZero] [Fintype fiberOne] where
  baseBoundary : Matrix baseZero baseOne (ZMod 2)
  fiberBoundary : Matrix fiberZero fiberOne (ZMod 2)
  connection :
    baseOne → baseZero →
      FiberAutomorphism fiberZero fiberOne fiberBoundary
def boundary1Matrix
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseZero] [DecidableEq fiberZero]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Matrix
      (C0Index baseZero fiberZero)
      (QubitIndex baseZero baseOne fiberZero fiberOne)
      (ZMod 2) :=
  fun (a, i) q =>
    match q with
    | Sum.inl (b, j) =>
        if i = (D.connection b a).onZero j
        then D.baseBoundary a b
        else 0
    | Sum.inr (a', j) =>
        if a = a' then D.fiberBoundary i j else 0
def boundary2Matrix
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Matrix
      (QubitIndex baseZero baseOne fiberZero fiberOne)
      (C2Index baseOne fiberOne)
      (ZMod 2) :=
  fun q (b, j) =>
    match q with
    | Sum.inl (b', i) =>
        if b' = b then D.fiberBoundary i j else 0
    | Sum.inr (a, j') =>
        if j' = (D.connection b a).onOne j
        then D.baseBoundary a b
        else 0
@[simp]
theorem boundary1Matrix_inl_apply
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseZero] [DecidableEq fiberZero]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (a : baseZero) (i j : fiberZero) (b : baseOne) :
    boundary1Matrix D (a, i) (Sum.inl (b, j)) =
      if i = (D.connection b a).onZero j
      then D.baseBoundary a b
      else 0 := by
  rfl
@[simp]
theorem boundary1Matrix_inr_apply
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseZero] [DecidableEq fiberZero]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (a a' : baseZero) (i : fiberZero) (j : fiberOne) :
    boundary1Matrix D (a, i) (Sum.inr (a', j)) =
      if a = a' then D.fiberBoundary i j else 0 := by
  rfl
@[simp]
theorem boundary2Matrix_inl_apply
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (b b' : baseOne) (i : fiberZero) (j : fiberOne) :
    boundary2Matrix D (Sum.inl (b', i)) (b, j) =
      if b' = b then D.fiberBoundary i j else 0 := by
  rfl
@[simp]
theorem boundary2Matrix_inr_apply
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype fiberZero] [Fintype fiberOne]
    [DecidableEq baseOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (a : baseZero) (b : baseOne) (j j' : fiberOne) :
    boundary2Matrix D (Sum.inr (a, j')) (b, j) =
      if j' = (D.connection b a).onOne j
      then D.baseBoundary a b
      else 0 := by
  rfl
theorem boundary1Matrix_mul_boundary2Matrix
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    boundary1Matrix D * boundary2Matrix D = 0 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, boundary1Matrix_inl_apply,
    boundary1Matrix_inr_apply, boundary2Matrix_inl_apply,
    boundary2Matrix_inr_apply]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hhorizontal :
      (∑ x : fiberZero,
        if i = (D.connection b a).onZero x
        then D.baseBoundary a b * D.fiberBoundary x j
        else 0) =
      D.baseBoundary a b *
        D.fiberBoundary ((D.connection b a).onZero.symm i) j := by
    calc
      _ = ∑ y : fiberZero,
          if i = y
          then D.baseBoundary a b *
            D.fiberBoundary ((D.connection b a).onZero.symm y) j
          else 0 := by
            apply Fintype.sum_equiv (D.connection b a).onZero
            intro x
            simp
      _ = _ := by simp
  have hnaturality :
      D.fiberBoundary i ((D.connection b a).onOne j) =
        D.fiberBoundary ((D.connection b a).onZero.symm i) j := by
    simpa using (D.connection b a).boundary_naturality
      ((D.connection b a).onZero.symm i) j
  have hvertical :
      (∑ x : baseZero,
        if a = x
        then D.fiberBoundary i ((D.connection b x).onOne j) *
          D.baseBoundary x b
        else 0) =
      D.fiberBoundary i ((D.connection b a).onOne j) *
        D.baseBoundary a b := by
    classical
    rw [Finset.sum_eq_single a]
    · simp
    · intro x _hx hxa
      simp [Ne.symm hxa]
    · simp
  rw [hhorizontal, hvertical]
  change _ = (0 : ZMod 2)
  rw [hnaturality]
  rw [mul_comm
    (D.fiberBoundary ((D.connection b a).onZero.symm i) j)
    (D.baseBoundary a b)]
  let x :=
    D.baseBoundary a b *
      D.fiberBoundary ((D.connection b a).onZero.symm i) j
  change x + x = 0
  calc
    x + x = x + (-x) := by rw [ZMod.neg_eq_self_mod_two]
    _ = 0 := add_neg_cancel x
noncomputable def boundary1
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2) (C0Index baseZero fiberZero) :=
  Matrix.toLin' (boundary1Matrix D)
noncomputable def boundary2
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    Word (ZMod 2) (C2Index baseOne fiberOne) →ₗ[ZMod 2]
      Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne) :=
  Matrix.toLin' (boundary2Matrix D)
theorem boundary_squared
    {baseZero baseOne fiberZero fiberOne : Type*}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (boundary1 D).comp (boundary2 D) = 0 := by
  change (Matrix.toLin' (boundary1Matrix D)).comp
    (Matrix.toLin' (boundary2Matrix D)) = 0
  rw [← Matrix.toLin'_mul]
  rw [boundary1Matrix_mul_boundary2Matrix]
  simp
noncomputable def chainComplex
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    ChainComplexData
      (ZMod 2)
      (Word (ZMod 2) (C0Index baseZero fiberZero))
      (Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
      (Word (ZMod 2) (C2Index baseOne fiberOne)) where
  boundary1 := boundary1 D
  boundary2 := boundary2 D
  boundary_squared := boundary_squared D
noncomputable def binaryCSSCode
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    CSSCode
      (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)
      (Semantics.Qubit.QubitRegister
        (QubitIndex baseZero baseOne fiberZero fiberOne)) :=
  (chainComplex D).binaryCSSCode
@[simp]
theorem binaryCSSCode_xCode
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (binaryCSSCode D).xCode = (chainComplex D).firstCoboundaryCheckCode := by
  rfl
@[simp]
theorem binaryCSSCode_zCode
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    (binaryCSSCode D).zCode = (chainComplex D).middleBoundaryCode := by
  rfl
noncomputable def binaryChainComplexCode
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :=
  (chainComplex D).binaryChainComplexCode
noncomputable def binarySourceValidStabilizer
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) :
    StabilizerCode.SourceValidBinary
      (QubitIndex baseZero baseOne fiberZero fiberOne) :=
  (chainComplex D).binaryCSSSourceValidStabilizer
abbrev BinaryPureXMinimumDistance
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (dX : Nat) : Prop :=
  PureXLogicalMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode dX
abbrev BinaryPureZMinimumDistance
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (dZ : Nat) : Prop :=
  PureZLogicalMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode dZ
abbrev BinaryAlgebraicCSSMinimumDistance
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne) (d : Nat) : Prop :=
  AlgebraicCSSMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode d
def cycleBoundary (n : Nat) [NeZero n] :
    Matrix (ZMod n) (ZMod n) (ZMod 2) :=
  fun i j => if i = j ∨ i = j + 1 then 1 else 0
def cycleRotationAutomorphism (n : Nat) [NeZero n] (t : ZMod n) :
    FiberAutomorphism (ZMod n) (ZMod n) (cycleBoundary n) where
  onZero := Equiv.addRight t
  onOne := Equiv.addRight t
  boundary_naturality := by
    intro i j
    simp only [cycleBoundary]
    congr 1
    apply propext
    constructor
    · intro h
      rcases h with h | h
      · left
        exact add_right_cancel h
      · right
        apply add_right_cancel (b := t)
        simpa [add_assoc, add_comm, add_left_comm] using h
    · intro h
      rcases h with h | h
      · left
        simp [h]
      · right
        simp [h, add_assoc, add_comm]
def cycleData
    {baseZero baseOne : Type*}
    [Fintype baseZero] [Fintype baseOne]
    (n : Nat) [NeZero n]
    (baseBoundary : Matrix baseZero baseOne (ZMod 2))
    (twist : baseOne → baseZero → ZMod n) :
    Data baseZero baseOne (ZMod n) (ZMod n) where
  baseBoundary := baseBoundary
  fiberBoundary := cycleBoundary n
  connection := fun b a => cycleRotationAutomorphism n (twist b a)
def multipleRotation (ell : Nat) [NeZero ell] (k : Fin ell) :
    ZMod (ell * ell) :=
  (k.val * ell : Nat)
def multipleRotationCycleData
    {baseZero baseOne : Type*}
    [Fintype baseZero] [Fintype baseOne]
    (ell : Nat) [NeZero ell]
    (baseBoundary : Matrix baseZero baseOne (ZMod 2))
    (twistIndex : baseOne → baseZero → Fin ell) :
    Data baseZero baseOne (ZMod (ell * ell)) (ZMod (ell * ell)) :=
  cycleData (ell * ell) baseBoundary
    (fun b a => multipleRotation ell (twistIndex b a))
end QEC.Coding.FiberBundle


