-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
-- name    : QEC_Coding_ExpanderCodes_LiftedProduct
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:52:31.993522+00:00
-- url     : https://prove2.me/theorems/ad900e94-032d-43f3-9dc9-f707253d1184
-- title:
--   Lifted Product
-- statement:
--   Definitions and structural lemmas for Lifted Product, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
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
namespace QEC.Coding.LiftedProduct
universe u v
structure Data (F G aRow aCol bRow bCol : Type*) [Semiring F] where
  A : Matrix aRow aCol (MonoidAlgebra F G)
  B : Matrix bRow bCol (MonoidAlgebra F G)
abbrev C0Index (aRow bRow G : Type*) := aRow × bRow × G
abbrev QubitIndex (aRow aCol bRow bCol G : Type*) :=
  Sum (aCol × bRow × G) (aRow × bCol × G)
abbrev C2Index (aCol bCol G : Type*) := aCol × bCol × G
def groupConj {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) : MonoidAlgebra F G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivCongrLeft (Equiv.inv G) a.coeff)
def leftRegularMatrix {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) : Matrix G G F :=
  fun i j => a.coeff (i * j⁻¹)
def rightRegularMatrix {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) : Matrix G G F :=
  fun i j => a.coeff (j⁻¹ * i)
@[simp]
theorem groupConj_apply {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) (g : G) :
    (groupConj a).coeff g = a.coeff g⁻¹ := by
  rfl
@[simp]
theorem groupConj_zero {F G : Type*} [Semiring F] [Group G] :
    groupConj (0 : MonoidAlgebra F G) = 0 := by
  ext g
  change (0 : MonoidAlgebra F G).coeff g⁻¹ = 0
  rfl
@[simp]
theorem groupConj_add {F G : Type*} [Semiring F] [Group G]
    (a b : MonoidAlgebra F G) :
    groupConj (a + b) = groupConj a + groupConj b := by
  ext g
  simp
@[simp]
theorem groupConj_smul {F G : Type*} [Semiring F] [Group G]
    (c : F) (a : MonoidAlgebra F G) :
    groupConj (c • a) = c • groupConj a := by
  ext g
  simp
@[simp]
theorem groupConj_groupConj {F G : Type*} [Semiring F] [Group G]
    (a : MonoidAlgebra F G) :
    groupConj (groupConj a) = a := by
  ext g
  simp
@[simp]
theorem leftRegularMatrix_zero {F G : Type*} [Semiring F] [Group G] :
    leftRegularMatrix (0 : MonoidAlgebra F G) = 0 := by
  ext i j
  rfl
@[simp]
theorem leftRegularMatrix_add {F G : Type*} [Semiring F] [Group G]
    (a b : MonoidAlgebra F G) :
    leftRegularMatrix (a + b) = leftRegularMatrix a + leftRegularMatrix b := by
  ext i j
  rfl
@[simp]
theorem leftRegularMatrix_smul {F G : Type*} [Semiring F] [Group G]
    (c : F) (a : MonoidAlgebra F G) :
    leftRegularMatrix (c • a) = c • leftRegularMatrix a := by
  ext i j
  rfl
@[simp]
theorem rightRegularMatrix_zero {F G : Type*} [Semiring F] [Group G] :
    rightRegularMatrix (0 : MonoidAlgebra F G) = 0 := by
  ext i j
  rfl
@[simp]
theorem rightRegularMatrix_add {F G : Type*} [Semiring F] [Group G]
    (a b : MonoidAlgebra F G) :
    rightRegularMatrix (a + b) = rightRegularMatrix a + rightRegularMatrix b := by
  ext i j
  rfl
@[simp]
theorem rightRegularMatrix_smul {F G : Type*} [Semiring F] [Group G]
    (c : F) (a : MonoidAlgebra F G) :
    rightRegularMatrix (c • a) = c • rightRegularMatrix a := by
  ext i j
  rfl
theorem leftRegularMatrix_mul_rightRegularMatrix {F G : Type*}
    [CommSemiring F] [Group G] [Fintype G] [DecidableEq G]
    (a b : MonoidAlgebra F G) :
    leftRegularMatrix a * rightRegularMatrix b =
      rightRegularMatrix b * leftRegularMatrix a := by
  ext i j
  simp only [Matrix.mul_apply, leftRegularMatrix, rightRegularMatrix]
  calc
    (∑ k : G, a.coeff (i * k⁻¹) * b.coeff (j⁻¹ * k)) =
        ∑ x : G, a.coeff x * b.coeff (j⁻¹ * (x⁻¹ * i)) := by
      rw [← Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft i))
        (fun x : G ↦ a.coeff x * b.coeff (j⁻¹ * (x⁻¹ * i)))]
      apply Fintype.sum_congr
      intro k
      simp [mul_assoc]
    _ = ∑ k : G, b.coeff (k⁻¹ * i) * a.coeff (k * j⁻¹) := by
      rw [← Equiv.sum_comp (Equiv.mulRight j⁻¹)
        (fun x : G ↦ a.coeff x * b.coeff (j⁻¹ * (x⁻¹ * i)))]
      apply Fintype.sum_congr
      intro k
      simp [mul_comm, mul_assoc]
@[simp]
theorem leftRegularMatrix_groupConj_transpose {F G : Type*}
    [Semiring F] [Group G] (a : MonoidAlgebra F G) :
    (leftRegularMatrix a).transpose = leftRegularMatrix (groupConj a) := by
  ext i j
  simp [leftRegularMatrix]
@[simp]
theorem rightRegularMatrix_groupConj_transpose {F G : Type*}
    [Semiring F] [Group G] (a : MonoidAlgebra F G) :
    (rightRegularMatrix a).transpose = rightRegularMatrix (groupConj a) := by
  ext i j
  simp [rightRegularMatrix]
def starTranspose {F G m n : Type*} [Semiring F] [Group G]
    (M : Matrix m n (MonoidAlgebra F G)) :
    Matrix n m (MonoidAlgebra F G) :=
  fun j i => groupConj (M i j)
@[simp]
theorem starTranspose_apply {F G m n : Type*} [Semiring F] [Group G]
    (M : Matrix m n (MonoidAlgebra F G)) (j : n) (i : m) :
    (starTranspose M) j i = groupConj (M i j) := by
  rfl
@[simp]
theorem starTranspose_zero {F G m n : Type*} [Semiring F] [Group G] :
    starTranspose (0 : Matrix m n (MonoidAlgebra F G)) = 0 := by
  ext j i
  simp [starTranspose]
@[simp]
theorem starTranspose_add {F G m n : Type*} [Semiring F] [Group G]
    (M N : Matrix m n (MonoidAlgebra F G)) :
    starTranspose (M + N) = starTranspose M + starTranspose N := by
  ext j i
  simp [starTranspose]
@[simp]
theorem starTranspose_smul {F G m n : Type*} [Semiring F] [Group G]
    (c : F) (M : Matrix m n (MonoidAlgebra F G)) :
    starTranspose (c • M) = c • starTranspose M := by
  ext j i
  simp [starTranspose]
@[simp]
theorem starTranspose_starTranspose {F G m n : Type*}
    [Semiring F] [Group G] (M : Matrix m n (MonoidAlgebra F G)) :
    starTranspose (starTranspose M) = M := by
  ext i j
  simp [starTranspose]
def boundary1Matrix {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Matrix (C0Index aRow bRow G)
      (QubitIndex aRow aCol bRow bCol G) F :=
  fun (ar, br, go) q =>
    match q with
    | Sum.inl (ac, br', gi) =>
        if br = br' then rightRegularMatrix (D.A ar ac) go gi else 0
    | Sum.inr (ar', bc, gi) =>
        if ar = ar' then - leftRegularMatrix (D.B br bc) go gi else 0
def boundary2Matrix {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Matrix (QubitIndex aRow aCol bRow bCol G)
      (C2Index aCol bCol G) F :=
  fun q (ac', bc', gi) =>
    match q with
    | Sum.inl (ac, br, go) =>
        if ac = ac' then leftRegularMatrix (D.B br bc') go gi else 0
    | Sum.inr (ar, bc, go) =>
        if bc = bc' then rightRegularMatrix (D.A ar ac') go gi else 0
@[simp]
theorem boundary1Matrix_inl_apply {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar : aRow) (br br' : bRow) (ac : aCol) (go gi : G) :
    boundary1Matrix D (ar, br, go) (Sum.inl (ac, br', gi)) =
      if br = br' then rightRegularMatrix (D.A ar ac) go gi else 0 := by
  rfl
@[simp]
theorem boundary1Matrix_inr_apply {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar ar' : aRow) (br : bRow) (bc : bCol) (go gi : G) :
    boundary1Matrix D (ar, br, go) (Sum.inr (ar', bc, gi)) =
      if ar = ar' then - leftRegularMatrix (D.B br bc) go gi else 0 := by
  rfl
@[simp]
theorem boundary2Matrix_inl_apply {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ac ac' : aCol) (br : bRow) (bc : bCol) (go gi : G) :
    boundary2Matrix D (Sum.inl (ac, br, go)) (ac', bc, gi) =
      if ac = ac' then leftRegularMatrix (D.B br bc) go gi else 0 := by
  rfl
@[simp]
theorem boundary2Matrix_inr_apply {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar : aRow) (ac : aCol) (bc bc' : bCol) (go gi : G) :
    boundary2Matrix D (Sum.inr (ar, bc, go)) (ac, bc', gi) =
      if bc = bc' then rightRegularMatrix (D.A ar ac) go gi else 0 := by
  rfl
@[simp]
theorem neg_leftRegularMatrix_apply_zmod2 {G : Type*} [Group G]
    (a : MonoidAlgebra (ZMod 2) G) (go gi : G) :
    - leftRegularMatrix a go gi = leftRegularMatrix a go gi := by
  exact ZMod.neg_eq_self_mod_two _
@[simp]
theorem boundary1Matrix_inr_apply_zmod2
    {G aRow aCol bRow bCol : Type*}
    [Group G] [Fintype G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol)
    (ar ar' : aRow) (br : bRow) (bc : bCol) (go gi : G) :
    boundary1Matrix D (ar, br, go) (Sum.inr (ar', bc, gi)) =
      if ar = ar' then leftRegularMatrix (D.B br bc) go gi else 0 := by
  simp only [boundary1Matrix_inr_apply, neg_leftRegularMatrix_apply_zmod2]
noncomputable def boundary1 {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Word F (QubitIndex aRow aCol bRow bCol G) →ₗ[F]
      Word F (C0Index aRow bRow G) :=
  Matrix.toLin' (boundary1Matrix D)
noncomputable def boundary2 {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    Word F (C2Index aCol bCol G) →ₗ[F]
      Word F (QubitIndex aRow aCol bRow bCol G) :=
  Matrix.toLin' (boundary2Matrix D)
theorem boundary1Matrix_mul_boundary2Matrix
    {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    boundary1Matrix D * boundary2Matrix D = 0 := by
  ext ⟨ar, br, go⟩ ⟨ac, bc, gi⟩
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, boundary1Matrix_inl_apply,
    boundary1Matrix_inr_apply, boundary2Matrix_inl_apply,
    boundary2Matrix_inr_apply]
  calc
    (∑ x : aCol, ∑ x_1 : bRow, ∑ x_2 : G,
          (if br = x_1 then rightRegularMatrix (D.A ar x) go x_2 else 0) *
            (if x = ac then leftRegularMatrix (D.B x_1 bc) x_2 gi else 0)) +
        ∑ x : aRow, ∑ x_1 : bCol, ∑ x_2 : G,
          (if ar = x then -leftRegularMatrix (D.B br x_1) go x_2 else 0) *
            (if x_1 = bc then rightRegularMatrix (D.A x ac) x_2 gi else 0) =
      (rightRegularMatrix (D.A ar ac) *
          leftRegularMatrix (D.B br bc)) go gi -
        (leftRegularMatrix (D.B br bc) *
          rightRegularMatrix (D.A ar ac)) go gi := by
      simp [Matrix.mul_apply, sub_eq_add_neg]
    _ = 0 := by
      rw [leftRegularMatrix_mul_rightRegularMatrix]
      exact sub_self _
theorem boundary_squared {F G aRow aCol bRow bCol : Type*}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    (boundary1 D).comp (boundary2 D) = 0 := by
  change (Matrix.toLin' (boundary1Matrix D)).comp
    (Matrix.toLin' (boundary2Matrix D)) = 0
  rw [← Matrix.toLin'_mul]
  rw [boundary1Matrix_mul_boundary2Matrix]
  simp
noncomputable def chainComplex
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    ChainComplexData F
      (Word F (C0Index aRow bRow G))
      (Word F (QubitIndex aRow aCol bRow bCol G))
      (Word F (C2Index aCol bCol G)) where
  boundary1 := boundary1 D
  boundary2 := boundary2 D
  boundary_squared := boundary_squared D
@[simp]
theorem chainComplex_boundary1
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    (chainComplex D).boundary1 = boundary1 D := by
  rfl
@[simp]
theorem chainComplex_boundary2
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    (chainComplex D).boundary2 = boundary2 D := by
  rfl
noncomputable def boundary1RowSupport
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (c0 : C0Index aRow bRow G) :
    Finset (QubitIndex aRow aCol bRow bCol G) := by
  classical
  exact hammingSupport
    (wordLinearMapTranspose (boundary1 D) (Pi.single c0 (1 : F)))
noncomputable def boundary2RowSupport
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (c2 : C2Index aCol bCol G) :
    Finset (QubitIndex aRow aCol bRow bCol G) := by
  classical
  exact hammingSupport (boundary2 D (Pi.single c2 (1 : F)))
noncomputable def boundaryIncidence
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) :
    QEC.QLDPC.CheckIncidence
      (Sum (C0Index aRow bRow G) (C2Index aCol bCol G))
      (QubitIndex aRow aCol bRow bCol G) := by
  classical
  exact QEC.QLDPC.chainComplexBoundaryIncidence (chainComplex D)
theorem transpose_boundary1_single_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    [decC0 : DecidableEq (C0Index aRow bRow G)]
    (D : Data F G aRow aCol bRow bCol)
    (c0 : C0Index aRow bRow G) (q : QubitIndex aRow aCol bRow bCol G) :
    (wordLinearMapTranspose (boundary1 D) (Pi.single c0 (1 : F))) q =
      boundary1Matrix D c0 q := by
  classical
  unfold wordLinearMapTranspose
  dsimp
  rw [Fintype.sum_eq_single c0]
  · simp [boundary1]
  · intro c0' hne
    rw [Pi.single_eq_of_ne hne, zero_mul]
theorem boundary2_single_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    [decC2 : DecidableEq (C2Index aCol bCol G)]
    (D : Data F G aRow aCol bRow bCol)
    (c2 : C2Index aCol bCol G) (q : QubitIndex aRow aCol bRow bCol G) :
    boundary2 D (Pi.single c2 (1 : F)) q = boundary2Matrix D q c2 := by
  classical
  simp [boundary2, Matrix.toLin'_apply, Matrix.mulVec]
theorem transpose_boundary1_canonicalBasisWord_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (c0 : C0Index aRow bRow G) (q : QubitIndex aRow aCol bRow bCol G) :
    (wordLinearMapTranspose (boundary1 D) (canonicalBasisWord (F := F) c0)) q =
      boundary1Matrix D c0 q := by
  classical
  unfold canonicalBasisWord wordLinearMapTranspose
  dsimp
  rw [Fintype.sum_eq_single c0]
  · simp [boundary1]
  · intro c0' hne
    have hne' : c0 ≠ c0' := Ne.symm hne
    simp [hne']
theorem boundary2_canonicalBasisWord_apply
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (c2 : C2Index aCol bCol G) (q : QubitIndex aRow aCol bRow bCol G) :
    boundary2 D (canonicalBasisWord (F := F) c2) q = boundary2Matrix D q c2 := by
  classical
  simp [canonicalBasisWord, boundary2, Matrix.toLin'_apply, Matrix.mulVec]
@[simp]
theorem mem_boundary1RowSupport_inl
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar : aRow) (br br' : bRow) (ac : aCol) (go gi : G) :
    Sum.inl (ac, br', gi) ∈ boundary1RowSupport D (ar, br, go) ↔
      br = br' ∧ (D.A ar ac).coeff (gi⁻¹ * go) ≠ 0 := by
  classical
  simp [boundary1RowSupport, hammingSupport, transpose_boundary1_single_apply,
    boundary1Matrix_inl_apply, rightRegularMatrix]
@[simp]
theorem mem_boundary1RowSupport_inr
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar ar' : aRow) (br : bRow) (bc : bCol) (go gi : G) :
    Sum.inr (ar', bc, gi) ∈ boundary1RowSupport D (ar, br, go) ↔
      ar = ar' ∧ (D.B br bc).coeff (go * gi⁻¹) ≠ 0 := by
  classical
  simp [boundary1RowSupport, hammingSupport, transpose_boundary1_single_apply,
    boundary1Matrix_inr_apply, leftRegularMatrix]
@[simp]
theorem mem_boundary2RowSupport_inl
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ac ac' : aCol) (br : bRow) (bc : bCol) (go gi : G) :
    Sum.inl (ac, br, go) ∈ boundary2RowSupport D (ac', bc, gi) ↔
      ac = ac' ∧ (D.B br bc).coeff (go * gi⁻¹) ≠ 0 := by
  classical
  simp [boundary2RowSupport, hammingSupport, boundary2_single_apply,
    boundary2Matrix_inl_apply, leftRegularMatrix]
@[simp]
theorem mem_boundary2RowSupport_inr
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol)
    (ar : aRow) (ac : aCol) (bc bc' : bCol) (go gi : G) :
    Sum.inr (ar, bc, go) ∈ boundary2RowSupport D (ac, bc', gi) ↔
      bc = bc' ∧ (D.A ar ac).coeff (gi⁻¹ * go) ≠ 0 := by
  classical
  simp [boundary2RowSupport, hammingSupport, boundary2_single_apply,
    boundary2Matrix_inr_apply, rightRegularMatrix]
@[simp]
theorem boundaryIncidence_checkSupport_inl
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (c0 : C0Index aRow bRow G) :
    (boundaryIncidence D).checkSupport (Sum.inl c0) = boundary1RowSupport D c0 := by
  classical
  unfold boundaryIncidence
  ext q
  simp [QEC.QLDPC.CheckIncidence.checkSupport,
    QEC.QLDPC.chainComplexBoundaryIncidence, boundary1RowSupport,
    hammingSupport, transpose_boundary1_canonicalBasisWord_apply,
    transpose_boundary1_single_apply]
@[simp]
theorem boundaryIncidence_checkSupport_inr
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (c2 : C2Index aCol bCol G) :
    (boundaryIncidence D).checkSupport (Sum.inr c2) = boundary2RowSupport D c2 := by
  classical
  unfold boundaryIncidence
  ext q
  simp [QEC.QLDPC.CheckIncidence.checkSupport,
    QEC.QLDPC.chainComplexBoundaryIncidence, boundary2RowSupport,
    hammingSupport, boundary2_canonicalBasisWord_apply, boundary2_single_apply]
noncomputable def binaryCSSCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    CSSCode (ZMod 2) (QubitIndex aRow aCol bRow bCol G)
      (Semantics.Qubit.QubitRegister (QubitIndex aRow aCol bRow bCol G)) :=
  (chainComplex D).binaryCSSCode
@[simp]
theorem binaryCSSCode_xCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    (binaryCSSCode D).xCode = (chainComplex D).firstCoboundaryCheckCode := by
  rfl
@[simp]
theorem binaryCSSCode_zCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    (binaryCSSCode D).zCode = (chainComplex D).middleBoundaryCode := by
  rfl
noncomputable def binaryChainComplexCode
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :=
  (chainComplex D).binaryChainComplexCode
noncomputable def binarySourceValidStabilizer
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) :
    StabilizerCode.SourceValidBinary (QubitIndex aRow aCol bRow bCol G) :=
  (chainComplex D).binaryCSSSourceValidStabilizer
abbrev BinaryPureXMinimumDistance
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) (dX : Nat) :=
  PureXLogicalMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode dX
abbrev BinaryPureZMinimumDistance
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) (dZ : Nat) :=
  PureZLogicalMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode dZ
abbrev BinaryAlgebraicCSSMinimumDistance
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data (ZMod 2) G aRow aCol bRow bCol) (d : Nat) :=
  AlgebraicCSSMinimumDistance
    (binaryCSSCode D).xCode (binaryCSSCode D).zCode d
def firstEmbedding {α β : Type*} : α ↪ Sum α β :=
  Function.Embedding.inl
def secondEmbedding {α β : Type*} : β ↪ Sum α β :=
  Function.Embedding.inr
def firstRestriction {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (_D : Data F G aRow aCol bRow bCol) :
    Word F (QubitIndex aRow aCol bRow bCol G) →ₗ[F]
      Word F (aCol × bRow × G) where
  toFun x i := x (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def secondRestriction {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (_D : Data F G aRow aCol bRow bCol) :
    Word F (QubitIndex aRow aCol bRow bCol G) →ₗ[F]
      Word F (aRow × bCol × G) where
  toFun x i := x (Sum.inr i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def firstZeroExtension {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (_D : Data F G aRow aCol bRow bCol) :
    Word F (aCol × bRow × G) →ₗ[F]
      Word F (QubitIndex aRow aCol bRow bCol G) where
  toFun x q := q.elim x (fun _ => 0)
  map_add' _ _ := by
    funext q
    cases q <;> simp
  map_smul' _ _ := by
    funext q
    cases q <;> simp
def secondZeroExtension {F G aRow aCol bRow bCol : Type*} [Semiring F]
    (_D : Data F G aRow aCol bRow bCol) :
    Word F (aRow × bCol × G) →ₗ[F]
      Word F (QubitIndex aRow aCol bRow bCol G) where
  toFun x q := q.elim (fun _ => 0) x
  map_add' _ _ := by
    funext q
    cases q <;> simp
  map_smul' _ _ := by
    funext q
    cases q <;> simp
end QEC.Coding.LiftedProduct


