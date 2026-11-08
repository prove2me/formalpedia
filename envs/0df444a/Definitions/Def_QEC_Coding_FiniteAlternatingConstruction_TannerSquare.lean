-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
-- name    : QEC_Coding_FiniteAlternatingConstruction_TannerSquare
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:17:27.682143+00:00
-- url     : https://prove2.me/theorems/c02924fe-a9b4-46ea-ae6c-2c7c7c28ce0f
-- title:
--   Tanner Square
-- statement:
--   Definitions and structural lemmas for Tanner Square, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TannerSquare.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_source_val
import Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRz_target_val
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_MultiscaleDecoder_historicalZeroSyndromeInput_supportFitsRadiusTwo
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_interactionLength_sym2_mk
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_diag_not_mem_fixedGeneratorInteractions
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sym2_mk_mem_interactionsAtLengthAtLeast_iff
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_adjoint_eq_self
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
import Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridCellQubits_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_gridOccupiedCells_iff
import Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_mem_qubitsInRectangle_iff
import Theorems.Thm_QEC_Locality_centeredRectangleClippedGrowthRadius_zero
import Theorems.Thm_QEC_Locality_mem_centeredRectangleQubits_iff
import Theorems.Thm_QEC_Locality_mem_longInteractionEndpointQubits_iff
import Theorems.Thm_QEC_Locality_mem_longNeighborsOf_iff
import Theorems.Thm_QEC_Locality_mem_squareQubits_iff
import Theorems.Thm_QEC_Locality_squareGrowthRadius_succ_sub
import Theorems.Thm_QEC_Locality_squareGrowthRadius_zero
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_source_val
attribute [local simp] QEC.Coding.BDL26FiniteAlternatingCore.finiteRz_target_val
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.MultiscaleDecoder.historicalZeroSyndromeInput_supportFitsRadiusTwo
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.interactionLength_sym2_mk
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_diag_not_mem_fixedGeneratorInteractions
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_iff_actual_support
attribute [local simp] QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_interactionsAtLengthAtLeast_iff
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_adjoint_eq_self
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
attribute [local simp] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridCellQubits_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_gridOccupiedCells_iff
attribute [local simp] QEC.Locality.UnitSeparatedEmbedding2D.mem_qubitsInRectangle_iff
attribute [local simp] QEC.Locality.centeredRectangleClippedGrowthRadius_zero
attribute [local simp] QEC.Locality.mem_centeredRectangleQubits_iff
attribute [local simp] QEC.Locality.mem_longInteractionEndpointQubits_iff
attribute [local simp] QEC.Locality.mem_longNeighborsOf_iff
attribute [local simp] QEC.Locality.mem_squareQubits_iff
attribute [local simp] QEC.Locality.squareGrowthRadius_succ_sub
attribute [local simp] QEC.Locality.squareGrowthRadius_zero
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
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC
namespace Coding
namespace BDL26FiniteTannerSquare
open BDL26FiniteAlternatingCore
open Module
abbrev Field := BDL26FiniteAlternatingCore.Field
abbrev Two := Fin 2
structure TannerSquareData where
  X : Type
  Q : Type
  Z : Type
  Face : Type
  xFintype : Fintype X
  qFintype : Fintype Q
  zFintype : Fintype Z
  faceFintype : Fintype Face
  xDecidableEq : DecidableEq X
  qDecidableEq : DecidableEq Q
  zDecidableEq : DecidableEq Z
  faceDecidableEq : DecidableEq Face
  xq : X → Q → Bool
  qz : Q → Z → Bool
  faceX : Face → X
  faceZ : Face → Z
  faceQ : Face → Two → Q
  faceQ_xq : ∀ f i, xq (faceX f) (faceQ f i) = true
  faceQ_qz : ∀ f i, qz (faceQ f i) (faceZ f) = true
attribute [instance] TannerSquareData.xFintype TannerSquareData.qFintype
  TannerSquareData.zFintype TannerSquareData.faceFintype
  TannerSquareData.xDecidableEq TannerSquareData.qDecidableEq
  TannerSquareData.zDecidableEq TannerSquareData.faceDecidableEq
abbrev FaceOver (D : TannerSquareData) (x : D.X) (z : D.Z) :=
  {f : D.Face // D.faceX f = x ∧ D.faceZ f = z}
abbrev SharedQ (D : TannerSquareData) (x : D.X) (z : D.Z) :=
  {q : D.Q // D.xq x q && D.qz q z}
def faceCornerToShared (D : TannerSquareData) (x : D.X) (z : D.Z) :
    FaceOver D x z × Two → SharedQ D x z := fun fi =>
  ⟨D.faceQ fi.1.1 fi.2, by
    simpa [fi.1.2.1, fi.1.2.2] using
      And.intro (D.faceQ_xq fi.1.1 fi.2) (D.faceQ_qz fi.1.1 fi.2)⟩
structure TannerSquarePresentation where
  data : TannerSquareData
  perfectPairing : ∀ x z, Function.Bijective (faceCornerToShared data x z)
namespace TannerSquarePresentation
abbrev X (P : TannerSquarePresentation) := P.data.X
abbrev Q (P : TannerSquarePresentation) := P.data.Q
abbrev Z (P : TannerSquarePresentation) := P.data.Z
abbrev Face (P : TannerSquarePresentation) := P.data.Face
abbrev xq (P : TannerSquarePresentation) := P.data.xq
abbrev qz (P : TannerSquarePresentation) := P.data.qz
abbrev faceX (P : TannerSquarePresentation) := P.data.faceX
abbrev faceZ (P : TannerSquarePresentation) := P.data.faceZ
abbrev faceQ (P : TannerSquarePresentation) := P.data.faceQ
noncomputable def faceCornerEquiv (P : TannerSquarePresentation) (x : P.X) (z : P.Z) :
    FaceOver P.data x z × Two ≃ SharedQ P.data x z :=
  Equiv.ofBijective (faceCornerToShared P.data x z) (P.perfectPairing x z)
end TannerSquarePresentation
structure TannerSquareCellularRegular (P : TannerSquarePresentation) where
  faceXZ_injective :
    Function.Injective (fun face : P.Face => (P.faceX face, P.faceZ face))
def transposeTannerSquareData (P : TannerSquarePresentation) : TannerSquareData where
  X := P.Z
  Q := P.Q
  Z := P.X
  Face := P.Face
  xFintype := P.data.zFintype
  qFintype := P.data.qFintype
  zFintype := P.data.xFintype
  faceFintype := P.data.faceFintype
  xDecidableEq := P.data.zDecidableEq
  qDecidableEq := P.data.qDecidableEq
  zDecidableEq := P.data.xDecidableEq
  faceDecidableEq := P.data.faceDecidableEq
  xq := fun z q => P.qz q z
  qz := fun q x => P.xq x q
  faceX := P.faceZ
  faceZ := P.faceX
  faceQ := P.faceQ
  faceQ_xq := P.data.faceQ_qz
  faceQ_qz := P.data.faceQ_xq
def transposeFaceOverEquiv (P : TannerSquarePresentation) (z : P.Z) (x : P.X) :
    FaceOver (transposeTannerSquareData P) z x ≃ FaceOver P.data x z where
  toFun := fun f => ⟨f.1, f.2.2, f.2.1⟩
  invFun := fun f => ⟨f.1, f.2.2, f.2.1⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl
def transposeSharedQEquiv (P : TannerSquarePresentation) (z : P.Z) (x : P.X) :
    SharedQ (transposeTannerSquareData P) z x ≃ SharedQ P.data x z where
  toFun := fun q => ⟨q.1, by simpa [transposeTannerSquareData, Bool.and_comm] using q.2⟩
  invFun := fun q => ⟨q.1, by simpa [transposeTannerSquareData, Bool.and_comm] using q.2⟩
  left_inv := fun q => Subtype.ext rfl
  right_inv := fun q => Subtype.ext rfl
def transposeFaceCornerDomainEquiv (P : TannerSquarePresentation)
    (z : P.Z) (x : P.X) :
    FaceOver (transposeTannerSquareData P) z x × Two ≃
      FaceOver P.data x z × Two :=
  Equiv.prodCongr (transposeFaceOverEquiv P z x) (Equiv.refl Two)
theorem transpose_faceCorner_commutes (P : TannerSquarePresentation)
    (z : P.Z) (x : P.X)
    (fi : FaceOver (transposeTannerSquareData P) z x × Two) :
    transposeSharedQEquiv P z x
        (faceCornerToShared (transposeTannerSquareData P) z x fi) =
      faceCornerToShared P.data x z (transposeFaceCornerDomainEquiv P z x fi) := by
  apply Subtype.ext
  rfl
noncomputable def transposePresentation (P : TannerSquarePresentation) :
    TannerSquarePresentation where
  data := transposeTannerSquareData P
  perfectPairing := by
    intro z x
    let A := transposeFaceCornerDomainEquiv P z x
    let B := transposeSharedQEquiv P z x
    constructor
    · intro a b hab
      apply A.injective
      apply (P.perfectPairing x z).1
      have h := congrArg B hab
      change transposeSharedQEquiv P z x _ = transposeSharedQEquiv P z x _ at h
      erw [transpose_faceCorner_commutes, transpose_faceCorner_commutes] at h
      exact h
    · intro y
      obtain ⟨a, ha⟩ := (P.perfectPairing x z).2 (B y)
      refine ⟨A.symm a, ?_⟩
      apply B.injective
      change transposeSharedQEquiv P z x _ = transposeSharedQEquiv P z x _
      erw [transpose_faceCorner_commutes]
      change faceCornerToShared P.data x z (A (A.symm a)) = B y
      erw [A.apply_symm_apply]
      exact ha
def transposeTannerSquareCellularRegular (P : TannerSquarePresentation)
    (R : TannerSquareCellularRegular P) :
    TannerSquareCellularRegular (transposePresentation P) where
  faceXZ_injective := by
    intro first second hpairs
    apply R.faceXZ_injective
    apply Prod.ext
    · exact congrArg Prod.snd hpairs
    · exact congrArg Prod.fst hpairs
inductive Vertex (P : TannerSquarePresentation) where
  | x : P.X → Vertex P
  | q : P.Q → Vertex P
  | z : P.Z → Vertex P
  deriving DecidableEq, Fintype
abbrev XQEdge (P : TannerSquarePresentation) :=
  {e : P.X × P.Q // P.xq e.1 e.2 = true}
abbrev QZEdge (P : TannerSquarePresentation) :=
  {e : P.Q × P.Z // P.qz e.1 e.2 = true}
abbrev Edge (P : TannerSquarePresentation) := XQEdge P ⊕ QZEdge P
def faceXQEdge (P : TannerSquarePresentation) (f : P.Face) (i : Two) : XQEdge P :=
  ⟨(P.faceX f, P.faceQ f i), P.data.faceQ_xq f i⟩
def faceQZEdge (P : TannerSquarePresentation) (f : P.Face) (i : Two) : QZEdge P :=
  ⟨(P.faceQ f i, P.faceZ f), P.data.faceQ_qz f i⟩
noncomputable def transposeVertexEquiv (P : TannerSquarePresentation) :
    Vertex (transposePresentation P) ≃ Vertex P where
  toFun
    | .x z => .z z
    | .q q => .q q
    | .z x => .x x
  invFun
    | .x x => .z x
    | .q q => .q q
    | .z z => .x z
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro v; cases v <;> rfl
noncomputable def transposeXQEdgeEquiv (P : TannerSquarePresentation) :
    XQEdge (transposePresentation P) ≃ QZEdge P where
  toFun := fun e => ⟨(e.1.2, e.1.1), e.2⟩
  invFun := fun e => ⟨(e.1.2, e.1.1), e.2⟩
  left_inv := fun e => Subtype.ext (by simp)
  right_inv := fun e => Subtype.ext (by simp)
noncomputable def transposeQZEdgeEquiv (P : TannerSquarePresentation) :
    QZEdge (transposePresentation P) ≃ XQEdge P where
  toFun := fun e => ⟨(e.1.2, e.1.1), e.2⟩
  invFun := fun e => ⟨(e.1.2, e.1.1), e.2⟩
  left_inv := fun e => Subtype.ext (by simp)
  right_inv := fun e => Subtype.ext (by simp)
noncomputable def transposeEdgeEquiv (P : TannerSquarePresentation) :
    Edge (transposePresentation P) ≃ Edge P where
  toFun
    | Sum.inl e => Sum.inr (transposeXQEdgeEquiv P e)
    | Sum.inr e => Sum.inl (transposeQZEdgeEquiv P e)
  invFun
    | Sum.inl e => Sum.inr ((transposeQZEdgeEquiv P).symm e)
    | Sum.inr e => Sum.inl ((transposeXQEdgeEquiv P).symm e)
  left_inv := by
    intro e
    rcases e with e | e <;> simp
  right_inv := by
    intro e
    rcases e with e | e <;> simp
@[simp] theorem transposeXQEdgeEquiv_faceXQEdge
    (P : TannerSquarePresentation) (f : P.Face) (i : Two) :
    transposeXQEdgeEquiv P (faceXQEdge (transposePresentation P) f i) =
      faceQZEdge P f i := rfl
@[simp] theorem transposeQZEdgeEquiv_faceQZEdge
    (P : TannerSquarePresentation) (f : P.Face) (i : Two) :
    transposeQZEdgeEquiv P (faceQZEdge (transposePresentation P) f i) =
      faceXQEdge P f i := rfl
@[simp] theorem transpose_faceXQEdge (P : TannerSquarePresentation)
    (f : P.Face) (i : Two) :
    transposeEdgeEquiv P
        (Sum.inl (faceXQEdge (transposePresentation P) f i)) =
      (Sum.inr (faceQZEdge P f i) : Edge P) := by
  rfl
@[simp] theorem transpose_faceQZEdge (P : TannerSquarePresentation)
    (f : P.Face) (i : Two) :
    transposeEdgeEquiv P
        (Sum.inr (faceQZEdge (transposePresentation P) f i)) =
      (Sum.inl (faceXQEdge P f i) : Edge P) := by
  rfl
def xqIncidenceMatrix (P : TannerSquarePresentation) : Matrix P.X P.Q Field :=
  fun x q => if P.xq x q = true then 1 else 0
def qzIncidenceMatrix (P : TannerSquarePresentation) : Matrix P.Q P.Z Field :=
  fun q z => if P.qz q z = true then 1 else 0
def edgeVertexMatrix (P : TannerSquarePresentation) : Matrix (Vertex P) (Edge P) Field
  | .x x, Sum.inl e => if x = e.1.1 then 1 else 0
  | .q q, Sum.inl e => if q = e.1.2 then 1 else 0
  | .q q, Sum.inr e => if q = e.1.1 then 1 else 0
  | .z z, Sum.inr e => if z = e.1.2 then 1 else 0
  | _, _ => 0
def faceEdgeMatrix (P : TannerSquarePresentation) : Matrix (Edge P) P.Face Field :=
  fun e f =>
    (if e = (Sum.inl (faceXQEdge P f 0) : Edge P) then 1 else 0) +
    (if e = (Sum.inr (faceQZEdge P f 0) : Edge P) then 1 else 0) +
    (if e = (Sum.inl (faceXQEdge P f 1) : Edge P) then 1 else 0) +
    (if e = (Sum.inr (faceQZEdge P f 1) : Edge P) then 1 else 0)
theorem sum_mul_eqIndicator {A : Type} [Fintype A] [DecidableEq A]
    (w : A → Field) (a : A) :
    (∑ b : A, w b * if b = a then 1 else 0) = w a := by
  classical
  simp
theorem field_add_self (a : Field) : a + a = 0 := by
  exact ZModModule.add_self a
theorem field_two_pairs (a b : Field) : ((a + a) + b) + b = 0 := by
  rw [field_add_self, zero_add, field_add_self]
theorem edgeVertexMatrix_mul_faceEdgeMatrix (P : TannerSquarePresentation) :
    edgeVertexMatrix P * faceEdgeMatrix P = 0 := by
  classical
  ext v f
  rw [Matrix.mul_apply]
  simp only [faceEdgeMatrix, mul_add, Finset.sum_add_distrib]
  simp only [sum_mul_eqIndicator]
  cases v with
  | x x =>
      simp [edgeVertexMatrix, faceXQEdge]
      exact field_add_self (if x = P.faceX f then (1 : Field) else 0)
  | q q =>
      simp [edgeVertexMatrix, faceXQEdge, faceQZEdge]
      exact field_two_pairs
          (if q = P.faceQ f 0 then (1 : Field) else 0)
          (if q = P.faceQ f 1 then (1 : Field) else 0)
  | z z =>
      simp [edgeVertexMatrix, faceQZEdge]
      exact field_add_self (if z = P.faceZ f then (1 : Field) else 0)
noncomputable def cellularBoundary1 (P : TannerSquarePresentation) :
    Word Field (Edge P) →ₗ[Field] Word Field (Vertex P) :=
  Matrix.toLin' (edgeVertexMatrix P)
noncomputable def cellularBoundary2 (P : TannerSquarePresentation) :
    Word Field P.Face →ₗ[Field] Word Field (Edge P) :=
  Matrix.toLin' (faceEdgeMatrix P)
theorem cellularBoundary_squared (P : TannerSquarePresentation) :
    (cellularBoundary1 P).comp (cellularBoundary2 P) = 0 := by
  rw [cellularBoundary1, cellularBoundary2, ← Matrix.toLin'_mul]
  rw [edgeVertexMatrix_mul_faceEdgeMatrix]
  simp
noncomputable def cellularCoboundary0 (P : TannerSquarePresentation) :=
  wordLinearMapTranspose (cellularBoundary1 P)
noncomputable def cellularCoboundary1 (P : TannerSquarePresentation) :=
  wordLinearMapTranspose (cellularBoundary2 P)
noncomputable def cellularChainComplex (P : TannerSquarePresentation) :
    ChainComplexData Field
      (Word Field (Vertex P)) (Word Field (Edge P)) (Word Field P.Face) where
  boundary1 := cellularBoundary1 P
  boundary2 := cellularBoundary2 P
  boundary_squared := cellularBoundary_squared P
abbrev BaseFace := Fin 4
def baseFaceX : BaseFace → BaseX := ![0, 0, 1, 1]
def baseFaceZ : BaseFace → BaseZ := ![0, 1, 0, 1]
def baseFaceQ : BaseFace → Two → BaseQubit :=
  !![0, 4;
     1, 4;
     2, 4;
     3, 4]
def baseTannerSquareData : TannerSquareData where
  X := BaseX
  Q := BaseQubit
  Z := BaseZ
  Face := BaseFace
  xFintype := inferInstance
  qFintype := inferInstance
  zFintype := inferInstance
  faceFintype := inferInstance
  xDecidableEq := inferInstance
  qDecidableEq := inferInstance
  zDecidableEq := inferInstance
  faceDecidableEq := inferInstance
  xq := fun x q => decide (baseBoundary1Matrix x q ≠ 0)
  qz := fun q z => decide (baseBoundary2Matrix q z ≠ 0)
  faceX := baseFaceX
  faceZ := baseFaceZ
  faceQ := baseFaceQ
  faceQ_xq := by decide +kernel
  faceQ_qz := by decide +kernel
def baseTannerSquarePresentation : TannerSquarePresentation where
  data := baseTannerSquareData
  perfectPairing := by
    intro x z
    decide +kernel +revert
def baseTannerSquareCellularRegular :
    TannerSquareCellularRegular baseTannerSquarePresentation where
  faceXZ_injective := by
    decide +kernel +revert
@[simp] theorem baseFace_card : Fintype.card BaseFace = 4 := by simp [BaseFace]
@[simp] theorem baseXQEdge_card : Fintype.card (XQEdge baseTannerSquarePresentation) = 6 := by
  decide +kernel
@[simp] theorem baseQZEdge_card : Fintype.card (QZEdge baseTannerSquarePresentation) = 6 := by
  decide +kernel
def faceUsesXQEdge (P : TannerSquarePresentation) (f : P.Face)
    (e : XQEdge P) : Bool :=
  decide (e = faceXQEdge P f 0 ∨ e = faceXQEdge P f 1)
def faceUsesQZEdge (P : TannerSquarePresentation) (f : P.Face)
    (e : QZEdge P) : Bool :=
  decide (e = faceQZEdge P f 0 ∨ e = faceQZEdge P f 1)
theorem transpose_faceUsesXQEdge (P : TannerSquarePresentation)
    (f : P.Face) (e : XQEdge (transposePresentation P)) :
    faceUsesXQEdge (transposePresentation P) f e =
      faceUsesQZEdge P f (transposeXQEdgeEquiv P e) := by
  apply Bool.decide_congr
  constructor
  · rintro (h | h)
    · left
      simpa using congrArg (transposeXQEdgeEquiv P) h
    · right
      simpa using congrArg (transposeXQEdgeEquiv P) h
  · rintro (h | h)
    · left
      apply (transposeXQEdgeEquiv P).injective
      simpa using h
    · right
      apply (transposeXQEdgeEquiv P).injective
      simpa using h
theorem transpose_faceUsesQZEdge (P : TannerSquarePresentation)
    (f : P.Face) (e : QZEdge (transposePresentation P)) :
    faceUsesQZEdge (transposePresentation P) f e =
      faceUsesXQEdge P f (transposeQZEdgeEquiv P e) := by
  apply Bool.decide_congr
  constructor
  · rintro (h | h)
    · left
      simpa using congrArg (transposeQZEdgeEquiv P) h
    · right
      simpa using congrArg (transposeQZEdgeEquiv P) h
  · rintro (h | h)
    · left
      apply (transposeQZEdgeEquiv P).injective
      simpa using h
    · right
      apply (transposeQZEdgeEquiv P).injective
      simpa using h
def xStarFaceMember (P : TannerSquarePresentation) (x : P.X) (f : P.Face) : Bool :=
  decide (P.faceX f = x)
def xStarEdgeMember (P : TannerSquarePresentation) (x : P.X) : Edge P → Bool
  | Sum.inl e => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ faceUsesXQEdge P f e = true)
  | Sum.inr e => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ faceUsesQZEdge P f e = true)
def xStarVertexMember (P : TannerSquarePresentation) (x : P.X) : Vertex P → Bool
  | .x x' => decide (x' = x)
  | .q q => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧
        (q = P.faceQ f 0 ∨ q = P.faceQ f 1))
  | .z z => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ z = P.faceZ f)
abbrev XStarFace (P : TannerSquarePresentation) (x : P.X) :=
  {f : P.Face // xStarFaceMember P x f}
abbrev XStarEdge (P : TannerSquarePresentation) (x : P.X) :=
  {e : Edge P // xStarEdgeMember P x e}
abbrev XStarVertex (P : TannerSquarePresentation) (x : P.X) :=
  {v : Vertex P // xStarVertexMember P x v}
def xStarBoundaryEdgeMember (P : TannerSquarePresentation) (x : P.X) : Edge P → Bool
  | Sum.inl _ => false
  | Sum.inr e => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ faceUsesQZEdge P f e = true)
def xStarBoundaryVertexMember (P : TannerSquarePresentation) (x : P.X) : Vertex P → Bool
  | .x _ => false
  | .q q => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧
        (q = P.faceQ f 0 ∨ q = P.faceQ f 1))
  | .z z => decide (∃ f : P.Face,
      xStarFaceMember P x f = true ∧ z = P.faceZ f)
abbrev XStarBoundaryEdge (P : TannerSquarePresentation) (x : P.X) :=
  {e : Edge P // xStarBoundaryEdgeMember P x e}
abbrev XStarBoundaryVertex (P : TannerSquarePresentation) (x : P.X) :=
  {v : Vertex P // xStarBoundaryVertexMember P x v}
theorem xStarBoundaryVertexMember_to_star (P : TannerSquarePresentation)
    (x : P.X) (v : Vertex P) (hv : xStarBoundaryVertexMember P x v) :
    xStarVertexMember P x v := by
  rcases v with x' | q | z
  · simp [xStarBoundaryVertexMember] at hv
  · simpa [xStarBoundaryVertexMember, xStarVertexMember] using hv
  · simpa [xStarBoundaryVertexMember, xStarVertexMember] using hv
theorem xStarBoundaryEdgeMember_to_star (P : TannerSquarePresentation)
    (x : P.X) (e : Edge P) (he : xStarBoundaryEdgeMember P x e) :
    xStarEdgeMember P x e := by
  rcases e with e | e
  · simp [xStarBoundaryEdgeMember] at he
  · simpa [xStarBoundaryEdgeMember, xStarEdgeMember] using he
def xStarBoundaryVertexToStar (P : TannerSquarePresentation) (x : P.X) :
    XStarBoundaryVertex P x → XStarVertex P x := fun v =>
  ⟨v.1, xStarBoundaryVertexMember_to_star P x v.1 v.2⟩
def xStarBoundaryEdgeToStar (P : TannerSquarePresentation) (x : P.X) :
    XStarBoundaryEdge P x → XStarEdge P x := fun e =>
  ⟨e.1, xStarBoundaryEdgeMember_to_star P x e.1 e.2⟩
def zStarFaceMember (P : TannerSquarePresentation) (z : P.Z) (f : P.Face) : Bool :=
  decide (P.faceZ f = z)
def zStarEdgeMember (P : TannerSquarePresentation) (z : P.Z) : Edge P → Bool
  | Sum.inl e => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ faceUsesXQEdge P f e = true)
  | Sum.inr e => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ faceUsesQZEdge P f e = true)
def zStarVertexMember (P : TannerSquarePresentation) (z : P.Z) : Vertex P → Bool
  | .x x => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ x = P.faceX f)
  | .q q => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧
        (q = P.faceQ f 0 ∨ q = P.faceQ f 1))
  | .z z' => decide (z' = z)
abbrev ZStarFace (P : TannerSquarePresentation) (z : P.Z) :=
  {f : P.Face // zStarFaceMember P z f}
abbrev ZStarEdge (P : TannerSquarePresentation) (z : P.Z) :=
  {e : Edge P // zStarEdgeMember P z e}
abbrev ZStarVertex (P : TannerSquarePresentation) (z : P.Z) :=
  {v : Vertex P // zStarVertexMember P z v}
def zStarBoundaryEdgeMember (P : TannerSquarePresentation) (z : P.Z) : Edge P → Bool
  | Sum.inl e => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ faceUsesXQEdge P f e = true)
  | Sum.inr _ => false
def zStarBoundaryVertexMember (P : TannerSquarePresentation) (z : P.Z) : Vertex P → Bool
  | .x x => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧ x = P.faceX f)
  | .q q => decide (∃ f : P.Face,
      zStarFaceMember P z f = true ∧
        (q = P.faceQ f 0 ∨ q = P.faceQ f 1))
  | .z _ => false
abbrev ZStarBoundaryEdge (P : TannerSquarePresentation) (z : P.Z) :=
  {e : Edge P // zStarBoundaryEdgeMember P z e}
abbrev ZStarBoundaryVertex (P : TannerSquarePresentation) (z : P.Z) :=
  {v : Vertex P // zStarBoundaryVertexMember P z v}
@[simp] theorem transpose_xStarFaceMember (P : TannerSquarePresentation)
    (z : P.Z) (f : P.Face) :
    xStarFaceMember (transposePresentation P) z f = zStarFaceMember P z f := rfl
@[simp] theorem transpose_xStarVertexMember (P : TannerSquarePresentation)
    (z : P.Z) (v : Vertex (transposePresentation P)) :
    xStarVertexMember (transposePresentation P) z v =
      zStarVertexMember P z (transposeVertexEquiv P v) := by
  rcases v with z' | q | x' <;> rfl
@[simp] theorem transpose_xStarEdgeMember (P : TannerSquarePresentation)
    (z : P.Z) (e : Edge (transposePresentation P)) :
    xStarEdgeMember (transposePresentation P) z e =
      zStarEdgeMember P z (transposeEdgeEquiv P e) := by
  rcases e with e | e
  · simp only [xStarEdgeMember, zStarEdgeMember]
    apply Bool.decide_congr
    constructor <;> rintro ⟨f, hf, he⟩
    · exact ⟨f, hf, (transpose_faceUsesXQEdge P f e) ▸ he⟩
    · exact ⟨f, hf, (transpose_faceUsesXQEdge P f e).symm ▸ he⟩
  · simp only [xStarEdgeMember, zStarEdgeMember]
    apply Bool.decide_congr
    constructor <;> rintro ⟨f, hf, he⟩
    · exact ⟨f, hf, (transpose_faceUsesQZEdge P f e) ▸ he⟩
    · exact ⟨f, hf, (transpose_faceUsesQZEdge P f e).symm ▸ he⟩
@[simp] theorem transpose_xStarBoundaryVertexMember
    (P : TannerSquarePresentation) (z : P.Z)
    (v : Vertex (transposePresentation P)) :
    xStarBoundaryVertexMember (transposePresentation P) z v =
      zStarBoundaryVertexMember P z (transposeVertexEquiv P v) := by
  rcases v with z' | q | x' <;> rfl
@[simp] theorem transpose_xStarBoundaryEdgeMember
    (P : TannerSquarePresentation) (z : P.Z)
    (e : Edge (transposePresentation P)) :
    xStarBoundaryEdgeMember (transposePresentation P) z e =
      zStarBoundaryEdgeMember P z (transposeEdgeEquiv P e) := by
  rcases e with e | e
  · rfl
  · simp only [xStarBoundaryEdgeMember, zStarBoundaryEdgeMember]
    apply Bool.decide_congr
    constructor <;> rintro ⟨f, hf, he⟩
    · exact ⟨f, hf, (transpose_faceUsesQZEdge P f e) ▸ he⟩
    · exact ⟨f, hf, (transpose_faceUsesQZEdge P f e).symm ▸ he⟩
noncomputable def transposeXStarFaceEquiv (P : TannerSquarePresentation) (z : P.Z) :
    XStarFace (transposePresentation P) z ≃ ZStarFace P z where
  toFun := fun f => ⟨f.1, f.2⟩
  invFun := fun f => ⟨f.1, f.2⟩
  left_inv := fun f => Subtype.ext rfl
  right_inv := fun f => Subtype.ext rfl
noncomputable def transposeXStarVertexEquiv (P : TannerSquarePresentation) (z : P.Z) :
    XStarVertex (transposePresentation P) z ≃ ZStarVertex P z where
  toFun := fun v => ⟨transposeVertexEquiv P v.1, by simpa using v.2⟩
  invFun := fun v => ⟨(transposeVertexEquiv P).symm v.1, by
    rw [transpose_xStarVertexMember, Equiv.apply_symm_apply]
    exact v.2⟩
  left_inv := fun v => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun v => Subtype.ext (Equiv.apply_symm_apply _ _)
noncomputable def transposeXStarEdgeEquiv (P : TannerSquarePresentation) (z : P.Z) :
    XStarEdge (transposePresentation P) z ≃ ZStarEdge P z where
  toFun := fun e => ⟨transposeEdgeEquiv P e.1, by simpa using e.2⟩
  invFun := fun e => ⟨(transposeEdgeEquiv P).symm e.1, by
    rw [transpose_xStarEdgeMember, Equiv.apply_symm_apply]
    exact e.2⟩
  left_inv := fun e => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun e => Subtype.ext (Equiv.apply_symm_apply _ _)
noncomputable def transposeXStarBoundaryVertexEquiv
    (P : TannerSquarePresentation) (z : P.Z) :
    XStarBoundaryVertex (transposePresentation P) z ≃ ZStarBoundaryVertex P z where
  toFun := fun v => ⟨transposeVertexEquiv P v.1, by simpa using v.2⟩
  invFun := fun v => ⟨(transposeVertexEquiv P).symm v.1, by
    rw [transpose_xStarBoundaryVertexMember, Equiv.apply_symm_apply]
    exact v.2⟩
  left_inv := fun v => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun v => Subtype.ext (Equiv.apply_symm_apply _ _)
noncomputable def transposeXStarBoundaryEdgeEquiv
    (P : TannerSquarePresentation) (z : P.Z) :
    XStarBoundaryEdge (transposePresentation P) z ≃ ZStarBoundaryEdge P z where
  toFun := fun e => ⟨transposeEdgeEquiv P e.1, by simpa using e.2⟩
  invFun := fun e => ⟨(transposeEdgeEquiv P).symm e.1, by
    rw [transpose_xStarBoundaryEdgeMember, Equiv.apply_symm_apply]
    exact e.2⟩
  left_inv := fun e => Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun e => Subtype.ext (Equiv.apply_symm_apply _ _)
@[simp] theorem transposeXStarFace_card (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarFace (transposePresentation P) z) =
      Fintype.card (ZStarFace P z) :=
  Fintype.card_congr (transposeXStarFaceEquiv P z)
@[simp] theorem transposeXStarVertex_card (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarVertex (transposePresentation P) z) =
      Fintype.card (ZStarVertex P z) :=
  Fintype.card_congr (transposeXStarVertexEquiv P z)
@[simp] theorem transposeXStarEdge_card (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarEdge (transposePresentation P) z) =
      Fintype.card (ZStarEdge P z) :=
  Fintype.card_congr (transposeXStarEdgeEquiv P z)
@[simp] theorem transposeXStarBoundaryVertex_card
    (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarBoundaryVertex (transposePresentation P) z) =
      Fintype.card (ZStarBoundaryVertex P z) :=
  Fintype.card_congr (transposeXStarBoundaryVertexEquiv P z)
@[simp] theorem transposeXStarBoundaryEdge_card
    (P : TannerSquarePresentation) (z : P.Z) :
    Fintype.card (XStarBoundaryEdge (transposePresentation P) z) =
      Fintype.card (ZStarBoundaryEdge P z) :=
  Fintype.card_congr (transposeXStarBoundaryEdgeEquiv P z)
def coordinateRestriction {A : Type} [Fintype A] [DecidableEq A]
    (member : A → Bool) :
    Word Field A →ₗ[Field] Word Field {a : A // member a} where
  toFun := fun w a => w a.1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
def coordinateExtensionZero {A : Type} [Fintype A] [DecidableEq A]
    (member : A → Bool) :
    Word Field {a : A // member a} →ₗ[Field] Word Field A where
  toFun := fun w a => if h : member a then w ⟨a, h⟩ else 0
  map_add' := by
    intros
    ext a
    by_cases h : member a <;> simp [h]
  map_smul' := by
    intros
    ext a
    by_cases h : member a <;> simp [h]
@[simp]
theorem coordinateRestriction_apply {A : Type} [Fintype A] [DecidableEq A]
    (member : A → Bool) (w : Word Field A) (a : {a : A // member a}) :
    coordinateRestriction member w a = w a.1 := rfl
@[simp]
theorem coordinateExtensionZero_apply_mem {A : Type} [Fintype A] [DecidableEq A]
    (member : A → Bool) (w : Word Field {a : A // member a})
    (a : {a : A // member a}) :
    coordinateExtensionZero member w a.1 = w a := by
  simp [coordinateExtensionZero, a.2]
noncomputable def vertexBasis (P : TannerSquarePresentation) :
    Basis (Vertex P) Field (Word Field (Vertex P)) := Pi.basisFun Field (Vertex P)
noncomputable def edgeBasis (P : TannerSquarePresentation) :
    Basis (Edge P) Field (Word Field (Edge P)) := Pi.basisFun Field (Edge P)
noncomputable def faceBasis (P : TannerSquarePresentation) :
    Basis P.Face Field (Word Field P.Face) := Pi.basisFun Field P.Face
structure OddScale where
  ell : Nat
  odd : ell % 2 = 1
  three_le : 3 ≤ ell
def OddScale.half (S : OddScale) : Nat := (S.ell - 1) / 2
theorem OddScale.half_pos (S : OddScale) : 0 < S.half := by
  have hthree := S.three_le
  unfold OddScale.half
  omega
abbrev SubdivisionVertex (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  XStarVertex P x ⊕
    ((XStarEdge P x × Fin (S.half - 1)) ⊕
      (XStarFace P x × Fin (S.half - 1) × Fin (S.half - 1)))
abbrev SubdivisionEdge (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  (XStarEdge P x × Fin S.half) ⊕
    ((XStarFace P x × Fin S.half × Fin (S.half - 1)) ⊕
      (XStarFace P x × Fin (S.half - 1) × Fin S.half))
abbrev SubdivisionFace (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  XStarFace P x × Fin S.half × Fin S.half
def subdivisionBoundaryVertexMember (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) : SubdivisionVertex P x S → Bool
  | Sum.inl v => xStarBoundaryVertexMember P x v.1
  | Sum.inr (Sum.inl ei) => xStarBoundaryEdgeMember P x ei.1.1
  | Sum.inr (Sum.inr _) => false
def subdivisionBoundaryEdgeMember (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) : SubdivisionEdge P x S → Bool
  | Sum.inl ei => xStarBoundaryEdgeMember P x ei.1.1
  | Sum.inr _ => false
abbrev SubdivisionBoundaryVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := {v : SubdivisionVertex P x S // subdivisionBoundaryVertexMember P x S v}
abbrev SubdivisionBoundaryEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := {e : SubdivisionEdge P x S // subdivisionBoundaryEdgeMember P x S e}
def subdivisionOriginalBoundaryVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (v : XStarBoundaryVertex P x) :
    SubdivisionBoundaryVertex P x S :=
  ⟨Sum.inl (xStarBoundaryVertexToStar P x v), v.2⟩
def subdivisionOriginalBoundaryEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarBoundaryEdge P x) (k : Fin S.half) :
    SubdivisionBoundaryEdge P x S :=
  ⟨Sum.inl (xStarBoundaryEdgeToStar P x e, k), e.2⟩
def scaleFive : OddScale where
  ell := 5
  odd := by decide
  three_le := by decide
@[simp] theorem scaleFive_half : scaleFive.half = 2 := by decide
@[simp] theorem baseX0StarVertex_card :
    Fintype.card (XStarVertex baseTannerSquarePresentation (0 : BaseX)) = 6 := by decide +kernel
@[simp] theorem baseX0StarEdge_card :
    Fintype.card (XStarEdge baseTannerSquarePresentation (0 : BaseX)) = 7 := by decide +kernel
@[simp] theorem baseX0StarFace_card :
    Fintype.card (XStarFace baseTannerSquarePresentation (0 : BaseX)) = 2 := by decide +kernel
@[simp] theorem baseX0StarBoundaryVertex_card :
    Fintype.card (XStarBoundaryVertex baseTannerSquarePresentation (0 : BaseX)) = 5 := by decide +kernel
@[simp] theorem baseX0StarBoundaryEdge_card :
    Fintype.card (XStarBoundaryEdge baseTannerSquarePresentation (0 : BaseX)) = 4 := by decide +kernel
@[simp] theorem baseX0SubdivisionVertex_card :
    Fintype.card (SubdivisionVertex baseTannerSquarePresentation (0 : BaseX) scaleFive) = 15 := by
  decide +kernel
@[simp] theorem baseX0SubdivisionEdge_card :
    Fintype.card (SubdivisionEdge baseTannerSquarePresentation (0 : BaseX) scaleFive) = 22 := by
  decide +kernel
@[simp] theorem baseX0SubdivisionFace_card :
    Fintype.card (SubdivisionFace baseTannerSquarePresentation (0 : BaseX) scaleFive) = 8 := by
  decide +kernel
@[simp] theorem baseX0SubdivisionBoundaryVertex_card :
    Fintype.card (SubdivisionBoundaryVertex baseTannerSquarePresentation (0 : BaseX) scaleFive) = 9 := by
  decide +kernel
@[simp] theorem baseX0SubdivisionBoundaryEdge_card :
    Fintype.card (SubdivisionBoundaryEdge baseTannerSquarePresentation (0 : BaseX) scaleFive) = 8 := by
  decide +kernel
def xStarFaceXQEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) : XStarEdge P x :=
  ⟨Sum.inl (faceXQEdge P f.1 i), by
    have hf : P.faceX f.1 = x := by
      simpa [xStarFaceMember] using f.2
    simp only [xStarEdgeMember]
    simp only [decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [xStarFaceMember] using hf
    · fin_cases i <;> simp [faceUsesXQEdge]⟩
def xStarFaceQZEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) : XStarEdge P x :=
  ⟨Sum.inr (faceQZEdge P f.1 i), by
    have hf : P.faceX f.1 = x := by
      simpa [xStarFaceMember] using f.2
    simp only [xStarEdgeMember]
    simp only [decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [xStarFaceMember] using hf
    · fin_cases i <;> simp [faceUsesQZEdge]⟩
def zStarFaceXQEdge (P : TannerSquarePresentation) (z : P.Z)
    (f : ZStarFace P z) (i : Two) : ZStarEdge P z :=
  ⟨Sum.inl (faceXQEdge P f.1 i), by
    have hf : P.faceZ f.1 = z := by
      simpa [zStarFaceMember] using f.2
    change decide (∃ face : P.Face,
      zStarFaceMember P z face = true ∧
        decide (faceXQEdge P f.1 i = faceXQEdge P face 0 ∨
          faceXQEdge P f.1 i = faceXQEdge P face 1) = true) = true
    rw [decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [zStarFaceMember] using hf
    · fin_cases i <;> simp⟩
def zStarFaceQZEdge (P : TannerSquarePresentation) (z : P.Z)
    (f : ZStarFace P z) (i : Two) : ZStarEdge P z :=
  ⟨Sum.inr (faceQZEdge P f.1 i), by
    have hf : P.faceZ f.1 = z := by
      simpa [zStarFaceMember] using f.2
    change decide (∃ face : P.Face,
      zStarFaceMember P z face = true ∧
        decide (faceQZEdge P f.1 i = faceQZEdge P face 0 ∨
          faceQZEdge P f.1 i = faceQZEdge P face 1) = true) = true
    rw [decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [zStarFaceMember] using hf
    · fin_cases i <;> simp⟩
def xStarFaceXVertex (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) : XStarVertex P x :=
  ⟨Vertex.x (P.faceX f.1), by
    have hf : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
    simp [xStarVertexMember, hf]⟩
def xStarFaceQVertex (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) : XStarVertex P x :=
  ⟨Vertex.q (P.faceQ f.1 i), by
    have hf : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
    simp only [xStarVertexMember, decide_eq_true_eq]
    refine ⟨f.1, ?_, ?_⟩
    · simpa [xStarFaceMember] using hf
    · fin_cases i <;> simp⟩
def xStarFaceZVertex (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) : XStarVertex P x :=
  ⟨Vertex.z (P.faceZ f.1), by
    have hf : P.faceX f.1 = x := by simpa [xStarFaceMember] using f.2
    simp only [xStarVertexMember, decide_eq_true_eq]
    exact ⟨f.1, by simpa [xStarFaceMember] using hf, rfl⟩⟩
def xStarFaceCorner (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (corner : Two × Two) : XStarVertex P x :=
  if corner.1 = 0 then
    if corner.2 = 0 then xStarFaceXVertex P x f
    else xStarFaceQVertex P x f 1
  else if corner.2 = 0 then xStarFaceQVertex P x f 0
  else xStarFaceZVertex P x f
@[simp] theorem xStarFaceCorner_zero_zero
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    xStarFaceCorner P x f (0, 0) = xStarFaceXVertex P x f := by
  simp [xStarFaceCorner]
@[simp] theorem xStarFaceCorner_zero_one
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    xStarFaceCorner P x f (0, 1) = xStarFaceQVertex P x f 1 := by
  simp [xStarFaceCorner]
@[simp] theorem xStarFaceCorner_one_zero
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    xStarFaceCorner P x f (1, 0) = xStarFaceQVertex P x f 0 := by
  simp [xStarFaceCorner]
@[simp] theorem xStarFaceCorner_one_one
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x) :
    xStarFaceCorner P x f (1, 1) = xStarFaceZVertex P x f := by
  simp [xStarFaceCorner]
@[simp] theorem xStarFaceXQEdge_ne_QZEdge
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x)
    (i j : Two) :
    xStarFaceXQEdge P x f i ≠ xStarFaceQZEdge P x f j := by
  intro h
  have hvalue := congrArg Subtype.val h
  cases hvalue
@[simp] theorem xStarFaceQZEdge_ne_XQEdge
    (P : TannerSquarePresentation) (x : P.X) (f : XStarFace P x)
    (i j : Two) :
    xStarFaceQZEdge P x f i ≠ xStarFaceXQEdge P x f j :=
  Ne.symm (xStarFaceXQEdge_ne_QZEdge P x f j i)
def xStarEdgeStart (P : TannerSquarePresentation) (x : P.X)
    (e : XStarEdge P x) : XStarVertex P x := by
  rcases e with ⟨e, he⟩
  rcases e with eq | eq
  · refine ⟨Vertex.x eq.1.1, ?_⟩
    simp only [xStarEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceXQEdge P f 0 ∨ eq = faceXQEdge P f 1 := by
      simpa [faceUsesXQEdge] using huse
    have hx : eq.1.1 = P.faceX f := by
      rcases huse' with huse | huse
      · exact congrArg (fun e : XQEdge P => e.1.1) huse
      · exact congrArg (fun e : XQEdge P => e.1.1) huse
    simp [xStarVertexMember, hx]
    simpa [xStarFaceMember] using hf
  · refine ⟨Vertex.q eq.1.1, ?_⟩
    simp only [xStarEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceQZEdge P f 0 ∨ eq = faceQZEdge P f 1 := by
      simpa [faceUsesQZEdge] using huse
    simp only [xStarVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact Or.inl (congrArg (fun e : QZEdge P => e.1.1) huse)
    · exact Or.inr (congrArg (fun e : QZEdge P => e.1.1) huse)
def xStarEdgeEnd (P : TannerSquarePresentation) (x : P.X)
    (e : XStarEdge P x) : XStarVertex P x := by
  rcases e with ⟨e, he⟩
  rcases e with eq | eq
  · refine ⟨Vertex.q eq.1.2, ?_⟩
    simp only [xStarEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceXQEdge P f 0 ∨ eq = faceXQEdge P f 1 := by
      simpa [faceUsesXQEdge] using huse
    simp only [xStarVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact Or.inl (congrArg (fun e : XQEdge P => e.1.2) huse)
    · exact Or.inr (congrArg (fun e : XQEdge P => e.1.2) huse)
  · refine ⟨Vertex.z eq.1.2, ?_⟩
    simp only [xStarEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceQZEdge P f 0 ∨ eq = faceQZEdge P f 1 := by
      simpa [faceUsesQZEdge] using huse
    simp only [xStarVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact congrArg (fun e : QZEdge P => e.1.2) huse
    · exact congrArg (fun e : QZEdge P => e.1.2) huse
def finCastGrid {m : Nat} (i : Fin m) : Fin (m + 1) :=
  ⟨i.1, Nat.lt_succ_of_lt i.2⟩
def finSuccGrid {m : Nat} (i : Fin m) : Fin (m + 1) :=
  ⟨i.1 + 1, by omega⟩
def finInteriorGrid (S : OddScale) (i : Fin (S.half - 1)) : Fin (S.half + 1) :=
  ⟨i.1 + 1, by have := S.half_pos; omega⟩
def finInteriorIndex (S : OddScale) (i : Fin (S.half + 1))
    (h0 : i.1 ≠ 0) (hlast : i.1 ≠ S.half) : Fin (S.half - 1) :=
  ⟨i.1 - 1, by have := i.2; omega⟩
def subdivisionSegmentStart (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarEdge P x) (k : Fin S.half) :
    SubdivisionVertex P x S :=
  if h : k.1 = 0 then
    Sum.inl (xStarEdgeStart P x e)
  else
    Sum.inr (Sum.inl (e, ⟨k.1 - 1, by have := k.2; omega⟩))
def subdivisionSegmentEnd (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : XStarEdge P x) (k : Fin S.half) :
    SubdivisionVertex P x S :=
  if h : k.1 + 1 = S.half then
    Sum.inl (xStarEdgeEnd P x e)
  else
    Sum.inr (Sum.inl (e, ⟨k.1, by have := k.2; omega⟩))
def subdivisionGridVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x)
    (i j : Fin (S.half + 1)) : SubdivisionVertex P x S :=
  if hi0 : i.1 = 0 then
    if hj0 : j.1 = 0 then Sum.inl (xStarFaceXVertex P x f)
    else if hjm : j.1 = S.half then Sum.inl (xStarFaceQVertex P x f 1)
    else Sum.inr (Sum.inl
      (xStarFaceXQEdge P x f 1, finInteriorIndex S j hj0 hjm))
  else if him : i.1 = S.half then
    if hj0 : j.1 = 0 then Sum.inl (xStarFaceQVertex P x f 0)
    else if hjm : j.1 = S.half then Sum.inl (xStarFaceZVertex P x f)
    else Sum.inr (Sum.inl
      (xStarFaceQZEdge P x f 0, finInteriorIndex S j hj0 hjm))
  else if hj0 : j.1 = 0 then
    Sum.inr (Sum.inl
      (xStarFaceXQEdge P x f 0, finInteriorIndex S i hi0 him))
  else if hjm : j.1 = S.half then
    Sum.inr (Sum.inl
      (xStarFaceQZEdge P x f 1, finInteriorIndex S i hi0 him))
  else
    Sum.inr (Sum.inr
      (f, finInteriorIndex S i hi0 him, finInteriorIndex S j hj0 hjm))
def subdivisionHorizontalEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (j : Fin (S.half + 1)) : SubdivisionEdge P x S :=
  if hj0 : j.1 = 0 then Sum.inl (xStarFaceXQEdge P x f 0, i)
  else if hjm : j.1 = S.half then Sum.inl (xStarFaceQZEdge P x f 1, i)
  else Sum.inr (Sum.inl (f, i, finInteriorIndex S j hj0 hjm))
def subdivisionVerticalEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin (S.half + 1))
    (j : Fin S.half) : SubdivisionEdge P x S :=
  if hi0 : i.1 = 0 then Sum.inl (xStarFaceXQEdge P x f 1, j)
  else if him : i.1 = S.half then Sum.inl (xStarFaceQZEdge P x f 0, j)
  else Sum.inr (Sum.inr (f, finInteriorIndex S i hi0 him, j))
def subdivisionEdgeStart (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) : SubdivisionEdge P x S → SubdivisionVertex P x S
  | Sum.inl ei => subdivisionSegmentStart P x S ei.1 ei.2
  | Sum.inr (Sum.inl h) =>
      subdivisionGridVertex P x S h.1 (finCastGrid h.2.1) (finInteriorGrid S h.2.2)
  | Sum.inr (Sum.inr v) =>
      subdivisionGridVertex P x S v.1 (finInteriorGrid S v.2.1) (finCastGrid v.2.2)
def subdivisionEdgeEnd (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) : SubdivisionEdge P x S → SubdivisionVertex P x S
  | Sum.inl ei => subdivisionSegmentEnd P x S ei.1 ei.2
  | Sum.inr (Sum.inl h) =>
      subdivisionGridVertex P x S h.1 (finSuccGrid h.2.1) (finInteriorGrid S h.2.2)
  | Sum.inr (Sum.inr v) =>
      subdivisionGridVertex P x S v.1 (finInteriorGrid S v.2.1) (finSuccGrid v.2.2)
@[simp]
theorem xStarEdgeStart_faceXQEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) :
    xStarEdgeStart P x (xStarFaceXQEdge P x f i) = xStarFaceXVertex P x f := by
  apply Subtype.ext
  rfl
@[simp]
theorem xStarEdgeEnd_faceXQEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) :
    xStarEdgeEnd P x (xStarFaceXQEdge P x f i) = xStarFaceQVertex P x f i := by
  apply Subtype.ext
  rfl
@[simp]
theorem xStarEdgeStart_faceQZEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) :
    xStarEdgeStart P x (xStarFaceQZEdge P x f i) = xStarFaceQVertex P x f i := by
  apply Subtype.ext
  rfl
@[simp]
theorem xStarEdgeEnd_faceQZEdge (P : TannerSquarePresentation) (x : P.X)
    (f : XStarFace P x) (i : Two) :
    xStarEdgeEnd P x (xStarFaceQZEdge P x f i) = xStarFaceZVertex P x f := by
  apply Subtype.ext
  rfl
@[simp]
theorem finInteriorGrid_finInteriorIndex (S : OddScale)
    (i : Fin (S.half + 1)) (h0 : i.1 ≠ 0) (hlast : i.1 ≠ S.half) :
    finInteriorGrid S (finInteriorIndex S i h0 hlast) = i := by
  apply Fin.ext
  simp [finInteriorGrid, finInteriorIndex]
  omega
def gridLast (S : OddScale) : Fin (S.half + 1) :=
  ⟨S.half, by omega⟩
def subdivisionGridCoordinate
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (f : XStarFace P x) :
    SubdivisionVertex P x S → Option (Fin (S.half + 1) × Fin (S.half + 1))
  | Sum.inl vertex =>
      if vertex = xStarFaceXVertex P x f then some (0, 0)
      else if vertex = xStarFaceQVertex P x f 1 then some (0, gridLast S)
      else if vertex = xStarFaceQVertex P x f 0 then some (gridLast S, 0)
      else if vertex = xStarFaceZVertex P x f then
        some (gridLast S, gridLast S)
      else none
  | Sum.inr (Sum.inl edgeInterior) =>
      if edgeInterior.1 = xStarFaceXQEdge P x f 1 then
        some (0, finInteriorGrid S edgeInterior.2)
      else if edgeInterior.1 = xStarFaceQZEdge P x f 0 then
        some (gridLast S, finInteriorGrid S edgeInterior.2)
      else if edgeInterior.1 = xStarFaceXQEdge P x f 0 then
        some (finInteriorGrid S edgeInterior.2, 0)
      else if edgeInterior.1 = xStarFaceQZEdge P x f 1 then
        some (finInteriorGrid S edgeInterior.2, gridLast S)
      else none
  | Sum.inr (Sum.inr faceInterior) =>
      if faceInterior.1 = f then
        some (finInteriorGrid S faceInterior.2.1,
          finInteriorGrid S faceInterior.2.2)
      else none
@[simp] theorem subdivisionGridVertex_edgeInterior_xq0
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (index : Fin (S.half - 1)) :
    subdivisionGridVertex P x S face
        ⟨index.1 + 1, by have := index.2; omega⟩ 0 =
      Sum.inr (Sum.inl (xStarFaceXQEdge P x face 0, index)) := by
  have hnot : index.1 + 1 ≠ S.half := by have := index.2; omega
  simp [subdivisionGridVertex, hnot, finInteriorIndex]
@[simp] theorem subdivisionGridVertex_edgeInterior_xq1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (index : Fin (S.half - 1)) :
    subdivisionGridVertex P x S face 0
        ⟨index.1 + 1, by have := index.2; omega⟩ =
      Sum.inr (Sum.inl (xStarFaceXQEdge P x face 1, index)) := by
  have hnot : index.1 + 1 ≠ S.half := by have := index.2; omega
  simp [subdivisionGridVertex, hnot, finInteriorIndex]
@[simp] theorem subdivisionGridVertex_edgeInterior_qz0
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (index : Fin (S.half - 1)) :
    subdivisionGridVertex P x S face
        ⟨S.half, by omega⟩
        ⟨index.1 + 1, by have := index.2; omega⟩ =
      Sum.inr (Sum.inl (xStarFaceQZEdge P x face 0, index)) := by
  have hnot : index.1 + 1 ≠ S.half := by have := index.2; omega
  have hpos := S.half_pos
  simp [subdivisionGridVertex, hnot, finInteriorIndex, S.half_pos.ne']
@[simp] theorem subdivisionGridVertex_edgeInterior_qz1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (index : Fin (S.half - 1)) :
    subdivisionGridVertex P x S face
        ⟨index.1 + 1, by have := index.2; omega⟩
        ⟨S.half, by omega⟩ =
      Sum.inr (Sum.inl (xStarFaceQZEdge P x face 1, index)) := by
  have hnot : index.1 + 1 ≠ S.half := by have := index.2; omega
  have hpos := S.half_pos
  simp [subdivisionGridVertex, hnot, finInteriorIndex, S.half_pos.ne']
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem subdivisionHorizontalEdge_start (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (j : Fin (S.half + 1)) :
    subdivisionEdgeStart P x S (subdivisionHorizontalEdge P x S f i j) =
      subdivisionGridVertex P x S f (finCastGrid i) j := by
  have hm := S.half_pos
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt hm
  have him : i.1 ≠ S.half := by omega
  let last : Fin (S.half + 1) := ⟨S.half, by omega⟩
  by_cases hjzero : j = 0
  · subst j
    by_cases hi0 : i.1 = 0
    ·
      simp [subdivisionHorizontalEdge, subdivisionEdgeStart,
        subdivisionSegmentStart, subdivisionGridVertex, finCastGrid, hm0, hi0]
    ·
      simp [subdivisionHorizontalEdge, subdivisionEdgeStart,
        subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
        finInteriorIndex, hm0, hi0, him]
  · by_cases hjlast : j = last
    · subst j
      by_cases hi0 : i.1 = 0
      ·
        simp [last, subdivisionHorizontalEdge, subdivisionEdgeStart,
          subdivisionSegmentStart, subdivisionGridVertex, finCastGrid, hm0, hi0]
      ·
        simp [last, subdivisionHorizontalEdge, subdivisionEdgeStart,
          subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
          finInteriorIndex, hm0, hi0, him]
    · have hj0 : j.1 ≠ 0 := by
        intro h
        apply hjzero
        apply Fin.ext
        simpa using h
      have hjm : j.1 ≠ S.half := by
        intro h
        apply hjlast
        apply Fin.ext
        simpa [last] using h
      by_cases hi0 : i.1 = 0
      ·
        simp [subdivisionHorizontalEdge, subdivisionEdgeStart,
          subdivisionGridVertex, finCastGrid, finInteriorGrid,
          finInteriorIndex, Fin.ext_iff, hm0, hjzero, hjlast, hj0, hjm, hi0]
        have hpred : j.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
      ·
        simp [subdivisionHorizontalEdge, subdivisionEdgeStart,
          subdivisionGridVertex, finCastGrid, finInteriorGrid,
          finInteriorIndex, Fin.ext_iff, hm0, hjzero, hjlast, hj0, hjm, hi0, him]
        have hpred : j.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem subdivisionHorizontalEdge_end (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin S.half)
    (j : Fin (S.half + 1)) :
    subdivisionEdgeEnd P x S (subdivisionHorizontalEdge P x S f i j) =
      subdivisionGridVertex P x S f (finSuccGrid i) j := by
  have hm := S.half_pos
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt hm
  have hisucc0 : i.1 + 1 ≠ 0 := by omega
  let last : Fin (S.half + 1) := ⟨S.half, by omega⟩
  by_cases hjzero : j = 0
  · subst j
    by_cases hilast : i.1 + 1 = S.half <;>
      simp [subdivisionHorizontalEdge, subdivisionEdgeEnd,
        subdivisionSegmentEnd, subdivisionGridVertex, finSuccGrid,
        finInteriorIndex, hm0, hisucc0, hilast]
  · by_cases hjlast : j = last
    · subst j
      by_cases hilast : i.1 + 1 = S.half <;>
        simp [last, subdivisionHorizontalEdge, subdivisionEdgeEnd,
          subdivisionSegmentEnd, subdivisionGridVertex, finSuccGrid,
          finInteriorIndex, hm0, hisucc0, hilast]
    · have hj0 : j.1 ≠ 0 := by
        intro h
        apply hjzero
        apply Fin.ext
        simpa using h
      have hjm : j.1 ≠ S.half := by
        intro h
        apply hjlast
        apply Fin.ext
        simpa [last] using h
      by_cases hilast : i.1 + 1 = S.half
      · simp [subdivisionHorizontalEdge, subdivisionEdgeEnd,
          subdivisionGridVertex, finSuccGrid, finInteriorGrid,
          finInteriorIndex, hm0, hj0, hjm, hisucc0, hilast]
        have hpred : j.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
      · simp [subdivisionHorizontalEdge, subdivisionEdgeEnd,
          subdivisionGridVertex, finSuccGrid, finInteriorGrid,
          finInteriorIndex, hm0, hj0, hjm, hisucc0, hilast]
        have hpred : j.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem subdivisionVerticalEdge_start (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin (S.half + 1))
    (j : Fin S.half) :
    subdivisionEdgeStart P x S (subdivisionVerticalEdge P x S f i j) =
      subdivisionGridVertex P x S f i (finCastGrid j) := by
  have hm := S.half_pos
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt hm
  have hjm : j.1 ≠ S.half := by omega
  let last : Fin (S.half + 1) := ⟨S.half, by omega⟩
  by_cases hizero : i = 0
  · subst i
    by_cases hj0 : j.1 = 0
    · simp [subdivisionVerticalEdge, subdivisionEdgeStart,
        subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
        hm0, hj0, hjm]
    · simp [subdivisionVerticalEdge, subdivisionEdgeStart,
        subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
        finInteriorIndex, hm0, hj0, hjm]
  · by_cases hilast : i = last
    · subst i
      by_cases hj0 : j.1 = 0
      · simp [last, subdivisionVerticalEdge, subdivisionEdgeStart,
          subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
          hm0, hj0, hjm]
      · simp [last, subdivisionVerticalEdge, subdivisionEdgeStart,
          subdivisionSegmentStart, subdivisionGridVertex, finCastGrid,
          finInteriorIndex, hm0, hj0, hjm]
    · have hi0 : i.1 ≠ 0 := by
        intro h
        apply hizero
        apply Fin.ext
        simpa using h
      have him : i.1 ≠ S.half := by
        intro h
        apply hilast
        apply Fin.ext
        simpa [last] using h
      by_cases hj0 : j.1 = 0
      · simp [subdivisionVerticalEdge, subdivisionEdgeStart,
          subdivisionGridVertex, finCastGrid, finInteriorGrid,
          finInteriorIndex, hi0, him, hj0, hjm]
        have hpred : i.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
      · simp [subdivisionVerticalEdge, subdivisionEdgeStart,
          subdivisionGridVertex, finCastGrid, finInteriorGrid,
          finInteriorIndex, hi0, him, hj0, hjm]
        have hpred : i.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem subdivisionVerticalEdge_end (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (f : XStarFace P x) (i : Fin (S.half + 1))
    (j : Fin S.half) :
    subdivisionEdgeEnd P x S (subdivisionVerticalEdge P x S f i j) =
      subdivisionGridVertex P x S f i (finSuccGrid j) := by
  have hm := S.half_pos
  have hm0 : S.half ≠ 0 := Nat.ne_of_gt hm
  have hjsucc0 : j.1 + 1 ≠ 0 := by omega
  let last : Fin (S.half + 1) := ⟨S.half, by omega⟩
  by_cases hizero : i = 0
  · subst i
    by_cases hjlast : j.1 + 1 = S.half <;>
      simp [subdivisionVerticalEdge, subdivisionEdgeEnd,
        subdivisionSegmentEnd, subdivisionGridVertex, finSuccGrid,
        finInteriorIndex, hm0, hjsucc0, hjlast]
  · by_cases hilast : i = last
    · subst i
      by_cases hjlast : j.1 + 1 = S.half <;>
        simp [last, subdivisionVerticalEdge, subdivisionEdgeEnd,
          subdivisionSegmentEnd, subdivisionGridVertex, finSuccGrid,
          finInteriorIndex, hm0, hjsucc0, hjlast]
    · have hi0 : i.1 ≠ 0 := by
        intro h
        apply hizero
        apply Fin.ext
        simpa using h
      have him : i.1 ≠ S.half := by
        intro h
        apply hilast
        apply Fin.ext
        simpa [last] using h
      by_cases hjlast : j.1 + 1 = S.half
      · simp [subdivisionVerticalEdge, subdivisionEdgeEnd,
          subdivisionGridVertex, finSuccGrid, finInteriorGrid,
          finInteriorIndex, hi0, him, hjsucc0, hjlast]
        have hpred : i.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
      · simp [subdivisionVerticalEdge, subdivisionEdgeEnd,
          subdivisionGridVertex, finSuccGrid, finInteriorGrid,
          finInteriorIndex, hi0, him, hjsucc0, hjlast]
        have hpred : i.1 - 1 + 1 ≠ S.half := by omega
        simp [hpred]
def subdivisionFaceBoundaryEdge
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) (slot : Two × Two) :
    SubdivisionEdge P x S :=
  if slot.1 = 0 then
    if slot.2 = 0 then
      subdivisionHorizontalEdge P x S face.1 face.2.1 (finCastGrid face.2.2)
    else
      subdivisionHorizontalEdge P x S face.1 face.2.1 (finSuccGrid face.2.2)
  else if slot.2 = 0 then
    subdivisionVerticalEdge P x S face.1 (finCastGrid face.2.1) face.2.2
  else
    subdivisionVerticalEdge P x S face.1 (finSuccGrid face.2.1) face.2.2
@[simp] theorem subdivisionFaceBoundaryEdge_zero_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    subdivisionFaceBoundaryEdge P x S face (0, 0) =
      subdivisionHorizontalEdge P x S face.1 face.2.1
        (finCastGrid face.2.2) := by
  simp [subdivisionFaceBoundaryEdge]
@[simp] theorem subdivisionFaceBoundaryEdge_zero_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    subdivisionFaceBoundaryEdge P x S face (0, 1) =
      subdivisionHorizontalEdge P x S face.1 face.2.1
        (finSuccGrid face.2.2) := by
  simp [subdivisionFaceBoundaryEdge]
@[simp] theorem subdivisionFaceBoundaryEdge_one_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    subdivisionFaceBoundaryEdge P x S face (1, 0) =
      subdivisionVerticalEdge P x S face.1
        (finCastGrid face.2.1) face.2.2 := by
  simp [subdivisionFaceBoundaryEdge]
@[simp] theorem subdivisionFaceBoundaryEdge_one_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (face : SubdivisionFace P x S) :
    subdivisionFaceBoundaryEdge P x S face (1, 1) =
      subdivisionVerticalEdge P x S face.1
        (finSuccGrid face.2.1) face.2.2 := by
  simp [subdivisionFaceBoundaryEdge]
noncomputable def subdivisionEdgeVertexMatrix (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Matrix (SubdivisionVertex P x S) (SubdivisionEdge P x S) Field := by
  classical
  exact fun v e =>
    (if v = subdivisionEdgeStart P x S e then 1 else 0) +
    (if v = subdivisionEdgeEnd P x S e then 1 else 0)
noncomputable def subdivisionFaceEdgeMatrix (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Matrix (SubdivisionEdge P x S) (SubdivisionFace P x S) Field := by
  classical
  exact fun e fij =>
    let f := fij.1
    let i := fij.2.1
    let j := fij.2.2
    (if e = subdivisionHorizontalEdge P x S f i (finCastGrid j) then 1 else 0) +
    (if e = subdivisionVerticalEdge P x S f (finSuccGrid i) j then 1 else 0) +
    (if e = subdivisionHorizontalEdge P x S f i (finSuccGrid j) then 1 else 0) +
    (if e = subdivisionVerticalEdge P x S f (finCastGrid i) j then 1 else 0)
theorem subdivisionEdgeVertexMatrix_mul_faceEdgeMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    subdivisionEdgeVertexMatrix P x S * subdivisionFaceEdgeMatrix P x S = 0 := by
  classical
  ext v fij
  rcases fij with ⟨f, i, j⟩
  rw [Matrix.mul_apply]
  simp only [subdivisionFaceEdgeMatrix, mul_add, Finset.sum_add_distrib,
    sum_mul_eqIndicator, subdivisionEdgeVertexMatrix]
  rw [subdivisionHorizontalEdge_start, subdivisionHorizontalEdge_end,
    subdivisionVerticalEdge_start, subdivisionVerticalEdge_end]
  rw [subdivisionHorizontalEdge_start, subdivisionHorizontalEdge_end,
    subdivisionVerticalEdge_start, subdivisionVerticalEdge_end]
  ring_nf
  simp [show (2 : Field) = 0 by
    change (2 : ZMod 2) = 0
    decide]
noncomputable def subdivisionBoundary1 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Word Field (SubdivisionEdge P x S) →ₗ[Field]
      Word Field (SubdivisionVertex P x S) := by
  classical
  exact Matrix.toLin' (subdivisionEdgeVertexMatrix P x S)
noncomputable def subdivisionBoundary2 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    Word Field (SubdivisionFace P x S) →ₗ[Field]
      Word Field (SubdivisionEdge P x S) := by
  classical
  exact Matrix.toLin' (subdivisionFaceEdgeMatrix P x S)
theorem subdivisionBoundary_squared (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    (subdivisionBoundary1 P x S).comp (subdivisionBoundary2 P x S) = 0 := by
  classical
  rw [subdivisionBoundary1, subdivisionBoundary2, ← Matrix.toLin'_mul]
  rw [subdivisionEdgeVertexMatrix_mul_faceEdgeMatrix]
  simp
noncomputable def subdivisionCoboundary0 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := wordLinearMapTranspose (subdivisionBoundary1 P x S)
noncomputable def subdivisionCoboundary1 (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := wordLinearMapTranspose (subdivisionBoundary2 P x S)
noncomputable def subdivisionChainComplex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :
    ChainComplexData Field
      (Word Field (SubdivisionVertex P x S))
      (Word Field (SubdivisionEdge P x S))
      (Word Field (SubdivisionFace P x S)) where
  boundary1 := subdivisionBoundary1 P x S
  boundary2 := subdivisionBoundary2 P x S
  boundary_squared := subdivisionBoundary_squared P x S
theorem xStarBoundaryEdge_start_mem (P : TannerSquarePresentation) (x : P.X)
    (e : XStarEdge P x) (he : xStarBoundaryEdgeMember P x e.1) :
    xStarBoundaryVertexMember P x (xStarEdgeStart P x e).1 := by
  rcases e with ⟨e, hstar⟩
  rcases e with eq | eq
  · simp [xStarBoundaryEdgeMember] at he
  · simp only [xStarBoundaryEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceQZEdge P f 0 ∨ eq = faceQZEdge P f 1 := by
      simpa [faceUsesQZEdge] using huse
    simp only [xStarEdgeStart, xStarBoundaryVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact Or.inl (congrArg (fun a : QZEdge P => a.1.1) huse)
    · exact Or.inr (congrArg (fun a : QZEdge P => a.1.1) huse)
theorem xStarBoundaryEdge_end_mem (P : TannerSquarePresentation) (x : P.X)
    (e : XStarEdge P x) (he : xStarBoundaryEdgeMember P x e.1) :
    xStarBoundaryVertexMember P x (xStarEdgeEnd P x e).1 := by
  rcases e with ⟨e, hstar⟩
  rcases e with eq | eq
  · simp [xStarBoundaryEdgeMember] at he
  · simp only [xStarBoundaryEdgeMember, decide_eq_true_eq] at he
    rcases he with ⟨f, hf, huse⟩
    have huse' : eq = faceQZEdge P f 0 ∨ eq = faceQZEdge P f 1 := by
      simpa [faceUsesQZEdge] using huse
    simp only [xStarEdgeEnd, xStarBoundaryVertexMember, decide_eq_true_eq]
    refine ⟨f, hf, ?_⟩
    rcases huse' with huse | huse
    · exact congrArg (fun a : QZEdge P => a.1.2) huse
    · exact congrArg (fun a : QZEdge P => a.1.2) huse
def subdivisionBoundaryEdgeStart (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : SubdivisionBoundaryEdge P x S) :
    SubdivisionBoundaryVertex P x S := by
  rcases e with ⟨e, he⟩
  rcases e with ei | interior
  · rcases ei with ⟨starEdge, k⟩
    refine ⟨subdivisionEdgeStart P x S (Sum.inl (starEdge, k)), ?_⟩
    simp only [subdivisionBoundaryEdgeMember] at he
    by_cases hk : k.1 = 0
    · simpa [subdivisionEdgeStart, subdivisionSegmentStart, hk,
        subdivisionBoundaryVertexMember] using
          xStarBoundaryEdge_start_mem P x starEdge he
    · simp [subdivisionEdgeStart, subdivisionSegmentStart, hk,
        subdivisionBoundaryVertexMember, he]
  · simp [subdivisionBoundaryEdgeMember] at he
def subdivisionBoundaryEdgeEnd (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) (e : SubdivisionBoundaryEdge P x S) :
    SubdivisionBoundaryVertex P x S := by
  rcases e with ⟨e, he⟩
  rcases e with ei | interior
  · rcases ei with ⟨starEdge, k⟩
    refine ⟨subdivisionEdgeEnd P x S (Sum.inl (starEdge, k)), ?_⟩
    simp only [subdivisionBoundaryEdgeMember] at he
    by_cases hk : k.1 + 1 = S.half
    · simpa [subdivisionEdgeEnd, subdivisionSegmentEnd, hk,
        subdivisionBoundaryVertexMember] using
          xStarBoundaryEdge_end_mem P x starEdge he
    · simp [subdivisionEdgeEnd, subdivisionSegmentEnd, hk,
        subdivisionBoundaryVertexMember, he]
  · simp [subdivisionBoundaryEdgeMember] at he
@[simp] theorem subdivisionBoundaryEdgeStart_value
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : SubdivisionBoundaryEdge P x S) :
    (subdivisionBoundaryEdgeStart P x S e).1 =
      subdivisionEdgeStart P x S e.1 := by
  rcases e with ⟨e, he⟩
  rcases e with ei | interior
  · rfl
  · simp [subdivisionBoundaryEdgeMember] at he
@[simp] theorem subdivisionBoundaryEdgeEnd_value
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (e : SubdivisionBoundaryEdge P x S) :
    (subdivisionBoundaryEdgeEnd P x S e).1 =
      subdivisionEdgeEnd P x S e.1 := by
  rcases e with ⟨e, he⟩
  rcases e with ei | interior
  · rfl
  · simp [subdivisionBoundaryEdgeMember] at he
abbrev SubdivisionBoundaryFace (_P : TannerSquarePresentation) (_x : _P.X)
    (_S : OddScale) := Fin 0
noncomputable def subdivisionBoundaryEdgeVertexMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Matrix (SubdivisionBoundaryVertex P x S)
      (SubdivisionBoundaryEdge P x S) Field := by
  classical
  exact fun v e =>
    (if v = subdivisionBoundaryEdgeStart P x S e then 1 else 0) +
    (if v = subdivisionBoundaryEdgeEnd P x S e then 1 else 0)
noncomputable def subdivisionBoundarySubcomplexBoundary1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionBoundaryEdge P x S) →ₗ[Field]
      Word Field (SubdivisionBoundaryVertex P x S) := by
  classical
  exact Matrix.toLin' (subdivisionBoundaryEdgeVertexMatrix P x S)
noncomputable def subdivisionBoundarySubcomplexBoundary2
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionBoundaryFace P x S) →ₗ[Field]
      Word Field (SubdivisionBoundaryEdge P x S) := 0
theorem subdivisionBoundarySubcomplexBoundary_squared
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    (subdivisionBoundarySubcomplexBoundary1 P x S).comp
      (subdivisionBoundarySubcomplexBoundary2 P x S) = 0 := by
  simp [subdivisionBoundarySubcomplexBoundary2]
noncomputable def subdivisionBoundarySubcomplex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    ChainComplexData Field
      (Word Field (SubdivisionBoundaryVertex P x S))
      (Word Field (SubdivisionBoundaryEdge P x S))
      (Word Field (SubdivisionBoundaryFace P x S)) where
  boundary1 := subdivisionBoundarySubcomplexBoundary1 P x S
  boundary2 := subdivisionBoundarySubcomplexBoundary2 P x S
  boundary_squared := subdivisionBoundarySubcomplexBoundary_squared P x S
abbrev DoubleCylinderVertex (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) := Two × SubdivisionVertex P x S
abbrev DoubleCylinderEdge (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :=
  (Two × SubdivisionEdge P x S) ⊕ SubdivisionBoundaryVertex P x S
abbrev DoubleCylinderFace (P : TannerSquarePresentation) (x : P.X)
    (S : OddScale) :=
  (Two × SubdivisionFace P x S) ⊕ SubdivisionBoundaryEdge P x S
@[simp] theorem baseX0DoubleCylinderVertex_card :
    Fintype.card (DoubleCylinderVertex baseTannerSquarePresentation
      (0 : BaseX) scaleFive) = 30 := by decide +kernel
@[simp] theorem baseX0DoubleCylinderEdge_card :
    Fintype.card (DoubleCylinderEdge baseTannerSquarePresentation
      (0 : BaseX) scaleFive) = 53 := by decide +kernel
@[simp] theorem baseX0DoubleCylinderFace_card :
    Fintype.card (DoubleCylinderFace baseTannerSquarePresentation
      (0 : BaseX) scaleFive) = 24 := by decide +kernel
noncomputable def doubleCylinderEdgeVertexMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Matrix (DoubleCylinderVertex P x S) (DoubleCylinderEdge P x S) Field := by
  classical
  exact fun tv e => match e with
    | Sum.inl se =>
        if tv.1 = se.1 then subdivisionEdgeVertexMatrix P x S tv.2 se.2 else 0
    | Sum.inr bv => if tv.2 = bv.1 then 1 else 0
noncomputable def doubleCylinderFaceEdgeMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Matrix (DoubleCylinderEdge P x S) (DoubleCylinderFace P x S) Field := by
  classical
  exact fun e face => match face with
    | Sum.inl sf => match e with
        | Sum.inl se =>
            if se.1 = sf.1 then subdivisionFaceEdgeMatrix P x S se.2 sf.2 else 0
        | Sum.inr _ => 0
    | Sum.inr be => match e with
        | Sum.inl se => if se.2 = be.1 then 1 else 0
        | Sum.inr bv =>
            (if bv = subdivisionBoundaryEdgeStart P x S be then 1 else 0) +
            (if bv = subdivisionBoundaryEdgeEnd P x S be then 1 else 0)
@[simp] theorem doubleCylinder_end_edge_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two) (v : SubdivisionVertex P x S) (e : SubdivisionEdge P x S) :
    doubleCylinderEdgeVertexMatrix P x S (t, v) (Sum.inl (t, e)) =
      subdivisionEdgeVertexMatrix P x S v e := by
  simp [doubleCylinderEdgeVertexMatrix]
@[simp] theorem doubleCylinder_vertical_edge_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two)
    (bv : SubdivisionBoundaryVertex P x S) :
    doubleCylinderEdgeVertexMatrix P x S (t, bv.1) (Sum.inr bv) = 1 := by
  classical
  simp [doubleCylinderEdgeVertexMatrix]
@[simp] theorem doubleCylinder_end_face_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two) (e : SubdivisionEdge P x S) (f : SubdivisionFace P x S) :
    doubleCylinderFaceEdgeMatrix P x S (Sum.inl (t, e)) (Sum.inl (t, f)) =
      subdivisionFaceEdgeMatrix P x S e f := by
  simp [doubleCylinderFaceEdgeMatrix]
@[simp] theorem doubleCylinder_rectangle_end_boundary
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (t : Two) (be : SubdivisionBoundaryEdge P x S) :
    doubleCylinderFaceEdgeMatrix P x S (Sum.inl (t, be.1)) (Sum.inr be) = 1 := by
  simp [doubleCylinderFaceEdgeMatrix]
def doubleCylinderRectangleCorner
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (corner : Two × Two) :
    DoubleCylinderVertex P x S :=
  (corner.1,
    if corner.2 = 0 then (subdivisionBoundaryEdgeStart P x S rectangle).1
    else (subdivisionBoundaryEdgeEnd P x S rectangle).1)
@[simp] theorem doubleCylinderRectangleCorner_copy_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (copy : Two) :
    doubleCylinderRectangleCorner P x S rectangle (copy, 0) =
      (copy, (subdivisionBoundaryEdgeStart P x S rectangle).1) := by
  simp [doubleCylinderRectangleCorner]
@[simp] theorem doubleCylinderRectangleCorner_copy_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (copy : Two) :
    doubleCylinderRectangleCorner P x S rectangle (copy, 1) =
      (copy, (subdivisionBoundaryEdgeEnd P x S rectangle).1) := by
  simp [doubleCylinderRectangleCorner]
def doubleCylinderRectangleBoundaryEdge
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (slot : Two × Two) :
    DoubleCylinderEdge P x S :=
  if slot.1 = 0 then
    Sum.inl (slot.2, rectangle.1)
  else if slot.2 = 0 then
    Sum.inr (subdivisionBoundaryEdgeStart P x S rectangle)
  else
    Sum.inr (subdivisionBoundaryEdgeEnd P x S rectangle)
@[simp] theorem doubleCylinderRectangleBoundaryEdge_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) (copy : Two) :
    doubleCylinderRectangleBoundaryEdge P x S rectangle (0, copy) =
      Sum.inl (copy, rectangle.1) := by
  simp [doubleCylinderRectangleBoundaryEdge]
@[simp] theorem doubleCylinderRectangleBoundaryEdge_one_zero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderRectangleBoundaryEdge P x S rectangle (1, 0) =
      Sum.inr (subdivisionBoundaryEdgeStart P x S rectangle) := by
  simp [doubleCylinderRectangleBoundaryEdge]
@[simp] theorem doubleCylinderRectangleBoundaryEdge_one_one
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale)
    (rectangle : SubdivisionBoundaryEdge P x S) :
    doubleCylinderRectangleBoundaryEdge P x S rectangle (1, 1) =
      Sum.inr (subdivisionBoundaryEdgeEnd P x S rectangle) := by
  simp [doubleCylinderRectangleBoundaryEdge]
theorem subtype_two_endpoint_sum
    {A B : Type} [Fintype A] [DecidableEq A] [DecidableEq B]
    (v : B) (value : A → B) (a b : A) :
    (∑ c : A, if v = value c then
      ((if c = a then (1 : Field) else 0) +
        (if c = b then 1 else 0)) else 0) =
      (if v = value a then 1 else 0) + (if v = value b then 1 else 0) := by
  calc
    _ = ∑ c : A, (if v = value c then (1 : Field) else 0) *
        ((if c = a then 1 else 0) + (if c = b then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases h : v = value c <;> simp [h]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, sum_mul_eqIndicator]
set_option maxHeartbeats 800000 in
/-- The quotient-free cylinder boundary squares to zero. -/
theorem doubleCylinderEdgeVertexMatrix_mul_faceEdgeMatrix
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    doubleCylinderEdgeVertexMatrix P x S *
      doubleCylinderFaceEdgeMatrix P x S = 0 := by
  classical
  ext tv face
  rcases tv with ⟨t, v⟩
  rcases face with sf | be
  · rcases sf with ⟨s, f⟩
    rw [Matrix.mul_apply]
    simp only [Fintype.sum_sum_type]
    rw [Fintype.sum_prod_type]
    fin_cases t <;> fin_cases s <;>
      simp [doubleCylinderEdgeVertexMatrix, doubleCylinderFaceEdgeMatrix,
        ← Matrix.mul_apply, subdivisionEdgeVertexMatrix_mul_faceEdgeMatrix]
  · rw [Matrix.mul_apply]
    simp only [Fintype.sum_sum_type]
    rw [Fintype.sum_prod_type]
    simp [doubleCylinderEdgeVertexMatrix, doubleCylinderFaceEdgeMatrix,
      subdivisionEdgeVertexMatrix]
    change
      (((if v = subdivisionEdgeStart P x S be.1 then (1 : Field) else 0) +
          (if v = subdivisionEdgeEnd P x S be.1 then 1 else 0)) +
        ∑ bv : SubdivisionBoundaryVertex P x S,
          if v = bv.1 then
            ((if bv = subdivisionBoundaryEdgeStart P x S be then 1 else 0) +
              (if bv = subdivisionBoundaryEdgeEnd P x S be then 1 else 0))
          else 0) = 0
    letI : DecidableEq (SubdivisionBoundaryVertex P x S) := Subtype.instDecidableEq
    have hsum :
        (∑ bv : SubdivisionBoundaryVertex P x S,
          if v = bv.1 then
            ((if bv = subdivisionBoundaryEdgeStart P x S be then (1 : Field) else 0) +
              (if bv = subdivisionBoundaryEdgeEnd P x S be then 1 else 0))
          else 0) =
        (if v = (subdivisionBoundaryEdgeStart P x S be).1 then 1 else 0) +
          (if v = (subdivisionBoundaryEdgeEnd P x S be).1 then 1 else 0) := by
      exact subtype_two_endpoint_sum v
        (fun bv : SubdivisionBoundaryVertex P x S => bv.1)
        (subdivisionBoundaryEdgeStart P x S be)
        (subdivisionBoundaryEdgeEnd P x S be)
    rw [hsum]
    simpa using field_add_self
      ((if v = (subdivisionBoundaryEdgeStart P x S be).1 then (1 : Field) else 0) +
        (if v = (subdivisionBoundaryEdgeEnd P x S be).1 then 1 else 0))
noncomputable def doubleCylinderBoundary1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (DoubleCylinderEdge P x S) →ₗ[Field]
      Word Field (DoubleCylinderVertex P x S) := by
  classical
  exact Matrix.toLin' (doubleCylinderEdgeVertexMatrix P x S)
noncomputable def doubleCylinderBoundary2
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (DoubleCylinderFace P x S) →ₗ[Field]
      Word Field (DoubleCylinderEdge P x S) := by
  classical
  exact Matrix.toLin' (doubleCylinderFaceEdgeMatrix P x S)
theorem doubleCylinderBoundary_squared
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    (doubleCylinderBoundary1 P x S).comp (doubleCylinderBoundary2 P x S) = 0 := by
  classical
  rw [doubleCylinderBoundary1, doubleCylinderBoundary2, ← Matrix.toLin'_mul]
  rw [doubleCylinderEdgeVertexMatrix_mul_faceEdgeMatrix]
  simp
noncomputable def doubleCylinderChainComplex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    ChainComplexData Field
      (Word Field (DoubleCylinderVertex P x S))
      (Word Field (DoubleCylinderEdge P x S))
      (Word Field (DoubleCylinderFace P x S)) where
  boundary1 := doubleCylinderBoundary1 P x S
  boundary2 := doubleCylinderBoundary2 P x S
  boundary_squared := doubleCylinderBoundary_squared P x S
noncomputable def doubleCylinderCoboundary0
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  wordLinearMapTranspose (doubleCylinderBoundary1 P x S)
noncomputable def doubleCylinderCoboundary1
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
noncomputable def subdivisionBoundaryVertexRestriction
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionVertex P x S) →ₗ[Field]
      Word Field (SubdivisionBoundaryVertex P x S) := by
  classical
  exact coordinateRestriction (subdivisionBoundaryVertexMember P x S)
noncomputable def subdivisionBoundaryVertexExtensionZero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionBoundaryVertex P x S) →ₗ[Field]
      Word Field (SubdivisionVertex P x S) := by
  classical
  exact coordinateExtensionZero (subdivisionBoundaryVertexMember P x S)
noncomputable def subdivisionBoundaryEdgeRestriction
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionEdge P x S) →ₗ[Field]
      Word Field (SubdivisionBoundaryEdge P x S) := by
  classical
  exact coordinateRestriction (subdivisionBoundaryEdgeMember P x S)
noncomputable def subdivisionBoundaryEdgeExtensionZero
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Word Field (SubdivisionBoundaryEdge P x S) →ₗ[Field]
      Word Field (SubdivisionEdge P x S) := by
  classical
  exact coordinateExtensionZero (subdivisionBoundaryEdgeMember P x S)
def doubleCylinderEndInclusion
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) (t : Two) :
    Word Field (SubdivisionVertex P x S) →ₗ[Field]
      Word Field (DoubleCylinderVertex P x S) where
  toFun := fun w tv => if tv.1 = t then w tv.2 else 0
  map_add' := by
    intros
    ext tv
    by_cases h : tv.1 = t <;> simp [h]
  map_smul' := by
    intros
    ext tv
    by_cases h : tv.1 = t <;> simp [h]
def doubleCylinderEndRestriction
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) (t : Two) :
    Word Field (DoubleCylinderVertex P x S) →ₗ[Field]
      Word Field (SubdivisionVertex P x S) where
  toFun := fun w v => w (t, v)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
noncomputable def subdivisionVertexBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Basis (SubdivisionVertex P x S) Field
      (Word Field (SubdivisionVertex P x S)) :=
  Pi.basisFun Field (SubdivisionVertex P x S)
noncomputable def subdivisionEdgeBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Basis (SubdivisionEdge P x S) Field
      (Word Field (SubdivisionEdge P x S)) :=
  Pi.basisFun Field (SubdivisionEdge P x S)
noncomputable def subdivisionFaceBasis
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :
    Basis (SubdivisionFace P x S) Field
      (Word Field (SubdivisionFace P x S)) :=
  Pi.basisFun Field (SubdivisionFace P x S)
noncomputable def subdivisionDualChainComplex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  dualChainComplex (subdivisionChainComplex P x S)
noncomputable def doubleCylinderDualChainComplex
    (P : TannerSquarePresentation) (x : P.X) (S : OddScale) :=
  dualChainComplex (doubleCylinderChainComplex P x S)
abbrev ZSubdivisionVertex (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  SubdivisionVertex (transposePresentation P) z S
abbrev ZSubdivisionEdge (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  SubdivisionEdge (transposePresentation P) z S
abbrev ZSubdivisionFace (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  SubdivisionFace (transposePresentation P) z S
abbrev ZSubdivisionBoundaryVertex (P : TannerSquarePresentation)
    (z : P.Z) (S : OddScale) :=
  SubdivisionBoundaryVertex (transposePresentation P) z S
abbrev ZSubdivisionBoundaryEdge (P : TannerSquarePresentation)
    (z : P.Z) (S : OddScale) :=
  SubdivisionBoundaryEdge (transposePresentation P) z S
abbrev ZDoubleCylinderVertex (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) := DoubleCylinderVertex (transposePresentation P) z S
abbrev ZDoubleCylinderEdge (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) := DoubleCylinderEdge (transposePresentation P) z S
abbrev ZDoubleCylinderFace (P : TannerSquarePresentation) (z : P.Z)
    (S : OddScale) := DoubleCylinderFace (transposePresentation P) z S
noncomputable def zSubdivisionChainComplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionChainComplex (transposePresentation P) z S
noncomputable def zSubdivisionBoundarySubcomplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundarySubcomplex (transposePresentation P) z S
noncomputable def zDoubleCylinderChainComplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  doubleCylinderChainComplex (transposePresentation P) z S
noncomputable def zSubdivisionBoundaryVertexRestriction
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundaryVertexRestriction (transposePresentation P) z S
noncomputable def zSubdivisionBoundaryVertexExtensionZero
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundaryVertexExtensionZero (transposePresentation P) z S
noncomputable def zSubdivisionBoundaryEdgeRestriction
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundaryEdgeRestriction (transposePresentation P) z S
noncomputable def zSubdivisionBoundaryEdgeExtensionZero
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionBoundaryEdgeExtensionZero (transposePresentation P) z S
noncomputable def zDoubleCylinderEndInclusion
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) (t : Two) :=
  doubleCylinderEndInclusion (transposePresentation P) z S t
noncomputable def zDoubleCylinderEndRestriction
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) (t : Two) :=
  doubleCylinderEndRestriction (transposePresentation P) z S t
noncomputable def zSubdivisionDualChainComplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  subdivisionDualChainComplex (transposePresentation P) z S
noncomputable def zDoubleCylinderDualChainComplex
    (P : TannerSquarePresentation) (z : P.Z) (S : OddScale) :=
  doubleCylinderDualChainComplex (transposePresentation P) z S
end BDL26FiniteTannerSquare
end Coding
end QEC


