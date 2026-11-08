-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
-- name    : QEC_Coding_BalancedProduct_LPSTanner
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:22:31.761345+00:00
-- url     : https://prove2.me/theorems/7efab53f-aed7-4a16-b348-87a2e8dcda38
-- title:
--   LPSTanner
-- statement:
--   Definitions and structural lemmas for LPSTanner, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTanner.lean

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_card_lpsGenerators401
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
noncomputable section
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
def localParityCheck :
    Word (ZMod 2) LocalCoordinate →ₗ[ZMod 2] Word (ZMod 2) (Fin 200) where
  toFun := fun w j =>
    w (Sum.inr j) - Matrix.vecMul (fun i => w (Sum.inl i)) localMatrix j
  map_add' := by
    intro x y
    funext j
    change (x (Sum.inr j) + y (Sum.inr j)) -
        Matrix.vecMul
          ((fun i => x (Sum.inl i)) + (fun i => y (Sum.inl i))) localMatrix j =
      (x (Sum.inr j) - Matrix.vecMul (fun i => x (Sum.inl i)) localMatrix j) +
        (y (Sum.inr j) - Matrix.vecMul (fun i => y (Sum.inl i)) localMatrix j)
    rw [Matrix.add_vecMul]
    exact add_sub_add_comm _ _ _ _
  map_smul' := by
    intro a x
    funext j
    change a * x (Sum.inr j) -
        Matrix.vecMul (a • fun i => x (Sum.inl i)) localMatrix j =
      a * (x (Sum.inr j) -
        Matrix.vecMul (fun i => x (Sum.inl i)) localMatrix j)
    rw [Matrix.smul_vecMul]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (mul_sub _ _ _).symm
@[simp]
theorem localParityCheck_apply (w : Word (ZMod 2) LocalCoordinate) (j : Fin 200) :
    localParityCheck w j =
      w (Sum.inr j) - Matrix.vecMul (fun i => w (Sum.inl i)) localMatrix j :=
  rfl
@[simp]
theorem localParityCheck_systematicEncode (m : Fin 202 → ZMod 2) :
    localParityCheck (systematicEncode localMatrix m) = 0 := by
  funext j
  simp [localParityCheck, systematicEncode]
abbrev Generator401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :=
  {s : PGL(2, ZMod q) // s ∈ lpsGenerators401 q hq}
theorem card_generator401
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Fintype.card (Generator401 q hq) = 402 := by
  simpa [Generator401] using card_lpsGenerators401 q hq40 hq
def generatorCoordinateEquiv
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Generator401 q hq ≃ LocalCoordinate :=
  Fintype.equivOfCardEq <|
    (card_generator401 q hq40 hq).trans localCoordinate_card.symm
def generatorNeighborEquiv
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    Generator401 q hq ≃ (lpsCayleyGraph401 q hq).neighborSet g :=
  Equiv.ofBijective
    (fun s : Generator401 q hq =>
      ⟨s.1 * g,
        (lpsCayleyGraph401_adj_iff q hq g (s.1 * g)).2
          ⟨s.1, s.2, rfl⟩⟩)
    ⟨by
      intro s t hst
      apply Subtype.ext
      apply mul_right_cancel (b := g)
      exact congrArg Subtype.val hst,
     by
      rintro ⟨w, hw⟩
      rcases (lpsCayleyGraph401_adj_iff q hq g w).1 hw with ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩⟩
def incidentGeneratorEquiv
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    (lpsCayleyGraph401 q hq).incidenceSet g ≃ Generator401 q hq :=
  ((lpsCayleyGraph401 q hq).incidenceSetEquivNeighborSet g).trans
    (generatorNeighborEquiv q hq g).symm
def incidentCoordinateEquiv
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    (lpsCayleyGraph401 q hq).incidenceSet g ≃ LocalCoordinate :=
  (incidentGeneratorEquiv q hq g).trans
    (generatorCoordinateEquiv q hq40 hq)
abbrev Vertex401 (q : ℕ) := PGL(2, ZMod q)
abbrev Edge401
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :=
  (lpsCayleyGraph401 q hq).edgeSet
noncomputable local instance edge401Fintype
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1) :
    Fintype (Edge401 q hq) := by
  letI : DecidableRel (lpsCayleyGraph401 q hq).Adj := Classical.decRel _
  exact SimpleGraph.fintypeEdgeSet (lpsCayleyGraph401 q hq)
abbrev Check401 (q : ℕ) := Vertex401 q × Fin 200
def edgeAsIncident
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) :
    (lpsCayleyGraph401 q hq).incidenceSet g :=
  ⟨e.1, e.2, hg⟩
def edgeLocalCoordinate
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) : LocalCoordinate :=
  incidentCoordinateEquiv q hq40 hq g (edgeAsIncident q hq e g hg)
def localCheckCoefficient (a : LocalCoordinate) (j : Fin 200) : ZMod 2 :=
  localParityCheck (canonicalBasisWord a) j
def incidentAsEdge
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    {g : Vertex401 q}
    (e : (lpsCayleyGraph401 q hq).incidenceSet g) : Edge401 q hq :=
  ⟨e.1, e.2.1⟩
def localView
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) :
    Word (ZMod 2) (Edge401 q hq) →ₗ[ZMod 2]
      Word (ZMod 2) LocalCoordinate where
  toFun := fun x a =>
    x (incidentAsEdge q hq
      ((incidentCoordinateEquiv q hq40 hq g).symm a))
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl
def tannerBoundary
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1) :
    Word (ZMod 2) (Edge401 q hq) →ₗ[ZMod 2]
      Word (ZMod 2) (Check401 q) where
  toFun := fun x gj => localParityCheck (localView q hq40 hq gj.1 x) gj.2
  map_add' := by
    intro x y
    funext gj
    exact congrFun
      ((localParityCheck.comp (localView q hq40 hq gj.1)).map_add x y) gj.2
  map_smul' := by
    intro a x
    funext gj
    exact congrFun
      ((localParityCheck.comp (localView q hq40 hq gj.1)).map_smul a x) gj.2
def activeLightVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) : Finset (Vertex401 q) := by
  classical
  exact Finset.univ.filter fun g =>
    localView q hq40 hq g x ≠ 0 ∧
      HammingWeight (localView q hq40 hq g x) < 41
def checkBlock
    (q : ℕ) (g : Vertex401 q) :
    Word (ZMod 2) (Check401 q) →ₗ[ZMod 2]
      Word (ZMod 2) (Fin 200) where
  toFun := fun y j => y (g, j)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl
structure DualExposureWitness
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) where
  edge : Edge401 q hq
  endpoint : g ∈ edge.1
  centerNonzero : checkBlock q g y ≠ 0
  localNonzero :
    wordLinearMapTranspose localParityCheck (checkBlock q g y)
      (edgeLocalCoordinate q hq40 hq edge g endpoint) ≠ 0
  otherZero : ∀ w : Vertex401 q, w ∈ edge.1 → w ≠ g →
    checkBlock q w y = 0
def dualExposedVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) : Finset (Vertex401 q) := by
  classical
  exact Finset.univ.filter fun g =>
    Nonempty (DualExposureWitness q hq40 hq y g)
end QEC.Coding.BalancedProduct.LPSTanner


