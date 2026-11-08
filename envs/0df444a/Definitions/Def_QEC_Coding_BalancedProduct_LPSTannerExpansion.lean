-- Prove2me | Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
-- name    : QEC_Coding_BalancedProduct_LPSTannerExpansion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:28:11.422024+00:00
-- url     : https://prove2.me/theorems/0a2484b8-847e-413e-9259-859e79f6b10f
-- title:
--   LPSTanner Expansion
-- statement:
--   Definitions and structural lemmas for LPSTanner Expansion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSTannerExpansion.lean

import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_checkBlock_basis_same
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_incidentAsEdge_edgeAsIncident
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
attribute [local simp] QEC.Coding.BalancedProduct.LPSTanner.checkBlock_basis_same
attribute [local simp] QEC.Coding.BalancedProduct.LPSTanner.incidentAsEdge_edgeAsIncident
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
namespace QEC.Coding.BalancedProduct.LPSTannerExpansion
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open LPSTanner LPSGraph GVPlus
def wordSupportGraph
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) : SimpleGraph (Vertex401 q) where
  Adj g w := ∃ e : Edge401 q hq, e.1 = s(g, w) ∧ x e ≠ 0
  symm := by
    constructor
    rintro g w ⟨e, he, hx⟩
    refine ⟨e, ?_, hx⟩
    simpa only [Sym2.eq_swap] using he
  loopless := ⟨by
    rintro g ⟨e, he, _hx⟩
    have hadj : (lpsCayleyGraph401 q hq).Adj g g := by
      rw [← SimpleGraph.mem_edgeSet]
      simpa [he] using e.2
    exact (lpsCayleyGraph401 q hq).loopless.irrefl g hadj⟩
theorem wordSupportGraph_le_lps
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    wordSupportGraph q hq x ≤ lpsCayleyGraph401 q hq := by
  intro g w hgw
  rcases hgw with ⟨e, he, _hx⟩
  rw [← SimpleGraph.mem_edgeSet]
  simpa [he] using e.2
theorem mem_wordSupportGraph_edgeSet_iff
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (a : Sym2 (Vertex401 q)) :
    a ∈ (wordSupportGraph q hq x).edgeSet ↔
      ∃ e : Edge401 q hq, e.1 = a ∧ x e ≠ 0 := by
  refine Sym2.inductionOn a ?_
  intro g w
  rw [SimpleGraph.mem_edgeSet]
  rfl
def supportEdgeEquiv
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (wordSupportGraph q hq x).edgeSet ≃
      {e : Edge401 q hq // x e ≠ 0} where
  toFun e := by
    let a : Edge401 q hq :=
      ⟨e.1, SimpleGraph.edgeSet_mono (wordSupportGraph_le_lps q hq x) e.2⟩
    refine ⟨a, ?_⟩
    rcases (mem_wordSupportGraph_edgeSet_iff q hq x e.1).1 e.2 with
      ⟨b, hb, hxb⟩
    have hba : b = a := by
      apply Subtype.ext
      exact hb
    simpa [hba] using hxb
  invFun e := by
    refine ⟨e.1.1, ?_⟩
    exact (mem_wordSupportGraph_edgeSet_iff q hq x e.1.1).2
      ⟨e.1, rfl, e.2⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
def localSupportEquivNeighborSet
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q) :
    {a : LocalCoordinate // localView q hq40 hq g x a ≠ 0} ≃
      (wordSupportGraph q hq x).neighborSet g := by
  let G := lpsCayleyGraph401 q hq
  let Λ := incidentCoordinateEquiv q hq40 hq g
  let E : LocalCoordinate ≃ G.neighborSet g :=
    Λ.symm.trans (G.incidenceSetEquivNeighborSet g)
  have hpred (a : LocalCoordinate) :
      localView q hq40 hq g x a ≠ 0 ↔
        (wordSupportGraph q hq x).Adj g (E a).1 := by
    let i := Λ.symm a
    have hi : i.1 = s(g, (G.incidenceSetEquivNeighborSet g i).1) := by
      have h := (G.incidenceSetEquivNeighborSet g).symm_apply_apply i
      exact (congrArg Subtype.val h).symm
    constructor
    · intro hx
      refine ⟨incidentAsEdge q hq i, hi, ?_⟩
      exact hx
    · rintro ⟨e, he, hxe⟩
      have hei : e = incidentAsEdge q hq i := by
        apply Subtype.ext
        exact he.trans hi.symm
      simpa [localView, E, i, Λ, hei] using hxe
  let e₁ :
      {a : LocalCoordinate // localView q hq40 hq g x a ≠ 0} ≃
        {w : G.neighborSet g //
          (wordSupportGraph q hq x).Adj g w.1} :=
    E.subtypeEquiv hpred
  let e₂ :
      {w : G.neighborSet g // (wordSupportGraph q hq x).Adj g w.1} ≃
        (wordSupportGraph q hq x).neighborSet g :=
    { toFun := fun w => ⟨w.1.1, w.2⟩
      invFun := fun w =>
        ⟨⟨w.1, (wordSupportGraph_le_lps q hq x) w.2⟩, w.2⟩
      left_inv := fun w => by ext; rfl
      right_inv := fun w => by ext; rfl }
  exact e₁.trans e₂
def primalSupportVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) : Finset (Vertex401 q) :=
  Finset.univ.filter fun g => localView q hq40 hq g x ≠ 0
def primalHeavyVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) : Finset (Vertex401 q) :=
  (primalSupportVertices q hq40 hq x).filter fun g =>
    41 ≤ HammingWeight (localView q hq40 hq g x)
def dualSupportVertices
    (q : ℕ) [Fact q.Prime]
    (y : Word (ZMod 2) (Check401 q)) : Finset (Vertex401 q) :=
  Finset.univ.filter fun g => checkBlock q g y ≠ 0
def localCoordinateNeighborEquiv
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : Vertex401 q) :
    LocalCoordinate ≃ (lpsCayleyGraph401 q hq).neighborSet g :=
  (incidentCoordinateEquiv q hq40 hq g).symm.trans
    ((lpsCayleyGraph401 q hq).incidenceSetEquivNeighborSet g)
def dualSupportedNeighbors
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) : Finset (Vertex401 q) :=
  let E := localCoordinateNeighborEquiv q hq40 hq g
  let emb : LocalCoordinate ↪ Vertex401 q :=
    E.toEmbedding.trans (Function.Embedding.subtype _)
  (hammingSupport
    (wordLinearMapTranspose localParityCheck (checkBlock q g y))).map emb
def dualUnexposedSupportVertices
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (y : Word (ZMod 2) (Check401 q)) : Finset (Vertex401 q) :=
  dualSupportVertices q y \ dualExposedVertices q hq40 hq y
end QEC.Coding.BalancedProduct.LPSTannerExpansion


