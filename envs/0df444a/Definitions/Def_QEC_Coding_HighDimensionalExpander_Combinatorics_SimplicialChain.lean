-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
-- name    : QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:59:20.450955+00:00
-- url     : https://prove2.me/theorems/a4bb717f-d068-436e-8a0d-00dd9924ed6b
-- title:
--   Simplicial Chain
-- statement:
--   Definitions and structural lemmas for Simplicial Chain, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/SimplicialChain.lean

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Finset.Interval
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
namespace QEC.Coding.HighDimensionalExpander.SimplicialChain
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
structure Face (K : AbstractSimplicialComplex V) (p : Nat) where
  vertices : Finset V
  mem_complex : vertices ∈ K
  card_vertices : vertices.card = p
namespace Face
variable {K : AbstractSimplicialComplex V} {p : Nat}
instance : DecidableEq (Face K p) := fun σ τ =>
  decidable_of_iff (σ.vertices = τ.vertices) ⟨by
    intro h
    cases σ
    cases τ
    cases h
    rfl, congrArg vertices⟩
noncomputable instance : Fintype (Face K p) :=
  Fintype.ofInjective vertices (by
    intro σ τ h
    cases σ
    cases τ
    cases h
    rfl)
end Face
variable (K : AbstractSimplicialComplex V)
def boundaryMatrix (p : Nat) :
    Matrix (Face K p) (Face K (p + 1)) (ZMod 2) :=
  fun σ τ => if σ.vertices ⊂ τ.vertices then 1 else 0
noncomputable def intermediateFaces
    (p : Nat) (σ : Face K p) (υ : Face K (p + 2)) :
    Finset (Face K (p + 1)) :=
  Finset.univ.filter fun τ =>
    σ.vertices ⊂ τ.vertices ∧ τ.vertices ⊂ υ.vertices
def intermediateFaceEquiv
    (p : Nat) (σ : Face K p) (υ : Face K (p + 2)) :
    {τ : Face K (p + 1) //
      σ.vertices ⊂ τ.vertices ∧ τ.vertices ⊂ υ.vertices} ≃
      {s : Finset V // s ∈ Finset.Ioo σ.vertices υ.vertices} where
  toFun τ := ⟨τ.1.vertices, Finset.mem_Ioo.mpr τ.2⟩
  invFun s := by
    have hs := Finset.mem_Ioo.mp s.2
    have hσs : σ.vertices ⊂ s.1 := hs.1
    have hsυ : s.1 ⊂ υ.vertices := hs.2
    have hCardLower : σ.vertices.card < s.1.card :=
      Finset.card_lt_card hσs
    have hCardUpper : s.1.card < υ.vertices.card :=
      Finset.card_lt_card hsυ
    have hCard : s.1.card = p + 1 := by
      rw [σ.card_vertices] at hCardLower
      rw [υ.card_vertices] at hCardUpper
      omega
    have hNonempty : s.1.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      have : s.1.card = 0 := by simp [hEmpty]
      omega
    exact ⟨⟨s.1,
      (K.isRelLowerSet_faces υ.mem_complex).2 hsυ.1 hNonempty,
      hCard⟩, hσs, hsυ⟩
  left_inv τ := by
    apply Subtype.ext
    cases τ with
    | mk τ _ =>
        cases τ
        rfl
  right_inv s := by
    apply Subtype.ext
    rfl
theorem card_intermediateFaces_of_ssubset
    (p : Nat) (σ : Face K p) (υ : Face K (p + 2))
    (hσυ : σ.vertices ⊂ υ.vertices) :
    (intermediateFaces K p σ υ).card = 2 := by
  have hCardEquiv := Fintype.card_congr
    (intermediateFaceEquiv K p σ υ)
  have hDifference : υ.vertices.card - σ.vertices.card = 2 := by
    rw [σ.card_vertices, υ.card_vertices]
    omega
  rw [Fintype.card_subtype, Fintype.card_coe] at hCardEquiv
  rw [Finset.card_Ioo_finset hσυ.1, hDifference] at hCardEquiv
  norm_num at hCardEquiv ⊢
  simpa [intermediateFaces] using hCardEquiv
theorem boundaryMatrix_mul_boundaryMatrix (p : Nat) :
    boundaryMatrix K p * boundaryMatrix K (p + 1) = 0 := by
  ext σ υ
  rw [Matrix.mul_apply]
  change (∑ τ,
    boundaryMatrix K p σ τ * boundaryMatrix K (p + 1) τ υ) =
      (0 : ZMod 2)
  by_cases hσυ : σ.vertices ⊂ υ.vertices
  · have hSum :
        (∑ τ,
          boundaryMatrix K p σ τ * boundaryMatrix K (p + 1) τ υ) =
          ∑ _τ ∈ intermediateFaces K p σ υ, (1 : ZMod 2) := by
      unfold intermediateFaces
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hστ : σ.vertices ⊂ τ.vertices <;>
        by_cases hτυ : τ.vertices ⊂ υ.vertices <;>
        simp [boundaryMatrix, hστ, hτυ]
    rw [hSum]
    have hCard := card_intermediateFaces_of_ssubset K p σ υ hσυ
    simp only [Finset.sum_const, hCard]
    simpa only [two_nsmul] using (ZModModule.add_self (1 : ZMod 2))
  · apply Finset.sum_eq_zero
    intro τ hτ
    simp only [boundaryMatrix]
    by_cases hστ : σ.vertices ⊂ τ.vertices
    · have hNotτυ : ¬τ.vertices ⊂ υ.vertices := by
        intro hτυ
        exact hσυ (hστ.trans hτυ)
      simp [hστ, hNotτυ]
    · simp [hστ]
noncomputable def boundary (p : Nat) :
    Word (ZMod 2) (Face K (p + 1)) →ₗ[ZMod 2]
      Word (ZMod 2) (Face K p) :=
  Matrix.toLin' (boundaryMatrix K p)
theorem boundary_squared (p : Nat) :
    (boundary K p).comp (boundary K (p + 1)) = 0 := by
  change (Matrix.toLin' (boundaryMatrix K p)).comp
    (Matrix.toLin' (boundaryMatrix K (p + 1))) = 0
  rw [← Matrix.toLin'_mul]
  rw [boundaryMatrix_mul_boundaryMatrix]
  simp
noncomputable def chainComplexAt (p : Nat) :
    ChainComplexData (ZMod 2)
      (Word (ZMod 2) (Face K p))
      (Word (ZMod 2) (Face K (p + 1)))
      (Word (ZMod 2) (Face K (p + 2))) where
  boundary1 := boundary K p
  boundary2 := boundary K (p + 1)
  boundary_squared := boundary_squared K p
def SystoleAtLeast (p d : Nat) : Prop :=
  ∀ z : Word (ZMod 2) (Face K (p + 1)),
    boundary K p z = 0 →
    (¬ ∃ y : Word (ZMod 2) (Face K (p + 2)),
      boundary K (p + 1) y = z) →
    d ≤ HammingWeight z
def CosystoleAtLeast (p d : Nat) : Prop :=
  ∀ x : Word (ZMod 2) (Face K (p + 1)),
    wordLinearMapTranspose (boundary K (p + 1)) x = 0 →
    (¬ ∃ y : Word (ZMod 2) (Face K p),
      wordLinearMapTranspose (boundary K p) y = x) →
    d ≤ HammingWeight x
noncomputable def facets
    (p : Nat) (τ : Face K (p + 1)) : Finset (Face K p) :=
  Finset.univ.filter fun σ => σ.vertices ⊂ τ.vertices
noncomputable def cofaces
    (p : Nat) (σ : Face K p) : Finset (Face K (p + 1)) :=
  Finset.univ.filter fun τ => σ.vertices ⊂ τ.vertices
def facetEquiv
    (p : Nat) (hp : 1 ≤ p) (τ : Face K (p + 1)) :
    {σ : Face K p // σ.vertices ⊂ τ.vertices} ≃
      {s : Finset V // s ∈ τ.vertices.powersetCard p} where
  toFun σ := ⟨σ.1.vertices,
    Finset.mem_powersetCard.mpr ⟨σ.2.1, σ.1.card_vertices⟩⟩
  invFun s := by
    have hs := Finset.mem_powersetCard.mp s.2
    have hNonempty : s.1.Nonempty := by
      apply Finset.card_pos.mp
      rw [hs.2]
      omega
    have hNe : s.1 ≠ τ.vertices := by
      intro hEq
      have hCardEq := congrArg Finset.card hEq
      rw [hs.2, τ.card_vertices] at hCardEq
      omega
    exact ⟨⟨s.1,
      (K.isRelLowerSet_faces τ.mem_complex).2 hs.1 hNonempty,
      hs.2⟩,
      Finset.ssubset_iff_subset_ne.mpr ⟨hs.1, hNe⟩⟩
  left_inv σ := by
    apply Subtype.ext
    cases σ with
    | mk σ _ =>
        cases σ
        rfl
  right_inv s := by
    apply Subtype.ext
    rfl
end QEC.Coding.HighDimensionalExpander.SimplicialChain


