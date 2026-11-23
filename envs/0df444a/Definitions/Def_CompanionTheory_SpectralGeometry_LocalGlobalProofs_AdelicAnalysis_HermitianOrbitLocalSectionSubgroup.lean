-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroup
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:12.4148+00:00
-- url     : https://prove2.me/theorems/c7bf527b-d6e8-4b9a-8ed2-d823cdf5ba8e
-- title:
--   Hermitian Orbit Local Section Subgroup
-- statement:
--   Definitions and structural lemmas for Hermitian Orbit Local Section Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOrbitLocalSectionSubgroup.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotentStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHermitianDiagonalizationUnitsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero


set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Tri
variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}
theorem tri_mul_diag {A B : Matrix (Fin n) (Fin n) K} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp
def triSub (ι : R →+* K) (U : Subgroup Rˣ) (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {x | (x : Matrix (Fin n) (Fin n) K).BlockTriangular id ∧
    ∀ i, ∃ u ∈ U, (x : Matrix (Fin n) (Fin n) K) i i = ι (u : Rˣ)}
  one_mem' := by
    refine ⟨?_, fun i => ⟨1, U.one_mem, by simp⟩⟩
    simpa using Matrix.blockTriangular_one (b := (id : Fin n → Fin n))
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simpa using ha.mul hb, fun i => ?_⟩
    obtain ⟨u, hu, e⟩ := ha' i
    obtain ⟨v, hv, f⟩ := hb' i
    refine ⟨u * v, U.mul_mem hu hv, ?_⟩
    rw [Units.val_mul, tri_mul_diag ha hb, e, f]
    simp
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    have hinv : ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = (x : Matrix (Fin n) (Fin n) K)⁻¹ := Matrix.coe_units_inv x
    have ht : ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
      rw [hinv]
      let : Invertible (x : Matrix (Fin n) (Fin n) K) := x.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular hx
    refine ⟨ht, fun i => ?_⟩
    obtain ⟨u, hu, e⟩ := hx' i
    refine ⟨u⁻¹, U.inv_mem hu, ?_⟩
    have h1 : (x : Matrix (Fin n) (Fin n) K) i i * ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = 1 := by
      rw [← tri_mul_diag hx ht, ← Units.val_mul, mul_inv_cancel]
      simp
    rw [e] at h1
    have h2 : ι ((u⁻¹ : Rˣ) : R) * ι (u : Rˣ) = 1 := by
      rw [← map_mul]; simp
    calc _ = ι ((u⁻¹ : Rˣ) : R) * ι (u : Rˣ) * ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i := by
          rw [h2, one_mul]
      _ = ι ((u⁻¹ : Rˣ) : R) := by rw [mul_assoc, h1, mul_one]
def nMat (m : {p : Fin n × Fin n // p.1 < p.2} → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if i = j then 1 else if h : i < j then m ⟨(i, j), h⟩ else 0
theorem nMat_tri (m : {p : Fin n × Fin n // p.1 < p.2} → K) : (nMat m).BlockTriangular id := by
  intro i j h
  have h' : j < i := h
  simp [nMat, h'.ne', h'.not_gt]
theorem nMat_det (m : {p : Fin n × Fin n // p.1 < p.2} → K) : (nMat m).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (nMat_tri m)]
  simp [nMat]
def aMat (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U) (m : {p : Fin n × Fin n // p.1 < p.2} → K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal (fun i => ι ((u i : Rˣ) : R)) * nMat m
theorem aMat_apply (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) (i j : Fin n) :
    aMat ι u m i j = ι ((u i : Rˣ) : R) * nMat m i j := by
  simp [aMat, Matrix.diagonal_mul]
theorem aMat_tri (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) : (aMat ι u m).BlockTriangular id := by
  intro i j h
  rw [aMat_apply, nMat_tri m h, mul_zero]
theorem aMat_det (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) :
    (aMat ι u m).det = ι ((∏ i, (u i : Rˣ) : Rˣ) : R) := by
  simp [aMat, Matrix.det_mul, nMat_det, Matrix.det_diagonal, map_prod]
def cInv (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U) : K :=
  ι (((∏ i, (u i : Rˣ) : Rˣ)⁻¹ : Rˣ) : R)
theorem cInv_mul (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) : cInv ι u * (aMat ι u m).det = 1 := by
  rw [aMat_det, cInv, ← map_mul, Units.inv_mul, map_one]
def aGL (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) : GL (Fin n) K where
  val := aMat ι u m
  inv := cInv ι u • (aMat ι u m).adjugate
  val_inv := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, cInv_mul, one_smul]
  inv_val := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, cInv_mul, one_smul]
theorem aGL_mem (ι : R →+* K) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) : aGL ι u m ∈ triSub ι U n := by
  refine ⟨aMat_tri ι u m, fun i => ⟨u i, (u i).2, ?_⟩⟩
  show aMat ι u m i i = _
  rw [aMat_apply]
  simp [nMat]
def uOf (ι : R →+* K) {U : Subgroup Rˣ} (x : triSub ι U n) (i : Fin n) : U :=
  ⟨(x.2.2 i).choose, (x.2.2 i).choose_spec.1⟩
theorem uOf_spec (ι : R →+* K) {U : Subgroup Rˣ} (x : triSub ι U n) (i : Fin n) :
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = ι ((uOf ι x i : Rˣ) : R) :=
  (x.2.2 i).choose_spec.2
def mOf (ι : R →+* K) {U : Subgroup Rˣ} (x : triSub ι U n) :
    {p : Fin n × Fin n // p.1 < p.2} → K :=
  fun p => ι (((uOf ι x p.1.1 : Rˣ)⁻¹ : Rˣ) : R) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.1.1 p.1.2
theorem unit_cancel (ι : R →+* K) (u : Rˣ) (a : K) : ι ((u⁻¹ : Rˣ) : R) * (ι (u : R) * a) = a := by
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
theorem unit_cancel' (ι : R →+* K) (u : Rˣ) (a : K) : ι (u : R) * (ι ((u⁻¹ : Rˣ) : R) * a) = a := by
  rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
theorem aGL_coords (ι : R →+* K) {U : Subgroup Rˣ} (x : triSub ι U n) :
    aGL ι (uOf ι x) (mOf ι x) = (x : GL (Fin n) K) := by
  apply Units.ext
  ext i j
  show aMat ι (uOf ι x) (mOf ι x) i j = _
  rw [aMat_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp only [nMat, Matrix.of_apply, h.ne, if_false, h, dif_pos, mOf]
    exact unit_cancel' ι _ _
  · subst h
    simp [nMat, uOf_spec]
  · have : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := x.2.1 h
    rw [this]
    simp [nMat, h.ne', h.not_gt]
theorem coords_aGL (ι : R →+* K) (hι : Function.Injective ι) {U : Subgroup Rˣ} (u : Fin n → U)
    (m : {p : Fin n × Fin n // p.1 < p.2} → K) :
    uOf ι ⟨aGL ι u m, aGL_mem ι u m⟩ = u ∧ mOf ι ⟨aGL ι u m, aGL_mem ι u m⟩ = m := by
  have h1 : uOf ι ⟨aGL ι u m, aGL_mem ι u m⟩ = u := by
    funext i
    apply Subtype.ext
    apply Units.ext
    apply hι
    rw [← uOf_spec]
    show aMat ι u m i i = _
    rw [aMat_apply]
    simp [nMat]
  refine ⟨h1, ?_⟩
  funext p
  obtain ⟨⟨i, j⟩, h⟩ := p
  have h' : i < j := h
  simp only [mOf, h1]
  show _ * aMat ι u m i j = _
  rw [aMat_apply]
  simp only [nMat, Matrix.of_apply, h'.ne, if_false, h', dif_pos]
  exact unit_cancel ι _ _
section Top
variable [TopologicalSpace R] [TopologicalSpace K] [IsTopologicalRing R] [IsTopologicalRing K]
theorem nMat_cont : Continuous (nMat : ({p : Fin n × Fin n // p.1 < p.2} → K) → _) := by
  refine continuous_matrix fun i j => ?_
  simp only [nMat, Matrix.of_apply]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _
  · exact continuous_const
theorem aMat_cont (ι : R →+* K) (hι : Continuous ι) (U : Subgroup Rˣ) :
    Continuous fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) => aMat ι p.1 p.2 := by
  refine Continuous.matrix_mul (Continuous.matrix_diagonal ?_) (nMat_cont.comp continuous_snd)
  refine continuous_pi fun i => hι.comp (Units.continuous_val.comp ?_)
  exact continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
theorem aGL_cont (ι : R →+* K) (hι : Continuous ι) (U : Subgroup Rˣ) :
    Continuous fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) => aGL ι p.1 p.2 := by
  refine Units.continuous_iff.2 ⟨aMat_cont ι hι U, ?_⟩
  have hc : Continuous fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) => cInv ι p.1 := by
    refine hι.comp (Units.continuous_val.comp (Continuous.inv ?_))
    refine continuous_finsetProd _ fun i _ => ?_
    exact continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)
  exact hc.smul (aMat_cont ι hι U).matrix_adjugate
theorem entry_cont (ι : R →+* K) (U : Subgroup Rˣ) (i j : Fin n) :
    Continuous fun x : triSub ι U n => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j :=
  (continuous_id.matrix_elem i j).comp (Units.continuous_val.comp continuous_subtype_val)
theorem uOf_cont (ι : R →+* K) (π : K → R) (hπ : Continuous π) (hπι : ∀ r, π (ι r) = r)
    (hv : IsInducing (Units.val : Rˣ → R)) (U : Subgroup Rˣ) (i : Fin n) :
    Continuous fun x : triSub ι U n => (uOf ι x i : Rˣ) := by
  refine hv.continuous_iff.2 ?_
  have : (Units.val ∘ fun x : triSub ι U n => (uOf ι x i : Rˣ))
      = fun x : triSub ι U n => π (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i) := by
    funext x
    simp [uOf_spec, hπι]
  rw [this]
  exact hπ.comp (entry_cont ι U i i)
def triHomeo (ι : R →+* K) (hι : Continuous ι) (π : K → R) (hπ : Continuous π)
    (hπι : ∀ r, π (ι r) = r) (hv : IsInducing (Units.val : Rˣ → R)) (U : Subgroup Rˣ) :
    ((Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K)) ≃ₜ triSub ι U n where
  toFun p := ⟨aGL ι p.1 p.2, aGL_mem ι p.1 p.2⟩
  invFun x := (uOf ι x, mOf ι x)
  left_inv p := by
    have hinj : Function.Injective ι := Function.LeftInverse.injective hπι
    exact Prod.ext (coords_aGL ι hinj p.1 p.2).1 (coords_aGL ι hinj p.1 p.2).2
  right_inv x := Subtype.ext (aGL_coords ι x)
  continuous_toFun := (aGL_cont ι hι U).subtype_mk _
  continuous_invFun := by
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)
    · exact (uOf_cont ι π hπ hπι hv U i).subtype_mk _
    · refine Continuous.mul ?_ (entry_cont ι U _ _)
      exact hι.comp (Units.continuous_val.comp (uOf_cont ι π hπ hπι hv U p.1.1).inv)
end Top
end GlobalTheory.CompanionTheory.SW.Tri
namespace GlobalTheory.CompanionTheory.SW
open GlobalTheory.CompanionTheory.SW.Tri
end GlobalTheory.CompanionTheory.SW


