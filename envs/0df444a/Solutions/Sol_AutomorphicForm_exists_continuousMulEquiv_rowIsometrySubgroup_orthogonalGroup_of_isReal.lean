-- Prove2me | solution 1 for AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3ae318fe-75ea-57eb-ba85-ff0e32fd10b4

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix
open scoped ComplexConjugate

namespace R4RowIsoUnitaryR

section RCLikeCore

variable {𝕜 : Type*} [RCLike 𝕜]

theorem norm_add_sq_rclike (u v : 𝕜) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * RCLike.re (conj u * v) + ‖v‖ ^ 2 := by
  have h := @norm_add_sq 𝕜 𝕜 _ _ _ u v
  rwa [RCLike.inner_apply'] at h

theorem im_eq_zero_of_I_eq_zero (hI : (RCLike.I : 𝕜) = 0) (z : 𝕜) : RCLike.im z = 0 := by
  have h := RCLike.mul_im_I_ax z
  rw [hI, map_zero, mul_zero] at h
  exact h.symm

theorem rows_orthonormal_of_isRowIsometry {k : GL (Fin 2) 𝕜} (hk : IsRowIsometry k) :
    ‖(k : Matrix (Fin 2) (Fin 2) 𝕜) 0 0‖ ^ 2 + ‖(k : Matrix (Fin 2) (Fin 2) 𝕜) 0 1‖ ^ 2 = 1 ∧
    ‖(k : Matrix (Fin 2) (Fin 2) 𝕜) 1 0‖ ^ 2 + ‖(k : Matrix (Fin 2) (Fin 2) 𝕜) 1 1‖ ^ 2 = 1 ∧
    conj ((k : Matrix (Fin 2) (Fin 2) 𝕜) 0 0) * (k : Matrix (Fin 2) (Fin 2) 𝕜) 1 0
      + conj ((k : Matrix (Fin 2) (Fin 2) 𝕜) 0 1) * (k : Matrix (Fin 2) (Fin 2) 𝕜) 1 1 = 0 := by
  obtain ⟨-, hiso⟩ := hk
  set a := (k : Matrix (Fin 2) (Fin 2) 𝕜) 0 0 with ha
  set b := (k : Matrix (Fin 2) (Fin 2) 𝕜) 0 1 with hb
  set c := (k : Matrix (Fin 2) (Fin 2) 𝕜) 1 0 with hc
  set d := (k : Matrix (Fin 2) (Fin 2) 𝕜) 1 1 with hd
  have E1 : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    have h := hiso 1 0
    simpa using h
  have E2 : ‖c‖ ^ 2 + ‖d‖ ^ 2 = 1 := by
    have h := hiso 0 1
    simpa using h
  have E3 : ‖a + c‖ ^ 2 + ‖b + d‖ ^ 2 = 2 := by
    have h := hiso 1 1
    simp only [one_mul, norm_one, one_pow] at h
    linarith
  have E4 : ‖a + RCLike.I * c‖ ^ 2 + ‖b + RCLike.I * d‖ ^ 2 = 1 + ‖(RCLike.I : 𝕜)‖ ^ 2 := by
    have h := hiso 1 RCLike.I
    simpa using h
  set Q : 𝕜 := conj a * c + conj b * d with hQ
  have hre : RCLike.re Q = 0 := by
    rw [norm_add_sq_rclike, norm_add_sq_rclike] at E3
    have : RCLike.re (conj a * c) + RCLike.re (conj b * d) = 0 := by linarith
    rw [hQ, map_add]
    exact this
  have him : RCLike.im Q = 0 := by
    rw [norm_add_sq_rclike, norm_add_sq_rclike] at E4
    have h1 : RCLike.re (conj a * (RCLike.I * c)) = -RCLike.im (conj a * c) := by
      rw [← mul_assoc, mul_comm (conj a) RCLike.I, mul_assoc, RCLike.I_mul_re]
    have h2 : RCLike.re (conj b * (RCLike.I * d)) = -RCLike.im (conj b * d) := by
      rw [← mul_assoc, mul_comm (conj b) RCLike.I, mul_assoc, RCLike.I_mul_re]
    rw [h1, h2, norm_mul, norm_mul, mul_pow, mul_pow] at E4
    have hI : ‖(RCLike.I : 𝕜)‖ ^ 2 * (‖c‖ ^ 2 + ‖d‖ ^ 2) = ‖(RCLike.I : 𝕜)‖ ^ 2 := by
      rw [E2, mul_one]
    have : RCLike.im (conj a * c) + RCLike.im (conj b * d) = 0 := by nlinarith [hI, E1, E4]
    rw [hQ, map_add]
    exact this
  have hQ0 : Q = 0 := by
    apply RCLike.ext
    · rw [hre, map_zero]
    · rw [him, map_zero]
  exact ⟨E1, E2, hQ0⟩

theorem mem_unitaryGroup_of_isRowIsometry {k : GL (Fin 2) 𝕜} (hk : IsRowIsometry k) :
    (k : Matrix (Fin 2) (Fin 2) 𝕜) ∈ Matrix.unitaryGroup (Fin 2) 𝕜 := by
  obtain ⟨E1, E2, hQ⟩ := rows_orthonormal_of_isRowIsometry hk
  set A := (k : Matrix (Fin 2) (Fin 2) 𝕜) with hA
  have E1' : A 0 0 * conj (A 0 0) + A 0 1 * conj (A 0 1) = 1 := by
    rw [RCLike.mul_conj, RCLike.mul_conj]
    exact_mod_cast E1
  have E2' : A 1 0 * conj (A 1 0) + A 1 1 * conj (A 1 1) = 1 := by
    rw [RCLike.mul_conj, RCLike.mul_conj]
    exact_mod_cast E2
  have hQ' : A 0 0 * conj (A 1 0) + A 0 1 * conj (A 1 1) = 0 := by
    have h := congrArg conj hQ
    simpa [map_add, map_mul, mul_comm] using h
  have hQ'' : A 1 0 * conj (A 0 0) + A 1 1 * conj (A 0 1) = 0 := by
    rw [mul_comm (A 1 0), mul_comm (A 1 1)]
    exact hQ
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, E1', E2', hQ', hQ'']

theorem isRowIsometry_of_mem_unitaryGroup {k : GL (Fin 2) 𝕜}
    (hk : (k : Matrix (Fin 2) (Fin 2) 𝕜) ∈ Matrix.unitaryGroup (Fin 2) 𝕜) : IsRowIsometry k := by
  set A := (k : Matrix (Fin 2) (Fin 2) 𝕜) with hA
  have hmul : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hk
  have hent : ∀ i j : Fin 2, (A * star A) i j = (1 : Matrix (Fin 2) (Fin 2) 𝕜) i j := fun i j => by
    rw [hmul]
  have h00 := hent 0 0
  have h01 := hent 0 1
  have h11 := hent 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h00 h01 h11

  have hstar : ∀ z : 𝕜, star z = conj z := fun z => rfl
  simp only [hstar] at h00 h01 h11
  have E1 : ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 = 1 := by
    rw [RCLike.mul_conj, RCLike.mul_conj] at h00
    exact_mod_cast h00
  have E2 : ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 = 1 := by
    rw [RCLike.mul_conj, RCLike.mul_conj] at h11
    exact_mod_cast h11
  have hQ : conj (A 0 0) * A 1 0 + conj (A 0 1) * A 1 1 = 0 := by
    have h := congrArg conj h01
    simpa [map_add, map_mul, mul_comm] using h
  refine ⟨?_, fun x y => ?_⟩
  ·
    have hdet : A.det * conj A.det = 1 := by
      have h := congrArg Matrix.det hmul
      rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at h
      exact h
    rw [RCLike.mul_conj] at hdet
    have h2 : ‖A.det‖ ^ 2 = 1 := by exact_mod_cast hdet
    have h3 : 0 ≤ ‖A.det‖ := norm_nonneg _
    nlinarith [h2, h3]
  · rw [norm_add_sq_rclike, norm_add_sq_rclike]
    have hcross : RCLike.re (conj (x * A 0 0) * (y * A 1 0)) + RCLike.re (conj (x * A 0 1) * (y * A 1 1))
        = 0 := by
      rw [← map_add]
      have : conj (x * A 0 0) * (y * A 1 0) + conj (x * A 0 1) * (y * A 1 1)
          = conj x * y * (conj (A 0 0) * A 1 0 + conj (A 0 1) * A 1 1) := by
        simp only [map_mul]; ring
      rw [this, hQ, mul_zero, map_zero]
    simp only [norm_mul, mul_pow]
    nlinarith [hcross, E1, E2, sq_nonneg ‖x‖, sq_nonneg ‖y‖]

theorem isRowIsometry_iff_mem_unitaryGroup (k : GL (Fin 2) 𝕜) :
    IsRowIsometry k ↔ (k : Matrix (Fin 2) (Fin 2) 𝕜) ∈ Matrix.unitaryGroup (Fin 2) 𝕜 :=
  ⟨mem_unitaryGroup_of_isRowIsometry, isRowIsometry_of_mem_unitaryGroup⟩

theorem isRowIsometry_toUnits (A : ↥(Matrix.unitaryGroup (Fin 2) 𝕜)) :
    IsRowIsometry (Unitary.toUnits A : GL (Fin 2) 𝕜) :=
  isRowIsometry_of_mem_unitaryGroup (k := (Unitary.toUnits A : GL (Fin 2) 𝕜)) A.2

def unitaryMulEquiv : ↥(rowIsometrySubgroup 𝕜) ≃* ↥(Matrix.unitaryGroup (Fin 2) 𝕜) where
  toFun k := ⟨((k : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜), mem_unitaryGroup_of_isRowIsometry k.2⟩
  invFun A := ⟨Unitary.toUnits A, isRowIsometry_toUnits A⟩
  left_inv k := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    rfl
  map_mul' k k' := by
    apply Subtype.ext
    rfl

theorem unitaryMulEquiv_apply_coe (k : ↥(rowIsometrySubgroup 𝕜)) :
    ((unitaryMulEquiv k : ↥(Matrix.unitaryGroup (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜)
      = ((k : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) := rfl

theorem continuous_unitaryMulEquiv : Continuous (unitaryMulEquiv (𝕜 := 𝕜)) := by
  apply Continuous.subtype_mk
  exact Units.continuous_val.comp continuous_subtype_val

theorem continuous_unitaryMulEquiv_symm : Continuous (unitaryMulEquiv (𝕜 := 𝕜)).symm := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact continuous_subtype_val
  · show Continuous fun A : ↥(Matrix.unitaryGroup (Fin 2) 𝕜) => (star (A : Matrix (Fin 2) (Fin 2) 𝕜))
    exact continuous_star.comp continuous_subtype_val

def unitaryEquiv : ↥(rowIsometrySubgroup 𝕜) ≃ₜ* ↥(Matrix.unitaryGroup (Fin 2) 𝕜) :=
  { unitaryMulEquiv with
    continuous_toFun := continuous_unitaryMulEquiv
    continuous_invFun := continuous_unitaryMulEquiv_symm }

theorem unitaryEquiv_apply_coe (k : ↥(rowIsometrySubgroup 𝕜)) :
    ((unitaryEquiv k : ↥(Matrix.unitaryGroup (Fin 2) 𝕜)) : Matrix (Fin 2) (Fin 2) 𝕜)
      = ((k : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) := rfl

end RCLikeCore

section Transport

variable {K L : Type*} [NormedField K] [NormedField L]

theorem isRowIsometry_glEquivOfRingEquiv (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) : IsRowIsometry (glEquivOfRingEquiv e k) := by
  obtain ⟨hd, hiso⟩ := hk
  refine ⟨?_, fun x y => ?_⟩
  · change ‖(RingEquiv.mapMatrix (m := Fin 2) e (k : Matrix (Fin 2) (Fin 2) K)).det‖ = 1
    rw [← RingEquiv.map_det, he, hd]
  · have hes : ∀ z : L, ‖e.symm z‖ = ‖z‖ := fun z => by rw [← he (e.symm z), e.apply_symm_apply]
    have hent : ∀ i j, ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        = e ((k : Matrix (Fin 2) (Fin 2) K) i j) := fun i j => rfl
    simp only [hent]
    calc ‖x * e ((k : Matrix (Fin 2) (Fin 2) K) 0 0) + y * e ((k : Matrix (Fin 2) (Fin 2) K) 1 0)‖ ^ 2
          + ‖x * e ((k : Matrix (Fin 2) (Fin 2) K) 0 1) + y * e ((k : Matrix (Fin 2) (Fin 2) K) 1 1)‖ ^ 2
        = ‖e (e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 0)‖ ^ 2
          + ‖e (e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 1)‖ ^ 2 := by
          simp only [map_add, map_mul, e.apply_symm_apply]
      _ = ‖e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
          + ‖e.symm x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + e.symm y * (k : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2 := by
          rw [he, he]
      _ = ‖e.symm x‖ ^ 2 + ‖e.symm y‖ ^ 2 := hiso (e.symm x) (e.symm y)
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by rw [hes, hes]

theorem norm_symm_of_norm (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) (z : L) : ‖e.symm z‖ = ‖z‖ := by
  rw [← he (e.symm z), e.apply_symm_apply]

theorem glEquivOfRingEquiv_symm_apply (e : K ≃+* L) (k : GL (Fin 2) K) :
    glEquivOfRingEquiv e.symm (glEquivOfRingEquiv e k) = k := by
  apply Units.ext
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, e.symm_apply_apply]

theorem glEquivOfRingEquiv_apply_symm (e : K ≃+* L) (k : GL (Fin 2) L) :
    glEquivOfRingEquiv e (glEquivOfRingEquiv e.symm k) = k := by
  apply Units.ext
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, e.apply_symm_apply]

theorem continuous_glEquivOfRingEquiv (e : K ≃+* L) (hc : Continuous e) :
    Continuous (glEquivOfRingEquiv e) := by
  have h : Continuous ((RingEquiv.mapMatrix (m := Fin 2) e).toMulEquiv.toMonoidHom) := by
    show Continuous fun M : Matrix (Fin 2) (Fin 2) K => M.map e
    exact continuous_id.matrix_map hc
  exact Continuous.units_map _ h

def rowIsoMulEquiv (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) :
    ↥(rowIsometrySubgroup K) ≃* ↥(rowIsometrySubgroup L) where
  toFun k := ⟨glEquivOfRingEquiv e k, isRowIsometry_glEquivOfRingEquiv e he k.2⟩
  invFun k := ⟨glEquivOfRingEquiv e.symm k, isRowIsometry_glEquivOfRingEquiv e.symm (norm_symm_of_norm e he) k.2⟩
  left_inv k := Subtype.ext (glEquivOfRingEquiv_symm_apply e k)
  right_inv k := Subtype.ext (glEquivOfRingEquiv_apply_symm e k)
  map_mul' k k' := Subtype.ext (map_mul (glEquivOfRingEquiv e) (k : GL (Fin 2) K) (k' : GL (Fin 2) K))

def rowIsoEquiv (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) (hc : Continuous e) (hcs : Continuous e.symm) :
    ↥(rowIsometrySubgroup K) ≃ₜ* ↥(rowIsometrySubgroup L) :=
  { rowIsoMulEquiv e he with
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (continuous_glEquivOfRingEquiv e hc).comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact (continuous_glEquivOfRingEquiv e.symm hcs).comp continuous_subtype_val }

theorem rowIsoEquiv_apply_entry (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) (hc : Continuous e)
    (hcs : Continuous e.symm) (k : ↥(rowIsometrySubgroup K)) (i j : Fin 2) :
    (((rowIsoEquiv e he hc hcs k : ↥(rowIsometrySubgroup L)) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
      = e (((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j) := rfl

end Transport

section Places

variable {F : Type} [Field F]

theorem continuous_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) :
    Continuous (ringEquivRealOfIsReal hw) :=
  (isometryEquivRealOfIsReal hw).continuous

theorem continuous_ringEquivRealOfIsReal_symm {w : InfinitePlace F} (hw : w.IsReal) :
    Continuous (ringEquivRealOfIsReal hw).symm :=
  (isometryEquivRealOfIsReal hw).symm.continuous

def realEquiv {w : InfinitePlace F} (hw : w.IsReal) :
    ↥(rowIsometrySubgroup w.Completion) ≃ₜ* ↥(Matrix.orthogonalGroup (Fin 2) ℝ) :=
  (rowIsoEquiv (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (continuous_ringEquivRealOfIsReal hw) (continuous_ringEquivRealOfIsReal_symm hw)).trans
    (unitaryEquiv (𝕜 := ℝ))

theorem realEquiv_apply_entry {w : InfinitePlace F} (hw : w.IsReal)
    (k : ↥(rowIsometrySubgroup w.Completion)) (i j : Fin 2) :
    ((realEquiv hw k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = extensionEmbeddingOfIsReal hw (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) :=
  rfl

end Places

end R4RowIsoUnitaryR

end

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem solution
    (F : Type) [Field F] (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ e : ↥(rowIsometrySubgroup w.Completion) ≃ₜ* ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
      ∀ (k : ↥(rowIsometrySubgroup w.Completion)) (i j : Fin 2),
        ((e k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j
          = extensionEmbeddingOfIsReal hw
              (((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) :=
  ⟨R4RowIsoUnitaryR.realEquiv hw, R4RowIsoUnitaryR.realEquiv_apply_entry hw⟩

end S_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal
end P2MW
export P2MW.S_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_orthogonalGroup_of_isReal (solution)
