-- Prove2me | solution 1 for AutomorphicForm.integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/861c0e5e-61a3-52f7-9c94-70ec5d7084cb

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_MeasureTheory_Measure_exists_haar_eq_smul_map_mul_prod_of_homeomorph
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace P2mAffineChart

section Algebra

variable {F : Type*} [Field F]

def Xmat (ϖ : F) : Matrix (Fin 2) (Fin 2) F := !![0, 1; ϖ, 0]

def torusMat (ϖ p r : F) : Matrix (Fin 2) (Fin 2) F := !![p, r; ϖ * r, p]

theorem det_torusMat (ϖ p r : F) : (torusMat ϖ p r).det = p ^ 2 - ϖ * r ^ 2 := by
  simp [torusMat, Matrix.det_fin_two]; ring

def sMat (α β : F) : Matrix (Fin 2) (Fin 2) F := !![1, 0; α, β]

theorem det_sMat (α β : F) : (sMat α β).det = β := by
  simp [sMat, Matrix.det_fin_two]

def sGL (α : F) (β : Fˣ) : GL (Fin 2) F where
  val := sMat α β
  inv := !![1, 0; -α * (β⁻¹ : Fˣ), (β⁻¹ : Fˣ)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sMat, Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_comm α, ← mul_assoc, mul_inv_cancel₀ β.ne_zero, one_mul, add_neg_cancel]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sMat, Matrix.mul_apply, Fin.sum_univ_two]
    try rw [mul_comm ((β : F)⁻¹) α, neg_add_cancel]

@[scoped simp] theorem sGL_coe (α : F) (β : Fˣ) : ((sGL α β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = sMat α β := rfl

theorem sGL_mul (α α' : F) (β β' : Fˣ) : sGL α β * sGL α' β' = sGL (α + β * α') (β * β') := by
  apply Units.ext
  simp only [Units.val_mul, sGL_coe, sMat, Units.val_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sGL_zero_one : sGL (0 : F) 1 = 1 := by
  apply Units.ext
  simp only [sGL_coe, sMat, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

def torusGL (ϖ p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) : GL (Fin 2) F where
  val := torusMat ϖ p r
  inv := !![p / (p ^ 2 - ϖ * r ^ 2), -r / (p ^ 2 - ϖ * r ^ 2);
    -(ϖ * r) / (p ^ 2 - ϖ * r ^ 2), p / (p ^ 2 - ϖ * r ^ 2)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [torusMat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [torusMat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

@[scoped simp] theorem torusGL_coe (ϖ p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) :
    ((torusGL ϖ p r h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = torusMat ϖ p r := rfl

theorem torusGL_inv_coe (ϖ p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) :
    (((torusGL ϖ p r h)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![p / (p ^ 2 - ϖ * r ^ 2), -r / (p ^ 2 - ϖ * r ^ 2);
        -(ϖ * r) / (p ^ 2 - ϖ * r ^ 2), p / (p ^ 2 - ϖ * r ^ 2)] := rfl

theorem sGL_inv_coe (α : F) (β : Fˣ) :
    (((sGL α β)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; -α * (β⁻¹ : Fˣ), (β⁻¹ : Fˣ)] := rfl

def XGL (ϖ : F) (hϖ : ϖ ≠ 0) : GL (Fin 2) F := torusGL ϖ 0 1 (by simpa using hϖ)

theorem XGL_coe (ϖ : F) (hϖ : ϖ ≠ 0) : ((XGL ϖ hϖ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Xmat ϖ := by
  rw [XGL, torusGL_coe]; ext i j; fin_cases i <;> fin_cases j <;> simp [torusMat, Xmat]

theorem commute_Xmat_iff (ϖ : F) (M : Matrix (Fin 2) (Fin 2) F) :
    M * Xmat ϖ = Xmat ϖ * M ↔ M 1 1 = M 0 0 ∧ M 1 0 = ϖ * M 0 1 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [Xmat, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    exact ⟨h01.symm, by rw [← h00, mul_comm]⟩
  · rintro ⟨h1, h2⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Xmat, Matrix.mul_apply, Fin.sum_univ_two, h1, h2, mul_comm]

theorem eq_torusMat_of_commute {ϖ : F} {M : Matrix (Fin 2) (Fin 2) F} (h : M * Xmat ϖ = Xmat ϖ * M) :
    M = torusMat ϖ (M 0 0) (M 0 1) := by
  obtain ⟨h1, h2⟩ := (commute_Xmat_iff ϖ M).1 h
  ext i j; fin_cases i <;> fin_cases j <;> simp [torusMat, h1, h2]

theorem torusMat_commute (ϖ p r : F) : torusMat ϖ p r * Xmat ϖ = Xmat ϖ * torusMat ϖ p r := by
  rw [commute_Xmat_iff]; simp [torusMat]

theorem mem_centralizer_XGL_iff (ϖ : F) (hϖ : ϖ ≠ 0) (g : GL (Fin 2) F) :
    g ∈ Subgroup.centralizer ({XGL ϖ hϖ} : Set (GL (Fin 2) F)) ↔
      (g : Matrix (Fin 2) (Fin 2) F) * Xmat ϖ = Xmat ϖ * g := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Units.val_mul, XGL_coe] using this
  · intro h
    apply Units.ext
    simp only [Units.val_mul, XGL_coe]
    exact h

theorem sGL_mem_centralizer_iff (ϖ : F) (hϖ : ϖ ≠ 0) (α : F) (β : Fˣ) :
    sGL α β ∈ Subgroup.centralizer ({XGL ϖ hϖ} : Set (GL (Fin 2) F)) ↔ α = 0 ∧ β = 1 := by
  rw [mem_centralizer_XGL_iff, sGL_coe, commute_Xmat_iff]
  simp only [sMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, Units.ext (by simpa using h1)⟩
    simpa using h2
  · rintro ⟨rfl, rfl⟩; simp

end Algebra

section Decomposition

variable {F : Type*} [Field F]

def Ssub : Subgroup (GL (Fin 2) F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg0, hg1⟩ ⟨hh0, hh1⟩
    refine ⟨?_, ?_⟩
    · simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, hh0]
    · simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, hh1]
  inv_mem' := by
    rintro g ⟨hg0, hg1⟩
    have h := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel g)
    simp only [Units.val_mul, Units.val_one] at h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, one_mul, zero_mul, add_zero, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h00 h01
    exact ⟨h00, h01⟩

theorem mem_Ssub_iff (g : GL (Fin 2) F) :
    g ∈ (Ssub : Subgroup (GL (Fin 2) F)) ↔
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := Iff.rfl

theorem sGL_mem_Ssub (α : F) (β : Fˣ) : sGL α β ∈ (Ssub : Subgroup (GL (Fin 2) F)) := by
  rw [mem_Ssub_iff]; simp [sMat]

def unit11 (g : (Ssub : Subgroup (GL (Fin 2) F))) : Fˣ where
  val := ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1
  inv := (((g : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1
  val_inv := by
    have hginv : ((g : GL (Fin 2) F)⁻¹) ∈ (Ssub : Subgroup (GL (Fin 2) F)) := Ssub.inv_mem g.2
    have h := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel (g : GL (Fin 2) F))
    simp only [Units.val_mul, Units.val_one] at h
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hginv.2, mul_zero, zero_add, Matrix.one_apply_eq] at h11
    exact h11
  inv_val := by
    have hginv : ((g : GL (Fin 2) F)⁻¹) ∈ (Ssub : Subgroup (GL (Fin 2) F)) := Ssub.inv_mem g.2
    have h := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) (mul_inv_cancel (g : GL (Fin 2) F))
    simp only [Units.val_mul, Units.val_one] at h
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hginv.2, mul_zero, zero_add, Matrix.one_apply_eq] at h11
    rw [mul_comm]; exact h11

@[scoped simp] theorem unit11_coe (g : (Ssub : Subgroup (GL (Fin 2) F))) :
    ((unit11 g : Fˣ) : F) = ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 := rfl

theorem sGL_unit11 (g : (Ssub : Subgroup (GL (Fin 2) F))) :
    sGL (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0) (unit11 g) = (g : GL (Fin 2) F) := by
  apply Units.ext
  obtain ⟨h0, h1⟩ := g.2
  ext i j; fin_cases i <;> fin_cases j <;> simp [sMat, h0, h1]

def sEquiv : Fˣ × F ≃ (Ssub : Subgroup (GL (Fin 2) F)) where
  toFun q := ⟨sGL q.2 q.1, sGL_mem_Ssub q.2 q.1⟩
  invFun g := (unit11 g, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0)
  left_inv q := by
    obtain ⟨β, α⟩ := q
    refine Prod.ext (Units.ext ?_) ?_ <;> simp [sMat]
  right_inv g := Subtype.ext (sGL_unit11 g)

variable (ϖ : F) (hϖ : ϖ ≠ 0) (hns : ∀ p r : F, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0)

include hns in
theorem sq_sub_ne_zero {p r : F} (h : ¬ (p = 0 ∧ r = 0)) : p ^ 2 - ϖ * r ^ 2 ≠ 0 := by
  intro h0
  have hr := hns p r h0
  rw [hr] at h0
  have hp : p = 0 := by simpa using h0
  exact h ⟨hp, hr⟩

abbrev Tsub : Subgroup (GL (Fin 2) F) := Subgroup.centralizer ({XGL ϖ hϖ} : Set (GL (Fin 2) F))

theorem torusGL_mem_Tsub (p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) : torusGL ϖ p r h ∈ Tsub ϖ hϖ := by
  rw [Tsub, mem_centralizer_XGL_iff, torusGL_coe]; exact torusMat_commute ϖ p r

theorem eq_one_of_mem_Tsub_of_mem_Ssub {g : GL (Fin 2) F} (hT : g ∈ Tsub ϖ hϖ)
    (hS : g ∈ (Ssub : Subgroup (GL (Fin 2) F))) : g = 1 := by
  rw [Tsub, mem_centralizer_XGL_iff, commute_Xmat_iff] at hT
  obtain ⟨h1, h2⟩ := hT
  obtain ⟨h0, h01⟩ := hS
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j
  · simpa using h0
  · simpa using h01
  · simp [h2, h01]
  · simp [h1, h0]

def colNorm (g : GL (Fin 2) F) : F :=
  ((g : Matrix (Fin 2) (Fin 2) F) 1 1) ^ 2 - ϖ * ((g : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2

include hns in
theorem colNorm_ne_zero (g : GL (Fin 2) F) : colNorm ϖ g ≠ 0 := by
  refine sq_sub_ne_zero ϖ hns (fun ⟨h1, h2⟩ => ?_)
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
  apply hdet
  rw [Matrix.det_fin_two, h1, h2]; ring

theorem det_coe_ne_zero (g : GL (Fin 2) F) : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero

def tp (g : GL (Fin 2) F) : F := (g : Matrix (Fin 2) (Fin 2) F) 1 1 * (g : Matrix (Fin 2) (Fin 2) F).det / colNorm ϖ g

def tr' (g : GL (Fin 2) F) : F := (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F).det / colNorm ϖ g

include hns in
theorem tp_sq_sub_eq (g : GL (Fin 2) F) :
    tp ϖ g ^ 2 - ϖ * tr' ϖ g ^ 2 = (g : Matrix (Fin 2) (Fin 2) F).det ^ 2 / colNorm ϖ g := by
  have hN := colNorm_ne_zero ϖ hns g
  simp only [tp, tr', colNorm] at hN ⊢
  field_simp

include hns in
theorem tp_sq_sub_ne_zero (g : GL (Fin 2) F) : tp ϖ g ^ 2 - ϖ * tr' ϖ g ^ 2 ≠ 0 := by
  rw [tp_sq_sub_eq ϖ hns]
  exact div_ne_zero (pow_ne_zero _ (det_coe_ne_zero g)) (colNorm_ne_zero ϖ hns g)

theorem torusGL_inv_mul_apply_00 (p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) (M : Matrix (Fin 2) (Fin 2) F) :
    ((((torusGL ϖ p r h)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * M) 0 0 =
      (p * M 0 0 - r * M 1 0) / (p ^ 2 - ϖ * r ^ 2) := by
  rw [torusGL_inv_coe]; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem torusGL_inv_mul_apply_01 (p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) (M : Matrix (Fin 2) (Fin 2) F) :
    ((((torusGL ϖ p r h)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * M) 0 1 =
      (p * M 0 1 - r * M 1 1) / (p ^ 2 - ϖ * r ^ 2) := by
  rw [torusGL_inv_coe]; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

def tpart (g : GL (Fin 2) F) : GL (Fin 2) F := torusGL ϖ (tp ϖ g) (tr' ϖ g) (tp_sq_sub_ne_zero ϖ hns g)

def spart (g : GL (Fin 2) F) : GL (Fin 2) F := (tpart ϖ hns g)⁻¹ * g

theorem tpart_mul_spart (g : GL (Fin 2) F) : tpart ϖ hns g * spart ϖ hns g = g := by
  rw [spart, mul_inv_cancel_left]

theorem tpart_mem (g : GL (Fin 2) F) : tpart ϖ hns g ∈ Tsub ϖ hϖ := torusGL_mem_Tsub ϖ hϖ _ _ _

theorem spart_mem (g : GL (Fin 2) F) : spart ϖ hns g ∈ (Ssub : Subgroup (GL (Fin 2) F)) := by
  have hN := colNorm_ne_zero ϖ hns g
  have hd := det_coe_ne_zero g
  have hD := tp_sq_sub_ne_zero ϖ hns g
  have hDeq := tp_sq_sub_eq ϖ hns g
  rw [mem_Ssub_iff, spart, Units.val_mul, tpart, torusGL_inv_mul_apply_00, torusGL_inv_mul_apply_01, hDeq]
  constructor
  · rw [div_eq_one_iff_eq (by rwa [← hDeq])]
    simp only [tp, tr', colNorm] at hN ⊢
    rw [Matrix.det_fin_two]
    field_simp
  · rw [div_eq_zero_iff]
    left
    simp only [tp, tr']
    ring

theorem tpart_spart_unique {g t s : GL (Fin 2) F} (ht : t ∈ Tsub ϖ hϖ) (hs : s ∈ (Ssub : Subgroup (GL (Fin 2) F)))
    (h : t * s = g) : t = tpart ϖ hns g ∧ s = spart ϖ hns g := by
  have h1 : (tpart ϖ hns g)⁻¹ * t = spart ϖ hns g * s⁻¹ := by
    rw [spart, ← h]; group
  have hT : (tpart ϖ hns g)⁻¹ * t ∈ Tsub ϖ hϖ := Subgroup.mul_mem _ (Subgroup.inv_mem _ (tpart_mem ϖ hϖ hns g)) ht
  have hS : (tpart ϖ hns g)⁻¹ * t ∈ (Ssub : Subgroup (GL (Fin 2) F)) := by
    rw [h1]; exact Subgroup.mul_mem _ (spart_mem ϖ hns g) (Subgroup.inv_mem _ hs)
  have hone := eq_one_of_mem_Tsub_of_mem_Ssub ϖ hϖ hT hS
  have ht' : t = tpart ϖ hns g := by
    calc t = tpart ϖ hns g * ((tpart ϖ hns g)⁻¹ * t) := by group
      _ = tpart ϖ hns g := by rw [hone, mul_one]
  refine ⟨ht', ?_⟩
  rw [hone] at h1
  calc s = (spart ϖ hns g * s⁻¹)⁻¹ * spart ϖ hns g := by group
    _ = spart ϖ hns g := by rw [← h1, inv_one, one_mul]

theorem tpart_mul (t g : GL (Fin 2) F) (ht : t ∈ Tsub ϖ hϖ) : tpart ϖ hns (t * g) = t * tpart ϖ hns g := by
  have := tpart_spart_unique ϖ hϖ hns (g := t * g) (Subgroup.mul_mem _ ht (tpart_mem ϖ hϖ hns g))
    (spart_mem ϖ hns g) (by rw [mul_assoc, tpart_mul_spart])
  exact this.1.symm

theorem spart_mul (t g : GL (Fin 2) F) (ht : t ∈ Tsub ϖ hϖ) : spart ϖ hns (t * g) = spart ϖ hns g := by
  have := tpart_spart_unique ϖ hϖ hns (g := t * g) (Subgroup.mul_mem _ ht (tpart_mem ϖ hϖ hns g))
    (spart_mem ϖ hns g) (by rw [mul_assoc, tpart_mul_spart])
  exact this.2.symm

theorem tpart_of_mem (t s : GL (Fin 2) F) (ht : t ∈ Tsub ϖ hϖ) (hs : s ∈ (Ssub : Subgroup (GL (Fin 2) F))) :
    tpart ϖ hns (t * s) = t :=
  (tpart_spart_unique ϖ hϖ hns ht hs rfl).1.symm

theorem spart_of_mem (t s : GL (Fin 2) F) (ht : t ∈ Tsub ϖ hϖ) (hs : s ∈ (Ssub : Subgroup (GL (Fin 2) F))) :
    spart ϖ hns (t * s) = s :=
  (tpart_spart_unique ϖ hϖ hns ht hs rfl).2.symm

def prodEquiv : (Tsub ϖ hϖ) × (Ssub : Subgroup (GL (Fin 2) F)) ≃ GL (Fin 2) F where
  toFun p := (p.1 : GL (Fin 2) F) * (p.2 : GL (Fin 2) F)
  invFun g := (⟨tpart ϖ hns g, tpart_mem ϖ hϖ hns g⟩, ⟨spart ϖ hns g, spart_mem ϖ hns g⟩)
  left_inv p := by
    obtain ⟨t, s⟩ := p
    ext1
    · exact Subtype.ext (tpart_of_mem ϖ hϖ hns t s t.2 s.2)
    · exact Subtype.ext (spart_of_mem ϖ hϖ hns t s t.2 s.2)
  right_inv g := tpart_mul_spart ϖ hns g

end Decomposition

section TopologyPart

variable {F : Type*} [NormedField F]

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → GL (Fin 2) F}
    (hval : ∀ i j, Continuous fun x => ((f x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

theorem continuous_entry (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_det : Continuous fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F).det :=
  Units.continuous_val.matrix_det

theorem continuous_sGL : Continuous fun q : Fˣ × F => sGL q.2 q.1 := by
  have hb : Continuous fun q : Fˣ × F => ((q.1 : Fˣ) : F) := Units.continuous_val.comp continuous_fst
  have hbi : Continuous fun q : Fˣ × F => (((q.1⁻¹ : Fˣ) : Fˣ) : F) := Units.continuous_val.comp continuous_fst.inv
  have ha : Continuous fun q : Fˣ × F => q.2 := continuous_snd
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact ha
    · exact hb
  · simp only [sGL_inv_coe]
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact (ha.neg).mul hbi
    · exact hbi

variable (ϖ : F) (hϖ : ϖ ≠ 0) (hns : ∀ p r : F, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0)

theorem continuous_colNorm : Continuous fun g : GL (Fin 2) F => colNorm ϖ g :=
  ((continuous_entry 1 1).pow 2).sub (continuous_const.mul ((continuous_entry 0 1).pow 2))

include hns in
theorem continuous_tp : Continuous fun g : GL (Fin 2) F => tp ϖ g :=
  ((continuous_entry 1 1).mul continuous_det).div (continuous_colNorm ϖ) (colNorm_ne_zero ϖ hns)

include hns in
theorem continuous_tr' : Continuous fun g : GL (Fin 2) F => tr' ϖ g :=
  ((continuous_entry 0 1).mul continuous_det).div (continuous_colNorm ϖ) (colNorm_ne_zero ϖ hns)

theorem continuous_tpart : Continuous fun g : GL (Fin 2) F => tpart ϖ hns g := by
  have hp := continuous_tp ϖ hns
  have hr := continuous_tr' ϖ hns
  have hD : Continuous fun g : GL (Fin 2) F => tp ϖ g ^ 2 - ϖ * tr' ϖ g ^ 2 :=
    (hp.pow 2).sub (continuous_const.mul (hr.pow 2))
  have hD0 := tp_sq_sub_ne_zero ϖ hns
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · simp only [tpart, torusGL_coe]
    fin_cases i <;> fin_cases j
    · exact hp
    · exact hr
    · exact continuous_const.mul hr
    · exact hp
  · simp only [tpart, torusGL_inv_coe]
    fin_cases i <;> fin_cases j
    · exact hp.div hD hD0
    · exact hr.neg.div hD hD0
    · exact (continuous_const.mul hr).neg.div hD hD0
    · exact hp.div hD hD0

theorem continuous_spart : Continuous fun g : GL (Fin 2) F => spart ϖ hns g :=
  (continuous_tpart ϖ hns).inv.mul continuous_id

def prodHomeo : (Tsub ϖ hϖ) × (Ssub : Subgroup (GL (Fin 2) F)) ≃ₜ GL (Fin 2) F where
  toEquiv := prodEquiv ϖ hϖ hns
  continuous_toFun := by
    change Continuous fun p : (Tsub ϖ hϖ) × (Ssub : Subgroup (GL (Fin 2) F)) =>
      (p.1 : GL (Fin 2) F) * (p.2 : GL (Fin 2) F)
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    change Continuous fun g : GL (Fin 2) F =>
      ((⟨tpart ϖ hns g, tpart_mem ϖ hϖ hns g⟩ : Tsub ϖ hϖ),
        (⟨spart ϖ hns g, spart_mem ϖ hns g⟩ : (Ssub : Subgroup (GL (Fin 2) F))))
    exact ((continuous_tpart ϖ hns).subtype_mk _).prodMk ((continuous_spart ϖ hns).subtype_mk _)

theorem prodHomeo_apply (p : (Tsub ϖ hϖ) × (Ssub : Subgroup (GL (Fin 2) F))) :
    prodHomeo ϖ hϖ hns p = (p.1 : GL (Fin 2) F) * (p.2 : GL (Fin 2) F) := rfl

def sHomeo : Fˣ × F ≃ₜ (Ssub : Subgroup (GL (Fin 2) F)) where
  toEquiv := sEquiv
  continuous_toFun := by
    change Continuous fun q : Fˣ × F => (⟨sGL q.2 q.1, sGL_mem_Ssub q.2 q.1⟩ : (Ssub : Subgroup (GL (Fin 2) F)))
    exact continuous_sGL.subtype_mk _
  continuous_invFun := by
    change Continuous fun g : (Ssub : Subgroup (GL (Fin 2) F)) =>
      (unit11 g, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0)
    refine Continuous.prodMk ?_ ((continuous_entry 1 0).comp continuous_subtype_val)
    rw [Units.continuous_iff]
    constructor
    · exact (continuous_entry 1 1).comp continuous_subtype_val
    · change Continuous fun g : (Ssub : Subgroup (GL (Fin 2) F)) =>
        (((g : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1
      exact (continuous_entry 1 1).comp (continuous_subtype_val.inv)

theorem sHomeo_apply (β : Fˣ) (α : F) : ((sHomeo (β, α) : (Ssub : Subgroup (GL (Fin 2) F))) : GL (Fin 2) F) = sGL α β :=
  rfl

end TopologyPart

section Elements

variable {F : Type*} [Field F]

theorem coe_scalar (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  change Matrix.scalar (Fin 2) (c : F) = _
  rw [Matrix.scalar_apply]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem coe_scalar_mul (c : Fˣ) (g : GL (Fin 2) F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.one_mul]

theorem scalar_mul_comm (c : Fˣ) (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  rw [coe_scalar_mul, Units.val_mul, coe_scalar, Matrix.mul_smul, Matrix.mul_one]

theorem torusMat_eq_smul_add (ϖ p r : F) : torusMat ϖ p r = p • (1 : Matrix (Fin 2) (Fin 2) F) + r • Xmat ϖ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torusMat, Xmat, mul_comm]

variable (ϖ : F) (hϖ : ϖ ≠ 0) (hns : ∀ p r : F, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0)

def gammaPR (c : Fˣ) (p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) c * torusGL ϖ p r h

theorem coe_gammaPR (c : Fˣ) (p r : F) (h : p ^ 2 - ϖ * r ^ 2 ≠ 0) :
    ((gammaPR ϖ c p r h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (c : F) • torusMat ϖ p r := by
  rw [gammaPR, coe_scalar_mul, torusGL_coe]

theorem mem_centralizer_gammaPR_iff (c : Fˣ) {p r : F} (hD : p ^ 2 - ϖ * r ^ 2 ≠ 0) (hr : r ≠ 0)
    (g : GL (Fin 2) F) :
    g ∈ Subgroup.centralizer ({gammaPR ϖ c p r hD} : Set (GL (Fin 2) F)) ↔ g ∈ Tsub ϖ hϖ := by
  rw [Tsub, mem_centralizer_XGL_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hm := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) h
    simp only [Units.val_mul, coe_gammaPR, Matrix.smul_mul, Matrix.mul_smul, torusMat_eq_smul_add, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at hm
    have hm' := smul_right_injective (Matrix (Fin 2) (Fin 2) F) c.ne_zero hm
    have hm'' : r • ((g : Matrix (Fin 2) (Fin 2) F) * Xmat ϖ) = r • (Xmat ϖ * (g : Matrix (Fin 2) (Fin 2) F)) := by
      have := hm'
      rw [add_right_inj] at this
      exact this
    exact smul_right_injective (Matrix (Fin 2) (Fin 2) F) hr hm''
  · intro h
    apply Units.ext
    simp only [Units.val_mul, coe_gammaPR, Matrix.smul_mul, Matrix.mul_smul, torusMat_eq_smul_add, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, h]

theorem sGL_inv_Xmat_sGL (α : F) (β : Fˣ) :
    (((sGL α β)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Xmat ϖ * sMat α β =
      !![α, (β : F); (ϖ - α ^ 2) / β, -α] := by
  rw [sGL_inv_coe]
  have hb : (β : F) ≠ 0 := β.ne_zero
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Xmat, sMat, Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;> field_simp <;> ring

theorem coe_conj_gammaPR (c : Fˣ) {p r : F} (hD : p ^ 2 - ϖ * r ^ 2 ≠ 0) (α : F) (β : Fˣ) :
    (((sGL α β)⁻¹ * gammaPR ϖ c p r hD * sGL α β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (p • (1 : Matrix (Fin 2) (Fin 2) F) + r • !![α, (β : F); (ϖ - α ^ 2) / β, -α]) := by
  rw [Units.val_mul, Units.val_mul, coe_gammaPR, torusMat_eq_smul_add, ← sGL_inv_Xmat_sGL ϖ α β, sGL_coe]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, smul_add]
  congr 1
  have : (((sGL α β)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * sMat α (β : F) = 1 := by
    rw [← sGL_coe α β, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [this]

end Elements

theorem isClosed_localIntegralSet' (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed (AutomorphicForm.localIntegralSet K v) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : T2Space (GL (Fin 2) (v.adicCompletion K)) := Units.isEmbedding_embedProduct.t2Space
  exact (AutomorphicForm.isCompact_localIntegralSet K v).isClosed

section Measures

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

theorem t2Space_GL : T2Space (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_units : SecondCountableTopology (v.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  secondCountableTopology_units
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar
  AutomorphicForm.localCentralizerBorel

theorem borelSpace_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    @BorelSpace (localCentralizer K v γ) _ (localCentralizerBorel K v γ) :=
  @BorelSpace.mk _ _ (localCentralizerBorel K v γ) rfl

theorem isClosed_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    IsClosed ((localCentralizer K v γ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
      Set (GL (Fin 2) (v.adicCompletion K))) :=
  Set.isClosed_centralizer _

theorem locallyCompactSpace_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    LocallyCompactSpace (localCentralizer K v γ) :=
  (isClosed_localCentralizer K v γ).isClosedEmbedding_subtypeVal.locallyCompactSpace

attribute [local instance] borelSpace_localCentralizer locallyCompactSpace_localCentralizer

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (μF : Measure (v.adicCompletion K)) [μF.IsAddHaarMeasure]
  (μU : Measure (v.adicCompletion K)ˣ) [μU.IsHaarMeasure]

def nuS : Measure (Ssub : Subgroup (GL (Fin 2) (v.adicCompletion K))) :=
  Measure.map (sHomeo : (v.adicCompletion K)ˣ × v.adicCompletion K ≃ₜ _) (μU.prod μF)

theorem nuS_apply (A : Set (Ssub : Subgroup (GL (Fin 2) (v.adicCompletion K)))) :
    nuS K v μF μU A = (μU.prod μF) ((sHomeo : (v.adicCompletion K)ˣ × v.adicCompletion K ≃ₜ _) ⁻¹' A) := by
  rw [nuS, ← Homeomorph.toMeasurableEquiv_coe, MeasurableEquiv.map_apply]

scoped instance sFinite_nuS : SFinite (nuS K v μF μU) := by unfold nuS; infer_instance

scoped instance isFiniteMeasureOnCompacts_nuS : IsFiniteMeasureOnCompacts (nuS K v μF μU) := ⟨fun A hA => by
  rw [nuS_apply, ← Homeomorph.image_symm]
  exact (hA.image (sHomeo).symm.continuous).measure_lt_top⟩

scoped instance isOpenPosMeasure_nuS : (nuS K v μF μU).IsOpenPosMeasure := ⟨fun U hU hne => by
  rw [nuS_apply, ← Homeomorph.image_symm]
  exact (((sHomeo).symm.isOpenMap U hU).measure_pos (μU.prod μF) (hne.image _)).ne'⟩

theorem sHomeo_mul (q q₀ : (v.adicCompletion K)ˣ × v.adicCompletion K) :
    (sHomeo q : (Ssub : Subgroup (GL (Fin 2) (v.adicCompletion K)))) * sHomeo q₀ =
      sHomeo (q.1 * q₀.1, q.2 + (q.1 : v.adicCompletion K) * q₀.2) := by
  apply Subtype.ext
  change sGL q.2 q.1 * sGL q₀.2 q₀.1 = sGL (q.2 + (q.1 : v.adicCompletion K) * q₀.2) (q.1 * q₀.1)
  rw [sGL_mul]

scoped instance isMulRightInvariant_nuS : (nuS K v μF μU).IsMulRightInvariant := by
  refine ⟨fun s₀ => ?_⟩
  set q₀ := (sHomeo).symm s₀ with hq₀
  have hs₀ : s₀ = sHomeo q₀ := ((sHomeo).apply_symm_apply s₀).symm
  set R : (v.adicCompletion K)ˣ × v.adicCompletion K → (v.adicCompletion K)ˣ × v.adicCompletion K :=
    fun q => (q.1 * q₀.1, q.2 + (q.1 : v.adicCompletion K) * q₀.2) with hR
  have hRmp : MeasurePreserving R (μU.prod μF) (μU.prod μF) := by
    refine (measurePreserving_mul_right μU q₀.1).skew_product (g := fun b a => a + (b : v.adicCompletion K) * q₀.2)
      ?_ (Filter.Eventually.of_forall fun b => (measurePreserving_add_right μF _).map_eq)
    exact (measurable_snd.add ((Units.continuous_val.measurable.comp measurable_fst).mul_const _))
  have hcomp : (fun s : (Ssub : Subgroup (GL (Fin 2) (v.adicCompletion K))) => s * s₀) ∘
      (sHomeo : (v.adicCompletion K)ˣ × v.adicCompletion K ≃ₜ _) = sHomeo ∘ R := by
    funext q; simp only [Function.comp_apply, hs₀, sHomeo_mul, hR]
  rw [nuS, Measure.map_map (measurable_mul_const s₀) (sHomeo).continuous.measurable, hcomp,
    ← Measure.map_map (sHomeo).continuous.measurable hRmp.measurable, hRmp.map_eq]

variable (ϖ : v.adicCompletion K) (hϖ : ϖ ≠ 0)
  (hns : ∀ p r : v.adicCompletion K, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0)

theorem exists_unfold (hright : (localHaar K v).IsMulRightInvariant)
    (τ : Measure (Tsub ϖ hϖ)) [τ.IsHaarMeasure] :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ ψ : GL (Fin 2) (v.adicCompletion K) → ℂ,
      ∫ g, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (tpart ϖ hns g) * ψ (spart ϖ hns g) ∂(localHaar K v) =
        (κ.toReal : ℂ) * (τ.real (((↑) : Tsub ϖ hϖ → GL (Fin 2) (v.adicCompletion K)) ⁻¹' localIntegralSet K v) : ℂ) *
          ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K, ψ (sGL q.2 q.1) ∂(μU.prod μF) := by
  haveI := hright
  haveI : SecondCountableTopology (Tsub ϖ hϖ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (Ssub : Subgroup (GL (Fin 2) (v.adicCompletion K))) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace ((Tsub ϖ hϖ) × (Ssub : Subgroup (GL (Fin 2) (v.adicCompletion K)))) := Prod.borelSpace
  obtain ⟨κ, hκ0, hκtop, hμ⟩ := MeasureTheory.Measure.exists_haar_eq_smul_map_mul_prod_of_homeomorph
    (Tsub ϖ hϖ) Ssub (prodHomeo ϖ hϖ hns) (prodHomeo_apply ϖ hϖ hns) (localHaar K v) τ (nuS K v μF μU)
  refine ⟨κ, hκ0, hκtop, fun ψ => ?_⟩
  set Φ : GL (Fin 2) (v.adicCompletion K) → ℂ :=
    fun g => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (tpart ϖ hns g) * ψ (spart ϖ hns g) with hΦ
  have hΦe : ∀ p : (Tsub ϖ hϖ) × (Ssub : Subgroup (GL (Fin 2) (v.adicCompletion K))),
      Φ (prodHomeo ϖ hϖ hns p) =
        ((((↑) : Tsub ϖ hϖ → GL (Fin 2) (v.adicCompletion K)) ⁻¹' localIntegralSet K v).indicator
          (fun _ => (1 : ℂ)) p.1) * ψ (p.2 : GL (Fin 2) (v.adicCompletion K)) := by
    rintro ⟨t, s⟩
    simp only [hΦ, prodHomeo_apply, tpart_of_mem ϖ hϖ hns _ _ t.2 s.2, spart_of_mem ϖ hϖ hns _ _ t.2 s.2]
    rfl
  calc ∫ g, Φ g ∂(localHaar K v)
      = ∫ g, Φ g ∂(κ • Measure.map (prodHomeo ϖ hϖ hns) (τ.prod (nuS K v μF μU))) := by rw [← hμ]
    _ = (κ.toReal : ℂ) * ∫ p, Φ (prodHomeo ϖ hϖ hns p) ∂(τ.prod (nuS K v μF μU)) := by
        rw [integral_smul_measure, (prodHomeo ϖ hϖ hns).measurableEmbedding.integral_map, Complex.real_smul]
    _ = (κ.toReal : ℂ) * ((∫ t, ((((↑) : Tsub ϖ hϖ → GL (Fin 2) (v.adicCompletion K)) ⁻¹' localIntegralSet K v).indicator
          (fun _ => (1 : ℂ)) t) ∂τ) * ∫ s, ψ (s : GL (Fin 2) (v.adicCompletion K)) ∂(nuS K v μF μU)) := by
        congr 1
        rw [← integral_prod_mul]
        congr 1 with p
        exact hΦe p
    _ = _ := by
        rw [integral_indicator_const _ ((isClosed_localIntegralSet' K v).preimage continuous_subtype_val).measurableSet,
          Complex.real_smul, mul_one, nuS, (sHomeo).measurableEmbedding.integral_map]
        simp only [mul_assoc]
        rfl

end Measures

section OrbitalIntegral

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  secondCountableTopology_units
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar
  AutomorphicForm.localCentralizerBorel borelSpace_localCentralizer locallyCompactSpace_localCentralizer

def centralizerCompacts (γ : GL (Fin 2) (v.adicCompletion K)) : PositiveCompacts (localCentralizer K v γ) where
  carrier := ((↑) : localCentralizer K v γ → GL (Fin 2) (v.adicCompletion K)) ⁻¹' localIntegralSet K v
  isCompact' := (isClosed_localCentralizer K v γ).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_localIntegralSet K v)
  interior_nonempty' := by
    rw [((isOpen_localIntegralSet K v).preimage continuous_subtype_val).interior_eq]
    exact ⟨1, one_mem_localIntegralSet K v⟩

def centralizerHaar (γ : GL (Fin 2) (v.adicCompletion K)) :
    @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ) :=
  Measure.haarMeasure (centralizerCompacts K v γ)

theorem isHaarMeasure_centralizerHaar (γ : GL (Fin 2) (v.adicCompletion K)) :
    @Measure.IsHaarMeasure (localCentralizer K v γ) _ _ (localCentralizerBorel K v γ) (centralizerHaar K v γ) :=
  Measure.isHaarMeasure_haarMeasure _

theorem centralizerHaar_self (γ : GL (Fin 2) (v.adicCompletion K)) :
    centralizerHaar K v γ
      (((↑) : localCentralizer K v γ → GL (Fin 2) (v.adicCompletion K)) ⁻¹' localIntegralSet K v) = 1 :=
  Measure.haarMeasure_self

variable {K v}

theorem torusMat_mul_comm (ϖ p r p' r' : v.adicCompletion K) :
    torusMat ϖ p r * torusMat ϖ p' r' = torusMat ϖ p' r' * torusMat ϖ p r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [torusMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

variable (ϖ : v.adicCompletion K) (hϖ : ϖ ≠ 0)
  (hns : ∀ p r : v.adicCompletion K, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0)

theorem comm_of_mem_Tsub {g h : GL (Fin 2) (v.adicCompletion K)} (hg : g ∈ Tsub ϖ hϖ) (hh : h ∈ Tsub ϖ hϖ) :
    g * h = h * g := by
  rw [Tsub, mem_centralizer_XGL_iff] at hg hh
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, eq_torusMat_of_commute hg, eq_torusMat_of_commute hh]
  exact torusMat_mul_comm _ _ _ _ _

include hϖ in

theorem isMulRightInvariant_centralizerHaar (c : (v.adicCompletion K)ˣ)
    {p r : v.adicCompletion K} (hD : p ^ 2 - ϖ * r ^ 2 ≠ 0) (hr : r ≠ 0) :
    (centralizerHaar K v (gammaPR ϖ c p r hD)).IsMulRightInvariant := by
  haveI := isHaarMeasure_centralizerHaar K v (gammaPR ϖ c p r hD)
  refine ⟨fun g => ?_⟩
  have hcomm : (fun t : localCentralizer K v (gammaPR ϖ c p r hD) => t * g) = fun t => g * t := by
    funext t
    refine Subtype.ext ?_
    change (t : GL (Fin 2) (v.adicCompletion K)) * g = g * t
    exact comm_of_mem_Tsub ϖ hϖ ((mem_centralizer_gammaPR_iff ϖ hϖ c hD hr _).1 t.2)
      ((mem_centralizer_gammaPR_iff ϖ hϖ c hD hr _).1 g.2)
  rw [hcomm]
  exact map_mul_left_eq_self _ g

theorem isCompact_units_annulus {r₁ : ℝ} (r₂ : ℝ) (hr₁ : 0 < r₁) :
    IsCompact {b : (v.adicCompletion K)ˣ | r₁ ≤ ‖(b : v.adicCompletion K)‖ ∧ ‖(b : v.adicCompletion K)‖ ≤ r₂} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have himg : ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) ''
      {b : (v.adicCompletion K)ˣ | r₁ ≤ ‖(b : v.adicCompletion K)‖ ∧ ‖(b : v.adicCompletion K)‖ ≤ r₂} =
      {x : v.adicCompletion K | r₁ ≤ ‖x‖} ∩ Metric.closedBall (0 : v.adicCompletion K) r₂ := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨b, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hx : x ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact lt_irrefl _ (hr₁.trans_le h1)
      exact ⟨Units.mk0 x hx, ⟨h1, h2⟩, rfl⟩
  rw [himg]
  exact (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const continuous_norm)

include hϖ in

theorem exists_bound_conj (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : HasCompactSupport fv)
    (hpar : ∀ a : v.adicCompletion K, ‖ϖ‖ ≤ ‖ϖ - a ^ 2‖)
    (c : (v.adicCompletion K)ˣ) {p r : v.adicCompletion K} (hD : p ^ 2 - ϖ * r ^ 2 ≠ 0) (hr : r ≠ 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (β : (v.adicCompletion K)ˣ) (α : v.adicCompletion K),
      fv ((sGL α β)⁻¹ * gammaPR ϖ c p r hD * sGL α β) ≠ 0 →
        C⁻¹ ≤ ‖(β : v.adicCompletion K)‖ ∧ ‖(β : v.adicCompletion K)‖ ≤ C ∧ ‖α‖ ≤ C := by

  have hbd : ∀ i j : Fin 2, ∃ B : ℝ, ∀ w ∈ tsupport fv, ‖(w : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ B :=
    fun i j => hfv.isCompact.exists_bound_of_continuousOn
      ((Units.continuous_val.matrix_elem i j).continuousOn (s := tsupport fv))
  obtain ⟨B00, hB00⟩ := hbd 0 0
  obtain ⟨B01, hB01⟩ := hbd 0 1
  obtain ⟨B10, hB10⟩ := hbd 1 0
  set B' : ℝ := max (max B00 B01) (max B10 1) with hB'
  have hent00 : ∀ w ∈ tsupport fv, ‖(w : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0‖ ≤ B' :=
    fun w hw => (hB00 w hw).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hent01 : ∀ w ∈ tsupport fv, ‖(w : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1‖ ≤ B' :=
    fun w hw => (hB01 w hw).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hent10 : ∀ w ∈ tsupport fv, ‖(w : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0‖ ≤ B' :=
    fun w hw => (hB10 w hw).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hB'1 : 1 ≤ B' := (le_max_right _ _).trans (le_max_right _ _)
  have hB'0 : 0 < B' := one_pos.trans_le hB'1
  have hrn : 0 < ‖r‖ := norm_pos_iff.2 hr
  have hcn : 0 < ‖(c : v.adicCompletion K)‖ := norm_pos_iff.2 c.ne_zero
  have hϖn : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ
  set C : ℝ := max (max 1 (B' / (‖(c : v.adicCompletion K)‖ * ‖r‖)))
    (max (max (B' / ‖(c : v.adicCompletion K)‖) ‖p‖ / ‖r‖) (B' / (‖r‖ * ‖ϖ‖ * ‖(c : v.adicCompletion K)‖))) with hC
  refine ⟨C, (le_max_left _ _).trans (le_max_left _ _), fun β α hne => ?_⟩
  have hw : (sGL α β)⁻¹ * gammaPR ϖ c p r hD * sGL α β ∈ tsupport fv := subset_tsupport _ (Function.mem_support.2 hne)
  have hE00 := hent00 _ hw
  have hE01 := hent01 _ hw
  have hE10 := hent10 _ hw
  simp only [coe_conj_gammaPR] at hE00 hE01 hE10
  have hβn : 0 < ‖(β : v.adicCompletion K)‖ := norm_pos_iff.2 β.ne_zero

  have e01 : ‖(c : v.adicCompletion K)‖ * (‖r‖ * ‖(β : v.adicCompletion K)‖) ≤ B' := by
    simpa [Matrix.add_apply, Matrix.smul_apply, norm_mul] using hE01
  have e00 : ‖(c : v.adicCompletion K)‖ * ‖p + r * α‖ ≤ B' := by
    simpa [Matrix.add_apply, Matrix.smul_apply, norm_mul] using hE00
  have e10 : ‖(c : v.adicCompletion K)‖ * (‖r‖ * (‖ϖ - α ^ 2‖ / ‖(β : v.adicCompletion K)‖)) ≤ B' := by
    simpa [Matrix.add_apply, Matrix.smul_apply, norm_mul, norm_div] using hE10
  refine ⟨?_, ?_, ?_⟩
  ·
    have h1 : ‖(c : v.adicCompletion K)‖ * (‖r‖ * (‖ϖ‖ / ‖(β : v.adicCompletion K)‖)) ≤ B' :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hpar α) hβn.le) hrn.le) hcn.le) e10
    have h2' : ‖r‖ * ‖ϖ‖ * ‖(c : v.adicCompletion K)‖ / B' ≤ ‖(β : v.adicCompletion K)‖ := by
      rw [div_le_iff₀ hB'0]
      have := h1
      rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ hβn] at this
      linarith [this]
    calc C⁻¹ ≤ (B' / (‖r‖ * ‖ϖ‖ * ‖(c : v.adicCompletion K)‖))⁻¹ := by
          apply inv_anti₀ (div_pos hB'0 (mul_pos (mul_pos hrn hϖn) hcn))
          exact (le_max_right _ _).trans (le_max_right _ _)
      _ = ‖r‖ * ‖ϖ‖ * ‖(c : v.adicCompletion K)‖ / B' := by rw [inv_div]
      _ ≤ _ := h2'
  ·
    have : ‖(β : v.adicCompletion K)‖ ≤ B' / (‖(c : v.adicCompletion K)‖ * ‖r‖) := by
      rw [le_div_iff₀ (mul_pos hcn hrn)]; nlinarith [e01]
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
  ·
    have hpα : ‖p + r * α‖ ≤ B' / ‖(c : v.adicCompletion K)‖ := by
      rw [le_div_iff₀ hcn]; nlinarith [e00]
    have hrα : ‖r * α‖ ≤ max (B' / ‖(c : v.adicCompletion K)‖) ‖p‖ := by
      have : r * α = (p + r * α) - p := by ring
      rw [this, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max hpα (by rw [norm_neg]))
    have : ‖α‖ ≤ max (B' / ‖(c : v.adicCompletion K)‖) ‖p‖ / ‖r‖ := by
      rw [le_div_iff₀ hrn, mul_comm, ← norm_mul]; exact hrα
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
  (μF : Measure (v.adicCompletion K)) [μF.IsAddHaarMeasure]
  (μU : Measure (v.adicCompletion K)ˣ) [μU.IsHaarMeasure]

def qpart (g : GL (Fin 2) (v.adicCompletion K)) : (v.adicCompletion K)ˣ × v.adicCompletion K :=
  (sHomeo).symm ⟨spart ϖ hns g, spart_mem ϖ hns g⟩

theorem continuous_qpart : Continuous (qpart ϖ hns) :=
  (sHomeo).symm.continuous.comp ((continuous_spart ϖ hns).subtype_mk _)

theorem sGL_qpart (g : GL (Fin 2) (v.adicCompletion K)) : sGL (qpart ϖ hns g).2 (qpart ϖ hns g).1 = spart ϖ hns g := by
  have := (sHomeo).apply_symm_apply (⟨spart ϖ hns g, spart_mem ϖ hns g⟩ : (Ssub : Subgroup (GL (Fin 2) (v.adicCompletion K))))
  exact congrArg Subtype.val this

include hϖ in
theorem qpart_sGL (β : (v.adicCompletion K)ˣ) (α : v.adicCompletion K) : qpart ϖ hns (sGL α β) = (β, α) := by
  have h1 : spart ϖ hns (sGL α β) = sGL α β := by
    have := spart_of_mem ϖ hϖ hns 1 (sGL α β) (Subgroup.one_mem _) (sGL_mem_Ssub α β)
    rwa [one_mul] at this
  simp only [qpart, h1]
  exact (sHomeo).symm_apply_apply (β, α)

include hϖ in
theorem qpart_mul (t g : GL (Fin 2) (v.adicCompletion K)) (ht : t ∈ Tsub ϖ hϖ) :
    qpart ϖ hns (t * g) = qpart ϖ hns g := by
  simp only [qpart, spart_mul ϖ hϖ hns t g ht]

include hϖ in
theorem qpart_spart (g : GL (Fin 2) (v.adicCompletion K)) : qpart ϖ hns (spart ϖ hns g) = qpart ϖ hns g := by
  have := spart_of_mem ϖ hϖ hns 1 (spart ϖ hns g) (Subgroup.one_mem _) (spart_mem ϖ hns g)
  rw [one_mul] at this
  simp only [qpart, this]

theorem conj_eq_conj_spart {γ x : GL (Fin 2) (v.adicCompletion K)} (h : tpart ϖ hns x * γ = γ * tpart ϖ hns x) :
    x⁻¹ * γ * x = (spart ϖ hns x)⁻¹ * γ * spart ϖ hns x := by
  conv_lhs => rw [← tpart_mul_spart ϖ hns x]
  rw [spart]
  have h' : (tpart ϖ hns x)⁻¹ * γ = γ * (tpart ϖ hns x)⁻¹ := by
    calc (tpart ϖ hns x)⁻¹ * γ = (tpart ϖ hns x)⁻¹ * (γ * tpart ϖ hns x) * (tpart ϖ hns x)⁻¹ := by group
      _ = (tpart ϖ hns x)⁻¹ * (tpart ϖ hns x * γ) * (tpart ϖ hns x)⁻¹ := by rw [h]
      _ = γ * (tpart ϖ hns x)⁻¹ := by group
  calc (tpart ϖ hns x * ((tpart ϖ hns x)⁻¹ * x))⁻¹ * γ * (tpart ϖ hns x * ((tpart ϖ hns x)⁻¹ * x))
      = x⁻¹ * γ * x := by group
    _ = x⁻¹ * (tpart ϖ hns x * ((tpart ϖ hns x)⁻¹ * γ)) * x := by group
    _ = x⁻¹ * (tpart ϖ hns x * (γ * (tpart ϖ hns x)⁻¹)) * x := by rw [h']
    _ = ((tpart ϖ hns x)⁻¹ * x)⁻¹ * γ * ((tpart ϖ hns x)⁻¹ * x) := by group

include hϖ hns in

theorem integral_conj_eq_zero (hright : (localHaar K v).IsMulRightInvariant)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : IsLocalTestFn K v fv)
    (hpar : ∀ a : v.adicCompletion K, ‖ϖ‖ ≤ ‖ϖ - a ^ 2‖)
    (c : (v.adicCompletion K)ˣ) {p r : v.adicCompletion K} (hD : p ^ 2 - ϖ * r ^ 2 ≠ 0) (hr : r ≠ 0)
    (hvan : ∀ τ : @Measure (localCentralizer K v (gammaPR ϖ c p r hD)) (localCentralizerBorel K v (gammaPR ϖ c p r hD)),
      @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v (gammaPR ϖ c p r hD)) τ →
        ∀ I : ℂ, IsOrbitalIntegral K v (gammaPR ϖ c p r hD) τ fv I → I = 0) :
    ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      fv ((sGL q.2 q.1)⁻¹ * gammaPR ϖ c p r hD * sGL q.2 q.1) ∂(μU.prod μF) = 0 := by
  set γ := gammaPR ϖ c p r hD with hγ

  set τ := centralizerHaar K v γ with hτ
  haveI hτH := isHaarMeasure_centralizerHaar K v γ
  haveI := isMulRightInvariant_centralizerHaar ϖ hϖ c hD hr
  have hTγ : ∀ g : GL (Fin 2) (v.adicCompletion K), g ∈ localCentralizer K v γ ↔ g ∈ Tsub ϖ hϖ :=
    fun g => mem_centralizer_gammaPR_iff ϖ hϖ c hD hr g

  obtain ⟨C, hC1, hC⟩ := exists_bound_conj ϖ hϖ fv hfv.2 hpar c hD hr
  have hC0 : 0 < C := one_pos.trans_le hC1
  set Q : Set ((v.adicCompletion K)ˣ × v.adicCompletion K) :=
    {b : (v.adicCompletion K)ˣ | C⁻¹ ≤ ‖(b : v.adicCompletion K)‖ ∧ ‖(b : v.adicCompletion K)‖ ≤ C} ×ˢ
      Metric.closedBall (0 : v.adicCompletion K) C with hQ
  have hQc : IsCompact Q := (isCompact_units_annulus C (inv_pos.2 hC0)).prod (isCompact_closedBall _ _)
  have hQcl : IsClosed Q := hQc.isClosed
  have hQmem : ∀ (β : (v.adicCompletion K)ˣ) (α : v.adicCompletion K),
      fv ((sGL α β)⁻¹ * γ * sGL α β) ≠ 0 → (β, α) ∈ Q := by
    intro β α h
    obtain ⟨h1, h2', h3⟩ := hC β α h
    exact ⟨⟨h1, h2'⟩, by simpa using h3⟩
  set W : Set (GL (Fin 2) (v.adicCompletion K)) :=
    {g | tpart ϖ hns g ∈ localIntegralSet K v ∧ qpart ϖ hns g ∈ Q} with hW
  have hWcl : IsClosed W :=
    ((isClosed_localIntegralSet' K v).preimage (continuous_tpart ϖ hns)).inter
      (hQcl.preimage (continuous_qpart ϖ hns))
  have hWc : IsCompact W := by
    set T₀ : Set (Tsub ϖ hϖ) := ((↑) : Tsub ϖ hϖ → GL (Fin 2) (v.adicCompletion K)) ⁻¹' localIntegralSet K v
    have hT₀ : IsCompact T₀ := (Set.isClosed_centralizer _).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_localIntegralSet K v)
    have hbig : IsCompact ((prodHomeo ϖ hϖ hns) '' (T₀ ×ˢ ((sHomeo) '' Q))) :=
      ((hT₀.prod (hQc.image (sHomeo).continuous)).image (prodHomeo ϖ hϖ hns).continuous)
    refine hbig.of_isClosed_subset hWcl (fun g hg => ?_)
    refine ⟨(⟨tpart ϖ hns g, tpart_mem ϖ hϖ hns g⟩, ⟨spart ϖ hns g, spart_mem ϖ hns g⟩), ⟨hg.1, ?_⟩,
      tpart_mul_spart ϖ hns g⟩
    exact ⟨qpart ϖ hns g, hg.2, (sHomeo).apply_symm_apply _⟩
  have hWm : MeasurableSet W := hWcl.measurableSet

  set w : GL (Fin 2) (v.adicCompletion K) → ℝ := W.indicator fun _ => 1 with hw
  have hsec : IsSectionFn K v γ τ fv w := by
    refine ⟨fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x, measurable_const.indicator hWm,
      HasCompactSupport.intro hWc (fun x hx => Set.indicator_of_notMem hx _), fun x hx => ?_⟩

    have htx : tpart ϖ hns x ∈ localCentralizer K v γ := (hTγ _).2 (tpart_mem ϖ hϖ hns x)
    have hcommx : tpart ϖ hns x * γ = γ * tpart ϖ hns x := Subgroup.mem_centralizer_singleton_iff.1 htx
    have hqx : qpart ϖ hns x ∈ Q := by
      rw [conj_eq_conj_spart ϖ hns hcommx, ← sGL_qpart ϖ hns x] at hx
      exact hQmem _ _ hx
    set t₁ : localCentralizer K v γ := ⟨tpart ϖ hns x, htx⟩ with ht₁
    have hset : {t : localCentralizer K v γ | (t : GL (Fin 2) (v.adicCompletion K)) * x ∈ W} =
        (fun t => t * t₁) ⁻¹'
          (((↑) : localCentralizer K v γ → GL (Fin 2) (v.adicCompletion K)) ⁻¹' localIntegralSet K v) := by
      ext t
      have ht : (t : GL (Fin 2) (v.adicCompletion K)) ∈ Tsub ϖ hϖ := (hTγ _).1 t.2
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hW, tpart_mul ϖ hϖ hns _ _ ht, qpart_mul ϖ hϖ hns _ _ ht, hqx,
        and_true]
      rfl
    have hind : (fun t : localCentralizer K v γ => w ((t : GL (Fin 2) (v.adicCompletion K)) * x)) =
        {t : localCentralizer K v γ | (t : GL (Fin 2) (v.adicCompletion K)) * x ∈ W}.indicator fun _ => (1 : ℝ) := by
      funext t
      by_cases h : (t : GL (Fin 2) (v.adicCompletion K)) * x ∈ W
      · rw [hw, Set.indicator_of_mem h, Set.indicator_of_mem (by exact h)]
      · rw [hw, Set.indicator_of_notMem h, Set.indicator_of_notMem (by exact h)]
    have hmeas : MeasurableSet {t : localCentralizer K v γ | (t : GL (Fin 2) (v.adicCompletion K)) * x ∈ W} :=
      (hWcl.preimage (continuous_subtype_val.mul continuous_const)).measurableSet
    rw [hind, integral_indicator_const _ hmeas, smul_eq_mul, mul_one, measureReal_def, hset, measure_preimage_mul_right,
      hτ, centralizerHaar_self, ENNReal.toReal_one]

  set I : ℂ := ∫ x, fv (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v) with hI
  have hI0 : I = 0 := hvan τ hτH I ⟨w, hsec, rfl⟩

  set ψ : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g => fv (g⁻¹ * γ * g) * Q.indicator (fun _ => (1 : ℂ)) (qpart ϖ hns g)
    with hψ
  have hptw : ∀ x, fv (x⁻¹ * γ * x) * (w x : ℂ) =
      (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (tpart ϖ hns x) * ψ (spart ϖ hns x) := by
    intro x
    have htx : tpart ϖ hns x ∈ localCentralizer K v γ := (hTγ _).2 (tpart_mem ϖ hϖ hns x)
    have hcommx : tpart ϖ hns x * γ = γ * tpart ϖ hns x := Subgroup.mem_centralizer_singleton_iff.1 htx
    simp only [hψ, qpart_spart ϖ hϖ hns, ← conj_eq_conj_spart ϖ hns hcommx, hw]
    by_cases h1 : tpart ϖ hns x ∈ localIntegralSet K v <;> by_cases h2 : qpart ϖ hns x ∈ Q
    · rw [Set.indicator_of_mem (show x ∈ W from ⟨h1, h2⟩), Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      push_cast; ring
    · rw [Set.indicator_of_notMem (show x ∉ W from fun h => h2 h.2), Set.indicator_of_notMem h2]
      push_cast; ring
    · rw [Set.indicator_of_notMem (show x ∉ W from fun h => h1 h.1), Set.indicator_of_notMem h1]
      push_cast; ring
    · rw [Set.indicator_of_notMem (show x ∉ W from fun h => h1 h.1), Set.indicator_of_notMem h1]
      push_cast; ring

  set TX₀ : PositiveCompacts (Tsub ϖ hϖ) := centralizerCompacts K v (XGL ϖ hϖ) with hTX₀
  set τX : Measure (Tsub ϖ hϖ) := Measure.haarMeasure TX₀ with hτX
  haveI : τX.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hτX1 : τX.real (((↑) : Tsub ϖ hϖ → GL (Fin 2) (v.adicCompletion K)) ⁻¹' localIntegralSet K v) = 1 := by
    rw [measureReal_def, hτX]
    change ((Measure.haarMeasure TX₀) (TX₀ : Set (Tsub ϖ hϖ))).toReal = 1
    rw [Measure.haarMeasure_self, ENNReal.toReal_one]
  obtain ⟨κ, hκ0, hκtop, hunfold⟩ := exists_unfold K v μF μU ϖ hϖ hns hright τX
  have hval : ∀ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      ψ (sGL q.2 q.1) = fv ((sGL q.2 q.1)⁻¹ * γ * sGL q.2 q.1) := by
    rintro ⟨β, α⟩
    simp only [hψ, qpart_sGL ϖ hϖ hns]
    by_cases h : fv ((sGL α β)⁻¹ * γ * sGL α β) = 0
    · rw [h, zero_mul]
    · rw [Set.indicator_of_mem (hQmem β α h), mul_one]
  have hmain : I = (κ.toReal : ℂ) * (1 : ℝ) *
      ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K, fv ((sGL q.2 q.1)⁻¹ * γ * sGL q.2 q.1) ∂(μU.prod μF) := by
    rw [hI, ← hτX1]
    simp_rw [hptw]
    rw [hunfold ψ]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hval)
  rw [hI0] at hmain
  have hκr : (κ.toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hκ0 hκtop).ne'
  simp only [Complex.ofReal_one, mul_one] at hmain
  exact (mul_eq_zero.1 hmain.symm).resolve_left hκr

end OrbitalIntegral

end P2mAffineChart
p2m_reactivate "P2MW.S_AutomorphicForm_integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero.P2mAffineChart"

namespace P2mAffineChart

open AutomorphicForm MeasureTheory

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_localGL
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel AutomorphicForm.isHaarMeasure_localHaar

theorem final (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (c : (v.adicCompletion K)ˣ)
    (ϖ : v.adicCompletion K) (hϖ : ϖ ≠ 0)
    (hϖsq : ∀ a t : v.adicCompletion K, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2)
    (p r : v.adicCompletion K) (hpr : p ^ 2 - ϖ * r ^ 2 ≠ 0) (hr : r ≠ 0)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![p, r; ϖ * r, p])
    (σ : v.adicCompletion K → (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K))
    (hσ : ∀ (a : v.adicCompletion K) (b : (v.adicCompletion K)ˣ),
      (σ a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, 0; a, (b : v.adicCompletion K)])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]
    (hvan : ∀ τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u))
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u)),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u)) τ →
        ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u) τ fv I →
          I = 0) :
    ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      fv ((σ q.2 q.1)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u) * σ q.2 q.1) ∂(ν.prod μ) = 0 := by

  have hns : ∀ p r : v.adicCompletion K, p ^ 2 - ϖ * r ^ 2 = 0 → r = 0 := by
    intro p' r' h
    by_contra hr'
    apply hϖsq p' r' hr'
    rw [sub_eq_zero] at h
    rw [← norm_pow, h, norm_mul, norm_pow]
  have hpar : ∀ a : v.adicCompletion K, ‖ϖ‖ ≤ ‖ϖ - a ^ 2‖ := by
    intro a
    have hne : ‖ϖ‖ ≠ ‖-(a ^ 2)‖ := by
      rw [norm_neg, norm_pow]
      intro h
      exact hϖsq a 1 one_ne_zero (by rw [← h]; simp)
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne]
    exact le_max_left _ _
  have huT : u = torusGL ϖ p r hpr := Units.ext hu
  have hσS : ∀ (a : v.adicCompletion K) (b : (v.adicCompletion K)ˣ), σ a b = sGL a b := fun a b => Units.ext (hσ a b)
  have hγ : Matrix.GeneralLinearGroup.scalar (Fin 2) c * u = gammaPR ϖ c p r hpr := by rw [huT]; rfl
  have hright : (localHaar K v).IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two (localHaar K v)).1
  have key := integral_conj_eq_zero (μF := μ) (μU := ν) ϖ hϖ hns hright fv hfv hpar c hpr hr (by rw [← hγ]; exact hvan)
  simp_rw [hσS, hγ]
  exact key

end P2mAffineChart
p2m_reactivate "P2MW.S_AutomorphicForm_integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero.P2mAffineChart"

open MeasureTheory NumberField IsDedekindDomain in
theorem solution (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (c : (v.adicCompletion K)ˣ)
    (ϖ : v.adicCompletion K) (hϖ : ϖ ≠ 0)
    (hϖsq : ∀ a t : v.adicCompletion K, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2)
    (p r : v.adicCompletion K) (hpr : p ^ 2 - ϖ * r ^ 2 ≠ 0) (hr : r ≠ 0)
    (u : GL (Fin 2) (v.adicCompletion K))
    (hu : (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![p, r; ϖ * r, p])
    (σ : v.adicCompletion K → (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K))
    (hσ : ∀ (a : v.adicCompletion K) (b : (v.adicCompletion K)ˣ),
      (σ a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![1, 0; a, (b : v.adicCompletion K)])
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]
    (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure]
    (hvan : ∀ τ : @Measure (AutomorphicForm.localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u))
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u)),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u)) τ →
        ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u) τ fv I →
          I = 0) :
    ∫ q : (v.adicCompletion K)ˣ × v.adicCompletion K,
      fv ((σ q.2 q.1)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) c * u) * σ q.2 q.1) ∂(ν.prod μ) = 0 :=
  P2mAffineChart.final K v fv hfv c ϖ hϖ hϖsq p r hpr hr u hu σ hσ μ ν hvan

end
end S_AutomorphicForm_integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_integral_conj_affineChart_eq_zero_of_forall_isOrbitalIntegral_eq_zero (solution)
