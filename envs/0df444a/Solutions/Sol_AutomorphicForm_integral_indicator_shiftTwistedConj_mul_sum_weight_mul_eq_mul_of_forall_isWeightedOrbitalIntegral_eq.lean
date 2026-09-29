-- Prove2me | solution 1 for AutomorphicForm.integral_indicator_shiftTwistedConj_mul_sum_weight_mul_eq_mul_of_forall_isWeightedOrbitalIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d61d0bfd-deaa-587a-8787-5030b0a38775

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Theorems.Thm_MeasureTheory_exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul
import Theorems.Thm_MeasureTheory_integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_indicator_shiftTwistedConj_mul_sum_weight_mul_eq_mul_of_forall_isWeightedOrbitalIntegral_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory MeasureTheory.Measure TopologicalSpace Function NumberField IsDedekindDomain Filter Set
open scoped NNReal ENNReal
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace P2mShiftReduction

open AutomorphicForm AutomorphicForm.LocalWeight

section IntegralPoints

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem mem_integers_iff_norm (y : Kv) : y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem norm_entry_le_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).1 i j)

theorem norm_inv_entry_le_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (i j : Fin 2) : ‖((g⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).2 i j)

theorem norm_det_le_mul_max (M : Matrix (Fin 2) (Fin 2) Kv) :
    ‖M.det‖ ≤ max ‖M 0 0‖ ‖M 0 1‖ * max ‖M 1 0‖ ‖M 1 1‖ := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))
  · rw [norm_neg, norm_mul]
    exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))

theorem norm_det_le_one {M : Matrix (Fin 2) (Fin 2) Kv} (hM : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 :=
  (norm_det_le_mul_max K v M).trans
    (mul_le_one₀ (max_le (hM 0 0) (hM 0 1)) (le_max_of_le_left (norm_nonneg _)) (max_le (hM 1 0) (hM 1 1)))

theorem norm_det_mul_norm_det_inv (g : GL (Fin 2) Kv) :
    ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ * ‖((g⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1 := by
  rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]

theorem norm_det_eq_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1 := by
  have h1 : ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ ≤ 1 := norm_det_le_one K v (norm_entry_le_one_of_mem K v hg)
  have h2 : ‖((g⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv).det‖ ≤ 1 :=
    norm_det_le_one K v (norm_inv_entry_le_one_of_mem K v hg)
  have hn := norm_det_mul_norm_det_inv K v g
  by_contra hne
  have hlt : ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ < 1 := lt_of_le_of_ne h1 hne
  exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2).ne hn

theorem mem_localIntegralSet_of_norm {g : GL (Fin 2) Kv}
    (h1 : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1)
    (h2 : ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1) : g ∈ localIntegralSet K v := by
  refine (mem_localIntegralSet K v).2 ⟨fun i j => (mem_integers_iff_norm K v _).2 (h1 i j), fun i j => ?_⟩
  rw [mem_integers_iff_norm, Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv',
    Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, h2, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · exact h1 1 1
  · simpa using h1 0 1
  · simpa using h1 1 0
  · exact h1 0 0

theorem mem_localIntegralSet_iff_norm (g : GL (Fin 2) Kv) :
    g ∈ localIntegralSet K v ↔ (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) Kv) i j‖ ≤ 1) ∧
      ‖(g : Matrix (Fin 2) (Fin 2) Kv).det‖ = 1 :=
  ⟨fun hg => ⟨norm_entry_le_one_of_mem K v hg, norm_det_eq_one_of_mem K v hg⟩,
    fun h => mem_localIntegralSet_of_norm K v h.1 h.2⟩

theorem norm_mul_entry_le_one {M N : Matrix (Fin 2) (Fin 2) Kv} (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hN : ∀ i j, ‖N i j‖ ≤ 1) (i j : Fin 2) : ‖(M * N) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul]
  · exact mul_le_one₀ (hM i 0) (norm_nonneg _) (hN 0 j)
  · exact mul_le_one₀ (hM i 1) (norm_nonneg _) (hN 1 j)

theorem mul_mem_localIntegralSet {g h : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet_iff_norm] at hg hh ⊢
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Units.val_mul]; exact norm_mul_entry_le_one K v hg.1 hh.1 i j
  · rw [Units.val_mul, Matrix.det_mul, norm_mul, hg.2, hh.2, one_mul]

theorem inv_mem_localIntegralSet {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem mul_mem_localIntegralSet_iff_right {g h : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ h ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hh => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v (inv_mem_localIntegralSet K v hg) hgh
  rwa [inv_mul_cancel_left] at this

end IntegralPoints

section Algebra

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem mem_centralizer_iff {a b : Kvˣ} (hab : a ≠ b) (t : GL (Fin 2) Kv) :
    t ∈ localCentralizer K v (diagUnits2 a b) ↔
      (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) Kv) 1 0 = 0 := by
  rw [localCentralizer, Subgroup.mem_centralizer_singleton_iff]
  have hab' : (a : Kv) ≠ b := fun h => hab (Units.ext h)
  have hba : (b : Kv) - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab')
  constructor
  · intro h
    have h' := congrArg (fun g : GL (Fin 2) Kv => (g : Matrix (Fin 2) (Fin 2) Kv)) h
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2] at h'
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
    refine ⟨?_, ?_⟩
    · have : (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 * ((b : Kv) - a) = 0 := by
        rw [mul_sub, sub_eq_zero, e01, mul_comm]
      exact (mul_eq_zero.1 this).resolve_right hba
    · have : (t : Matrix (Fin 2) (Fin 2) Kv) 1 0 * ((b : Kv) - a) = 0 := by
        rw [mul_sub, sub_eq_zero, mul_comm, e10]
      exact (mul_eq_zero.1 this).resolve_right hba
  · rintro ⟨h01, h10⟩
    apply Units.ext
    simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, mul_comm]

theorem centralizer_entries {a b : Kvˣ} (hab : a ≠ b) (t : localCentralizer K v (diagUnits2 a b)) :
    ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 0 1 = 0 ∧
      ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 1 0 = 0 :=
  (mem_centralizer_iff K v hab _).1 t.2

theorem centralizer_diag_ne_zero {a b : Kvˣ} (hab : a ≠ b) (t : localCentralizer K v (diagUnits2 a b)) :
    ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 0 0 ≠ 0 ∧
      ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) 1 1 ≠ 0 := by
  obtain ⟨h01, h10⟩ := centralizer_entries K v hab t
  have hdet : ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv).det ≠ 0 :=
    (Matrix.isUnits_det_units (t : GL (Fin 2) Kv)).ne_zero
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem centralizer_comm {a b : Kvˣ} (hab : a ≠ b) (s t : localCentralizer K v (diagUnits2 a b)) :
    s * t = t * s := by
  obtain ⟨s01, s10⟩ := centralizer_entries K v hab s
  obtain ⟨t01, t10⟩ := centralizer_entries K v hab t
  apply Subtype.ext
  apply Units.ext
  change ((s : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) * ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) =
    ((t : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) * ((s : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, s01, s10, t01, t10, mul_comm]

theorem centralizer_eq_diagUnits2 {a b : Kvˣ} (hab : a ≠ b) (t : localCentralizer K v (diagUnits2 a b)) :
    (t : GL (Fin 2) Kv) =
      diagUnits2 (Units.mk0 _ (centralizer_diag_ne_zero K v hab t).1)
        (Units.mk0 _ (centralizer_diag_ne_zero K v hab t).2) := by
  obtain ⟨h01, h10⟩ := centralizer_entries K v hab t
  apply Units.ext
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10]

theorem diagUnits2_mul_diagUnits2 (s₁ s₂ t₁ t₂ : Kvˣ) :
    diagUnits2 s₁ s₂ * diagUnits2 t₁ t₂ = (diagUnits2 (s₁ * t₁) (s₂ * t₂) : GL (Fin 2) Kv) := by
  apply Units.ext
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_comm (s₁ s₂ t₁ t₂ : Kvˣ) :
    diagUnits2 s₁ s₂ * diagUnits2 t₁ t₂ = (diagUnits2 t₁ t₂ * diagUnits2 s₁ s₂ : GL (Fin 2) Kv) := by
  rw [diagUnits2_mul_diagUnits2, diagUnits2_mul_diagUnits2, mul_comm s₁, mul_comm s₂]

theorem diagUnits2_one : (diagUnits2 1 1 : GL (Fin 2) Kv) = 1 := by
  apply Units.ext
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diagUnits2_inv (t₁ t₂ : Kvˣ) : (diagUnits2 t₁ t₂ : GL (Fin 2) Kv)⁻¹ = diagUnits2 t₁⁻¹ t₂⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diagUnits2_mul_diagUnits2, mul_inv_cancel, mul_inv_cancel, diagUnits2_one]

theorem centralizer_mul_diagUnits2 {a b : Kvˣ} (hab : a ≠ b) (t : localCentralizer K v (diagUnits2 a b))
    (s₁ s₂ : Kvˣ) : (t : GL (Fin 2) Kv) * diagUnits2 s₁ s₂ = diagUnits2 s₁ s₂ * t := by
  rw [centralizer_eq_diagUnits2 K v hab t, diagUnits2_comm]

def diagHom : Kvˣ × Kvˣ →* GL (Fin 2) Kv where
  toFun p := diagUnits2 p.1 p.2
  map_one' := diagUnits2_one K v
  map_mul' p q := (diagUnits2_mul_diagUnits2 K v p.1 p.2 q.1 q.2).symm

end Algebra

namespace WeightKit

variable {F : Type*} [NormedField F]

theorem det_norm_pos (x : GL (Fin 2) F) : 0 < ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
  norm_pos_iff.mpr (Matrix.isUnits_det_units x).ne_zero

theorem row0_ne_zero (x : GL (Fin 2) F) :
    ¬ ((x : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hdet : (x : Matrix (Fin 2) (Fin 2) F).det = 0 := by
    rw [Matrix.det_fin_two, h0, h1]; ring
  exact (Matrix.isUnits_det_units x).ne_zero hdet

theorem topMax_pos (x : GL (Fin 2) F) :
    0 < max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ := by
  rcases lt_or_ge 0 (max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖) with h | h
  · exact h
  · exfalso
    have h0 : ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ≤ 0 := (le_max_left _ _).trans h
    have h1 : ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ ≤ 0 := (le_max_right _ _).trans h
    exact row0_ne_zero x ⟨norm_le_zero_iff.mp h0, norm_le_zero_iff.mp h1⟩

theorem arg_pos (x : GL (Fin 2) F) :
    0 < max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
        AdelicHeight.rowMaxNorm (x : Matrix (Fin 2) (Fin 2) F) / ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
  div_pos (mul_pos (topMax_pos x) (AdelicHeight.rowMaxNorm_pos x)) (det_norm_pos x)

theorem continuous_weight : Continuous (weight : GL (Fin 2) F → ℝ) := by
  have hc : ∀ i j : Fin 2, Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F) i j‖ :=
    fun i j => (Units.continuous_val.matrix_elem i j).norm
  have hdet : Continuous fun x : GL (Fin 2) F => ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
    (Units.continuous_val.matrix_det).norm
  unfold weight
  refine continuous_const.mul (Continuous.log ?_ fun x => (arg_pos x).ne')
  exact (((hc 0 0).max (hc 0 1)).mul ((hc 1 0).max (hc 1 1))).div hdet fun x => (det_norm_pos x).ne'

theorem weight_eq (x : GL (Fin 2) F) :
    weight x = 2 * Real.log
      (max ‖(x : Matrix (Fin 2) (Fin 2) F) 0 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 0 1‖ *
        max ‖(x : Matrix (Fin 2) (Fin 2) F) 1 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) 1 1‖ /
        ‖(x : Matrix (Fin 2) (Fin 2) F).det‖) := rfl

theorem weight_diagUnits2_mul (t₁ t₂ : Fˣ) (x : GL (Fin 2) F) :
    weight (diagUnits2 t₁ t₂ * x) = weight x := by
  rw [weight_eq, weight_eq]
  congr 2
  have hM : ((diagUnits2 t₁ t₂ * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 0, (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 1;
        (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 0, (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 1] := by
    rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hM, Matrix.det_fin_two_of]
  have h1 : 0 < ‖(t₁ : F)‖ := norm_pos_iff.2 t₁.ne_zero
  have h2 : 0 < ‖(t₂ : F)‖ := norm_pos_iff.2 t₂.ne_zero
  have hdet : (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 0 * ((t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 1) -
      (t₁ : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 1 * ((t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 0) =
      (t₁ : F) * (t₂ : F) * (x : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Matrix.det_fin_two]; ring
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, norm_mul]
  rw [hdet, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ h1.le, ← mul_max_of_nonneg _ _ h2.le]
  field_simp

section Ultra

variable [IsUltrametricDist F]

theorem norm_mul_entry_le_rowMax (M N : Matrix (Fin 2) (Fin 2) F) (hN : ∀ i j, ‖N i j‖ ≤ 1) (i j : Fin 2) :
    ‖(M * N) i j‖ ≤ max ‖M i 0‖ ‖M i 1‖ := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hN 0 j)).trans (le_max_left _ _)
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hN 1 j)).trans (le_max_right _ _)

theorem rowMax_mul_le (M N : Matrix (Fin 2) (Fin 2) F) (hN : ∀ i j, ‖N i j‖ ≤ 1) (i : Fin 2) :
    max ‖(M * N) i 0‖ ‖(M * N) i 1‖ ≤ max ‖M i 0‖ ‖M i 1‖ :=
  max_le (norm_mul_entry_le_rowMax M N hN i 0) (norm_mul_entry_le_rowMax M N hN i 1)

theorem rowMax_mul_eq (x k : GL (Fin 2) F) (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1) (i : Fin 2) :
    max ‖((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 0‖ ‖((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i 1‖ =
      max ‖(x : Matrix (Fin 2) (Fin 2) F) i 0‖ ‖(x : Matrix (Fin 2) (Fin 2) F) i 1‖ := by
  refine le_antisymm ?_ ?_
  · rw [Units.val_mul]; exact rowMax_mul_le _ _ hk i
  · have hx : (x : Matrix (Fin 2) (Fin 2) F) = ((x * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
    conv_lhs => rw [hx]
    exact rowMax_mul_le _ _ hk' i

theorem weight_mul_of_norm_le_one (x k : GL (Fin 2) F) (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1)
    (hdet : ‖(k : Matrix (Fin 2) (Fin 2) F).det‖ = 1) :
    weight (x * k) = weight x := by
  rw [weight_eq, weight_eq]
  have h0 := rowMax_mul_eq x k hk hk' 0
  have h1 := rowMax_mul_eq x k hk hk' 1
  rw [h0, h1, Units.val_mul, Matrix.det_mul, norm_mul, hdet, mul_one]

theorem norm_det_le_mul_max' (M : Matrix (Fin 2) (Fin 2) F) :
    ‖M.det‖ ≤ max ‖M 0 0‖ ‖M 0 1‖ * max ‖M 1 0‖ ‖M 1 1‖ := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))
  · rw [norm_neg, norm_mul]
    exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (le_max_left _ _))

theorem weight_nonneg (x : GL (Fin 2) F) : 0 ≤ weight x := by
  rw [weight_eq]
  refine mul_nonneg (by norm_num) (Real.log_nonneg ?_)
  rw [le_div_iff₀ (det_norm_pos x), one_mul]
  exact norm_det_le_mul_max' _

end Ultra

end WeightKit

section Strings

variable {G : Type*} [Group G]

def listProd {m : ℕ} (g : Fin m → G) : G := (List.ofFn g).prod

theorem listProd_zero (g : Fin 0 → G) : listProd g = 1 := by
  simp [listProd]

theorem listProd_succ {m : ℕ} (g : Fin (m + 1) → G) :
    listProd g = listProd (fun k : Fin m => g (Fin.castSucc k)) * g (Fin.last m) := by
  unfold listProd
  rw [List.ofFn_succ', List.prod_concat]

theorem listProd_telescope : ∀ {m : ℕ} (x : Fin (m + 1) → G) (E : Fin m → G),
    listProd (fun k : Fin m => (x (Fin.castSucc k))⁻¹ * E k * x (Fin.succ k)) =
      (x 0)⁻¹ * listProd E * x (Fin.last m)
  | 0, x, E => by simp [listProd_zero]
  | m + 1, x, E => by
      rw [listProd_succ, listProd_succ E]
      have ih := listProd_telescope (fun k : Fin (m + 1) => x (Fin.castSucc k)) (fun k => E (Fin.castSucc k))
      have hfun : (fun k : Fin m => (x (Fin.castSucc (Fin.castSucc k)))⁻¹ * E (Fin.castSucc k) *
          x (Fin.castSucc (Fin.succ k))) =
          fun k : Fin m => (x (Fin.castSucc (Fin.castSucc k)))⁻¹ * E (Fin.castSucc k) *
            x (Fin.succ (Fin.castSucc k)) := by
        funext k; rw [Fin.succ_castSucc]
      rw [← hfun, ih, Fin.succ_last]
      simp only [Fin.castSucc_zero]
      group

theorem listProd_mem {S : Set G} (h1 : (1 : G) ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) :
    ∀ {m : ℕ} (g : Fin m → G), (∀ k, g k ∈ S) → listProd g ∈ S
  | 0, g, _ => by rw [listProd_zero]; exact h1
  | m + 1, g, hg => by
      rw [listProd_succ]
      exact hmul _ (listProd_mem h1 hmul _ fun k => hg _) _ (hg _)

theorem finRotate_castSucc {m : ℕ} (k : Fin m) : finRotate (m + 1) (Fin.castSucc k) = Fin.succ k := by
  have hk : (Fin.castSucc k : Fin (m + 1)) = ⟨(k : ℕ), Nat.lt_succ_of_lt k.2⟩ := rfl
  rw [hk, finRotate_of_lt k.2]
  rfl

end Strings

section Theta

variable {G : Type*} [Group G] {m : ℕ} (D : Fin (m + 1) → G)
  (Θ : (Fin (m + 1) → G) → Fin (m + 1) → G)
  (hΘ0 : ∀ x, Θ x 0 = x 0)
  (hΘs : ∀ x (k : Fin m), Θ x k.succ = (x k.castSucc)⁻¹ * D k.castSucc * x k.succ)

include hΘs in

theorem twistedConj_last (x : Fin (m + 1) → G) :
    (x (Fin.last m))⁻¹ * D (Fin.last m) * x 0 =
      (listProd (fun k : Fin m => Θ x k.succ))⁻¹ * ((x 0)⁻¹ * listProd D * x 0) := by
  have htail : (fun k : Fin m => Θ x k.succ) =
      fun k : Fin m => (x (Fin.castSucc k))⁻¹ * D (Fin.castSucc k) * x (Fin.succ k) :=
    funext fun k => hΘs x k
  rw [htail, listProd_telescope, listProd_succ D]
  group

include hΘ0 hΘs in

theorem theta_const_mul {t : G} (ht : ∀ j, t * D j = D j * t) (x : Fin (m + 1) → G) :
    Θ (fun i => t * x i) = Fin.cons (t * x 0) (Fin.tail (Θ x)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [hΘ0, Fin.cons_zero]
  · rw [Fin.cons_succ, Fin.tail, hΘs, hΘs]
    have hD : t⁻¹ * D (Fin.castSucc k) * t = D (Fin.castSucc k) := by
      rw [mul_assoc, inv_mul_eq_iff_eq_mul]; exact (ht _).symm
    calc (t * x (Fin.castSucc k))⁻¹ * D (Fin.castSucc k) * (t * x (Fin.succ k))
        = (x (Fin.castSucc k))⁻¹ * (t⁻¹ * D (Fin.castSucc k) * t) * x (Fin.succ k) := by group
      _ = (x (Fin.castSucc k))⁻¹ * D (Fin.castSucc k) * x (Fin.succ k) := by rw [hD]

include hΘ0 in
theorem theta_symm_apply_zero (Θe : (Fin (m + 1) → G) ≃ (Fin (m + 1) → G)) (hΘe : ∀ x, Θe x = Θ x)
    (z : Fin (m + 1) → G) : Θe.symm z 0 = z 0 := by
  have h := hΘ0 (Θe.symm z)
  rw [← hΘe, Equiv.apply_symm_apply] at h
  exact h.symm

end Theta

section Instances

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem secondCountableTopology_GL : SecondCountableTopology (GL (Fin 2) Kv) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Kv))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem t2Space_GL : T2Space (GL (Fin 2) Kv) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) Kv) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → Kv))
  exact Units.isEmbedding_embedProduct.t2Space

theorem isClosed_centralizer (γ : GL (Fin 2) Kv) :
    IsClosed ((localCentralizer K v γ : Subgroup (GL (Fin 2) Kv)) : Set (GL (Fin 2) Kv)) := by
  have : ((localCentralizer K v γ : Subgroup (GL (Fin 2) Kv)) : Set (GL (Fin 2) Kv)) =
      {x | x * γ = γ * x} := by
    ext x; exact Subgroup.mem_centralizer_singleton_iff
  rw [this]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem isInvInvariant_of_comm {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  letI : CommGroup T := { mul_comm := hcomm }
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : T → G)).secondCountableTopology
  haveI : PseudoMetrizableSpace T := PseudoMetrizableSpace.of_regularSpace_secondCountableTopology T
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : τ.InnerRegular := inferInstance
  exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

end Instances

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.isHaarMeasure_localHaar AutomorphicForm.locallyCompactSpace_localGL secondCountableTopology_GL
  t2Space_GL AutomorphicForm.localCentralizerBorel

section Main

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem borelSpace_centralizer (γ : GL (Fin 2) Kv) : BorelSpace (localCentralizer K v γ) := ⟨rfl⟩

attribute [local instance] borelSpace_centralizer

theorem continuous_cons {X : Type*} [TopologicalSpace X] {m : ℕ} :
    Continuous fun p : X × (Fin m → X) => (Fin.cons p.1 p.2 : Fin (m + 1) → X) := by
  refine continuous_pi fun j => Fin.cases ?_ (fun k => ?_) j
  · simp only [Fin.cons_zero]; exact continuous_fst
  · simp only [Fin.cons_succ]; exact (continuous_apply k).comp continuous_snd

theorem continuous_conj (γ : GL (Fin 2) Kv) : Continuous fun x : GL (Fin 2) Kv => x⁻¹ * γ * x :=
  (continuous_id.inv.mul continuous_const).mul continuous_id

theorem main (n : ℕ) (a b : Kvˣ) (hab : a ≠ b)
    (α β : Fin (n + 1) → Kvˣ) (hα : ∏ i, α i = a) (hβ : ∏ i, β i = b)
    (τ : Measure (localCentralizer K v (diagUnits2 a b))) [τ.IsHaarMeasure]
    (c : ℂ)
    (hc : ∀ J : ℂ, IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) J → J = c)
    (s : (Fin (n + 1) → GL (Fin 2) Kv) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : Fin (n + 1) → GL (Fin 2) Kv,
      (∀ i, (x i)⁻¹ * diagUnits2 (α i) (β i) * x (finRotate (n + 1) i) ∈ localIntegralSet K v) →
        ∫ t : localCentralizer K v (diagUnits2 a b), s (fun i => ((t : GL (Fin 2) Kv)) * x i) ∂τ = 1) :
    ∫ x : Fin (n + 1) → GL (Fin 2) Kv,
        (Set.pi Set.univ fun _ : Fin (n + 1) => localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (fun i => (x i)⁻¹ * diagUnits2 (α i) (β i) * x (finRotate (n + 1) i)) *
          ((∑ i, weight (x i) : ℝ) : ℂ) * (s x : ℂ)
      ∂(Measure.pi fun _ : Fin (n + 1) => localHaar K v) = ((n + 1 : ℕ) : ℂ) * c := by
  classical

  set K₀ : Set (GL (Fin 2) Kv) := localIntegralSet K v with hK₀
  set δ : Fin (n + 1) → GL (Fin 2) Kv := fun i => diagUnits2 (α i) (β i) with hδ
  have hK₀meas : MeasurableSet K₀ := (isOpen_localIntegralSet K v).measurableSet
  have hμK₀ : (localHaar K v) K₀ = 1 := localHaar_localIntegralSet K v

  have hprod : listProd δ = (diagUnits2 a b) := by
    have h : δ = diagHom K v ∘ (fun j => (α j, β j)) := rfl
    unfold listProd
    rw [h, ← List.map_ofFn, ← map_list_prod, List.prod_ofFn]
    have hp : (∏ j, (α j, β j)) = (∏ j, α j, ∏ j, β j) := Prod.ext (Prod.fst_prod) (Prod.snd_prod)
    rw [hp, hα, hβ]
    rfl

  obtain ⟨Θ, hΘmp, hΘ⟩ :=
    MeasureTheory.exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul (localHaar K v) δ
  have hΘ0 : ∀ x, Θ x 0 = x 0 := fun x => (hΘ x).1
  have hΘs : ∀ x (k : Fin n), Θ x k.succ = (x k.castSucc)⁻¹ * δ k.castSucc * x k.succ := fun x k => (hΘ x).2 k
  have hΘsymm0 : ∀ z, Θ.symm z 0 = z 0 :=
    fun z => theta_symm_apply_zero Θ hΘ0 Θ.toEquiv (fun _ => rfl) z

  set E : (Fin (n + 1) → (GL (Fin 2) Kv)) → Prop := fun x => ∀ i, (x i)⁻¹ * δ i * x (finRotate (n + 1) i) ∈ K₀ with hE
  set P : (Fin (n + 1) → (GL (Fin 2) Kv)) → Prop := fun z => (∀ k : Fin n, z k.succ ∈ K₀) ∧ (z 0)⁻¹ * (diagUnits2 a b) * z 0 ∈ K₀ with hP
  have hEP : ∀ x, E x ↔ P (Θ x) := by
    intro x
    simp only [hE, hP]
    constructor
    · intro h
      have hk : ∀ k : Fin n, Θ x k.succ ∈ K₀ := by
        intro k
        rw [hΘs, ← finRotate_castSucc]
        exact h _
      refine ⟨hk, ?_⟩
      rw [hΘ0]
      have hlast := h (Fin.last n)
      rw [finRotate_last, twistedConj_last δ Θ hΘs x, hprod] at hlast
      have hL : listProd (fun k : Fin n => Θ x k.succ) ∈ K₀ :=
        listProd_mem (one_mem_localIntegralSet K v) (fun a ha b hb => mul_mem_localIntegralSet K v ha hb) _ hk
      rwa [mul_mem_localIntegralSet_iff_right K v (inv_mem_localIntegralSet K v hL)] at hlast
    · rintro ⟨hk, h0⟩ i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · rw [finRotate_last, twistedConj_last δ Θ hΘs x, hprod]
        have hL : listProd (fun k : Fin n => Θ x k.succ) ∈ K₀ :=
          listProd_mem (one_mem_localIntegralSet K v) (fun a ha b hb => mul_mem_localIntegralSet K v ha hb) _ hk
        rw [mul_mem_localIntegralSet_iff_right K v (inv_mem_localIntegralSet K v hL)]
        rw [hΘ0] at h0
        exact h0
      · rw [finRotate_castSucc, ← hΘs]
        exact hk k

  have hwt : ∀ x, E x → ∀ i, weight (x i) = weight (x 0) := by
    intro x hx i
    refine Fin.induction rfl (fun k ih => ?_) i
    have hu : (x k.castSucc)⁻¹ * δ k.castSucc * x k.succ ∈ K₀ := by
      have := hx (Fin.castSucc k)
      rwa [finRotate_castSucc] at this
    set u := (x k.castSucc)⁻¹ * δ k.castSucc * x k.succ with hudef
    have hxs : x k.succ = (δ k.castSucc)⁻¹ * x k.castSucc * u := by
      rw [hudef]; group
    rw [hxs, hδ]
    simp only []
    rw [diagUnits2_inv, mul_assoc, WeightKit.weight_diagUnits2_mul,
      WeightKit.weight_mul_of_norm_le_one _ _ (norm_entry_le_one_of_mem K v hu)
        (norm_inv_entry_le_one_of_mem K v hu) (norm_det_eq_one_of_mem K v hu), ih]
  have hsumwt : ∀ x, E x → (∑ i, weight (x i)) = (n + 1 : ℕ) * weight (x 0) := by
    intro x hx
    rw [Finset.sum_congr rfl fun i _ => hwt x hx i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]

  set F : (Fin (n + 1) → (GL (Fin 2) Kv)) → ℝ := fun z =>
    ((n + 1 : ℕ) : ℝ) * ((if P z then (1 : ℝ) else 0) * weight (z 0) * s (Θ.symm z)) with hF
  have hF0 : ∀ z, 0 ≤ F z := by
    intro z
    refine mul_nonneg (by positivity) (mul_nonneg (mul_nonneg ?_ (WeightKit.weight_nonneg _)) (hs0 _))
    split_ifs <;> norm_num

  have hintegrand : (fun x : Fin (n + 1) → (GL (Fin 2) Kv) =>
      (Set.pi Set.univ fun _ : Fin (n + 1) => K₀).indicator (fun _ => (1 : ℂ))
          (fun i => (x i)⁻¹ * diagUnits2 (α i) (β i) * x (finRotate (n + 1) i)) *
        ((∑ i, weight (x i) : ℝ) : ℂ) * (s x : ℂ)) = fun x => ((F (Θ x) : ℝ) : ℂ) := by
    funext x
    have hmem : (fun i => (x i)⁻¹ * diagUnits2 (α i) (β i) * x (finRotate (n + 1) i)) ∈
        Set.pi Set.univ (fun _ : Fin (n + 1) => K₀) ↔ E x := by
      rw [Set.mem_univ_pi]
    by_cases hx : E x
    · rw [Set.indicator_of_mem (hmem.2 hx), hF]
      simp only []
      rw [if_pos ((hEP x).1 hx), Θ.symm_apply_apply, hΘ0, hsumwt x hx]
      push_cast
      ring
    · rw [Set.indicator_of_notMem (fun h => hx (hmem.1 h)), hF]
      simp only []
      rw [if_neg (fun h => hx ((hEP x).2 h))]
      push_cast
      ring

  have hPmeas : MeasurableSet {z : Fin (n + 1) → (GL (Fin 2) Kv) | P z} := by
    have h1 : {z : Fin (n + 1) → (GL (Fin 2) Kv) | P z} =
        (⋂ k : Fin n, (fun z : Fin (n + 1) → (GL (Fin 2) Kv) => z k.succ) ⁻¹' K₀) ∩
          (fun z : Fin (n + 1) → (GL (Fin 2) Kv) => (z 0)⁻¹ * (diagUnits2 a b) * z 0) ⁻¹' K₀ := by
      ext z
      simp only [hP, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rw [h1]
    refine (MeasurableSet.iInter fun k => hK₀meas.preimage (continuous_apply k.succ).measurable).inter ?_
    exact hK₀meas.preimage ((continuous_conj K v (diagUnits2 a b)).measurable.comp (continuous_apply (0 : Fin (n + 1))).measurable)
  have hFm : Measurable F := by
    refine measurable_const.mul (((Measurable.ite hPmeas measurable_const measurable_const).mul
      (WeightKit.continuous_weight.measurable.comp (continuous_apply (0 : Fin (n + 1))).measurable)).mul
        (hsm.comp Θ.symm.measurable))

  have hC : ∫ x, ((F (Θ x) : ℝ) : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => (localHaar K v)) =
      (((∫⁻ z, ENNReal.ofReal (F z) ∂(Measure.pi fun _ : Fin (n + 1) => (localHaar K v))).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, hΘmp.integral_comp' (fun z => F z),
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hFm.aestronglyMeasurable]

  set e₀ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => (GL (Fin 2) Kv)) 0 with he₀
  have he₀mp : MeasurePreserving e₀.symm ((localHaar K v).prod (Measure.pi fun _ : Fin n => (localHaar K v))) (Measure.pi fun _ => (localHaar K v)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (localHaar K v)) 0).symm
  have he₀symm : ∀ q : (GL (Fin 2) Kv) × (Fin n → (GL (Fin 2) Kv)), e₀.symm q = Fin.cons q.1 q.2 := by
    intro q
    rw [he₀, MeasurableEquiv.piFinSuccAbove_symm_apply]
    funext j
    rw [Fin.insertNthEquiv_apply, Fin.insertNth_zero']
  set H : (GL (Fin 2) Kv) × (Fin n → (GL (Fin 2) Kv)) → ℝ≥0∞ := fun q => ENNReal.ofReal (F (Fin.cons q.1 q.2)) with hH
  have hHm : Measurable H :=
    ENNReal.measurable_ofReal.comp (hFm.comp continuous_cons.measurable)
  have hD : ∫⁻ z, ENNReal.ofReal (F z) ∂(Measure.pi fun _ : Fin (n + 1) => (localHaar K v)) =
      ∫⁻ g, ∫⁻ z0, H (z0, g) ∂(localHaar K v) ∂(Measure.pi fun _ : Fin n => (localHaar K v)) := by
    rw [← he₀mp.map_eq, lintegral_map_equiv]
    have h1 : (fun q : (GL (Fin 2) Kv) × (Fin n → (GL (Fin 2) Kv)) => ENNReal.ofReal (F (e₀.symm q))) = H := by
      funext q; rw [hH, he₀symm]
    rw [h1, lintegral_prod_symm H hHm.aemeasurable]

  have hτinv : τ.IsInvInvariant :=
    isInvInvariant_of_comm (localCentralizer K v (diagUnits2 a b)) (isClosed_centralizer K v _) (centralizer_comm K v hab) τ

  set Fγ : (GL (Fin 2) Kv) → ℂ := fun z => K₀.indicator (fun _ => (1 : ℂ)) (z⁻¹ * (diagUnits2 a b) * z) with hFγ
  have hFγm : Measurable Fγ := by
    have : Fγ = ((fun z : (GL (Fin 2) Kv) => z⁻¹ * (diagUnits2 a b) * z) ⁻¹' K₀).indicator fun _ => (1 : ℂ) := by
      funext z; simp only [hFγ, Set.indicator_apply, Set.mem_preimage]
    rw [this]
    exact measurable_const.indicator (hK₀meas.preimage (continuous_conj K v (diagUnits2 a b)).measurable)
  have hFγb : ∃ C : ℝ, ∀ z, ‖Fγ z‖ ≤ C := ⟨1, fun z => by
    rw [hFγ]; simp only [Set.indicator_apply]; split_ifs <;> simp⟩
  have hFγT : ∀ (t : (localCentralizer K v (diagUnits2 a b))) (z : (GL (Fin 2) Kv)), Fγ ((t : (GL (Fin 2) Kv)) * z) = Fγ z := by
    intro t z
    have ht : (t : (GL (Fin 2) Kv)) * (diagUnits2 a b) = (diagUnits2 a b) * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
    have key : ((t : (GL (Fin 2) Kv)) * z)⁻¹ * (diagUnits2 a b) * ((t : (GL (Fin 2) Kv)) * z) = z⁻¹ * (diagUnits2 a b) * z := by
      have h2 : ((t : GL (Fin 2) Kv))⁻¹ * (diagUnits2 a b) * (t : GL (Fin 2) Kv) = diagUnits2 a b := by
        rw [mul_assoc, inv_mul_eq_iff_eq_mul]; exact ht.symm
      calc ((t : (GL (Fin 2) Kv)) * z)⁻¹ * (diagUnits2 a b) * ((t : (GL (Fin 2) Kv)) * z)
          = z⁻¹ * (((t : GL (Fin 2) Kv))⁻¹ * (diagUnits2 a b) * (t : GL (Fin 2) Kv)) * z := by group
        _ = z⁻¹ * (diagUnits2 a b) * z := by rw [h2]
    rw [hFγ]
    simp only [key]
  have hWT : ∀ (t : (localCentralizer K v (diagUnits2 a b))) (z : (GL (Fin 2) Kv)), weight ((t : (GL (Fin 2) Kv)) * z) = weight z := by
    intro t z
    rw [centralizer_eq_diagUnits2 K v hab t, WeightKit.weight_diagUnits2_mul]

  have hslice : ∀ g : Fin n → (GL (Fin 2) Kv), (∀ k, g k ∈ K₀) →
      ∫⁻ z0, H (z0, g) ∂(localHaar K v) = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * c.re) ∧ 0 ≤ c.re ∧ c = ((c.re : ℝ) : ℂ) := by
    intro g hg
    set w : (GL (Fin 2) Kv) → ℝ := fun z0 => s (Θ.symm (Fin.cons z0 g)) with hw
    have hw0 : ∀ z, 0 ≤ w z := fun z => hs0 _
    have hwm : Measurable w :=
      hsm.comp (Θ.symm.measurable.comp (continuous_cons.measurable.comp (measurable_id.prodMk measurable_const)))
    have hwc : HasCompactSupport w := by
      refine HasCompactSupport.intro (hsc.image (continuous_apply 0)) fun z hz => ?_
      by_contra hne
      apply hz
      refine ⟨Θ.symm (Fin.cons z g), subset_tsupport _ (Function.mem_support.2 hne), ?_⟩
      show Θ.symm (Fin.cons z g) 0 = z
      rw [hΘsymm0, Fin.cons_zero]

    have hwsec : ∀ z : (GL (Fin 2) Kv), Fγ z ≠ 0 → ∫ t : (localCentralizer K v (diagUnits2 a b)), w ((t : (GL (Fin 2) Kv)) * z) ∂τ = 1 := by
      intro z hz
      have hz' : z⁻¹ * (diagUnits2 a b) * z ∈ K₀ := by
        by_contra h
        apply hz
        rw [hFγ]; simp only []; rw [Set.indicator_of_notMem h]
      set x := Θ.symm (Fin.cons z g) with hx
      have hΘx : Θ x = Fin.cons z g := Θ.apply_symm_apply _
      have hx0 : x 0 = z := by rw [hx, hΘsymm0, Fin.cons_zero]
      have hEx : E x := by
        rw [hEP, hΘx]
        refine ⟨fun k => ?_, ?_⟩
        · rw [Fin.cons_succ]; exact hg k
        · rw [Fin.cons_zero]; exact hz'
      have h1 := hs1 x hEx
      have htr : ∀ t : (localCentralizer K v (diagUnits2 a b)), w ((t : (GL (Fin 2) Kv)) * z) = s (fun i => (t : (GL (Fin 2) Kv)) * x i) := by
        intro t
        rw [hw]
        simp only []
        congr 1
        apply Θ.injective
        rw [Θ.apply_symm_apply]
        have hcomm : ∀ j, (t : (GL (Fin 2) Kv)) * δ j = δ j * t := fun j => centralizer_mul_diagUnits2 K v hab t _ _
        rw [theta_const_mul δ Θ hΘ0 hΘs hcomm x, hx0, hΘx, Fin.tail_cons]
      simp_rw [htr]
      exact h1

    have hJ : IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ (K₀.indicator fun _ => (1 : ℂ))
        (∫ z, Fγ z * (weight z : ℂ) * (w z : ℂ) ∂(localHaar K v)) :=
      ⟨w, ⟨hw0, hwm, hwc, hwsec⟩, rfl⟩
    have hJc := hc _ hJ

    obtain ⟨hint, -⟩ :=
      MeasureTheory.integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
        (localCentralizer K v (diagUnits2 a b)) (isClosed_centralizer K v _) (localHaar K v) τ Fγ hFγm hFγb hFγT weight WeightKit.continuous_weight hWT
        w w ⟨hw0, hwm, hwc, hwsec⟩ ⟨hw0, hwm, hwc, hwsec⟩

    set φ : (GL (Fin 2) Kv) → ℝ := fun z0 => (if z0⁻¹ * (diagUnits2 a b) * z0 ∈ K₀ then (1 : ℝ) else 0) * weight z0 * w z0 with hφ
    have hφC : ∀ z, Fγ z * (weight z : ℂ) * (w z : ℂ) = ((φ z : ℝ) : ℂ) := by
      intro z
      rw [hφ, hFγ]
      simp only [Set.indicator_apply]
      split_ifs <;> push_cast <;> ring
    have hφint : Integrable φ (localHaar K v) := by
      have h := hint.re
      refine h.congr (Eventually.of_forall fun z => ?_)
      simp only [hφC, RCLike.re_to_complex, Complex.ofReal_re]
    have hφ0 : ∀ z, 0 ≤ φ z := by
      intro z
      refine mul_nonneg (mul_nonneg ?_ (WeightKit.weight_nonneg _)) (hw0 _)
      split_ifs <;> norm_num
    have hJφ : c = ((∫ z, φ z ∂(localHaar K v) : ℝ) : ℂ) := by
      rw [← hJc, ← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall hφC)
    have hcre : c.re = ∫ z, φ z ∂(localHaar K v) := by rw [hJφ, Complex.ofReal_re]

    have hHg : ∀ z0, H (z0, g) = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * φ z0) := by
      intro z0
      have hPz : P (Fin.cons z0 g) ↔ z0⁻¹ * (diagUnits2 a b) * z0 ∈ K₀ := by
        simp only [hP, Fin.cons_succ, Fin.cons_zero]
        exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
      have h0 : (Fin.cons z0 g : Fin (n + 1) → GL (Fin 2) Kv) 0 = z0 := rfl
      simp only [hH, hF, hφ, hw, h0]
      by_cases hz : z0⁻¹ * (diagUnits2 a b) * z0 ∈ K₀
      · simp only [if_pos (hPz.2 hz), if_pos hz]
      · simp only [if_neg (fun h => hz (hPz.1 h)), if_neg hz]
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [hHg]
      rw [← ofReal_integral_eq_lintegral_ofReal (hφint.const_mul _)
        (Eventually.of_forall fun z => mul_nonneg (by positivity) (hφ0 z)), integral_const_mul, hcre]
    · rw [hcre]; exact integral_nonneg hφ0
    · rw [hJφ, Complex.ofReal_re]
  have hslice0 : ∀ g : Fin n → (GL (Fin 2) Kv), ¬ (∀ k, g k ∈ K₀) → ∫⁻ z0, H (z0, g) ∂(localHaar K v) = 0 := by
    intro g hg
    have h0 : ∀ z0, H (z0, g) = 0 := by
      intro z0
      rw [hH, hF]
      simp only []
      have hnP : ¬ P (Fin.cons z0 g) := by
        simp only [hP, Fin.cons_succ]
        exact fun h => hg h.1
      rw [if_neg hnP]
      simp
    simp_rw [h0, lintegral_zero]

  have hcre : ∃ g : Fin n → (GL (Fin 2) Kv), ∀ k, g k ∈ K₀ := ⟨fun _ => 1, fun _ => one_mem_localIntegralSet K v⟩
  obtain ⟨g₁, hg₁⟩ := hcre
  have hcform : c = ((c.re : ℝ) : ℂ) := (hslice g₁ hg₁).2.2
  have hc0 : 0 ≤ c.re := (hslice g₁ hg₁).2.1
  have hinner : ∀ g : Fin n → (GL (Fin 2) Kv), ∫⁻ z0, H (z0, g) ∂(localHaar K v) =
      (Set.pi Set.univ fun _ : Fin n => K₀).indicator (fun _ => ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * c.re)) g := by
    intro g
    by_cases hg : ∀ k, g k ∈ K₀
    · rw [(hslice g hg).1, Set.indicator_of_mem]
      rw [Set.mem_univ_pi]; exact hg
    · rw [hslice0 g hg, Set.indicator_of_notMem]
      rw [Set.mem_univ_pi]; exact hg
  have hpiK₀ : MeasurableSet (Set.pi Set.univ fun _ : Fin n => K₀) :=
    MeasurableSet.univ_pi fun _ => hK₀meas
  have houter : ∫⁻ g, ∫⁻ z0, H (z0, g) ∂(localHaar K v) ∂(Measure.pi fun _ : Fin n => (localHaar K v)) =
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * c.re) := by
    rw [lintegral_congr hinner, lintegral_indicator_const hpiK₀, Measure.pi_pi]
    simp only [hμK₀, Finset.prod_const_one, mul_one]

  rw [hintegrand, hC, hD, houter, ENNReal.toReal_ofReal (mul_nonneg (by positivity) hc0)]
  conv_rhs => rw [hcform]
  push_cast
  ring

end Main

end P2mShiftReduction

end

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : Fin (n + 1) → (v.adicCompletion K)ˣ) (hα : ∏ i, α i = a) (hβ : ∏ i, β i = b)
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (c : ℂ)
    (hc : ∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) J → J = c)
    [MeasurableSpace (GL (Fin 2) (v.adicCompletion K))] [BorelSpace (GL (Fin 2) (v.adicCompletion K))]
    (μ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ.IsHaarMeasure]
    (hμ : μ (AutomorphicForm.localIntegralSet K v) = 1)
    (s : (Fin (n + 1) → GL (Fin 2) (v.adicCompletion K)) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : Fin (n + 1) → GL (Fin 2) (v.adicCompletion K),
      (∀ i, (x i)⁻¹ * diagUnits2 (α i) (β i) * x (finRotate (n + 1) i) ∈
          AutomorphicForm.localIntegralSet K v) →
        ∫ t : AutomorphicForm.localCentralizer K v (diagUnits2 a b),
          s (fun i => ((t : GL (Fin 2) (v.adicCompletion K)) * x i)) ∂τ = 1) :
    ∫ x : Fin (n + 1) → GL (Fin 2) (v.adicCompletion K),
        (Set.pi Set.univ fun _ : Fin (n + 1) => AutomorphicForm.localIntegralSet K v).indicator
            (fun _ => (1 : ℂ))
            (fun i => (x i)⁻¹ * diagUnits2 (α i) (β i) * x (finRotate (n + 1) i)) *
          ((∑ i, AutomorphicForm.LocalWeight.weight (x i) : ℝ) : ℂ) * (s x : ℂ)
      ∂(Measure.pi fun _ : Fin (n + 1) => μ) = ((n + 1 : ℕ) : ℂ) * c := by

  obtain ⟨hB⟩ := ‹BorelSpace (GL (Fin 2) (v.adicCompletion K))›
  subst hB
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := borel _
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := ⟨rfl⟩
  haveI := AutomorphicForm.locallyCompactSpace_localGL K v
  haveI := P2mShiftReduction.secondCountableTopology_GL K v
  haveI : (AutomorphicForm.localHaar K v).IsHaarMeasure := AutomorphicForm.isHaarMeasure_localHaar K v
  have hμ' : μ = AutomorphicForm.localHaar K v := by
    rw [Measure.haarMeasure_unique μ (AutomorphicForm.localIntegralCompacts K v),
      Measure.haarMeasure_unique (AutomorphicForm.localHaar K v) (AutomorphicForm.localIntegralCompacts K v)]
    change μ (AutomorphicForm.localIntegralSet K v) • _ = AutomorphicForm.localHaar K v (AutomorphicForm.localIntegralSet K v) • _
    rw [hμ, AutomorphicForm.localHaar_localIntegralSet]
  subst hμ'
  haveI := hτ
  exact P2mShiftReduction.main K v n a b hab α β hα hβ τ c hc s hs0 hsm hsc hs1

end S_AutomorphicForm_integral_indicator_shiftTwistedConj_mul_sum_weight_mul_eq_mul_of_forall_isWeightedOrbitalIntegral_eq
end P2MW
export P2MW.S_AutomorphicForm_integral_indicator_shiftTwistedConj_mul_sum_weight_mul_eq_mul_of_forall_isWeightedOrbitalIntegral_eq (solution)
