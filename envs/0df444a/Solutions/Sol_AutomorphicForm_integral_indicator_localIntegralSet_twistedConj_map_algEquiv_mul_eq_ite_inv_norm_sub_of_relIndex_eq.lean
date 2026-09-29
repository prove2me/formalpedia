-- Prove2me | solution 1 for AutomorphicForm.integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/48c26647-6595-5eaf-8ec6-76b5ea05ee27

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Theorems.Thm_LocalGL2_iwasawa_decomposition
import Theorems.Thm_MeasureTheory_integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
import Theorems.Thm_AutomorphicForm_localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain TopologicalSpace Filter Set
open scoped NNReal ENNReal
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace R4S30UnitE

open AutomorphicForm

section Norms

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev qv : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem one_lt_qv : 1 < qv K v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  unfold qv
  exact_mod_cast this

theorem qv_pos : 0 < qv K v := lt_trans zero_lt_one (one_lt_qv K v)

theorem qv_ne_zero : qv K v ≠ 0 := (qv_pos K v).ne'

theorem mem_integers_iff_norm (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem exists_norm_eq_zpow_and_v_eq {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = qv K v ^ k ∧ (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_, ?_⟩
  · rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  · conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl

theorem norm_eq_zero_or_zpow (x : v.adicCompletion K) : ‖x‖ = 0 ∨ ∃ n : ℤ, ‖x‖ = qv K v ^ n := by
  by_cases hx : x = 0
  · exact Or.inl (by rw [hx, norm_zero])
  · obtain ⟨k, hk, -⟩ := exists_norm_eq_zpow_and_v_eq K v hx
    exact Or.inr ⟨k, hk⟩

theorem v_eq_exp_of_norm_eq_zpow {x : v.adicCompletion K} {k : ℤ} (h : ‖x‖ = qv K v ^ k) :
    (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at h
    exact (zpow_pos (qv_pos K v) k).ne h
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [hk'] at h
  have hk : k' = k := zpow_right_injective₀ (qv_pos K v) (one_lt_qv K v).ne' h
  rw [hv, hk]

theorem norm_eq_zpow_of_v_eq_exp {x : v.adicCompletion K} {k : ℤ}
    (h : (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k) : ‖x‖ = qv K v ^ k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, map_zero] at h
    exact WithZero.coe_ne_zero h.symm
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [hv] at h
  have : k' = k := WithZero.exp_injective h
  rw [hk', this]

theorem norm_eq_one_iff_v (x : v.adicCompletion K) :
    ‖x‖ = 1 ↔ (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
  constructor
  · intro h
    have := v_eq_exp_of_norm_eq_zpow K v (k := 0) (by rw [h, zpow_zero])
    rwa [WithZero.exp_zero] at this
  · intro h
    have := norm_eq_zpow_of_v_eq_exp K v (k := 0) (by rw [h, WithZero.exp_zero])
    rwa [zpow_zero] at this

theorem zpow_add_one_le_norm_of_lt {x : v.adicCompletion K} {n : ℤ} (h : qv K v ^ n < ‖x‖) :
    qv K v ^ (n + 1) ≤ ‖x‖ := by
  rcases norm_eq_zero_or_zpow K v x with h0 | ⟨k, hk⟩
  · rw [h0] at h; exact absurd h (not_lt.2 (zpow_nonneg (qv_pos K v).le _))
  · rw [hk] at h ⊢
    have hlt : n < k := (zpow_lt_zpow_iff_right₀ (one_lt_qv K v)).1 h
    exact zpow_le_zpow_right₀ (one_lt_qv K v).le (by omega)

theorem exists_norm_eq_inv : ∃ ϖ : v.adicCompletion K, ‖ϖ‖ = (qv K v)⁻¹ := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1))
  exact ⟨x, by rw [norm_eq_zpow_of_v_eq_exp K v hx, zpow_neg, zpow_one]⟩

end Norms

section IntegralPoints

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

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

theorem mul_mem_localIntegralSet_iff_left {g h : GL (Fin 2) Kv} (hh : h ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ g ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v hgh (inv_mem_localIntegralSet K v hh)
  rwa [mul_inv_cancel_right] at this

theorem mul_mem_localIntegralSet_iff_right {g h : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    g * h ∈ localIntegralSet K v ↔ h ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hh => mul_mem_localIntegralSet K v hg hh⟩
  have := mul_mem_localIntegralSet K v (inv_mem_localIntegralSet K v hg) hgh
  rwa [inv_mul_cancel_left] at this

theorem upper_mem_iff {g : GL (Fin 2) Kv} {A B D : Kv}
    (hg : (g : Matrix (Fin 2) (Fin 2) Kv) = !![A, B; 0, D]) :
    g ∈ localIntegralSet K v ↔ ‖A‖ = 1 ∧ ‖D‖ = 1 ∧ ‖B‖ ≤ 1 := by
  rw [mem_localIntegralSet_iff_norm, hg, Matrix.det_fin_two_of]
  simp only [mul_zero, sub_zero, norm_mul]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : ‖A‖ ≤ 1 := by simpa using h1 0 0
    have hb : ‖D‖ ≤ 1 := by simpa using h1 1 1
    have hy : ‖B‖ ≤ 1 := by simpa using h1 0 1
    have ha1 : ‖A‖ = 1 := by
      by_contra hne
      exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (lt_of_le_of_ne ha hne) hb).ne h2
    exact ⟨ha1, by rwa [ha1, one_mul] at h2, hy⟩
  · rintro ⟨ha, hb, hy⟩
    refine ⟨fun i j => ?_, by rw [ha, hb, one_mul]⟩
    fin_cases i <;> fin_cases j
    · simpa using ha.le
    · simpa using hy
    · simp
    · simpa using hb.le

theorem unipotentGL2_mem_iff (y : Kv) : unipotentGL2 y ∈ localIntegralSet K v ↔ ‖y‖ ≤ 1 := by
  rw [upper_mem_iff K v (A := 1) (B := y) (D := 1) (unipotentGL2_coe y)]
  simp

theorem diagUnits2_mem_iff (t₁ t₂ : Kvˣ) :
    diagUnits2 t₁ t₂ ∈ localIntegralSet K v ↔ ‖(t₁ : Kv)‖ = 1 ∧ ‖(t₂ : Kv)‖ = 1 := by
  rw [upper_mem_iff K v (A := (t₁ : Kv)) (B := 0) (D := (t₂ : Kv))
    (by rw [LanglandsTunnell.CubicInduction.coe_diagUnits2])]
  simp

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

theorem diag_ne_zero_of_offdiag {t : GL (Fin 2) Kv} (h01 : (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 = 0) :
    (t : Matrix (Fin 2) (Fin 2) Kv) 0 0 ≠ 0 ∧ (t : Matrix (Fin 2) (Fin 2) Kv) 1 1 ≠ 0 := by
  have hdet : (t : Matrix (Fin 2) (Fin 2) Kv).det ≠ 0 := (Matrix.isUnits_det_units t).ne_zero
  rw [Matrix.det_fin_two, h01, zero_mul, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem eq_diagUnits2_of_offdiag {t : GL (Fin 2) Kv} (h01 : (t : Matrix (Fin 2) (Fin 2) Kv) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) Kv) 1 0 = 0) :
    t = diagUnits2 (Units.mk0 _ (diag_ne_zero_of_offdiag K v h01).1)
      (Units.mk0 _ (diag_ne_zero_of_offdiag K v h01).2) := by
  apply Units.ext
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10]

theorem diagUnits2_mem_centralizer {a b : Kvˣ} (hab : a ≠ b) (t₁ t₂ : Kvˣ) :
    diagUnits2 t₁ t₂ ∈ localCentralizer K v (diagUnits2 a b) := by
  rw [mem_centralizer_iff K v hab, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  simp

theorem diagUnits2_mul_unipotentGL2 (t₁ t₂ : Kvˣ) (y : Kv) :
    diagUnits2 t₁ t₂ * unipotentGL2 y = unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ := by
  apply Units.ext
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotentGL2_inv (y : Kv) : (unipotentGL2 y)⁻¹ = unipotentGL2 (-y) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]

theorem diagUnits2_mul_diagUnits2 (s₁ s₂ t₁ t₂ : Kvˣ) :
    diagUnits2 s₁ s₂ * diagUnits2 t₁ t₂ = (diagUnits2 (s₁ * t₁) (s₂ * t₂) : GL (Fin 2) Kv) := by
  apply Units.ext
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_inv (t₁ t₂ : Kvˣ) : (diagUnits2 t₁ t₂ : GL (Fin 2) Kv)⁻¹ = diagUnits2 t₁⁻¹ t₂⁻¹ := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, diagUnits2_mul_diagUnits2, inv_mul_cancel, inv_mul_cancel]
  apply Units.ext
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem coe_unipotent_twist_conj (A D : Kvˣ) (y y' : Kv) :
    (((unipotentGL2 y)⁻¹ * diagUnits2 A D * unipotentGL2 y' : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) =
      !![(A : Kv), (A : Kv) * y' - D * y; 0, (D : Kv)] := by
  rw [unipotentGL2_inv, Units.val_mul, Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try ring)

theorem map_diagUnits2 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (s t : Rˣ) :
    Matrix.GeneralLinearGroup.map f (diagUnits2 s t) =
      diagUnits2 (Units.map (f : R →* S) s) (Units.map (f : R →* S) t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem map_unipotentGL2 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (y : R) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (unipotentGL2 y) = unipotentGL2 (f y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Algebra

section Iwasawa

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem mem_localIntegralSet_of_mem_integralSubgroup {g : GL (Fin 2) Kv}
    (hg : g ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) Kv) : g ∈ localIntegralSet K v := by
  obtain ⟨k, rfl⟩ := hg
  refine (mem_localIntegralSet K v).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · exact ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2
  · rw [← map_inv]
    exact (((k⁻¹ : GL (Fin 2) (v.adicCompletionIntegers K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j).2

theorem iwasawa (x : GL (Fin 2) Kv) :
    ∃ (t₁ t₂ : Kvˣ) (y : Kv) (k : GL (Fin 2) Kv), k ∈ localIntegralSet K v ∧
      x = diagUnits2 t₁ t₂ * unipotentGL2 y * k := by
  obtain ⟨b, k, hk, hb10, rfl⟩ :=
    LocalGL2.iwasawa_decomposition (v.adicCompletionIntegers K) Kv x
  have hdet : (b : Matrix (Fin 2) (Fin 2) Kv).det ≠ 0 := (Matrix.isUnits_det_units b).ne_zero
  rw [Matrix.det_fin_two, hb10, mul_zero, sub_zero] at hdet
  have h00 : (b : Matrix (Fin 2) (Fin 2) Kv) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h11 : (b : Matrix (Fin 2) (Fin 2) Kv) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 _ h00, Units.mk0 _ h11,
    (b : Matrix (Fin 2) (Fin 2) Kv) 0 1 * ((b : Matrix (Fin 2) (Fin 2) Kv) 0 0)⁻¹, k,
    mem_localIntegralSet_of_mem_integralSubgroup K v hk, ?_⟩
  congr 1
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb10]
  rw [mul_comm ((b : Matrix (Fin 2) (Fin 2) Kv) 0 0), mul_assoc, inv_mul_cancel₀ h00, mul_one]

end Iwasawa

namespace WeightKit

open AutomorphicForm.LocalWeight

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

end Ultra

theorem weight_unipotentGL2 (y : F) : weight (unipotentGL2 y) = 2 * Real.log (max 1 ‖y‖) := by
  rw [weight_eq, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

end WeightKit

section Instances

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

theorem secondCountableTopology_GL : SecondCountableTopology (GL (Fin 2) Kv) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → Kv))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) Kv)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem continuous_unipotentGL2' : Continuous (fun y : Kv => (unipotentGL2 y : GL (Fin 2) Kv)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun y : Kv => ((unipotentGL2 y : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv))
    simp only [unipotentGL2_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun y : Kv => (((unipotentGL2 y)⁻¹ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv)) =
        fun y => !![1, -y; 0, 1] := rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem weight_unipotentGL2_mul {y : Kv} {k : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v) :
    LocalWeight.weight (unipotentGL2 y * k) = 2 * Real.log (max 1 ‖y‖) := by
  have hK := (mem_localIntegralSet_iff_norm K v k).1 hk
  have hK' := (mem_localIntegralSet_iff_norm K v k⁻¹).1 (inv_mem_localIntegralSet K v hk)
  rw [WeightKit.weight_mul_of_norm_le_one _ _ hK.1 hK'.1 hK.2, WeightKit.weight_unipotentGL2]

theorem norm_sub_le_one_of_eq {y y' : Kv} {k k' : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v)
    (hk' : k' ∈ localIntegralSet K v) (h : unipotentGL2 y * k = unipotentGL2 y' * k') : ‖y' - y‖ ≤ 1 := by
  have h2 : unipotentGL2 (y' - y) = k * k'⁻¹ := by
    rw [sub_eq_neg_add, unipotentGL2_add, ← unipotentGL2_inv K v, eq_mul_inv_iff_mul_eq, mul_assoc, ← h,
      ← mul_assoc, inv_mul_cancel, one_mul]
  rw [← unipotentGL2_mem_iff K v, h2]
  exact mul_mem_localIntegralSet K v hk (inv_mem_localIntegralSet K v hk')

def NK : Set (GL (Fin 2) Kv) := {x | ∃ (y : Kv) (k : GL (Fin 2) Kv), k ∈ localIntegralSet K v ∧ x = unipotentGL2 y * k}

theorem diag_mul_mem_NK_iff (t₁ t₂ : Kvˣ) (y : Kv) {k : GL (Fin 2) Kv} (hk : k ∈ localIntegralSet K v) :
    diagUnits2 t₁ t₂ * unipotentGL2 y * k ∈ NK K v ↔ diagUnits2 t₁ t₂ ∈ localIntegralSet K v := by
  rw [diagUnits2_mul_unipotentGL2]
  constructor
  · rintro ⟨y', k', hk', h⟩
    have h2 : (unipotentGL2 y')⁻¹ * unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ = k' * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      calc (unipotentGL2 y')⁻¹ * unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ * k
          = (unipotentGL2 y')⁻¹ * (unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ * k) := by
            simp only [mul_assoc]
        _ = k' := by rw [h, inv_mul_cancel_left]
    have hmem : (unipotentGL2 y')⁻¹ * unipotentGL2 ((t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)) * diagUnits2 t₁ t₂ ∈
        localIntegralSet K v := by
      rw [h2]; exact mul_mem_localIntegralSet K v hk' (inv_mem_localIntegralSet K v hk)
    rw [unipotentGL2_inv, ← unipotentGL2_add] at hmem
    set z : Kv := -y' + (t₁ : Kv) * y * (t₂⁻¹ : Kvˣ)
    have hM : ((unipotentGL2 z * diagUnits2 t₁ t₂ : GL (Fin 2) Kv) : Matrix (Fin 2) (Fin 2) Kv) =
        !![(t₁ : Kv), z * (t₂ : Kv); 0, (t₂ : Kv)] := by
      rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, unipotentGL2_coe]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    obtain ⟨ha, hb, -⟩ := (upper_mem_iff K v hM).1 hmem
    exact (diagUnits2_mem_iff K v t₁ t₂).2 ⟨ha, hb⟩
  · intro hd
    exact ⟨_, diagUnits2 t₁ t₂ * k, mul_mem_localIntegralSet K v hd hk, by rw [mul_assoc]⟩

end Instances

section Unramified

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

scoped instance isScalarTower_int : IsScalarTower (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem liesOver : w.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
include hw

theorem v_algebraMap (x : Kv) :
    (Valued.v (algebraMap Kv Lw x) : WithZero (Multiplicative ℤ)) = Valued.v x := by
  change Valued.v (w.adicCompletionSemialgHom K L x) = _
  rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w x, hw, pow_one]

theorem norm_algebraMap_eq_one_iff (x : Kv) : ‖algebraMap Kv Lw x‖ = 1 ↔ ‖x‖ = 1 := by
  rw [norm_eq_one_iff_v, norm_eq_one_iff_v, v_algebraMap K L v w hw]

theorem norm_algebraMap_uniformizer {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) :
    ‖algebraMap Kv Lw ϖ‖ = (qv L w.1)⁻¹ := by
  have h1 := v_eq_exp_of_norm_eq_zpow K v (k := -1) (by rw [hϖ, zpow_neg, zpow_one])
  rw [← v_algebraMap K L v w hw] at h1
  rw [norm_eq_zpow_of_v_eq_exp L w.1 h1, zpow_neg, zpow_one]

theorem exists_eq_algebraMap_mul_unit {y : Lw} (hy : y ≠ 0) :
    ∃ x : Kv, x ≠ 0 ∧ (Valued.v (y * (algebraMap Kv Lw x)⁻¹) : WithZero (Multiplicative ℤ)) = 1 := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v
    (Valued.v y : WithZero (Multiplicative ℤ))
  have hy0 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact hy0 hx.symm
  refine ⟨x, hx0, ?_⟩
  rw [map_mul, map_inv₀, v_algebraMap K L v w hw, hx, mul_inv_cancel₀ hy0]

theorem qv_w_eq_pow : qv L w.1 = qv K v ^ Module.finrank Kv Lw := by
  have hef := HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w
  have hw' : v.asIdeal.ramificationIdx' w.1.asIdeal = 1 := by
    have h2 : HeightOneSpectrum.under (𝓞 K) w.1 = v := w.2
    have h3 := hw
    rw [h2] at h3
    exact h3
  rw [hw', one_mul] at hef
  haveI := liesOver K L v w
  unfold qv
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot, hef]
  push_cast
  rfl

omit hw in

theorem isIntegral_of_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) :
    IsIntegral (v.adicCompletionIntegers K) y := by
  haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.of_finite _ _
  have h : IsIntegral (v.adicCompletionIntegers K) (⟨y, hy⟩ : w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.isIntegral _
  exact h.map (IsScalarTower.toAlgHom (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L))

omit hw in

theorem mem_of_isIntegral {y : Lw} (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    y ∈ w.1.adicCompletionIntegers L := by
  have h2 : IsIntegral (w.1.adicCompletionIntegers L) y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.1.adicCompletionIntegers L)
    (K := w.1.adicCompletion L)).1 h2
  rw [← hz]
  exact z.2

variable (θ : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))

omit hw in

theorem theta_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) : θ y ∈ w.1.adicCompletionIntegers L := by
  apply mem_of_isIntegral K L v w
  exact (isIntegral_of_mem K L v w hy).map (θ.restrictScalars (v.adicCompletionIntegers K)).toAlgHom

omit hw in

theorem v_theta_eq_one {y : Lw} (hy : (Valued.v y : WithZero (Multiplicative ℤ)) = 1) :
    (Valued.v (θ y) : WithZero (Multiplicative ℤ)) = 1 := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
  have h1 : θ y ∈ w.1.adicCompletionIntegers L :=
    theta_mem K L v w θ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hy.le)
  have h2 : θ y⁻¹ ∈ w.1.adicCompletionIntegers L :=
    theta_mem K L v w θ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hy, inv_one]))
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h3 : (Valued.v (θ y) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ θ.injective).2 hy0)
  exact le_antisymm h1 (by rwa [inv_le_one₀ (zero_lt_iff.2 h3)] at h2)

theorem v_theta (y : Lw) : (Valued.v (θ y) : WithZero (Multiplicative ℤ)) = Valued.v y := by
  by_cases hy : y = 0
  · rw [hy, map_zero]
  obtain ⟨x, hx0, hu⟩ := exists_eq_algebraMap_mul_unit K L v w hw hy
  have ha0 : algebraMap Kv Lw x ≠ 0 := (map_ne_zero _).2 hx0
  have hy' : y = (y * (algebraMap Kv Lw x)⁻¹) * algebraMap Kv Lw x := by
    rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  conv_lhs => rw [hy', map_mul, AlgEquiv.commutes, map_mul, v_theta_eq_one K L v w θ hu]
  conv_rhs => rw [hy', map_mul, hu]

theorem norm_theta (y : Lw) : ‖θ y‖ = ‖y‖ := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, v_theta K L v w hw θ]

theorem norm_theta_pow (i : ℕ) (y : Lw) : ‖(θ ^ i) y‖ = ‖y‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, norm_theta K L v w hw, ih]

theorem norm_eq_one_iff_of_normString {ℓ : ℕ} (hℓ : 0 < ℓ) (α : Lw) (a : Kv)
    (h : ∏ i ∈ Finset.range ℓ, (θ ^ i) α = algebraMap Kv Lw a) : ‖α‖ = 1 ↔ ‖a‖ = 1 := by
  have key : ‖algebraMap Kv Lw a‖ = ‖α‖ ^ ℓ := by
    rw [← h, norm_prod, Finset.prod_congr rfl fun i _ => norm_theta_pow K L v w hw θ i α, Finset.prod_const,
      Finset.card_range]
  rw [← norm_algebraMap_eq_one_iff K L v w hw, key]
  constructor
  · intro h1; rw [h1, one_pow]
  · intro h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hℓ.ne').1 h1

theorem map_theta_mem_iff (g : GL (Fin 2) Lw) :
    Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom g ∈ localIntegralSet L w.1 ↔ g ∈ localIntegralSet L w.1 := by
  have hval : ((Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom g : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) =
      (g : Matrix (Fin 2) (Fin 2) Lw).map θ.toAlgHom.toRingHom := by
    simp only [Matrix.GeneralLinearGroup.val_map_apply]
  have hdet : ((g : Matrix (Fin 2) (Fin 2) Lw).map θ.toAlgHom.toRingHom).det = θ (g : Matrix (Fin 2) (Fin 2) Lw).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [mem_localIntegralSet_iff_norm, mem_localIntegralSet_iff_norm, hval, hdet]
  change (∀ i j, ‖θ ((g : Matrix (Fin 2) (Fin 2) Lw) i j)‖ ≤ 1) ∧ ‖θ (g : Matrix (Fin 2) (Fin 2) Lw).det‖ = 1 ↔ _
  simp only [norm_theta K L v w hw θ]

omit hw in

theorem continuous_map_theta : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) θ.toAlgHom.toRingHom) := by
  have hθ : Continuous θ := IsModuleTopology.continuous_of_linearMap θ.toLinearMap
  apply Continuous.units_map
  exact continuous_id.matrix_map hθ

end Unramified

section Shells

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

abbrev OK : AddSubgroup Kv := (v.adicCompletionIntegers K).toAddSubgroup

variable (Λ : AddSubgroup (v.adicCompletion K)) (π : v.adicCompletion K)

def Lam (s : ℕ) : AddSubgroup Kv := Λ ⊓ (OK K v).comap (AddMonoidHom.mulLeft (π ^ s))

theorem mem_Lam (s : ℕ) (y : Kv) : y ∈ Lam K v Λ π s ↔ y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K := by
  rw [Lam, AddSubgroup.mem_inf, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft]
  exact Iff.rfl

def V (s : ℕ) : Set (GL (Fin 2) Kv) :=
  {x | ∃ (y : Kv) (k : GL (Fin 2) Kv), (y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K) ∧
    k ∈ localIntegralSet K v ∧ x = unipotentGL2 y * k}

theorem isOpen_V (s : ℕ) : IsOpen (V K v Λ π s) := by
  have hV : V K v Λ π s = ⋃ y ∈ {y : Kv | y ∈ Λ ∧ π ^ s * y ∈ v.adicCompletionIntegers K},
      (fun k => unipotentGL2 y * k) '' localIntegralSet K v := by
    ext x
    simp only [V, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨y, k, hy, hk, rfl⟩; exact ⟨y, hy, k, hk, rfl⟩
    · rintro ⟨y, hy, k, hk, rfl⟩; exact ⟨y, k, hy, hk, rfl⟩
  rw [hV]
  exact isOpen_biUnion fun y _ => (isOpenMap_mul_left _) _ (isOpen_localIntegralSet K v)

def Uball (s : ℕ) : Set (GL (Fin 2) Kv) :=
  (fun p : Kv × GL (Fin 2) Kv => unipotentGL2 p.1 * p.2) '' ({y : Kv | ‖y‖ ≤ qv K v ^ s} ×ˢ localIntegralSet K v)

theorem isCompact_Uball (s : ℕ) : IsCompact (Uball K v s) := by
  refine IsCompact.image (IsCompact.prod ?_ (isCompact_localIntegralSet K v)) ?_
  · have : {y : Kv | ‖y‖ ≤ qv K v ^ s} = Metric.closedBall 0 (qv K v ^ s) := by
      ext y; simp
    rw [this]
    exact isCompact_closedBall _ _
  · exact ((continuous_unipotentGL2' K v).comp continuous_fst).mul continuous_snd

variable (hπ : ‖π‖ = (qv K v)⁻¹)
include hπ

theorem norm_pi_pow (n : ℕ) : ‖π ^ n‖ = (qv K v ^ n)⁻¹ := by
  rw [norm_pow, hπ, inv_pow]

theorem pow_mul_mem_iff (s : ℕ) (y : Kv) : π ^ s * y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ qv K v ^ s := by
  rw [mem_integers_iff_norm, norm_mul, norm_pi_pow K v π hπ, inv_mul_le_iff₀ (pow_pos (qv_pos K v) _), mul_one]

theorem pow_mul_mem_mono {s t : ℕ} (hst : s ≤ t) {y : Kv} (hy : π ^ s * y ∈ v.adicCompletionIntegers K) :
    π ^ t * y ∈ v.adicCompletionIntegers K := by
  rw [pow_mul_mem_iff K v π hπ] at hy ⊢
  exact hy.trans (pow_le_pow_right₀ (one_lt_qv K v).le hst)

theorem Lam_mono {s t : ℕ} (hst : s ≤ t) : Lam K v Λ π s ≤ Lam K v Λ π t := by
  intro y hy
  rw [mem_Lam] at hy ⊢
  exact ⟨hy.1, pow_mul_mem_mono K v π hπ hst hy.2⟩

theorem V_subset_Uball (s : ℕ) : V K v Λ π s ⊆ Uball K v s := by
  rintro x ⟨y, k, hy, hk, rfl⟩
  exact ⟨(y, k), ⟨(pow_mul_mem_iff K v π hπ s y).1 hy.2, hk⟩, rfl⟩

attribute [local instance] AutomorphicForm.localGLBorel in

theorem shells (m : ℕ) (hfin : ∀ s ≤ m, (OK K v).relIndex (Lam K v Λ π s) ≠ 0) :
    (∀ s ≤ m, localHaar K v (V K v Λ π s) = (OK K v).relIndex (Lam K v Λ π s)) ∧
    (∫ x in V K v Λ π m, LocalWeight.weight x ∂(localHaar K v)) =
      2 * Real.log (qv K v) * ∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) *
        (((OK K v).relIndex (Lam K v Λ π (s + 1)) : ℝ) - ((OK K v).relIndex (Lam K v Λ π s) : ℝ)) :=
  AutomorphicForm.localHaar_setOf_unipotentGL2_mul_eq_relIndex_and_setIntegral_weight_eq_of_norm_eq_inv
    K v Λ π hπ m hfin

end Shells

section Twisted

open scoped Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)
local notation "θG" => Matrix.GeneralLinearGroup.map (AlgHom.toRingHom (AlgEquiv.toAlgHom θ))
local notation "θU" => Units.map (MonoidHomClass.toMonoidHom (AlgHom.toRingHom (AlgEquiv.toAlgHom θ)))

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.isHaarMeasure_localHaar AutomorphicForm.locallyCompactSpace_localGL secondCountableTopology_GL

theorem thG_unipotentGL2 (y : Lw) : θG (unipotentGL2 y) = unipotentGL2 (θ y) :=
  map_unipotentGL2 _ y

theorem thG_diagUnits2 (t₁ t₂ : Lwˣ) : θG (diagUnits2 t₁ t₂) = diagUnits2 (θU t₁) (θU t₂) :=
  map_diagUnits2 _ _ _

theorem coe_thU (t : Lwˣ) : ((θU t : Lwˣ) : Lw) = θ t := rfl

def TorusHyp (a b : Kvˣ) (α β : Lwˣ) : Prop :=
  sigmaCentralizer θG (diagUnits2 α β) =
    (localCentralizer K v (diagUnits2 a b)).map (Matrix.GeneralLinearGroup.map (algebraMap Kv Lw))

theorem mem_torus_iff {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (t : GL (Fin 2) Lw) :
    t ∈ sigmaCentralizer θG (diagUnits2 α β) ↔ ∃ t₁ t₂ : Kvˣ,
      t = diagUnits2 (Units.map (algebraMap Kv Lw : Kv →* Lw) t₁) (Units.map (algebraMap Kv Lw : Kv →* Lw) t₂) := by
  rw [show sigmaCentralizer θG (diagUnits2 α β) = _ from hT, Subgroup.mem_map]
  constructor
  · rintro ⟨t', ht', rfl⟩
    obtain ⟨h01, h10⟩ := (mem_centralizer_iff K v hab t').1 ht'
    refine ⟨Units.mk0 _ (diag_ne_zero_of_offdiag K v h01).1, Units.mk0 _ (diag_ne_zero_of_offdiag K v h01).2, ?_⟩
    conv_lhs => rw [eq_diagUnits2_of_offdiag K v h01 h10]
    exact map_diagUnits2 _ _ _
  · rintro ⟨t₁, t₂, rfl⟩
    exact ⟨diagUnits2 t₁ t₂, diagUnits2_mem_centralizer K v hab t₁ t₂, map_diagUnits2 _ _ _⟩

theorem torus_offdiag {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (t : sigmaCentralizer θG (diagUnits2 α β)) :
    ((t : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) 0 1 = 0 ∧ ((t : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) 1 0 = 0 := by
  obtain ⟨t₁, t₂, ht⟩ := (mem_torus_iff K L v w θ hab hT t).1 t.2
  rw [ht, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  simp

theorem torus_eq_diag {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (t : sigmaCentralizer θG (diagUnits2 α β)) :
    (t : GL (Fin 2) Lw) = diagUnits2 (Units.mk0 _ (diag_ne_zero_of_offdiag L w.1 (torus_offdiag K L v w θ hab hT t).1).1)
      (Units.mk0 _ (diag_ne_zero_of_offdiag L w.1 (torus_offdiag K L v w θ hab hT t).1).2) :=
  eq_diagUnits2_of_offdiag L w.1 (torus_offdiag K L v w θ hab hT t).1 (torus_offdiag K L v w θ hab hT t).2

theorem torus_comm {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (s t : sigmaCentralizer θG (diagUnits2 α β)) : s * t = t * s := by
  obtain ⟨s01, s10⟩ := torus_offdiag K L v w θ hab hT s
  obtain ⟨t01, t10⟩ := torus_offdiag K L v w θ hab hT t
  apply Subtype.ext
  apply Units.ext
  change ((s : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) * ((t : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) =
    ((t : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw) * ((s : GL (Fin 2) Lw) : Matrix (Fin 2) (Fin 2) Lw)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, s01, s10, t01, t10, mul_comm]

theorem weight_torus_mul {a b : Kvˣ} (hab : a ≠ b) {α β : Lwˣ} (hT : TorusHyp K L v w θ a b α β)
    (t : sigmaCentralizer θG (diagUnits2 α β)) (x : GL (Fin 2) Lw) :
    LocalWeight.weight ((t : GL (Fin 2) Lw) * x) = LocalWeight.weight x := by
  rw [torus_eq_diag K L v w θ hab hT t]
  exact WeightKit.weight_diagUnits2_mul _ _ x

theorem isClosed_torus (α β : Lwˣ) :
    IsClosed ((sigmaCentralizer θG (diagUnits2 α β) : Subgroup (GL (Fin 2) Lw)) : Set (GL (Fin 2) Lw)) := by
  have : ((sigmaCentralizer θG (diagUnits2 α β) : Subgroup (GL (Fin 2) Lw)) : Set (GL (Fin 2) Lw)) =
      {t | t * diagUnits2 α β * (θG t)⁻¹ = diagUnits2 α β} := rfl
  rw [this]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul ((continuous_map_theta K L v w θ).comp continuous_id).inv)
    continuous_const

def Fδ (α β : Lwˣ) (x : GL (Fin 2) Lw) : ℂ :=
  (localIntegralSet L w.1).indicator (fun _ => (1 : ℂ)) (x⁻¹ * diagUnits2 α β * θG x)

theorem Fδ_apply (α β : Lwˣ) (x : GL (Fin 2) Lw) :
    Fδ K L v w θ α β x = if x⁻¹ * diagUnits2 α β * θG x ∈ localIntegralSet L w.1 then 1 else 0 := by
  rw [Fδ, Set.indicator_apply]

theorem Fδ_ne_zero_iff (α β : Lwˣ) (x : GL (Fin 2) Lw) :
    Fδ K L v w θ α β x ≠ 0 ↔ x⁻¹ * diagUnits2 α β * θG x ∈ localIntegralSet L w.1 := by
  rw [Fδ_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hc; exact h (if_neg hc)
  · rw [if_pos h]; exact one_ne_zero

theorem Fδ_eq_one_of_mem {α β : Lwˣ} {x : GL (Fin 2) Lw} (h : x⁻¹ * diagUnits2 α β * θG x ∈ localIntegralSet L w.1) :
    Fδ K L v w θ α β x = 1 := by
  rw [Fδ_apply, if_pos h]

theorem norm_Fδ_le_one (α β : Lwˣ) (x : GL (Fin 2) Lw) : ‖Fδ K L v w θ α β x‖ ≤ 1 := by
  rw [Fδ_apply]; split_ifs <;> simp

theorem continuous_twistedConj (α β : Lwˣ) : Continuous fun x : GL (Fin 2) Lw => x⁻¹ * diagUnits2 α β * θG x :=
  (continuous_id.inv.mul continuous_const).mul ((continuous_map_theta K L v w θ).comp continuous_id)

theorem measurable_Fδ (α β : Lwˣ) : Measurable (Fδ K L v w θ α β) := by
  have : Fδ K L v w θ α β =
      ((fun x : GL (Fin 2) Lw => x⁻¹ * diagUnits2 α β * θG x) ⁻¹' localIntegralSet L w.1).indicator fun _ => (1 : ℂ) := by
    funext x
    simp only [Fδ, Set.indicator_apply, Set.mem_preimage]
  rw [this]
  exact measurable_const.indicator
    (((isOpen_localIntegralSet L w.1).preimage (continuous_twistedConj K L v w θ α β)).measurableSet)

theorem Fδ_torus_mul {α β : Lwˣ} (t : sigmaCentralizer θG (diagUnits2 α β)) (x : GL (Fin 2) Lw) :
    Fδ K L v w θ α β ((t : GL (Fin 2) Lw) * x) = Fδ K L v w θ α β x := by
  have ht : ((t : GL (Fin 2) Lw))⁻¹ * diagUnits2 α β * θG (t : GL (Fin 2) Lw) = diagUnits2 α β :=
    mem_sigmaCentralizer_iff_inv.1 t.2
  unfold Fδ
  congr 1
  rw [mul_inv_rev, map_mul]
  calc x⁻¹ * ((t : GL (Fin 2) Lw))⁻¹ * diagUnits2 α β * (θG (t : GL (Fin 2) Lw) * θG x)
      = x⁻¹ * (((t : GL (Fin 2) Lw))⁻¹ * diagUnits2 α β * θG (t : GL (Fin 2) Lw)) * θG x := by
        simp only [mul_assoc]
    _ = x⁻¹ * diagUnits2 α β * θG x := by rw [ht]

theorem twistedConj_eq (α β t₁ t₂ : Lwˣ) (y : Lw) (k : GL (Fin 2) Lw) :
    (diagUnits2 t₁ t₂ * unipotentGL2 y * k)⁻¹ * diagUnits2 α β * θG (diagUnits2 t₁ t₂ * unipotentGL2 y * k) =
      k⁻¹ * ((unipotentGL2 y)⁻¹ * diagUnits2 (t₁⁻¹ * α * θU t₁) (t₂⁻¹ * β * θU t₂) * unipotentGL2 (θ y)) * θG k := by
  rw [map_mul, map_mul, thG_diagUnits2, thG_unipotentGL2, ← diagUnits2_mul_diagUnits2, ← diagUnits2_mul_diagUnits2,
    ← diagUnits2_inv]
  simp only [mul_inv_rev, mul_assoc]

theorem norm_coe_twistUnit (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (t α : Lwˣ) : ‖((t⁻¹ * α * θU t : Lwˣ) : Lw)‖ = ‖(α : Lw)‖ := by
  rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, coe_thU, norm_mul, norm_mul, norm_inv,
    norm_theta K L v w hw θ]
  have h : ‖(t : Lw)‖ ≠ 0 := norm_ne_zero_iff.2 t.ne_zero
  field_simp

theorem twistedConj_mem_iff (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (α β t₁ t₂ : Lwˣ) (y : Lw) {k : GL (Fin 2) Lw} (hk : k ∈ localIntegralSet L w.1) :
    (diagUnits2 t₁ t₂ * unipotentGL2 y * k)⁻¹ * diagUnits2 α β * θG (diagUnits2 t₁ t₂ * unipotentGL2 y * k) ∈
        localIntegralSet L w.1 ↔
      ‖(α : Lw)‖ = 1 ∧ ‖(β : Lw)‖ = 1 ∧
        ‖((t₁⁻¹ * α * θU t₁ : Lwˣ) : Lw) * θ y - ((t₂⁻¹ * β * θU t₂ : Lwˣ) : Lw) * y‖ ≤ 1 := by
  rw [twistedConj_eq, mul_mem_localIntegralSet_iff_left L w.1 ((map_theta_mem_iff K L v w hw θ k).2 hk),
    mul_mem_localIntegralSet_iff_right L w.1 (inv_mem_localIntegralSet L w.1 hk),
    upper_mem_iff L w.1 (coe_unipotent_twist_conj L w.1 _ _ y (θ y)), norm_coe_twistUnit K L v w θ hw,
    norm_coe_twistUnit K L v w θ hw]

theorem units_of_Fδ_ne_zero (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    {α β : Lwˣ} {x : GL (Fin 2) Lw} (hx : Fδ K L v w θ α β x ≠ 0) : ‖(α : Lw)‖ = 1 ∧ ‖(β : Lw)‖ = 1 := by
  rw [Fδ_ne_zero_iff] at hx
  obtain ⟨t₁, t₂, y, k, hk, rfl⟩ := iwasawa L w.1 x
  obtain ⟨ha, hb, -⟩ := (twistedConj_mem_iff K L v w θ hw α β t₁ t₂ y hk).1 hx
  exact ⟨ha, hb⟩

theorem Fδ_unipotent_mul_ne_zero_iff (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (α β : Lwˣ) (y : Lw) {k : GL (Fin 2) Lw} (hk : k ∈ localIntegralSet L w.1) :
    Fδ K L v w θ α β (unipotentGL2 y * k) ≠ 0 ↔
      ‖(α : Lw)‖ = 1 ∧ ‖(β : Lw)‖ = 1 ∧ ‖(α : Lw) * θ y - β * y‖ ≤ 1 := by
  have h := twistedConj_mem_iff K L v w θ hw α β 1 1 y hk
  have h11 : (diagUnits2 1 1 : GL (Fin 2) Lw) = 1 := by
    apply Units.ext
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [h11, one_mul] at h
  rw [Fδ_ne_zero_iff, h]
  simp

def LamC (c : Lw) : AddSubgroup Lw :=
  (w.1.adicCompletionIntegers L).toAddSubgroup.comap
    ((AlgHom.toRingHom (AlgEquiv.toAlgHom θ)).toAddMonoidHom - AddMonoidHom.mulLeft c)

theorem mem_LamC (c y : Lw) : y ∈ LamC K L v w θ c ↔ θ y - c * y ∈ w.1.adicCompletionIntegers L := by
  rw [LamC, AddSubgroup.mem_comap, AddMonoidHom.sub_apply, AddMonoidHom.coe_mulLeft]
  exact Iff.rfl

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

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] (T : Subgroup G) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] (τ : Measure T) [τ.IsMulLeftInvariant] : τ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun t : T => t * g) = fun t : T => g * t := funext fun t => hcomm t g
  rw [this]
  exact map_mul_left_eq_self τ g

section UnitCase

variable {α β : (w.1.adicCompletion L)ˣ} (ha1 : ‖(α : w.1.adicCompletion L)‖ = 1)
  (hb1 : ‖(β : w.1.adicCompletion L)‖ = 1)
include ha1 hb1

theorem norm_c : ‖((β * α⁻¹ : Lwˣ) : Lw)‖ = 1 := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, ha1, hb1, inv_one, mul_one]

omit hb1 in
theorem norm_key (y : Lw) : ‖(α : Lw) * θ y - β * y‖ = ‖θ y - ((β * α⁻¹ : Lwˣ) : Lw) * y‖ := by
  have h : (α : Lw) * θ y - β * y = α * (θ y - ((β * α⁻¹ : Lwˣ) : Lw) * y) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_sub, mul_comm (β : Lw) ((α : Lw)⁻¹), ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ α.ne_zero, one_mul]
  rw [h, norm_mul, ha1, one_mul]

theorem Fδ_unipotent_mul_ne_zero_iff_mem
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (y : Lw) {k : GL (Fin 2) Lw} (hk : k ∈ localIntegralSet L w.1) :
    Fδ K L v w θ α β (unipotentGL2 y * k) ≠ 0 ↔ y ∈ LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw) := by
  rw [Fδ_unipotent_mul_ne_zero_iff K L v w θ hw α β y hk, mem_LamC, mem_integers_iff_norm, norm_key K L v w θ ha1]
  simp [ha1, hb1]

theorem OK_le_Lam (π : Lw) (hπ : ‖π‖ = (qv L w.1)⁻¹) (s : ℕ) :
    OK L w.1 ≤ Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π s := by
  intro y hy
  change y ∈ w.1.adicCompletionIntegers L at hy
  rw [mem_Lam, mem_LamC]
  refine ⟨sub_mem (theta_mem K L v w θ hy) ?_, ?_⟩
  · rw [mem_integers_iff_norm] at hy ⊢
    rw [norm_mul, norm_c K L v w ha1 hb1, one_mul]; exact hy
  · rw [pow_mul_mem_iff L w.1 π hπ]
    exact ((mem_integers_iff_norm L w.1 y).1 hy).trans (one_le_pow₀ (one_lt_qv L w.1).le)

variable (π : w.1.adicCompletion L) (hπ : ‖π‖ = (qv L w.1)⁻¹) (M : ℕ)
  (hidx : ∀ s : ℕ, (OK L w.1).relIndex
    (Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L)) π s) =
      Ideal.absNorm v.asIdeal ^ min s M)
include hπ hidx

theorem Lam_eq_of_le {s : ℕ} (hs : M ≤ s) :
    Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π s = Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M := by
  have hle := Lam_mono L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π hπ hs
  have h := AddSubgroup.relIndex_mul_relIndex (OK L w.1) _ _ (OK_le_Lam K L v w θ ha1 hb1 π hπ M) hle
  rw [hidx M, hidx s, min_self, min_eq_right hs] at h
  have hq : Ideal.absNorm v.asIdeal ^ M ≠ 0 :=
    pow_ne_zero _ (by have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega)
  have h1 : (Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M).relIndex
      (Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π s) = 1 :=
    (mul_right_inj' hq).1 (by rw [h, mul_one])
  exact le_antisymm (AddSubgroup.relIndex_eq_one.1 h1) hle

theorem mem_LamM_of_mem_LamC {y : Lw} (hy : y ∈ LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) :
    y ∈ Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M := by
  rcases norm_eq_zero_or_zpow L w.1 y with h0 | ⟨n, hn⟩
  · rw [norm_eq_zero] at h0
    rw [h0]; exact zero_mem _
  · have hN : y ∈ Lam L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π (max n.toNat M) := by
      rw [mem_Lam, pow_mul_mem_iff L w.1 π hπ, hn]
      refine ⟨hy, ?_⟩
      have h1 : (n : ℤ) ≤ ((max n.toNat M : ℕ) : ℤ) := (Int.self_le_toNat n).trans (by exact_mod_cast le_max_left _ _)
      have := zpow_le_zpow_right₀ (one_lt_qv L w.1).le h1
      rwa [zpow_natCast] at this
    rwa [Lam_eq_of_le K L v w θ ha1 hb1 π hπ M hidx (le_max_right _ _)] at hN

theorem mem_V_iff (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (x : GL (Fin 2) Lw) :
    x ∈ V L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M ↔ x ∈ NK L w.1 ∧ Fδ K L v w θ α β x ≠ 0 := by
  constructor
  · rintro ⟨y, k, hy, hk, rfl⟩
    exact ⟨⟨y, k, hk, rfl⟩, (Fδ_unipotent_mul_ne_zero_iff_mem K L v w θ ha1 hb1 hw y hk).2 hy.1⟩
  · rintro ⟨⟨y, k, hk, rfl⟩, hx⟩
    have hy := (Fδ_unipotent_mul_ne_zero_iff_mem K L v w θ ha1 hb1 hw y hk).1 hx
    exact ⟨y, k, (mem_Lam L w.1 _ π M y).1 (mem_LamM_of_mem_LamC K L v w θ ha1 hb1 π hπ M hidx hy), hk, rfl⟩

theorem integral_indicator_V_translate
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    {a b : Kvˣ} (hab : a ≠ b) (hT : TorusHyp K L v w θ a b α β)
    (τ' : @Measure (sigmaCentralizer θG (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) Lw) ∈ localIntegralSet L w.1} = 1)
    (x : GL (Fin 2) Lw) (hx : Fδ K L v w θ α β x ≠ 0) :
    (letI : MeasurableSpace (sigmaCentralizer θG (diagUnits2 α β)) := borel _
     ∫ t : sigmaCentralizer θG (diagUnits2 α β),
        (V L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M).indicator (fun _ => (1 : ℝ)) ((t : GL (Fin 2) Lw) * x) ∂τ') = 1 := by
  letI : MeasurableSpace (sigmaCentralizer θG (diagUnits2 α β)) := borel _
  haveI : BorelSpace (sigmaCentralizer θG (diagUnits2 α β)) := ⟨rfl⟩
  haveI := hτ'
  haveI : τ'.IsMulRightInvariant := isMulRightInvariant_of_comm _ (torus_comm K L v w θ hab hT) τ'
  obtain ⟨t₁, t₂, y, k, hk, rfl⟩ := iwasawa L w.1 x

  have hset : ∀ t : sigmaCentralizer θG (diagUnits2 α β),
      (t : GL (Fin 2) Lw) * (diagUnits2 t₁ t₂ * unipotentGL2 y * k) ∈ V L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M ↔
        (t : GL (Fin 2) Lw) * diagUnits2 t₁ t₂ ∈ localIntegralSet L w.1 := by
    intro t
    rw [mem_V_iff K L v w θ ha1 hb1 π hπ M hidx hw, Fδ_torus_mul, and_iff_left hx, torus_eq_diag K L v w θ hab hT t,
      ← mul_assoc, ← mul_assoc, diagUnits2_mul_diagUnits2, diag_mul_mem_NK_iff L w.1 _ _ y hk]

  obtain ⟨x₁, hx₁, hu₁⟩ := exists_eq_algebraMap_mul_unit K L v w hw t₁.ne_zero
  obtain ⟨x₂, hx₂, hu₂⟩ := exists_eq_algebraMap_mul_unit K L v w hw t₂.ne_zero
  set t₀ : sigmaCentralizer θG (diagUnits2 α β) :=
    ⟨diagUnits2 (Units.map (algebraMap Kv Lw : Kv →* Lw) (Units.mk0 x₁ hx₁)⁻¹)
        (Units.map (algebraMap Kv Lw : Kv →* Lw) (Units.mk0 x₂ hx₂)⁻¹),
      (mem_torus_iff K L v w θ hab hT _).2 ⟨(Units.mk0 x₁ hx₁)⁻¹, (Units.mk0 x₂ hx₂)⁻¹, rfl⟩⟩ with ht₀
  have ht₀d : (t₀ : GL (Fin 2) Lw) * diagUnits2 t₁ t₂ ∈ localIntegralSet L w.1 := by
    change diagUnits2 _ _ * diagUnits2 t₁ t₂ ∈ localIntegralSet L w.1
    rw [diagUnits2_mul_diagUnits2, diagUnits2_mem_iff, norm_eq_one_iff_v, norm_eq_one_iff_v]
    constructor
    · rw [Units.val_mul, map_inv, Units.val_inv_eq_inv_val, Units.coe_map, mul_comm]; exact hu₁
    · rw [Units.val_mul, map_inv, Units.val_inv_eq_inv_val, Units.coe_map, mul_comm]; exact hu₂
  have hset2 : ∀ t : sigmaCentralizer θG (diagUnits2 α β),
      (t : GL (Fin 2) Lw) * diagUnits2 t₁ t₂ ∈ localIntegralSet L w.1 ↔
        ((t * t₀⁻¹ : sigmaCentralizer θG (diagUnits2 α β)) : GL (Fin 2) Lw) ∈ localIntegralSet L w.1 := by
    intro t
    have : (t : GL (Fin 2) Lw) * diagUnits2 t₁ t₂ =
        ((t * t₀⁻¹ : sigmaCentralizer θG (diagUnits2 α β)) : GL (Fin 2) Lw) * ((t₀ : GL (Fin 2) Lw) * diagUnits2 t₁ t₂) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
    rw [this, mul_mem_localIntegralSet_iff_left L w.1 ht₀d]
  have hfun : (fun t : sigmaCentralizer θG (diagUnits2 α β) =>
        (V L w.1 (LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw)) π M).indicator (fun _ => (1 : ℝ))
          ((t : GL (Fin 2) Lw) * (diagUnits2 t₁ t₂ * unipotentGL2 y * k))) =
      ((fun t => t * t₀⁻¹) ⁻¹' {t : sigmaCentralizer θG (diagUnits2 α β) | (t : GL (Fin 2) Lw) ∈ localIntegralSet L w.1}).indicator
        fun _ => (1 : ℝ) := by
    funext t
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_setOf_eq, hset t, hset2 t]
  have hmeas : MeasurableSet {t : sigmaCentralizer θG (diagUnits2 α β) | (t : GL (Fin 2) Lw) ∈ localIntegralSet L w.1} :=
    ((isOpen_localIntegralSet L w.1).preimage continuous_subtype_val).measurableSet
  rw [hfun, integral_indicator_const _ (measurableSet_preimage (measurable_mul_const _) hmeas), smul_eq_mul, mul_one,
    measureReal_def, measure_preimage_mul_right, hτ'1, ENNReal.toReal_one]

end UnitCase

end Twisted

section Main

open scoped Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

attribute [local instance] AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel
  AutomorphicForm.isHaarMeasure_localHaar AutomorphicForm.locallyCompactSpace_localGL secondCountableTopology_GL

omit [NumberField K] in

theorem shellSum_eq (q : ℝ) (hq : q ≠ 0) (M : ℕ) :
    ∑ s ∈ Finset.range M, ((s + 1 : ℕ) : ℝ) * (q ^ min (s + 1) M - q ^ min s M) =
      ∑ s ∈ Finset.range (M + 1), (s : ℝ) * (q ^ s - q ^ s / q) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  rw [min_eq_left (by omega : s + 1 ≤ M), min_eq_left (by omega : s ≤ M), pow_succ, mul_div_assoc, div_self hq,
    mul_one]

theorem main
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (w.1.adicCompletion L)ˣ)
    (hNα : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (α : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a)
    (hNβ : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (β : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) b)
    (hT : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))))
    (hidx : ‖(a : v.adicCompletion K)‖ = 1 → ‖(b : v.adicCompletion K)‖ = 1 →
      ∀ ϖ : v.adicCompletion K, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ → ∀ s : ℕ,
        (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
            (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (θ.toAlgHom.toRingHom.toAddMonoidHom -
                  AddMonoidHom.mulLeft ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L))) ⊓
              ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (AddMonoidHom.mulLeft
                  (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))) =
          Ideal.absNorm v.asIdeal ^ min s m.toNat)
    (τ' : @Measure (AutomorphicForm.sigmaCentralizer
        (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1)
    (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable[AutomorphicForm.localGLBorel L w.1] s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x ∈
          AutomorphicForm.localIntegralSet L w.1 →
        ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom)
            (diagUnits2 α β), s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ' = 1) :
    ∫ x : GL (Fin 2) (w.1.adicCompletion L),
        (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
            (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) * (s x : ℂ)
      ∂(AutomorphicForm.localHaar L w.1) =
      if ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1 then
        (((‖(a : v.adicCompletion K) - (b : v.adicCompletion K)‖⁻¹ : ℝ)) : ℂ)
      else 0 := by
  have hℓ : 0 < Module.finrank Kv Lw := Module.finrank_pos
  change ∫ x, Fδ K L v w θ α β x * (s x : ℂ) ∂(localHaar L w.1) = _
  by_cases hu : ‖(a : Kv)‖ = 1 ∧ ‖(b : Kv)‖ = 1
  swap
  ·
    rw [if_neg hu]
    have h0 : ∀ x, Fδ K L v w θ α β x = 0 := fun x => by
      by_contra hne
      obtain ⟨ha, hb⟩ := units_of_Fδ_ne_zero K L v w θ hw hne
      exact hu ⟨(norm_eq_one_iff_of_normString K L v w hw θ hℓ _ _ hNα).1 ha,
        (norm_eq_one_iff_of_normString K L v w hw θ hℓ _ _ hNβ).1 hb⟩
    simp [h0]

  rw [if_pos hu]
  have ha1 : ‖(α : Lw)‖ = 1 := (norm_eq_one_iff_of_normString K L v w hw θ hℓ _ _ hNα).2 hu.1
  have hb1 : ‖(β : Lw)‖ = 1 := (norm_eq_one_iff_of_normString K L v w hw θ hℓ _ _ hNβ).2 hu.2
  obtain ⟨ϖ, hϖ⟩ := exists_norm_eq_inv K v
  set π : Lw := algebraMap Kv Lw ϖ with hπdef
  have hπ : ‖π‖ = (qv L w.1)⁻¹ := norm_algebraMap_uniformizer K L v w hw hϖ
  set M : ℕ := m.toNat with hM
  set Λ : AddSubgroup Lw := LamC K L v w θ ((β * α⁻¹ : Lwˣ) : Lw) with hΛ
  have hidx' : ∀ s : ℕ, (OK L w.1).relIndex (Lam L w.1 Λ π s) = Ideal.absNorm v.asIdeal ^ min s M := by
    intro s
    have h := hidx hu.1 hu.2 ϖ hϖ s
    rw [map_pow] at h
    exact h
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega
  have hfin : ∀ s ≤ M, (OK L w.1).relIndex (Lam L w.1 Λ π s) ≠ 0 := fun s _ => by
    rw [hidx' s]; exact pow_ne_zero _ hq0

  letI : MeasurableSpace (sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) :=
    borel _
  haveI : BorelSpace (sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) := ⟨rfl⟩
  haveI := hτ'
  haveI : τ'.IsInvInvariant :=
    isInvInvariant_of_comm _ (isClosed_torus K L v w θ α β) (torus_comm K L v w θ hab hT) τ'

  set s₀ : GL (Fin 2) Lw → ℝ := (V L w.1 Λ π M).indicator fun _ => (1 : ℝ) with hs₀
  have hs₀' : (∀ x, 0 ≤ s₀ x) ∧ Measurable s₀ ∧ HasCompactSupport s₀ ∧
      ∀ x, Fδ K L v w θ α β x ≠ 0 →
        ∫ t : sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β),
          s₀ ((t : GL (Fin 2) Lw) * x) ∂τ' = 1 := by
    refine ⟨fun x => ?_, measurable_const.indicator (isOpen_V L w.1 Λ π M).measurableSet,
      HasCompactSupport.intro (isCompact_Uball L w.1 M) fun x hx =>
        Set.indicator_of_notMem (fun h => hx (V_subset_Uball L w.1 Λ π hπ M h)) _, fun x hx => ?_⟩
    · rw [hs₀, Set.indicator_apply]; split_ifs <;> simp
    · exact integral_indicator_V_translate K L v w θ ha1 hb1 π hπ M hidx' hw hab hT τ' hτ' hτ'1 x hx
  have hs' : (∀ x, 0 ≤ s x) ∧ Measurable s ∧ HasCompactSupport s ∧
      ∀ x, Fδ K L v w θ α β x ≠ 0 →
        ∫ t : sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β),
          s ((t : GL (Fin 2) Lw) * x) ∂τ' = 1 :=
    ⟨hs0, hsm, hsc, fun x hx => hs1 x ((Fδ_ne_zero_iff K L v w θ α β x).1 hx)⟩

  have hind := (MeasureTheory.integrable_and_integral_mul_mul_eq_of_integral_subgroup_translate_eq_one_of_continuous
    (sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β))
    (isClosed_torus K L v w θ α β) (localHaar L w.1) τ'
    (Fδ K L v w θ α β) (measurable_Fδ K L v w θ α β) ⟨1, norm_Fδ_le_one K L v w θ α β⟩
    (fun t x => Fδ_torus_mul K L v w θ t x)
    (fun _ => (1 : ℝ)) continuous_const (fun _ _ => rfl)
    s s₀ hs' hs₀').2
  have hind' : ∫ x, Fδ K L v w θ α β x * (s x : ℂ) ∂(localHaar L w.1) =
      ∫ x, Fδ K L v w θ α β x * (s₀ x : ℂ) ∂(localHaar L w.1) := by
    have h1 : (fun x => Fδ K L v w θ α β x * (((1 : ℝ) : ℝ) : ℂ) * (s x : ℂ)) =
        fun x => Fδ K L v w θ α β x * (s x : ℂ) := by
      funext x; push_cast; ring
    have h2 : (fun x => Fδ K L v w θ α β x * (((1 : ℝ) : ℝ) : ℂ) * (s₀ x : ℂ)) =
        fun x => Fδ K L v w θ α β x * (s₀ x : ℂ) := by
      funext x; push_cast; ring
    rw [← h1, ← h2]
    exact hind

  have hmeasV := (shells L w.1 Λ π hπ M hfin).1 M le_rfl
  have hval : ∫ x, Fδ K L v w θ α β x * (s₀ x : ℂ) ∂(localHaar L w.1) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ M : ℝ) : ℂ) := by
    have hfun : (fun x => Fδ K L v w θ α β x * (s₀ x : ℂ)) = (V L w.1 Λ π M).indicator fun _ => (1 : ℂ) := by
      funext x
      by_cases hx : x ∈ V L w.1 Λ π M
      · rw [Set.indicator_of_mem hx, hs₀, Set.indicator_of_mem hx,
          Fδ_eq_one_of_mem K L v w θ ((Fδ_ne_zero_iff K L v w θ α β x).1
            ((mem_V_iff K L v w θ ha1 hb1 π hπ M hidx' hw x).1 hx).2)]
        simp
      · rw [Set.indicator_of_notMem hx, hs₀, Set.indicator_of_notMem hx]
        simp
    rw [hfun, integral_indicator_const _ (isOpen_V L w.1 Λ π M).measurableSet, measureReal_def, hmeasV, hidx' M,
      min_self]
    simp

  have hm0 : 0 ≤ m := by
    have hle : ‖(a : Kv) - b‖ ≤ 1 := by
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu.1.le ?_)
      rw [norm_neg]; exact hu.2.le
    rw [hm] at hle
    by_contra hneg
    have hneg' : m < 0 := lt_of_not_ge hneg
    have : (1 : ℝ) < qv K v ^ (-m) := one_lt_zpow₀ (one_lt_qv K v) (by omega)
    exact absurd hle (not_le.2 this)
  have hqM : ((Ideal.absNorm v.asIdeal : ℝ) ^ M : ℝ) = ‖(a : Kv) - b‖⁻¹ := by
    rw [hm, ← zpow_neg, neg_neg, hM, ← zpow_natCast, Int.toNat_of_nonneg hm0]
  rw [hind', hval, hqM]

end Main

end R4S30UnitE
p2m_reactivate "P2MW.S_AutomorphicForm_integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq.R4S30UnitE"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq.R4S30UnitE"

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (w.1.adicCompletion L)ˣ)
    (hNα : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (α : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a)
    (hNβ : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (β : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) b)
    (hT : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))))
    (hidx : ‖(a : v.adicCompletion K)‖ = 1 → ‖(b : v.adicCompletion K)‖ = 1 →
      ∀ ϖ : v.adicCompletion K, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ → ∀ s : ℕ,
        (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
            (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (θ.toAlgHom.toRingHom.toAddMonoidHom -
                  AddMonoidHom.mulLeft ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L))) ⊓
              ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (AddMonoidHom.mulLeft
                  (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))) =
          Ideal.absNorm v.asIdeal ^ min s m.toNat)
    (τ' : @Measure (AutomorphicForm.sigmaCentralizer
        (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1)
    (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable[AutomorphicForm.localGLBorel L w.1] s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x ∈
          AutomorphicForm.localIntegralSet L w.1 →
        ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom)
            (diagUnits2 α β), s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ' = 1) :
    ∫ x : GL (Fin 2) (w.1.adicCompletion L),
        (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
            (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) * (s x : ℂ)
      ∂(AutomorphicForm.localHaar L w.1) =
      if ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1 then
        (((‖(a : v.adicCompletion K) - (b : v.adicCompletion K)‖⁻¹ : ℝ)) : ℂ)
      else 0 :=
  R4S30UnitE.main K L v w hw θ hθ a b hab m hm α β hNα hNβ hT hidx τ' hτ' hτ'1 s hs0 hsm hsc hs1

end S_AutomorphicForm_integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq
end P2MW
export P2MW.S_AutomorphicForm_integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq (solution)
