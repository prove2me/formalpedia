-- Prove2me | solution 1 for AutomorphicForm.apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2cbcae9f-3bf5-522e-a083-3115cdcaf3d7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace P2mEllipticGerm

section Chart

variable {F : Type*} [Field F]

def Y (lam a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; (lam - a ^ 2) / b, -a]

@[scoped simp] theorem Y_apply_00 (lam a b : F) : Y lam a b 0 0 = a := rfl
@[scoped simp] theorem Y_apply_01 (lam a b : F) : Y lam a b 0 1 = b := rfl
@[scoped simp] theorem Y_apply_10 (lam a b : F) : Y lam a b 1 0 = (lam - a ^ 2) / b := rfl
@[scoped simp] theorem Y_apply_11 (lam a b : F) : Y lam a b 1 1 = -a := rfl

def E10 (x : F) : Matrix (Fin 2) (Fin 2) F := !![0, 0; x, 0]

@[scoped simp] theorem E10_apply_00 (x : F) : E10 x 0 0 = 0 := rfl
@[scoped simp] theorem E10_apply_01 (x : F) : E10 x 0 1 = 0 := rfl
@[scoped simp] theorem E10_apply_10 (x : F) : E10 x 1 0 = x := rfl
@[scoped simp] theorem E10_apply_11 (x : F) : E10 x 1 1 = 0 := rfl

def AB (a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; 0, -a]

@[scoped simp] theorem AB_apply_00 (a b : F) : AB a b 0 0 = a := rfl
@[scoped simp] theorem AB_apply_01 (a b : F) : AB a b 0 1 = b := rfl
@[scoped simp] theorem AB_apply_10 (a b : F) : AB a b 1 0 = 0 := rfl
@[scoped simp] theorem AB_apply_11 (a b : F) : AB a b 1 1 = -a := rfl

theorem Y_eq_E10_add_AB (lam a b : F) : Y lam a b = E10 ((lam - a ^ 2) / b) + AB a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Y, E10, AB]

theorem Y_sub_Y (lam lam' a b : F) : Y lam a b - Y lam' a b = E10 ((lam - lam') / b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Y, E10] ; ring

theorem one_add_Y_eq (lam a b : F) : (1 : Matrix (Fin 2) (Fin 2) F) + Y lam a b =
    (1 + E10 ((lam - a ^ 2) / b)) + AB a b := by
  rw [Y_eq_E10_add_AB, add_assoc]

end Chart

section Bounds

variable {F : Type*} [NontriviallyNormedField F]

def EntryLE (M : Matrix (Fin 2) (Fin 2) F) (δ : ℝ) : Prop := ∀ i j, ‖M i j‖ ≤ δ

theorem EntryLE.mono {M : Matrix (Fin 2) (Fin 2) F} {δ δ' : ℝ} (h : EntryLE M δ) (hδ : δ ≤ δ') :
    EntryLE M δ' := fun i j => (h i j).trans hδ

theorem entryLE_zero (δ : ℝ) (hδ : 0 ≤ δ) : EntryLE (0 : Matrix (Fin 2) (Fin 2) F) δ :=
  fun i j => by simp [hδ]

theorem EntryLE.neg {M : Matrix (Fin 2) (Fin 2) F} {δ : ℝ} (h : EntryLE M δ) : EntryLE (-M) δ :=
  fun i j => by rw [Matrix.neg_apply, norm_neg]; exact h i j

variable [IsUltrametricDist F]

theorem EntryLE.add {M N : Matrix (Fin 2) (Fin 2) F} {δ : ℝ} (hM : EntryLE M δ) (hN : EntryLE N δ) :
    EntryLE (M + N) δ :=
  fun i j => by
    rw [Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hM i j) (hN i j))

theorem EntryLE.sub {M N : Matrix (Fin 2) (Fin 2) F} {δ : ℝ} (hM : EntryLE M δ) (hN : EntryLE N δ) :
    EntryLE (M - N) δ := by
  rw [sub_eq_add_neg]; exact hM.add hN.neg

omit [IsUltrametricDist F] in
theorem entryLE_E10 {x : F} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ‖x‖ ≤ δ) : EntryLE (E10 x) δ := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E10, hδ, hx]

omit [IsUltrametricDist F] in
theorem entryLE_AB {a b : F} {δ : ℝ} (ha : ‖a‖ ≤ δ) (hb : ‖b‖ ≤ δ) : EntryLE (AB a b) δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans ha
  intro i j; fin_cases i <;> fin_cases j <;> simp [AB, hδ, ha, hb]

end Bounds

section Parity

variable {F : Type*} [NontriviallyNormedField F]

def Parity (ϖ : F) : Prop := ∀ a t : F, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2

variable {ϖ : F}

theorem norm_mul_sq (ϖ r : F) : ‖ϖ * r ^ 2‖ = ‖ϖ‖ * ‖r‖ ^ 2 := by
  rw [norm_mul, norm_pow]

variable [IsUltrametricDist F]

theorem norm_lam_sub_sq (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0) (a : F) :
    ‖ϖ * r ^ 2 - a ^ 2‖ = max (‖ϖ * r ^ 2‖) (‖a‖ ^ 2) := by
  have hne : ‖ϖ * r ^ 2‖ ≠ ‖-(a ^ 2)‖ := by
    rw [norm_neg, norm_pow, norm_mul_sq]
    exact fun h => hϖ a r hr h.symm
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_pow]

theorem lam_sub_sq_ne_zero (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0) (a : F) : ϖ * r ^ 2 - a ^ 2 ≠ 0 := by
  intro h
  have h1 := norm_lam_sub_sq hϖ hr a
  rw [h, norm_zero] at h1
  have h2 : ‖a‖ ^ 2 ≤ 0 := by rw [h1]; exact le_max_right _ _
  have ha : a = 0 := by
    have : ‖a‖ ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
  subst ha
  have : ϖ * r ^ 2 = 0 := by simpa using h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact hϖ 0 r hr (by rw [h0]; simp)
  · exact hr ((pow_eq_zero_iff two_ne_zero).1 h0)

theorem norm_lam_pos (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0) : 0 < ‖ϖ * r ^ 2‖ := by
  have := lam_sub_sq_ne_zero hϖ hr 0
  rw [norm_pos_iff]
  simpa using this

theorem le_norm_lam_sub_sq (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0) (a : F) :
    ‖ϖ * r ^ 2‖ ≤ ‖ϖ * r ^ 2 - a ^ 2‖ := by
  rw [norm_lam_sub_sq hϖ hr]; exact le_max_left _ _

theorem sq_le_norm_lam_sub_sq (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0) (a : F) :
    ‖a‖ ^ 2 ≤ ‖ϖ * r ^ 2 - a ^ 2‖ := by
  rw [norm_lam_sub_sq hϖ hr]; exact le_max_right _ _

end Parity

end P2mEllipticGerm
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

namespace P2mEllipticGerm

section UniformLC

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isUltrametricDist_matrix : IsUltrametricDist (Matrix (Fin 2) (Fin 2) F) :=
  inferInstanceAs (IsUltrametricDist (Fin 2 → Fin 2 → F))

attribute [local instance] isUltrametricDist_matrix

theorem entryLE_iff_norm_le {M : Matrix (Fin 2) (Fin 2) F} {δ : ℝ} (hδ : 0 ≤ δ) :
    EntryLE M δ ↔ ‖M‖ ≤ δ := (Matrix.norm_le_iff hδ).symm

theorem exists_forall_add_eq {Φ : Matrix (Fin 2) (Fin 2) F → ℂ} (hΦ : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Φ (M + E) = Φ M := by

  have hrad : ∀ M : Matrix (Fin 2) (Fin 2) F, ∃ ε : ℝ, 0 < ε ∧ ∀ N, ‖N - M‖ < ε → Φ N = Φ M := by
    intro M
    obtain ⟨U, hU, hMU, hconst⟩ := hΦ.exists_open M
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU M hMU
    exact ⟨ε, hε, fun N hN => hconst N (hball (by rwa [Metric.mem_ball, dist_eq_norm]))⟩
  choose ε hε hconst using hrad
  obtain ⟨t, -, hcover⟩ := hΦc.isCompact.elim_nhds_subcover (fun M => Metric.ball M (ε M))
    (fun M _ => Metric.ball_mem_nhds M (hε M))

  by_cases ht : t.Nonempty
  · set δ : ℝ := (t.image ε).min' (ht.image ε) / 2 with hδ
    have hδpos : 0 < δ := by
      rw [hδ]
      refine div_pos ?_ two_pos
      obtain ⟨M₀, hM₀, hmin⟩ := Finset.mem_image.1 ((t.image ε).min'_mem (ht.image ε))
      rw [← hmin]; exact hε M₀
    have hδlt : ∀ M ∈ t, δ < ε M := by
      intro M hM
      have h1 : (t.image ε).min' (ht.image ε) ≤ ε M := Finset.min'_le _ _ (Finset.mem_image_of_mem ε hM)
      have h2 : δ < (t.image ε).min' (ht.image ε) := by
        rw [hδ]; exact half_lt_self (by
          obtain ⟨M₀, hM₀, hmin⟩ := Finset.mem_image.1 ((t.image ε).min'_mem (ht.image ε))
          rw [← hmin]; exact hε M₀)
      exact h2.trans_le h1
    refine ⟨δ, hδpos, fun M E hE => ?_⟩
    have hEn : ‖E‖ ≤ δ := (entryLE_iff_norm_le hδpos.le).1 hE

    have key : ∀ N N' : Matrix (Fin 2) (Fin 2) F, N ∈ tsupport Φ → ‖N' - N‖ ≤ δ → Φ N' = Φ N := by
      intro N N' hN hNN'
      obtain ⟨M₀, hM₀t, hNM₀⟩ := Set.mem_iUnion₂.1 (hcover hN)
      rw [Metric.mem_ball, dist_eq_norm] at hNM₀
      have h1 : Φ N = Φ M₀ := hconst M₀ N hNM₀
      have h2 : ‖N' - M₀‖ < ε M₀ := by
        have : N' - M₀ = (N' - N) + (N - M₀) := by abel
        rw [this]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
          (max_lt (hNN'.trans_lt (hδlt M₀ hM₀t)) hNM₀)
      rw [h1, hconst M₀ N' h2]
    by_cases hM : M ∈ tsupport Φ
    · exact key M (M + E) hM (by rw [add_sub_cancel_left]; exact hEn)
    · by_cases hME : M + E ∈ tsupport Φ
      · exact (key (M + E) M hME (by rw [sub_add_cancel_left, norm_neg]; exact hEn)).symm
      · rw [image_eq_zero_of_notMem_tsupport hM, image_eq_zero_of_notMem_tsupport hME]
  ·
    rw [Finset.not_nonempty_iff_eq_empty] at ht
    have hzero : ∀ M, Φ M = 0 := by
      intro M
      apply image_eq_zero_of_notMem_tsupport
      intro hM
      have := hcover hM
      rw [ht] at this
      simp at this
    exact ⟨1, one_pos, fun M E _ => by rw [hzero, hzero]⟩

theorem exists_bound_of_ne_zero {Φ : Matrix (Fin 2) (Fin 2) F → ℂ} (hΦc : HasCompactSupport Φ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ M : Matrix (Fin 2) (Fin 2) F, Φ M ≠ 0 → EntryLE M B := by
  obtain ⟨C, hC⟩ := hΦc.isCompact.exists_bound_of_continuousOn
    (continuous_id (X := Matrix (Fin 2) (Fin 2) F)).continuousOn
  refine ⟨max C 1, le_max_right _ _, fun M hM i j => ?_⟩
  have h := hC M (subset_tsupport _ (Function.mem_support.2 hM))
  exact (Matrix.norm_entry_le_entrywise_sup_norm M).trans (h.trans (le_max_left _ _))

theorem exists_norm_apply_le {Φ : Matrix (Fin 2) (Fin 2) F → ℂ} (hΦ : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) : ∃ C : ℝ, ∀ M, ‖Φ M‖ ≤ C := by
  obtain ⟨C, hC⟩ := hΦc.exists_bound_of_continuous hΦ.continuous
  exact ⟨C, hC⟩

end UniformLC
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

end P2mEllipticGerm
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

namespace P2mEllipticGerm

section Functional

variable {F : Type*} [NontriviallyNormedField F]

theorem secondCountableTopology_units [SecondCountableTopology F] : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

attribute [local instance] secondCountableTopology_units

def chartFn (Θ : Matrix (Fin 2) (Fin 2) F → ℂ) (lam : F) : Fˣ × F → ℂ :=
  fun p => Θ (1 + Y lam p.2 (p.1 : F))

theorem chartFn_apply (Θ : Matrix (Fin 2) (Fin 2) F → ℂ) (lam : F) (b : Fˣ) (a : F) :
    chartFn Θ lam (b, a) = Θ (1 + Y lam a b) := rfl

theorem continuous_chart (lam : F) :
    Continuous fun p : Fˣ × F => (1 : Matrix (Fin 2) (Fin 2) F) + Y lam p.2 (p.1 : F) := by
  refine continuous_const.add (continuous_matrix fun i j => ?_)
  have hb : Continuous fun p : Fˣ × F => ((p.1 : Fˣ) : F) := Units.continuous_val.comp continuous_fst
  have hbi : Continuous fun p : Fˣ × F => (((p.1⁻¹ : Fˣ) : Fˣ) : F) :=
    Units.continuous_val.comp (continuous_fst.inv)
  have ha : Continuous fun p : Fˣ × F => p.2 := continuous_snd
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · show Continuous fun p : Fˣ × F => (lam - p.2 ^ 2) / ((p.1 : Fˣ) : F)
    have : (fun p : Fˣ × F => (lam - p.2 ^ 2) / ((p.1 : Fˣ) : F)) =
        fun p : Fˣ × F => (lam - p.2 ^ 2) * (((p.1⁻¹ : Fˣ) : Fˣ) : F) := by
      funext p; rw [div_eq_mul_inv, Units.val_inv_eq_inv_val]
    rw [this]
    exact (continuous_const.sub (ha.pow 2)).mul hbi
  · show Continuous fun p : Fˣ × F => -p.2
    exact ha.neg

theorem isCompact_units_annulus [ProperSpace F] {r₁ : ℝ} (r₂ : ℝ) (hr₁ : 0 < r₁) :
    IsCompact {b : Fˣ | r₁ ≤ ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ r₂} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have himg : ((↑) : Fˣ → F) '' {b : Fˣ | r₁ ≤ ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ r₂} =
      {x : F | r₁ ≤ ‖x‖} ∩ Metric.closedBall (0 : F) r₂ := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨b, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hx : x ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact (lt_irrefl _ (hr₁.trans_le h1))
      exact ⟨Units.mk0 x hx, ⟨h1, h2⟩, rfl⟩
  rw [himg]
  exact (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const continuous_norm)

variable [IsUltrametricDist F]

theorem entryLE_of_entryLE_one_add {M : Matrix (Fin 2) (Fin 2) F} {B : ℝ} (hB : 1 ≤ B)
    (h : EntryLE (1 + M) B) : EntryLE M B := by
  have h1 : EntryLE (1 : Matrix (Fin 2) (Fin 2) F) B := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [(zero_le_one.trans hB), hB]
  have := h.sub h1
  rwa [add_sub_cancel_left] at this

variable {ϖ : F}

theorem support_chartFn {Θ : Matrix (Fin 2) (Fin 2) F → ℂ} {B : ℝ} (hB : 1 ≤ B)
    (hsupp : ∀ M, Θ M ≠ 0 → EntryLE M B) (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0) {b : Fˣ} {a : F}
    (h : chartFn Θ (ϖ * r ^ 2) (b, a) ≠ 0) :
    ‖a‖ ≤ B ∧ ‖ϖ * r ^ 2‖ / B ≤ ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ B := by
  have hE := entryLE_of_entryLE_one_add hB (hsupp _ h)
  have hB0 : 0 < B := one_pos.trans_le hB
  refine ⟨by simpa using hE 0 0, ?_, by simpa using hE 0 1⟩
  have h10 : ‖(ϖ * r ^ 2 - a ^ 2) / (b : F)‖ ≤ B := by simpa using hE 1 0
  rw [norm_div, div_le_iff₀ (norm_pos_iff.2 b.ne_zero)] at h10
  rw [div_le_iff₀ hB0]
  calc ‖ϖ * r ^ 2‖ ≤ ‖ϖ * r ^ 2 - a ^ 2‖ := le_norm_lam_sub_sq hϖ hr a
    _ ≤ B * ‖(b : F)‖ := h10
    _ = ‖(b : F)‖ * B := mul_comm _ _

variable [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]

theorem integrable_of_bounded_of_support_subset {X : Type*} [MeasurableSpace X] {ρ : Measure X} {f : X → ℂ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {S : Set X} (hS : ρ S ≠ ⊤)
    (hsupp : Function.support f ⊆ S) : Integrable f ρ := by
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  exact Measure.integrableOn_of_bounded hS hf.aestronglyMeasurable (ae_of_all _ fun x => hC x)

theorem integrable_chartFn {Θ : Matrix (Fin 2) (Fin 2) F → ℂ} {B C : ℝ} (hB : 1 ≤ B)
    (hsupp : ∀ M, Θ M ≠ 0 → EntryLE M B) (hbdd : ∀ M, ‖Θ M‖ ≤ C) (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0)
    (hmeas : Measurable (chartFn Θ (ϖ * r ^ 2))) :
    Integrable (chartFn Θ (ϖ * r ^ 2)) (ν.prod μ) := by
  have hB0 : 0 < B := one_pos.trans_le hB
  refine integrable_of_bounded_of_support_subset hmeas (C := C) (fun p => hbdd _)
    (S := {b : Fˣ | ‖ϖ * r ^ 2‖ / B ≤ ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ B} ×ˢ Metric.closedBall (0 : F) B) ?_ ?_
  · rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top
      ((isCompact_units_annulus B (div_pos (norm_lam_pos hϖ hr) hB0)).measure_lt_top)
      ((isCompact_closedBall _ _).measure_lt_top)).ne
  · rintro ⟨b, a⟩ hp
    rw [Function.mem_support] at hp
    obtain ⟨ha, hb1, hb2⟩ := support_chartFn hB hsupp hϖ hr hp
    exact ⟨⟨hb1, hb2⟩, by simpa using ha⟩

theorem integral_integral_eq_integral_prod {Θ : Matrix (Fin 2) (Fin 2) F → ℂ} {lam : F}
    (hint : Integrable (chartFn Θ lam) (ν.prod μ)) :
    ∫ b, ∫ a, Θ (1 + !![a, (b : F); (lam - a ^ 2) / b, -a]) ∂μ ∂ν = ∫ p, chartFn Θ lam p ∂(ν.prod μ) := by
  rw [integral_prod _ hint]
  rfl

end Functional
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

end P2mEllipticGerm
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

namespace P2mEllipticGerm

section ClaimA

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

theorem norm_sub_le_max (x y : F) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

variable {ϖ : F}

theorem norm_lam_le_of_norm_le (ϖ : F) {r r' : F} (h : ‖r'‖ ≤ ‖r‖) : ‖ϖ * r' ^ 2‖ ≤ ‖ϖ * r ^ 2‖ := by
  rw [norm_mul_sq, norm_mul_sq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) (norm_nonneg _)

theorem ne_zero_of_norm_le {r r' : F} (hr' : r' ≠ 0) (h : ‖r'‖ ≤ ‖r‖) : r ≠ 0 := by
  rintro rfl
  rw [norm_zero] at h
  exact hr' (norm_eq_zero.1 (le_antisymm h (norm_nonneg _)))

theorem norm_lt_of_chart_bound (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0) {δ B : ℝ} (hδ : 0 < δ) (hB : 1 ≤ B)
    (h2 : ‖ϖ * r ^ 2‖ * B ≤ δ ^ 3) {a : F} {b : Fˣ} (hb : ‖(b : F)‖ < ‖ϖ * r ^ 2‖ / δ)
    (hc : ‖(ϖ * r ^ 2 - a ^ 2) / (b : F)‖ ≤ B) : ‖a‖ < δ := by
  have hB0 : 0 < B := one_pos.trans_le hB
  have hbpos : 0 < ‖(b : F)‖ := norm_pos_iff.2 b.ne_zero
  rw [norm_div, div_le_iff₀ hbpos] at hc
  have h3 : ‖a‖ ^ 2 < δ ^ 2 := by
    calc ‖a‖ ^ 2 ≤ ‖ϖ * r ^ 2 - a ^ 2‖ := sq_le_norm_lam_sub_sq hϖ hr a
      _ ≤ B * ‖(b : F)‖ := hc
      _ < B * (‖ϖ * r ^ 2‖ / δ) := mul_lt_mul_of_pos_left hb hB0
      _ = ‖ϖ * r ^ 2‖ * B / δ := by ring
      _ ≤ δ ^ 3 / δ := div_le_div_of_nonneg_right h2 hδ.le
      _ = δ ^ 2 := by field_simp
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le h3

variable [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]

attribute [local instance] secondCountableTopology_units

theorem setIntegral_comp_div (g : F → ℂ) (κ : Fˣ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ b in {b : Fˣ | ‖(b : F)‖ < ρ}, g ((κ : F) / (b : F)) ∂ν =
      ∫ b in {b : Fˣ | ‖(κ : F)‖ / ρ < ‖(b : F)‖}, g b ∂ν := by
  set e : Fˣ ≃ₜ Fˣ := (Homeomorph.inv Fˣ).trans (Homeomorph.mulLeft κ) with he
  have hecoe : ∀ b : Fˣ, e b = κ * b⁻¹ := fun b => rfl
  have hmp : MeasurePreserving e ν ν := by
    have : (e : Fˣ → Fˣ) = (fun b => κ * b) ∘ (fun b => b⁻¹) := by funext b; rfl
    rw [this]
    exact (measurePreserving_mul_left ν κ).comp (Measure.measurePreserving_inv ν)
  have hpre : e ⁻¹' {b : Fˣ | ‖(κ : F)‖ / ρ < ‖(b : F)‖} = {b : Fˣ | ‖(b : F)‖ < ρ} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hecoe, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv]
    have hκ : 0 < ‖(κ : F)‖ := norm_pos_iff.2 κ.ne_zero
    have hb : 0 < ‖(b : F)‖ := norm_pos_iff.2 b.ne_zero
    rw [← div_eq_mul_inv, div_lt_div_iff_of_pos_left hκ hρ hb]
  have key := hmp.setIntegral_preimage_emb e.measurableEmbedding (fun b : Fˣ => g (b : F))
    {b : Fˣ | ‖(κ : F)‖ / ρ < ‖(b : F)‖}
  rw [hpre] at key
  rw [← key]
  refine setIntegral_congr_fun ?_ (fun b _ => ?_)
  · exact (isOpen_lt (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  · simp only [hecoe, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]

theorem setIntegral_tail_eq (g : F → ℂ) {δ : ℝ} (hg : ∀ x : F, ‖x‖ ≤ δ → g x = 0) {θ : ℝ} (hθ : θ ≤ δ) :
    ∫ b in {b : Fˣ | θ < ‖(b : F)‖}, g b ∂ν = ∫ b, g b ∂ν := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun b hb => hg _ ?_)
  simp only [Set.mem_setOf_eq, not_lt] at hb
  exact hb.trans hθ

theorem inner_integral_eq (g : F → ℂ) {δ : ℝ} (hδ : 0 < δ) (hg : ∀ x : F, ‖x‖ ≤ δ → g x = 0)
    (hϖ : Parity ϖ) {r r' : F} (hr' : r' ≠ 0) (hrr' : ‖r'‖ ≤ ‖r‖) (a : F) :
    ∫ b in {b : Fˣ | ‖(b : F)‖ < ‖ϖ * r ^ 2‖ / δ}, g ((ϖ * r ^ 2 - a ^ 2) / (b : F)) ∂ν =
      ∫ b in {b : Fˣ | ‖(b : F)‖ < ‖ϖ * r ^ 2‖ / δ}, g ((ϖ * r' ^ 2 - a ^ 2) / (b : F)) ∂ν := by
  have hr : r ≠ 0 := ne_zero_of_norm_le hr' hrr'
  set ρ : ℝ := ‖ϖ * r ^ 2‖ / δ with hρdef
  have hlam : 0 < ‖ϖ * r ^ 2‖ := norm_lam_pos hϖ hr
  have hρ : 0 < ρ := div_pos hlam hδ
  set κ : Fˣ := Units.mk0 _ (lam_sub_sq_ne_zero hϖ hr a) with hκ
  set κ' : Fˣ := Units.mk0 _ (lam_sub_sq_ne_zero hϖ hr' a) with hκ'
  have h1 := setIntegral_comp_div ν g κ hρ
  have h1' := setIntegral_comp_div ν g κ' hρ
  simp only [hκ, hκ', Units.val_mk0] at h1 h1'
  rw [h1, h1']
  have hle : ‖ϖ * r' ^ 2‖ ≤ ‖ϖ * r ^ 2‖ := norm_lam_le_of_norm_le ϖ hrr'
  rcases lt_or_gt_of_ne (hϖ a r hr) with hlt | hgt
  ·
    rw [← norm_mul_sq] at hlt
    have hρid : ‖ϖ * r ^ 2‖ / ρ = δ := by
      rw [hρdef]; field_simp
    have hk : ‖ϖ * r ^ 2 - a ^ 2‖ / ρ ≤ δ := by
      rw [norm_lam_sub_sq hϖ hr, max_eq_left hlt.le, hρid]
    have hk' : ‖ϖ * r' ^ 2 - a ^ 2‖ / ρ ≤ δ := by
      have : ‖ϖ * r' ^ 2 - a ^ 2‖ ≤ ‖ϖ * r ^ 2‖ := by
        rw [norm_lam_sub_sq hϖ hr']; exact max_le hle hlt.le
      calc ‖ϖ * r' ^ 2 - a ^ 2‖ / ρ ≤ ‖ϖ * r ^ 2‖ / ρ := div_le_div_of_nonneg_right this hρ.le
        _ = δ := hρid
    rw [setIntegral_tail_eq ν g hg hk, setIntegral_tail_eq ν g hg hk']
  ·
    rw [← norm_mul_sq] at hgt
    have e1 : ‖ϖ * r ^ 2 - a ^ 2‖ = ‖a‖ ^ 2 := by rw [norm_lam_sub_sq hϖ hr, max_eq_right hgt.le]
    have e2 : ‖ϖ * r' ^ 2 - a ^ 2‖ = ‖a‖ ^ 2 := by
      rw [norm_lam_sub_sq hϖ hr', max_eq_right (hle.trans hgt.le)]
    rw [e1, e2]

variable {μ ν}

theorem integral_chartFn_eq_of_vanish_near_one {Ψ : Matrix (Fin 2) (Fin 2) F → ℂ} {δ B C : ℝ}
    (hδ : 0 < δ) (hB : 1 ≤ B)
    (hinv : ∀ M E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Ψ (M + E) = Ψ M)
    (hsupp : ∀ M, Ψ M ≠ 0 → EntryLE M B) (hbdd : ∀ M, ‖Ψ M‖ ≤ C)
    (hvan1 : ∀ E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Ψ (1 + E) = 0)
    (hϖ : Parity ϖ) {r r' : F} (hr' : r' ≠ 0) (hrr' : ‖r'‖ ≤ ‖r‖)
    (hmeas : Measurable (chartFn Ψ (ϖ * r ^ 2))) (hmeas' : Measurable (chartFn Ψ (ϖ * r' ^ 2)))
    (h1 : ‖ϖ * r ^ 2‖ ≤ δ ^ 2) (h2 : ‖ϖ * r ^ 2‖ * B ≤ δ ^ 3) :
    ∫ p, chartFn Ψ (ϖ * r ^ 2) p ∂(ν.prod μ) = ∫ p, chartFn Ψ (ϖ * r' ^ 2) p ∂(ν.prod μ) := by
  have hr : r ≠ 0 := ne_zero_of_norm_le hr' hrr'
  set lam := ϖ * r ^ 2 with hlamdef
  set lam' := ϖ * r' ^ 2 with hlam'def
  have hlam : 0 < ‖lam‖ := norm_lam_pos hϖ hr
  set ρ : ℝ := ‖lam‖ / δ with hρdef
  have hρ : 0 < ρ := div_pos hlam hδ
  have hρδ : ρ ≤ δ := by
    rw [hρdef, div_le_iff₀ hδ]; nlinarith [h1]
  have hle : ‖lam'‖ ≤ ‖lam‖ := norm_lam_le_of_norm_le ϖ hrr'
  have h2' : ‖lam'‖ * B ≤ δ ^ 3 := (mul_le_mul_of_nonneg_right hle (zero_le_one.trans hB)).trans h2

  set R₁ : Set (Fˣ × F) := {p | ρ ≤ ‖((p.1 : Fˣ) : F)‖} with hR₁
  have hcont1 : Continuous fun p : Fˣ × F => ‖((p.1 : Fˣ) : F)‖ :=
    continuous_norm.comp (Units.continuous_val.comp continuous_fst)
  have hR₁m : MeasurableSet R₁ := (isClosed_le continuous_const hcont1).measurableSet
  have hR₁c : R₁ᶜ = {b : Fˣ | ‖(b : F)‖ < ρ} ×ˢ (Set.univ : Set F) := by
    ext p; simp [hR₁, not_le]
  have hint : Integrable (chartFn Ψ lam) (ν.prod μ) := integrable_chartFn μ ν hB hsupp hbdd hϖ hr hmeas
  have hint' : Integrable (chartFn Ψ lam') (ν.prod μ) := integrable_chartFn μ ν hB hsupp hbdd hϖ hr' hmeas'
  rw [← integral_add_compl hR₁m hint, ← integral_add_compl hR₁m hint']

  set ψ : F → ℂ := fun x => Ψ (1 + E10 x) with hψdef
  have hψ0 : ∀ x : F, ‖x‖ ≤ δ → ψ x = 0 := fun x hx => hvan1 _ (entryLE_E10 hδ.le hx)

  have hred : ∀ {s : F}, s ≠ 0 → ‖ϖ * s ^ 2‖ * B ≤ δ ^ 3 → ‖ϖ * s ^ 2‖ ≤ ‖lam‖ →
      ∀ p : Fˣ × F, p ∈ R₁ᶜ →
        chartFn Ψ (ϖ * s ^ 2) p = ψ ((ϖ * s ^ 2 - p.2 ^ 2) / ((p.1 : Fˣ) : F)) := by
    intro s hs hs2 hsle p hp
    obtain ⟨b, a⟩ := p
    have hb : ‖(b : F)‖ < ρ := by simpa [hR₁] using hp
    have hbs : ‖(b : F)‖ < ‖ϖ * s ^ 2‖ / δ ∨ ‖ϖ * s ^ 2‖ ≤ ‖lam‖ := Or.inr hsle
    rw [chartFn_apply, one_add_Y_eq]
    by_cases ha : ‖a‖ ≤ δ
    · exact hinv _ _ (entryLE_AB ha (hb.le.trans hρδ))
    ·
      have hzero_of : ‖(ϖ * s ^ 2 - a ^ 2) / (b : F)‖ ≤ B → False := by
        intro hc

        have hb' : ‖(b : F)‖ < ‖lam‖ / δ := hb
        have : ‖a‖ < δ := by
          have hB0 : 0 < B := one_pos.trans_le hB
          have hbpos : 0 < ‖(b : F)‖ := norm_pos_iff.2 b.ne_zero
          rw [norm_div, div_le_iff₀ hbpos] at hc
          have h3 : ‖a‖ ^ 2 < δ ^ 2 := by
            calc ‖a‖ ^ 2 ≤ ‖ϖ * s ^ 2 - a ^ 2‖ := sq_le_norm_lam_sub_sq hϖ hs a
              _ ≤ B * ‖(b : F)‖ := hc
              _ < B * (‖lam‖ / δ) := mul_lt_mul_of_pos_left hb' hB0
              _ = ‖lam‖ * B / δ := by ring
              _ ≤ δ ^ 3 / δ := div_le_div_of_nonneg_right h2 hδ.le
              _ = δ ^ 2 := by field_simp
          exact lt_of_pow_lt_pow_left₀ 2 hδ.le h3
        exact ha this.le
      have hl : Ψ (1 + E10 ((ϖ * s ^ 2 - a ^ 2) / (b : F)) + AB a (b : F)) = 0 := by
        by_contra hne
        have hE := entryLE_of_entryLE_one_add hB (by
          have := hsupp _ hne; rwa [add_assoc] at this)
        exact hzero_of (by simpa [E10, AB] using hE 1 0)
      have hr0 : ψ ((ϖ * s ^ 2 - a ^ 2) / (b : F)) = 0 := by
        by_contra hne
        have hE := entryLE_of_entryLE_one_add hB (hsupp _ hne)
        exact hzero_of (by simpa [E10] using hE 1 0)
      rw [hl, hr0]

  have hiter : ∀ {s : F} (hs : s ≠ 0), ‖ϖ * s ^ 2‖ * B ≤ δ ^ 3 → ‖ϖ * s ^ 2‖ ≤ ‖lam‖ →
      Integrable (chartFn Ψ (ϖ * s ^ 2)) (ν.prod μ) →
      ∫ p in R₁ᶜ, chartFn Ψ (ϖ * s ^ 2) p ∂(ν.prod μ) =
        ∫ a, ∫ b in {b : Fˣ | ‖(b : F)‖ < ρ}, ψ ((ϖ * s ^ 2 - a ^ 2) / (b : F)) ∂ν ∂μ := by
    intro s hs hs2 hsle hints
    set G : Fˣ × F → ℂ := fun p => ψ ((ϖ * s ^ 2 - p.2 ^ 2) / ((p.1 : Fˣ) : F)) with hG
    have hEq : Set.EqOn (chartFn Ψ (ϖ * s ^ 2)) G R₁ᶜ := fun p hp => hred hs hs2 hsle p hp
    rw [setIntegral_congr_fun hR₁m.compl hEq]
    have hGint : IntegrableOn G R₁ᶜ (ν.prod μ) := (hints.integrableOn).congr_fun hEq hR₁m.compl
    rw [hR₁c] at hGint ⊢
    change ∫ p in {b : Fˣ | ‖(b : F)‖ < ρ} ×ˢ (Set.univ : Set F), G p ∂(ν.prod μ) = _
    rw [← Measure.restrict_prod_eq_prod_univ]
    have hGint' : Integrable G ((ν.restrict {b : Fˣ | ‖(b : F)‖ < ρ}).prod μ) := by
      rw [Measure.restrict_prod_eq_prod_univ]; exact hGint
    rw [integral_prod_symm G hGint']
  rw [hiter hr h2 le_rfl hint, hiter hr' h2' hle hint']
  congr 1
  ·
    refine setIntegral_congr_fun hR₁m (fun p hp => ?_)
    obtain ⟨b, a⟩ := p
    have hb : ρ ≤ ‖(b : F)‖ := hp
    rw [chartFn_apply, chartFn_apply]
    have hY : Y lam a b = Y lam' a b + E10 ((lam - lam') / b) := by rw [← Y_sub_Y]; abel
    rw [hY, ← add_assoc]
    refine hinv _ _ (entryLE_E10 hδ.le ?_)
    rw [norm_div]
    calc ‖lam - lam'‖ / ‖(b : F)‖ ≤ ‖lam‖ / ρ :=
          div_le_div₀ (norm_nonneg _) ((norm_sub_le_max _ _).trans (max_le le_rfl hle)) hρ hb
      _ = δ := by rw [hρdef]; field_simp
  · congr 1 with a
    exact inner_integral_eq ν ψ hδ hψ0 hϖ hr' hrr' a

end ClaimA
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

end P2mEllipticGerm
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

namespace P2mEllipticGerm

section ClaimB

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

def boxOne (δ : ℝ) : Set (Matrix (Fin 2) (Fin 2) F) := {M | EntryLE (M - 1) δ}

def chi (δ : ℝ) : Matrix (Fin 2) (Fin 2) F → ℂ := (boxOne δ).indicator fun _ => 1

theorem chi_of_mem {δ : ℝ} {M : Matrix (Fin 2) (Fin 2) F} (h : EntryLE (M - 1) δ) : chi δ M = 1 :=
  Set.indicator_of_mem (by exact h) _

theorem chi_of_not_mem {δ : ℝ} {M : Matrix (Fin 2) (Fin 2) F} (h : ¬ EntryLE (M - 1) δ) : chi δ M = 0 :=
  Set.indicator_of_notMem (by exact h) _

theorem norm_chi_le (δ : ℝ) (M : Matrix (Fin 2) (Fin 2) F) : ‖chi δ M‖ ≤ 1 := by
  by_cases h : EntryLE (M - 1) δ
  · rw [chi_of_mem h, norm_one]
  · rw [chi_of_not_mem h, norm_zero]; exact zero_le_one

theorem chi_add {δ : ℝ} (M E : Matrix (Fin 2) (Fin 2) F) (hE : EntryLE E δ) : chi δ (M + E) = chi δ M := by
  by_cases h : EntryLE (M - 1) δ
  · rw [chi_of_mem h, chi_of_mem]
    have : M + E - 1 = (M - 1) + E := by abel
    rw [this]; exact h.add hE
  · rw [chi_of_not_mem h, chi_of_not_mem]
    intro h'
    apply h
    have : M - 1 = (M + E - 1) - E := by abel
    rw [this]; exact h'.sub hE

theorem chi_one_add {δ : ℝ} (E : Matrix (Fin 2) (Fin 2) F) (hE : EntryLE E δ) : chi δ (1 + E) = 1 :=
  chi_of_mem (by rwa [add_sub_cancel_left])

theorem entryLE_of_chi_ne_zero {δ : ℝ} (hδ1 : δ ≤ 1) {M : Matrix (Fin 2) (Fin 2) F} (h : chi δ M ≠ 0) :
    EntryLE M 1 := by
  by_cases hM : EntryLE (M - 1) δ
  · have h1 : EntryLE (1 : Matrix (Fin 2) (Fin 2) F) 1 := by
      intro i j; fin_cases i <;> fin_cases j <;> simp
    have := (hM.mono hδ1).add h1
    rwa [sub_add_cancel] at this
  · exact absurd (chi_of_not_mem hM) h

def Rset (δ : ℝ) (lam : F) : Set (Fˣ × F) :=
  {p | ‖p.2‖ ≤ δ ∧ ‖((p.1 : Fˣ) : F)‖ ≤ δ ∧ ‖(lam - p.2 ^ 2) / ((p.1 : Fˣ) : F)‖ ≤ δ}

theorem entryLE_Y_iff (δ : ℝ) (lam a : F) (b : F) :
    EntryLE (Y lam a b) δ ↔ ‖a‖ ≤ δ ∧ ‖b‖ ≤ δ ∧ ‖(lam - a ^ 2) / b‖ ≤ δ := by
  constructor
  · intro h; exact ⟨by simpa using h 0 0, by simpa using h 0 1, by simpa using h 1 0⟩
  · rintro ⟨ha, hb, hc⟩ i j
    fin_cases i <;> fin_cases j
    · simpa using ha
    · simpa using hb
    · simpa using hc
    · simpa using ha

theorem chartFn_chi (δ : ℝ) (lam : F) :
    chartFn (chi δ) lam = (Rset δ lam).indicator fun _ => (1 : ℂ) := by
  funext p
  obtain ⟨b, a⟩ := p
  rw [chartFn_apply]
  have hiff : EntryLE (1 + Y lam a b - 1) δ ↔ (b, a) ∈ Rset δ lam := by
    rw [add_sub_cancel_left, entryLE_Y_iff]; rfl
  by_cases h : (b, a) ∈ Rset δ lam
  · rw [Set.indicator_of_mem h, chi_of_mem (hiff.2 h)]
  · rw [Set.indicator_of_notMem h, chi_of_not_mem (fun h' => h (hiff.1 h'))]

theorem isClosed_Rset (δ : ℝ) (lam : F) : IsClosed (Rset δ lam) := by
  have h1 : Continuous fun p : Fˣ × F => ‖p.2‖ := continuous_norm.comp continuous_snd
  have h2 : Continuous fun p : Fˣ × F => ‖((p.1 : Fˣ) : F)‖ :=
    continuous_norm.comp (Units.continuous_val.comp continuous_fst)
  have h3 : Continuous fun p : Fˣ × F => ‖(lam - p.2 ^ 2) / ((p.1 : Fˣ) : F)‖ := by
    have h := (continuous_chart lam).matrix_elem 1 0
    refine continuous_norm.comp ?_
    convert h using 1
    funext p
    simp [Matrix.add_apply, Y]
  exact (isClosed_le h1 continuous_const).inter
    ((isClosed_le h2 continuous_const).inter (isClosed_le h3 continuous_const))

variable {ϖ : F}

theorem Rset_subset (δ : ℝ) (hϖ : Parity ϖ) {r r' : F} (hr' : r' ≠ 0) (hrr' : ‖r'‖ ≤ ‖r‖) :
    Rset δ (ϖ * r ^ 2) ⊆ Rset δ (ϖ * r' ^ 2) := by
  have hr : r ≠ 0 := ne_zero_of_norm_le hr' hrr'
  rintro ⟨b, a⟩ ⟨ha, hb, hc⟩
  refine ⟨ha, hb, le_trans ?_ hc⟩
  simp only [norm_div]
  refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_lam_sub_sq hϖ hr, norm_lam_sub_sq hϖ hr']
  exact max_le_max (norm_lam_le_of_norm_le ϖ hrr') le_rfl

theorem Rset_subset_prod {δ : ℝ} (hδ : 0 < δ) (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0) :
    Rset δ (ϖ * r ^ 2) ⊆
      {b : Fˣ | ‖ϖ * r ^ 2‖ / δ ≤ ‖(b : F)‖ ∧ ‖(b : F)‖ ≤ δ} ×ˢ Metric.closedBall (0 : F) δ := by
  rintro ⟨b, a⟩ ⟨ha, hb, hc⟩
  refine ⟨⟨?_, hb⟩, by simpa using ha⟩
  rw [norm_div, div_le_iff₀ (norm_pos_iff.2 b.ne_zero)] at hc
  rw [div_le_iff₀ hδ]
  calc ‖ϖ * r ^ 2‖ ≤ ‖ϖ * r ^ 2 - a ^ 2‖ := le_norm_lam_sub_sq hϖ hr a
    _ ≤ δ * ‖(b : F)‖ := hc
    _ = ‖(b : F)‖ * δ := mul_comm _ _

variable [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]

attribute [local instance] secondCountableTopology_units

theorem measurableSet_Rset (δ : ℝ) (lam : F) : MeasurableSet (Rset δ lam) :=
  (isClosed_Rset δ lam).measurableSet

theorem measurable_chartFn_chi (δ : ℝ) (lam : F) : Measurable (chartFn (chi δ) lam) := by
  rw [chartFn_chi]; exact measurable_const.indicator (measurableSet_Rset δ lam)

theorem integral_chartFn_chi (δ : ℝ) (lam : F) :
    ∫ p, chartFn (chi δ) lam p ∂(ν.prod μ) = (((ν.prod μ).real (Rset δ lam) : ℝ) : ℂ) := by
  rw [chartFn_chi, integral_indicator_const _ (measurableSet_Rset δ lam), Complex.real_smul, mul_one]

theorem measure_Rset_lt_top {δ : ℝ} (hδ : 0 < δ) (hϖ : Parity ϖ) {r : F} (hr : r ≠ 0) :
    (ν.prod μ) (Rset δ (ϖ * r ^ 2)) < ⊤ := by
  refine (measure_mono (Rset_subset_prod hδ hϖ hr)).trans_lt ?_
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top
    ((isCompact_units_annulus δ (div_pos (norm_lam_pos hϖ hr) hδ)).measure_lt_top)
    ((isCompact_closedBall _ _).measure_lt_top)

theorem measure_Rset_lt {δ : ℝ} {d : F} (hd : d ≠ 0) (hdδ : ‖d‖ = δ) (hϖ : Parity ϖ) {r r' : F}
    (hr' : r' ≠ 0) (hrr' : ‖r'‖ < ‖r‖) (h1 : ‖ϖ * r ^ 2‖ ≤ δ ^ 2) (h3 : ‖ϖ * r ^ 2‖ ≤ 1) :
    (ν.prod μ) (Rset δ (ϖ * r ^ 2)) < (ν.prod μ) (Rset δ (ϖ * r' ^ 2)) := by
  have hδ : 0 < δ := by rw [← hdδ]; exact norm_pos_iff.2 hd
  have hr : r ≠ 0 := ne_zero_of_norm_le hr' hrr'.le
  set lam := ϖ * r ^ 2 with hlam
  set lam' := ϖ * r' ^ 2 with hlam'
  have hlam0 : 0 < ‖lam‖ := norm_lam_pos hϖ hr
  have hlam'0 : 0 < ‖lam'‖ := norm_lam_pos hϖ hr'
  have hlt : ‖lam'‖ < ‖lam‖ := by
    rw [hlam, hlam', norm_mul_sq, norm_mul_sq]
    have hϖ0 : 0 < ‖ϖ‖ := by
      have := hlam0; rw [hlam, norm_mul_sq] at this
      exact pos_of_mul_pos_left this (sq_nonneg _)
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hrr' (norm_nonneg _) two_ne_zero) hϖ0
  have hle : ‖lam'‖ ≤ ‖lam‖ := hlt.le

  set η : ℝ := min δ ‖lam'‖ with hη
  have hη0 : 0 < η := lt_min hδ hlam'0
  set P : Set (Fˣ × F) := {b : Fˣ | ‖(b : F)‖ = ‖lam'‖ / δ} ×ˢ Metric.closedBall (0 : F) η with hP
  have hPsub : P ⊆ Rset δ lam' := by
    rintro ⟨b, a⟩ ⟨hb, ha⟩
    simp only [Set.mem_setOf_eq] at hb
    simp only [Metric.mem_closedBall, dist_zero_right] at ha
    have ha2 : ‖a‖ ^ 2 ≤ ‖lam'‖ := by
      calc ‖a‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
        _ ≤ ‖lam'‖ ^ 2 := pow_le_pow_left₀ hη0.le (min_le_right _ _) 2
        _ ≤ ‖lam'‖ ^ 1 := pow_le_pow_of_le_one hlam'0.le (hle.trans h3) one_le_two
        _ = ‖lam'‖ := pow_one _
    refine ⟨ha.trans (min_le_left _ _), ?_, ?_⟩
    · rw [hb, div_le_iff₀ hδ]; nlinarith [hle.trans h1]
    · rw [norm_div, hb, norm_lam_sub_sq hϖ hr', max_eq_left ha2, div_div_eq_mul_div, mul_div_assoc,
        mul_div_cancel₀ _ hlam'0.ne']
  have hPdisj : Disjoint (Rset δ lam) P := by
    rw [Set.disjoint_left]
    rintro ⟨b, a⟩ ⟨-, -, hc⟩ ⟨hb, -⟩
    simp only [Set.mem_setOf_eq] at hb
    rw [norm_div, hb, div_le_iff₀ (div_pos hlam'0 hδ)] at hc
    have : ‖lam‖ ≤ ‖lam - a ^ 2‖ := le_norm_lam_sub_sq hϖ hr a
    have h4 : ‖lam‖ ≤ ‖lam'‖ := by
      have := this.trans hc
      rwa [mul_div_cancel₀ _ hδ.ne'] at this
    exact absurd h4 (not_le.2 hlt)
  have hPmeas : MeasurableSet P := by
    refine MeasurableSet.prod ?_ measurableSet_closedBall
    exact ((IsUltrametricDist.isOpen_sphere (0 : F) (div_pos hlam'0 hδ).ne').preimage
      Units.continuous_val).measurableSet |> fun h => by
        convert h using 1; ext b; simp
  have hPpos : 0 < (ν.prod μ) P := by
    rw [hP, Measure.prod_prod]
    refine ENNReal.mul_pos ?_ (Metric.measure_closedBall_pos μ _ hη0).ne'
    have hopen : IsOpen {b : Fˣ | ‖(b : F)‖ = ‖lam'‖ / δ} := by
      have := (IsUltrametricDist.isOpen_sphere (0 : F) (div_pos hlam'0 hδ).ne').preimage
        Units.continuous_val
      convert this using 1; ext b; simp
    have hne : {b : Fˣ | ‖(b : F)‖ = ‖lam'‖ / δ}.Nonempty := by
      refine ⟨Units.mk0 (lam' / d) (div_ne_zero (norm_pos_iff.1 hlam'0) hd), ?_⟩
      simp only [Set.mem_setOf_eq, Units.val_mk0, norm_div, hdδ]
    exact (hopen.measure_pos ν hne).ne'
  calc (ν.prod μ) (Rset δ lam)
      < (ν.prod μ) (Rset δ lam) + (ν.prod μ) P := by
        exact ENNReal.lt_add_right (measure_Rset_lt_top μ ν hδ hϖ hr).ne hPpos.ne'
    _ = (ν.prod μ) (Rset δ lam ∪ P) := (measure_union hPdisj hPmeas).symm
    _ ≤ (ν.prod μ) (Rset δ lam') :=
        measure_mono (Set.union_subset (Rset_subset δ hϖ hr' hrr'.le) hPsub)

theorem re_integral_chartFn_chi_lt {δ : ℝ} {d : F} (hd : d ≠ 0) (hdδ : ‖d‖ = δ) (hϖ : Parity ϖ) {r r' : F}
    (hr' : r' ≠ 0) (hrr' : ‖r'‖ < ‖r‖) (h1 : ‖ϖ * r ^ 2‖ ≤ δ ^ 2) (h3 : ‖ϖ * r ^ 2‖ ≤ 1) :
    (∫ p, chartFn (chi δ) (ϖ * r ^ 2) p ∂(ν.prod μ)).re <
      (∫ p, chartFn (chi δ) (ϖ * r' ^ 2) p ∂(ν.prod μ)).re := by
  have hδ : 0 < δ := by rw [← hdδ]; exact norm_pos_iff.2 hd
  rw [integral_chartFn_chi, integral_chartFn_chi, Complex.ofReal_re, Complex.ofReal_re, measureReal_def,
    measureReal_def, ENNReal.toReal_lt_toReal (measure_Rset_lt_top μ ν hδ hϖ (ne_zero_of_norm_le hr' hrr'.le)).ne
      (measure_Rset_lt_top μ ν hδ hϖ hr').ne]
  exact measure_Rset_lt μ ν hd hdδ hϖ hr' hrr' h1 h3

end ClaimB
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

end P2mEllipticGerm
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

namespace P2mEllipticGerm

section Main

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
  [ProperSpace F] [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]

attribute [local instance] secondCountableTopology_units

theorem measurable_chartFn_of_continuous {Φ : Matrix (Fin 2) (Fin 2) F → ℂ} (hΦ : Continuous Φ) (lam : F) :
    Measurable (chartFn Φ lam) :=
  (hΦ.comp (continuous_chart lam)).measurable

theorem continuous_one_add_E10 : Continuous fun x : F => (1 : Matrix (Fin 2) (Fin 2) F) + E10 x := by
  refine continuous_const.add (continuous_matrix fun i j => ?_)
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_id
  · exact continuous_const

theorem chi_one_add_E10 {δ : ℝ} (hδ : 0 ≤ δ) (x : F) :
    chi δ (1 + E10 x) = {x : F | ‖x‖ ≤ δ}.indicator (fun _ => (1 : ℂ)) x := by
  by_cases hx : ‖x‖ ≤ δ
  · rw [Set.indicator_of_mem (by exact hx), chi_one_add _ (entryLE_E10 hδ hx)]
  · rw [Set.indicator_of_notMem (by exact hx), chi_of_not_mem]
    rw [add_sub_cancel_left]
    intro h
    exact hx (by simpa [E10] using h 1 0)

theorem exists_norm_le_ne_zero {δ : ℝ} (hδ : 0 < δ) : ∃ d : F, d ≠ 0 ∧ ‖d‖ ≤ δ := by
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one F
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hx1
  refine ⟨x ^ n, pow_ne_zero _ (norm_pos_iff.1 hx0), ?_⟩
  rw [norm_pow]; exact hn.le

theorem apply_one_eq_zero (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (hΦ : IsLocallyConstant Φ)
    (hΦc : HasCompactSupport Φ) (ϖ : F) (hϖ1 : ‖ϖ‖ < 1) (hϖ : Parity ϖ)
    (hvan : ∀ ε : ℝ, 0 < ε → ∃ r r' : F, r' ≠ 0 ∧ ‖r'‖ < ‖r‖ ∧ ‖r‖ < ε ∧
      (∫ b, ∫ a, Φ (1 + !![a, (b : F); (ϖ * r ^ 2 - a ^ 2) / b, -a]) ∂μ ∂ν) = 0 ∧
      (∫ b, ∫ a, Φ (1 + !![a, (b : F); (ϖ * r' ^ 2 - a ^ 2) / b, -a]) ∂μ ∂ν) = 0) :
    Φ 1 = 0 := by

  obtain ⟨δ₀, hδ₀, hinv₀⟩ := exists_forall_add_eq hΦ hΦc
  obtain ⟨d, hd, hdle⟩ := exists_norm_le_ne_zero (F := F) (lt_min hδ₀ one_pos)
  set δ : ℝ := ‖d‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.2 hd
  have hδ1 : δ ≤ 1 := hdle.trans (min_le_right _ _)
  have hinvΦ : ∀ M E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Φ (M + E) = Φ M :=
    fun M E hE => hinv₀ M E (hE.mono (hdle.trans (min_le_left _ _)))

  obtain ⟨B, hB, hsuppΦ⟩ := exists_bound_of_ne_zero hΦc
  obtain ⟨C, hCΦ⟩ := exists_norm_apply_le hΦ hΦc
  have hB0 : 0 < B := one_pos.trans_le hB

  set Ψ : Matrix (Fin 2) (Fin 2) F → ℂ := fun M => Φ M - Φ 1 * chi δ M with hΨdef
  have hinvΨ : ∀ M E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Ψ (M + E) = Ψ M := by
    intro M E hE; simp only [hΨdef, hinvΦ M E hE, chi_add M E hE]
  have hsuppχ : ∀ M : Matrix (Fin 2) (Fin 2) F, chi δ M ≠ 0 → EntryLE M B :=
    fun M h => (entryLE_of_chi_ne_zero hδ1 h).mono hB
  have hsuppΨ : ∀ M, Ψ M ≠ 0 → EntryLE M B := by
    intro M hM
    by_cases h1 : Φ M ≠ 0
    · exact hsuppΦ M h1
    · rw [not_ne_iff] at h1
      have : chi δ M ≠ 0 := by
        intro h2; apply hM; simp only [hΨdef, h1, h2, mul_zero, sub_zero]
      exact hsuppχ M this
  have hbddχ : ∀ M : Matrix (Fin 2) (Fin 2) F, ‖chi δ M‖ ≤ 1 := norm_chi_le δ
  have hbddΨ : ∀ M, ‖Ψ M‖ ≤ C + ‖Φ 1‖ := by
    intro M
    calc ‖Ψ M‖ ≤ ‖Φ M‖ + ‖Φ 1 * chi δ M‖ := norm_sub_le _ _
      _ ≤ C + ‖Φ 1‖ * 1 := add_le_add (hCΦ M) (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hbddχ M) (norm_nonneg _))
      _ = C + ‖Φ 1‖ := by rw [mul_one]
  have hvan1 : ∀ E : Matrix (Fin 2) (Fin 2) F, EntryLE E δ → Ψ (1 + E) = 0 := by
    intro E hE
    simp only [hΨdef, hinvΦ 1 E hE, chi_one_add E hE, mul_one, sub_self]

  have hmeasΦ : ∀ lam : F, Measurable (chartFn Φ lam) := measurable_chartFn_of_continuous hΦ.continuous
  have hmeasχ : ∀ lam : F, Measurable (chartFn (chi δ) lam) := fun lam => measurable_chartFn_chi δ lam
  have hΨchart : ∀ lam : F, chartFn Ψ lam = fun p => chartFn Φ lam p - Φ 1 * chartFn (chi δ) lam p := by
    intro lam; funext p; rfl
  have hmeasΨ : ∀ lam : F, Measurable (chartFn Ψ lam) := by
    intro lam; rw [hΨchart]; exact (hmeasΦ lam).sub ((hmeasχ lam).const_mul _)

  set ε : ℝ := δ ^ 2 / B with hεdef
  have hε : 0 < ε := div_pos (pow_pos hδ 2) hB0
  obtain ⟨r, r', hr', hrr', hrε, hI, hI'⟩ := hvan ε hε
  have hr : r ≠ 0 := ne_zero_of_norm_le hr' hrr'.le
  have hlam_le : ‖ϖ * r ^ 2‖ ≤ δ ^ 3 / B := by
    rw [norm_mul_sq]
    have hr2 : ‖r‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hrε.le 2
    have hε2 : ε ^ 2 ≤ δ ^ 3 / B := by
      rw [hεdef, div_pow, div_le_div_iff₀ (pow_pos hB0 2) hB0]
      have hδB : δ ≤ B := hδ1.trans hB
      have h0 : 0 ≤ δ ^ 3 * B := by positivity
      calc (δ ^ 2) ^ 2 * B = δ ^ 3 * B * δ := by ring
        _ ≤ δ ^ 3 * B * B := mul_le_mul_of_nonneg_left hδB h0
        _ = δ ^ 3 * B ^ 2 := by ring
    calc ‖ϖ‖ * ‖r‖ ^ 2 ≤ 1 * ‖r‖ ^ 2 := mul_le_mul_of_nonneg_right hϖ1.le (sq_nonneg _)
      _ ≤ δ ^ 3 / B := by rw [one_mul]; exact hr2.trans hε2
  have h2 : ‖ϖ * r ^ 2‖ * B ≤ δ ^ 3 := by rwa [← le_div_iff₀ hB0]
  have h1 : ‖ϖ * r ^ 2‖ ≤ δ ^ 2 := by
    refine hlam_le.trans ?_
    rw [div_le_iff₀ hB0]
    nlinarith [pow_pos hδ 2, hδ1, hB]
  have h3 : ‖ϖ * r ^ 2‖ ≤ 1 := h1.trans (by nlinarith [hδ1, hδ])

  have hintΦ : ∀ {s : F}, s ≠ 0 → Integrable (chartFn Φ (ϖ * s ^ 2)) (ν.prod μ) :=
    fun hs => integrable_chartFn μ ν hB hsuppΦ hCΦ hϖ hs (hmeasΦ _)
  have hintχ : ∀ {s : F}, s ≠ 0 → Integrable (chartFn (chi δ) (ϖ * s ^ 2)) (ν.prod μ) :=
    fun hs => integrable_chartFn μ ν hB hsuppχ hbddχ hϖ hs (hmeasχ _)
  have hintΨ : ∀ {s : F}, s ≠ 0 → Integrable (chartFn Ψ (ϖ * s ^ 2)) (ν.prod μ) :=
    fun hs => integrable_chartFn μ ν hB hsuppΨ hbddΨ hϖ hs (hmeasΨ _)
  rw [integral_integral_eq_integral_prod μ ν (hintΦ hr)] at hI
  rw [integral_integral_eq_integral_prod μ ν (hintΦ hr')] at hI'

  have hlin : ∀ {s : F}, s ≠ 0 →
      ∫ p, chartFn Φ (ϖ * s ^ 2) p ∂(ν.prod μ) =
        Φ 1 * ∫ p, chartFn (chi δ) (ϖ * s ^ 2) p ∂(ν.prod μ) + ∫ p, chartFn Ψ (ϖ * s ^ 2) p ∂(ν.prod μ) := by
    intro s hs
    have : chartFn Φ (ϖ * s ^ 2) = fun p => Φ 1 * chartFn (chi δ) (ϖ * s ^ 2) p + chartFn Ψ (ϖ * s ^ 2) p := by
      funext p; rw [hΨchart]; ring
    rw [this, integral_add ((hintχ hs).const_mul _) (hintΨ hs), integral_const_mul]

  have hA := integral_chartFn_eq_of_vanish_near_one (μ := μ) (ν := ν) hδ hB hinvΨ hsuppΨ hbddΨ hvan1 hϖ hr'
    hrr'.le (hmeasΨ _) (hmeasΨ _) h1 h2
  have hBlt := re_integral_chartFn_chi_lt μ ν hd hδdef.symm hϖ hr' hrr' h1 h3
  rw [hlin hr] at hI
  rw [hlin hr'] at hI'
  have hdiff : Φ 1 * (∫ p, chartFn (chi δ) (ϖ * r ^ 2) p ∂(ν.prod μ) -
      ∫ p, chartFn (chi δ) (ϖ * r' ^ 2) p ∂(ν.prod μ)) = 0 := by
    have := congrArg₂ (· - ·) hI hI'
    simp only [sub_zero] at this
    rw [hA] at this
    linear_combination this
  rcases mul_eq_zero.1 hdiff with h | h
  · exact h
  · exfalso
    have := congrArg Complex.re (sub_eq_zero.1 h)
    exact (ne_of_lt hBlt) this

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

end P2mEllipticGerm
p2m_reactivate "P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero.P2mEllipticGerm"

open MeasureTheory in
theorem solution
    {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (μ : Measure F) [μ.IsAddHaarMeasure] (ν : Measure Fˣ) [ν.IsHaarMeasure]
    (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (ϖ : F) (hϖ : ‖ϖ‖ < 1) (hϖsq : ∀ a t : F, t ≠ 0 → ‖a‖ ^ 2 ≠ ‖ϖ‖ * ‖t‖ ^ 2)
    (hvan : ∀ ε : ℝ, 0 < ε → ∃ r r' : F, r' ≠ 0 ∧ ‖r'‖ < ‖r‖ ∧ ‖r‖ < ε ∧
      (∫ b, ∫ a, Φ (1 + !![a, (b : F); (ϖ * r ^ 2 - a ^ 2) / b, -a]) ∂μ ∂ν) = 0 ∧
      (∫ b, ∫ a, Φ (1 + !![a, (b : F); (ϖ * r' ^ 2 - a ^ 2) / b, -a]) ∂μ ∂ν) = 0) :
    Φ 1 = 0 :=
  P2mEllipticGerm.apply_one_eq_zero μ ν Φ hΦ hΦc ϖ hϖ hϖsq hvan

end
end S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_apply_one_eq_zero_of_isLocallyConstant_of_forall_exists_integral_integral_eq_zero (solution)
