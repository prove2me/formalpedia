-- Prove2me | solution 1 for AutomorphicForm.GL2Real.withDensity_volume_iwasawaBox_eq_two_mul_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/efd3a4ba-d214-574d-a2f9-d570f0f8c10d

import Mathlib
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory Set AutomorphicForm
open scoped ENNReal Real

noncomputable section

namespace P2mIwasawaBox

def rotAB (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : GL (Fin 2) ℝ :=
  ⟨!![a, b; -b, a], !![a, -b; b, a],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination h | ring,
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination h | ring⟩

@[scoped simp] theorem rotAB_val (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ((rotAB a b h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a] := rfl

theorem rotAB_mem (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : rotAB a b h ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [rotAB_val, Matrix.det_fin_two_of]
    linear_combination h
  · rw [rotAB_val, Matrix.det_fin_two_of]
    rw [show a * a - b * -b = 1 by linear_combination h, norm_one]
  · intro x y
    simp only [rotAB_val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * h

theorem exists_angle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ ∈ Set.Icc (-Real.pi) Real.pi, Real.cos θ = a ∧ Real.sin θ = b := by
  set z : ℂ := ⟨a, b⟩ with hz
  have hz1 : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      nlinarith [h]
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [h2, h0]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz1
    exact zero_ne_one hz1
  refine ⟨Complex.arg z, ⟨(Complex.arg_mem_Ioc z).1.le, (Complex.arg_mem_Ioc z).2⟩, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hz1, div_one]
  · rw [Complex.sin_arg, hz1, div_one]

abbrev P : Type := (ℝ × ℝ) × (ℝ × ℝ)

def Bset : Set P :=
  {p | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ x ∈ Set.Icc (0 : ℝ) 1,
      ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧
        p = ((b₁ * a - b₁ * x * b, b₁ * b + b₁ * x * a), (-(b₂ * b), b₂ * a))}

def dP (p : P) : ℝ≥0∞ := (ENNReal.ofReal ((p.1.1 * p.2.2 - p.1.2 * p.2.1) ^ 2))⁻¹

def G (p : P) : ℝ≥0∞ := Bset.indicator dP p

def rad (w : ℝ × ℝ) : ℝ := Real.sqrt (w.1 ^ 2 + w.2 ^ 2)

theorem rad_nonneg (w : ℝ × ℝ) : 0 ≤ rad w := Real.sqrt_nonneg _

theorem rad_sq (w : ℝ × ℝ) : rad w ^ 2 = w.1 ^ 2 + w.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem continuous_rad : Continuous rad :=
  ((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt

def chart (q : (ℝ × ℝ × ℝ) × ℝ) : P :=
  ((q.1.1 * Real.cos q.2 - q.1.1 * q.1.2.2 * Real.sin q.2, q.1.1 * Real.sin q.2 + q.1.1 * q.1.2.2 * Real.cos q.2),
    (-(q.1.2.1 * Real.sin q.2), q.1.2.1 * Real.cos q.2))

theorem continuous_chart : Continuous chart := by
  have c1 : Continuous fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.1 := continuous_fst.comp continuous_fst
  have c2 : Continuous fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_fst)
  have c3 : Continuous fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_fst)
  have cc : Continuous fun q : (ℝ × ℝ × ℝ) × ℝ => Real.cos q.2 := Real.continuous_cos.comp continuous_snd
  have cs : Continuous fun q : (ℝ × ℝ × ℝ) × ℝ => Real.sin q.2 := Real.continuous_sin.comp continuous_snd
  unfold chart
  exact (((c1.mul cc).sub ((c1.mul c3).mul cs)).prodMk ((c1.mul cs).add ((c1.mul c3).mul cc))).prodMk
    ((c2.mul cs).neg.prodMk (c2.mul cc))

def paramBox : Set ((ℝ × ℝ × ℝ) × ℝ) :=
  (Set.Icc 1 (Real.exp 1) ×ˢ Set.Icc 1 (Real.exp 1) ×ˢ Set.Icc 0 1) ×ˢ Set.Icc (-Real.pi) Real.pi

theorem isCompact_paramBox : IsCompact paramBox :=
  ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc)

theorem Bset_eq_image : Bset = chart '' paramBox := by
  ext p
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, x, hx, a, b, hab, rfl⟩
    obtain ⟨θ, hθ, hcos, hsin⟩ := exists_angle hab
    refine ⟨((b₁, b₂, x), θ), ⟨⟨hb₁, hb₂, hx⟩, hθ⟩, ?_⟩
    simp only [chart, hcos, hsin]
  · rintro ⟨⟨⟨b₁, b₂, x⟩, θ⟩, ⟨⟨hb₁, hb₂, hx⟩, hθ⟩, rfl⟩
    exact ⟨b₁, hb₁, b₂, hb₂, x, hx, Real.cos θ, Real.sin θ, Real.cos_sq_add_sin_sq θ, by
      simp only [chart]⟩

theorem isCompact_Bset : IsCompact Bset := by
  rw [Bset_eq_image]; exact isCompact_paramBox.image continuous_chart

theorem measurableSet_Bset : MeasurableSet Bset := isCompact_Bset.isClosed.measurableSet

theorem measurable_dP : Measurable dP := by
  unfold dP
  exact (ENNReal.measurable_ofReal.comp (((measurable_fst.fst.mul measurable_snd.snd).sub
    (measurable_fst.snd.mul measurable_snd.fst)).pow_const 2)).inv

theorem measurable_G : Measurable G := measurable_dP.indicator measurableSet_Bset

theorem rad_mem_of_mem_Bset {v w : ℝ × ℝ} (h : (v, w) ∈ Bset) : rad w ∈ Set.Icc (1 : ℝ) (Real.exp 1) := by
  obtain ⟨b₁, hb₁, b₂, hb₂, x, hx, a, b, hab, hp⟩ := h
  have hw : w = (-(b₂ * b), b₂ * a) := (Prod.ext_iff.mp hp).2
  have hb2 : 0 ≤ b₂ := le_trans zero_le_one hb₂.1
  have : rad w = b₂ := by
    rw [rad, hw]
    have : (-(b₂ * b)) ^ 2 + (b₂ * a) ^ 2 = b₂ ^ 2 := by linear_combination b₂ ^ 2 * hab
    rw [this, Real.sqrt_sq hb2]
  rw [this]; exact hb₂

def rot (a b : ℝ) (u : ℝ × ℝ) : ℝ × ℝ := (u.1 * a - u.2 * b, u.1 * b + u.2 * a)

def Treg : Set (ℝ × ℝ) := {u | u.1 ∈ Set.Icc (1 : ℝ) (Real.exp 1) ∧ 0 ≤ u.2 ∧ u.2 ≤ u.1}

theorem rot_injective {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) : Function.Injective (rot a b) := by
  intro u u' h
  simp only [rot, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : u.1 = u'.1 := by linear_combination a * h1 + b * h2 + (u'.1 - u.1) * hab
  have e2 : u.2 = u'.2 := by linear_combination (-b) * h1 + a * h2 + (u'.2 - u.2) * hab
  exact Prod.ext e1 e2

theorem continuous_rot (a b : ℝ) : Continuous (rot a b) := by
  unfold rot
  exact ((continuous_fst.mul continuous_const).sub (continuous_snd.mul continuous_const)).prodMk
    ((continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const))

theorem isClosed_Treg : IsClosed Treg := by
  have h1 : IsClosed {u : ℝ × ℝ | u.1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)} := isClosed_Icc.preimage continuous_fst
  have h2 : IsClosed {u : ℝ × ℝ | 0 ≤ u.2} := isClosed_le continuous_const continuous_snd
  have h3 : IsClosed {u : ℝ × ℝ | u.2 ≤ u.1} := isClosed_le continuous_snd continuous_fst
  have : Treg = {u : ℝ × ℝ | u.1 ∈ Set.Icc (1 : ℝ) (Real.exp 1)} ∩ ({u | 0 ≤ u.2} ∩ {u | u.2 ≤ u.1}) := by
    ext u; simp [Treg]
  rw [this]
  exact h1.inter (h2.inter h3)

theorem Treg_subset : Treg ⊆ Set.Icc (1 : ℝ) (Real.exp 1) ×ˢ Set.Icc (0 : ℝ) (Real.exp 1) := by
  rintro ⟨α, β⟩ ⟨hα, hβ0, hβα⟩
  exact ⟨hα, hβ0, hβα.trans hα.2⟩

theorem isCompact_Treg : IsCompact Treg :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_Treg Treg_subset

theorem measurableSet_Treg : MeasurableSet Treg := isClosed_Treg.measurableSet

theorem measurableSet_rot_image (a b : ℝ) : MeasurableSet (rot a b '' Treg) :=
  (isCompact_Treg.image (continuous_rot a b)).isClosed.measurableSet

theorem mem_Bset_iff {w : ℝ × ℝ} (hw : rad w ∈ Set.Icc (1 : ℝ) (Real.exp 1)) (v : ℝ × ℝ) :
    (v, w) ∈ Bset ↔ v ∈ rot (w.2 / rad w) (-w.1 / rad w) '' Treg := by
  set r := rad w with hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hw.1
  have hrne : r ≠ 0 := hr0.ne'
  have hrsq : r ^ 2 = w.1 ^ 2 + w.2 ^ 2 := rad_sq w
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, x, hx, a, b, hab, hp⟩
    obtain ⟨hv, hw'⟩ := Prod.ext_iff.mp hp
    simp only at hv hw'
    have hb2 : 0 ≤ b₂ := le_trans zero_le_one hb₂.1
    have hrb : r = b₂ := by
      rw [hr, rad, hw']
      have : (-(b₂ * b)) ^ 2 + (b₂ * a) ^ 2 = b₂ ^ 2 := by linear_combination b₂ ^ 2 * hab
      rw [this, Real.sqrt_sq hb2]
    have hb2ne : b₂ ≠ 0 := (lt_of_lt_of_le one_pos hb₂.1).ne'
    have ha : w.2 / r = a := by
      rw [hrb, hw']
      show b₂ * a / b₂ = a
      rw [mul_comm]; exact mul_div_cancel_right₀ a hb2ne
    have hb : -w.1 / r = b := by
      rw [hrb, hw']
      show -(-(b₂ * b)) / b₂ = b
      rw [neg_neg, mul_comm]; exact mul_div_cancel_right₀ b hb2ne
    rw [ha, hb]
    refine ⟨(b₁, b₁ * x), ⟨hb₁, ?_, ?_⟩, ?_⟩
    · exact mul_nonneg (le_trans zero_le_one hb₁.1) hx.1
    · have := mul_le_mul_of_nonneg_left hx.2 (le_trans zero_le_one hb₁.1)
      simpa using this
    · rw [hv]
      refine Prod.ext ?_ ?_ <;> dsimp only [rot]
  · rintro ⟨⟨α, β⟩, ⟨hα, hβ0, hβα⟩, rfl⟩
    have hα0 : 0 < α := lt_of_lt_of_le one_pos hα.1
    have hab : (w.2 / r) ^ 2 + (-w.1 / r) ^ 2 = 1 := by
      rw [div_pow, div_pow, neg_sq, ← add_div, add_comm, ← hrsq]
      exact div_self (pow_ne_zero 2 hrne)
    have h1 : α * (β / α) = β := by rw [mul_comm]; exact div_mul_cancel₀ β hα0.ne'
    have e3 : -(r * (-w.1 / r)) = w.1 := by
      rw [mul_div_assoc', mul_comm, ← mul_div_assoc', div_self hrne]; ring
    have e4 : r * (w.2 / r) = w.2 := by
      rw [mul_comm]; exact div_mul_cancel₀ w.2 hrne
    refine ⟨α, hα, r, hw, β / α, ⟨div_nonneg hβ0 hα0.le, (div_le_one hα0).mpr hβα⟩, w.2 / r, -w.1 / r, hab, ?_⟩
    rw [h1, e3, e4]
    refine Prod.ext (Prod.ext ?_ ?_) rfl <;> dsimp only [rot]

theorem G_eq_zero_of_not_mem {w : ℝ × ℝ} (hw : rad w ∉ Set.Icc (1 : ℝ) (Real.exp 1)) (v : ℝ × ℝ) :
    G (v, w) = 0 := by
  unfold G
  rw [Set.indicator_of_notMem]
  exact fun h => hw (rad_mem_of_mem_Bset h)

def rotM (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, -b; b, a]

theorem rot_eq (a b : ℝ) :
    rot a b = (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ∘ (Matrix.toLin' (rotM a b)) ∘
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm := by
  funext u
  simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply, MeasurableEquiv.finTwoArrow_symm_apply,
    Matrix.toLin'_apply, rotM, rot]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor <;> ring

theorem measurePreserving_rot {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    MeasurePreserving (rot a b) (volume : Measure (ℝ × ℝ)) volume := by
  have hdet : (rotM a b).det = 1 := by
    rw [rotM, Matrix.det_fin_two_of]; linear_combination hab
  have hlin : MeasurePreserving (Matrix.toLin' (rotM a b)) (volume : Measure (Fin 2 → ℝ)) volume := by
    refine ⟨(Matrix.toLin' (rotM a b)).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  rw [rot_eq]
  exact ((volume_preserving_finTwoArrow ℝ).comp hlin).comp (volume_preserving_finTwoArrow ℝ).symm

theorem lintegral_inv_Icc : ∫⁻ α in Set.Icc (1 : ℝ) (Real.exp 1), ENNReal.ofReal (α⁻¹) = 1 := by
  have hle : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hcont : ContinuousOn (fun α : ℝ => α⁻¹) (Set.Icc (1 : ℝ) (Real.exp 1)) :=
    continuousOn_inv₀.mono fun α hα => (lt_of_lt_of_le one_pos hα.1).ne'
  have hint : IntegrableOn (fun α : ℝ => α⁻¹) (Set.Icc (1 : ℝ) (Real.exp 1)) volume :=
    hcont.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) (Real.exp 1))] fun α : ℝ => α⁻¹ := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun α hα => inv_nonneg.mpr (le_trans zero_le_one hα.1)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle, integral_inv_of_pos one_pos (Real.exp_pos 1), div_one, Real.log_exp,
    ENNReal.ofReal_one]

theorem lintegral_Treg (r : ℝ) (hr : 0 < r) :
    ∫⁻ u, Treg.indicator (fun u : ℝ × ℝ => ENNReal.ofReal (((r * u.1) ^ 2)⁻¹)) u ∂(volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal ((r ^ 2)⁻¹) := by
  have hmeas : Measurable (Treg.indicator fun u : ℝ × ℝ => ENNReal.ofReal (((r * u.1) ^ 2)⁻¹)) := by
    refine Measurable.indicator ?_ measurableSet_Treg
    exact ENNReal.measurable_ofReal.comp ((measurable_const.mul measurable_fst).pow_const 2).inv
  rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]

  have hinner : ∀ α : ℝ, ∫⁻ β, Treg.indicator (fun u : ℝ × ℝ => ENNReal.ofReal (((r * u.1) ^ 2)⁻¹)) (α, β) =
      (Set.Icc (1 : ℝ) (Real.exp 1)).indicator
        (fun α => ENNReal.ofReal (((r * α) ^ 2)⁻¹) * ENNReal.ofReal α) α := by
    intro α
    by_cases hα : α ∈ Set.Icc (1 : ℝ) (Real.exp 1)
    · rw [Set.indicator_of_mem hα]
      have hα0 : 0 ≤ α := le_trans zero_le_one hα.1
      have heq : (fun β => Treg.indicator (fun u : ℝ × ℝ => ENNReal.ofReal (((r * u.1) ^ 2)⁻¹)) (α, β)) =
          (Set.Icc 0 α).indicator (fun _ => ENNReal.ofReal (((r * α) ^ 2)⁻¹)) := by
        funext β
        by_cases hβ : β ∈ Set.Icc 0 α
        · rw [Set.indicator_of_mem hβ, Set.indicator_of_mem (show (α, β) ∈ Treg from ⟨hα, hβ.1, hβ.2⟩)]
        · rw [Set.indicator_of_notMem hβ, Set.indicator_of_notMem]
          rintro ⟨_, h1, h2⟩; exact hβ ⟨h1, h2⟩
      rw [heq, lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc, sub_zero]
    · rw [Set.indicator_of_notMem hα]
      have heq : (fun β => Treg.indicator (fun u : ℝ × ℝ => ENNReal.ofReal (((r * u.1) ^ 2)⁻¹)) (α, β)) =
          fun _ => 0 := by
        funext β
        rw [Set.indicator_of_notMem]
        rintro ⟨h1, _, _⟩; exact hα h1
      rw [heq, lintegral_zero]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Icc]
  have heq2 : ∀ α ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      ENNReal.ofReal (((r * α) ^ 2)⁻¹) * ENNReal.ofReal α = ENNReal.ofReal ((r ^ 2)⁻¹) * ENNReal.ofReal (α⁻¹) := by
    intro α hα
    have hα0 : 0 < α := lt_of_lt_of_le one_pos hα.1
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Icc heq2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_inv_Icc, mul_one]

theorem lintegral_annulus :
    ∫⁻ w, (rad ⁻¹' Set.Icc (1 : ℝ) (Real.exp 1)).indicator (fun w => ENNReal.ofReal ((rad w ^ 2)⁻¹)) w
        ∂(volume : Measure (ℝ × ℝ)) = ENNReal.ofReal (2 * Real.pi) := by
  set F : ℝ × ℝ → ℝ≥0∞ :=
    (rad ⁻¹' Set.Icc (1 : ℝ) (Real.exp 1)).indicator (fun w => ENNReal.ofReal ((rad w ^ 2)⁻¹)) with hF
  rw [← lintegral_comp_polarCoord_symm F]

  set g : ℝ → ℝ≥0∞ := (Set.Icc (1 : ℝ) (Real.exp 1)).indicator fun t => ENNReal.ofReal (t⁻¹) with hg
  have hmeas_g : Measurable g := (ENNReal.measurable_ofReal.comp measurable_inv).indicator measurableSet_Icc
  have hcongr : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • F (polarCoord.symm p) = g p.1 * 1 := by
    rintro ⟨t, θ⟩ ⟨ht, hθ⟩
    simp only [Set.mem_Ioi] at ht
    have hrad : rad (polarCoord.symm (t, θ)) = t := by
      rw [rad, polarCoord_symm_apply]
      simp only
      have : (t * Real.cos θ) ^ 2 + (t * Real.sin θ) ^ 2 = t ^ 2 := by
        linear_combination t ^ 2 * Real.cos_sq_add_sin_sq θ
      rw [this, Real.sqrt_sq ht.le]
    rw [mul_one, smul_eq_mul, hF]
    simp only
    by_cases hmem : t ∈ Set.Icc (1 : ℝ) (Real.exp 1)
    · rw [Set.indicator_of_mem (show polarCoord.symm (t, θ) ∈ rad ⁻¹' Set.Icc (1 : ℝ) (Real.exp 1) by
        rw [Set.mem_preimage, hrad]; exact hmem), hrad, hg, Set.indicator_of_mem hmem,
        ← ENNReal.ofReal_mul ht.le]
      congr 1
      field_simp
    · rw [Set.indicator_of_notMem (show polarCoord.symm (t, θ) ∉ rad ⁻¹' Set.Icc (1 : ℝ) (Real.exp 1) by
        rw [Set.mem_preimage, hrad]; exact hmem), hg, Set.indicator_of_notMem hmem, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hcongr]
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
  rw [htarget, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict,
    lintegral_prod_mul hmeas_g.aemeasurable aemeasurable_const,
    lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, one_mul]

  have hrad_int : ∫⁻ t in Set.Ioi (0 : ℝ), g t = 1 := by
    rw [hg, lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have : Set.Icc (1 : ℝ) (Real.exp 1) ∩ Set.Ioi 0 = Set.Icc (1 : ℝ) (Real.exp 1) := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, lt_of_lt_of_le one_pos h.1⟩
    rw [this, lintegral_inv_Icc]
  rw [hrad_int, one_mul]
  congr 1; ring

theorem lintegral_G_section (w : ℝ × ℝ) :
    ∫⁻ v, G (v, w) ∂(volume : Measure (ℝ × ℝ)) =
      (rad ⁻¹' Set.Icc (1 : ℝ) (Real.exp 1)).indicator (fun w => ENNReal.ofReal ((rad w ^ 2)⁻¹)) w := by
  by_cases hw : rad w ∈ Set.Icc (1 : ℝ) (Real.exp 1)
  · rw [Set.indicator_of_mem (show w ∈ rad ⁻¹' Set.Icc (1 : ℝ) (Real.exp 1) from hw)]
    set r := rad w with hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hw.1
    have hrsq : r ^ 2 = w.1 ^ 2 + w.2 ^ 2 := rad_sq w
    set a := w.2 / r with ha
    set b := -w.1 / r with hb
    have hab : a ^ 2 + b ^ 2 = 1 := by
      rw [ha, hb]; field_simp; linarith [hrsq]
    have hw1 : w.1 = -(r * b) := by rw [hb]; field_simp
    have hw2 : w.2 = r * a := by rw [ha]; field_simp

    have hGv : (fun v => G (v, w)) = (rot a b '' Treg).indicator fun v => dP (v, w) := by
      funext v
      unfold G
      by_cases hv : v ∈ rot a b '' Treg
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem ((mem_Bset_iff hw v).mpr hv)]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem]
        exact fun h => hv ((mem_Bset_iff hw v).mp h)
    rw [hGv]

    have hmeasF : Measurable ((rot a b '' Treg).indicator fun v => dP (v, w)) :=
      (measurable_dP.comp (measurable_id.prodMk measurable_const)).indicator (measurableSet_rot_image a b)
    rw [← (measurePreserving_rot hab).lintegral_comp hmeasF]
    have hcomp : (fun u => (rot a b '' Treg).indicator (fun v => dP (v, w)) (rot a b u)) =
        Treg.indicator fun u : ℝ × ℝ => ENNReal.ofReal (((r * u.1) ^ 2)⁻¹) := by
      funext u
      by_cases hu : u ∈ Treg
      · rw [Set.indicator_of_mem ((rot_injective hab).mem_set_image.mpr hu), Set.indicator_of_mem hu, dP]
        have hdet : (rot a b u).1 * w.2 - (rot a b u).2 * w.1 = r * u.1 := by
          simp only [rot]
          rw [hw1, hw2]
          linear_combination (r * u.1) * hab
        have hu0 : 0 < u.1 := lt_of_lt_of_le one_pos hu.1.1
        have hpos : 0 < (r * u.1) ^ 2 := by positivity
        show (ENNReal.ofReal (((rot a b u).1 * w.2 - (rot a b u).2 * w.1) ^ 2))⁻¹ = _
        rw [hdet, ENNReal.ofReal_inv_of_pos hpos]
      · rw [Set.indicator_of_notMem (fun h => hu ((rot_injective hab).mem_set_image.mp h)),
          Set.indicator_of_notMem hu]
    rw [hcomp, lintegral_Treg r hr0]
  · rw [Set.indicator_of_notMem (show w ∉ rad ⁻¹' Set.Icc (1 : ℝ) (Real.exp 1) from hw)]
    have : (fun v => G (v, w)) = fun _ => 0 := funext (G_eq_zero_of_not_mem hw)
    rw [this, lintegral_zero]

theorem lintegral_G : ∫⁻ p, G p ∂(volume : Measure P) = ENNReal.ofReal (2 * Real.pi) := by
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ measurable_G.aemeasurable]
  simp_rw [lintegral_G_section]
  exact lintegral_annulus

abbrev Ent : Type := Fin 2 → Fin 2 → ℝ

def Ψ : Ent ≃ᵐ P :=
  (MeasurableEquiv.piFinTwo fun _ : Fin 2 => Fin 2 → ℝ).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow)

theorem Ψ_apply (q : Ent) : Ψ q = ((q 0 0, q 0 1), (q 1 0, q 1 1)) := rfl

theorem measurePreserving_Ψ : MeasurePreserving Ψ (volume : Measure Ent) (volume : Measure P) := by
  have h1 := volume_preserving_piFinTwo fun _ : Fin 2 => Fin 2 → ℝ
  have h2 : MeasurePreserving (Prod.map (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
      (volume : Measure ((Fin 2 → ℝ) × (Fin 2 → ℝ))) (volume : Measure P) :=
    (volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ)
  exact h2.comp h1

def boxSet : Set Ent :=
  {q | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
      ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
      Matrix.of q = !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}

theorem mem_boxSet_iff (q : Ent) : q ∈ boxSet ↔ Ψ q ∈ Bset := by
  rw [Ψ_apply]
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, x, hx, k, hq⟩
    obtain ⟨h10, h11, hsq⟩ := entries_of_mem_rowIsometrySubgroup₀ k.2
    set a := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0
    set b := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1
    have hk : ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; -b, a] := by
      rw [Matrix.eta_fin_two ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), h10, h11]
    rw [hk] at hq
    have e00 := congrFun (congrFun hq 0) 0
    have e01 := congrFun (congrFun hq 0) 1
    have e10 := congrFun (congrFun hq 1) 0
    have e11 := congrFun (congrFun hq 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    refine ⟨b₁, hb₁, b₂, hb₂, x, hx, a, b, hsq, ?_⟩
    simp only [Prod.mk.injEq]
    exact ⟨⟨by linear_combination e00, by linear_combination e01⟩, by linear_combination e10,
      by linear_combination e11⟩
  · rintro ⟨b₁, hb₁, b₂, hb₂, x, hx, a, b, hab, hp⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨⟨e00, e01⟩, e10, e11⟩ := hp
    refine ⟨b₁, hb₁, b₂, hb₂, x, hx, ⟨rotAB a b hab, rotAB_mem a b hab⟩, ?_⟩
    show Matrix.of q = !![b₁, b₁ * x; 0, b₂] * !![a, b; -b, a]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination e00
        | linear_combination e01
        | linear_combination e10
        | linear_combination e11

theorem boxSet_eq_preimage : boxSet = Ψ ⁻¹' Bset := Set.ext mem_boxSet_iff

theorem measurableSet_boxSet : MeasurableSet boxSet := by
  rw [boxSet_eq_preimage]; exact Ψ.measurable measurableSet_Bset

theorem dens_eq (q : Ent) : (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹ = dP (Ψ q) := by
  rw [dP, Ψ_apply, Matrix.det_fin_two]
  simp only [Matrix.of_apply]

theorem main :
    ((volume : Measure Ent).withDensity fun q => (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹) boxSet =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [withDensity_apply _ measurableSet_boxSet, ← lintegral_indicator measurableSet_boxSet]
  have h : (boxSet.indicator fun q : Ent => (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹) = G ∘ Ψ := by
    funext q
    simp only [Function.comp_apply, G]
    by_cases hq : q ∈ boxSet
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem ((mem_boxSet_iff q).mp hq), dens_eq]
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => hq ((mem_boxSet_iff q).mpr h))]
  rw [h]
  exact (measurePreserving_Ψ.lintegral_comp_emb Ψ.measurableEmbedding G).trans lintegral_G

end P2mIwasawaBox
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi.P2mIwasawaBox"

open P2mIwasawaBox in
theorem solution :
    ((volume : Measure (Fin 2 → Fin 2 → ℝ)).withDensity
        fun q => (ENNReal.ofReal ((Matrix.of q).det ^ 2))⁻¹)
      {q | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
          ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
          Matrix.of q = !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)} =
      ENNReal.ofReal (2 * Real.pi) :=
  main

end
end S_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_withDensity_volume_iwasawaBox_eq_two_mul_pi (solution)
