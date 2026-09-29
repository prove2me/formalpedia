-- Prove2me | solution 1 for AutomorphicForm.GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/afb5ceb2-efc8-5c12-adb7-d66a46cec233

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Theorems.Thm_AutomorphicForm_GL2Real_tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero
import Theorems.Thm_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero
import Theorems.Thm_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi

set_option autoImplicit false

open MeasureTheory Set Filter

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "GL2Real.tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "upperHalfPlaneElt ellipticElt ellipticTransform entrySlice tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero"
namespace RCoord
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

def Mp (r θ : ℝ) (q : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r * (Real.cos θ - q.2), r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1); -(r * q.1), r * (Real.cos θ + q.2)]

def Mm (r θ : ℝ) (q : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r * (Real.cos θ + q.2), -(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1)); r * q.1, r * (Real.cos θ - q.2)]

theorem det_Mp (r θ : ℝ) (q : ℝ × ℝ) (hq : q.1 ≠ 0) : (Mp r θ q).det = r ^ 2 := by
  have h1 : (Real.sin θ ^ 2 + q.2 ^ 2) / q.1 * q.1 = Real.sin θ ^ 2 + q.2 ^ 2 := div_mul_cancel₀ _ hq
  simp only [Mp, Matrix.det_fin_two_of]
  linear_combination r ^ 2 * h1 + r ^ 2 * Real.sin_sq_add_cos_sq θ

theorem det_Mm (r θ : ℝ) (q : ℝ × ℝ) (hq : q.1 ≠ 0) : (Mm r θ q).det = r ^ 2 := by
  have h1 : (Real.sin θ ^ 2 + q.2 ^ 2) / q.1 * q.1 = Real.sin θ ^ 2 + q.2 ^ 2 := div_mul_cancel₀ _ hq
  simp only [Mm, Matrix.det_fin_two_of]
  linear_combination r ^ 2 * h1 + r ^ 2 * Real.sin_sq_add_cos_sq θ

def Nf (f : GL (Fin 2) ℝ → ℂ) (r θ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (if h : (Mp r θ q).det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) +
    (if h : (Mm r θ q).det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0)

def G (f : GL (Fin 2) ℝ → ℂ) (r θ : ℝ) (q : ℝ × ℝ) : ℂ := Nf f r θ q / (q.1 : ℂ)

theorem Nf_of_pos (f : GL (Fin 2) ℝ → ℂ) (r θ : ℝ) (hr : 0 < r) (q : ℝ × ℝ) (hq : 0 < q.1) :
    Nf f r θ q =
      f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mp r θ q) (by rw [det_Mp _ _ _ hq.ne']; positivity)) +
        f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mm r θ q) (by rw [det_Mm _ _ _ hq.ne']; positivity)) := by
  unfold Nf
  rw [dif_pos, dif_pos]

theorem conj_ellipticElt_eq (f : GL (Fin 2) ℝ → ℂ) (r θ x y : ℝ) (hr : 0 < r) (hy : 0 < y)
    (hs : 0 < Real.sin θ) :
    f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) +
        f (upperHalfPlaneElt x y hy * ellipticElt r (-θ) hr * (upperHalfPlaneElt x y hy)⁻¹) =
      Nf f r θ (Real.sin θ / y, x * Real.sin θ / y) := by
  unfold Nf
  have hu : Real.sin θ / y ≠ 0 := (div_pos hs hy).ne'
  have hdp : (Mp r θ (Real.sin θ / y, x * Real.sin θ / y)).det ≠ 0 := by
    rw [det_Mp _ _ _ hu]; positivity
  have hdm : (Mm r θ (Real.sin θ / y, x * Real.sin θ / y)).det ≠ 0 := by
    rw [det_Mm _ _ _ hu]; positivity
  rw [dif_pos hdp, dif_pos hdm]
  have hy0 : y ≠ 0 := hy.ne'
  have hs0 : Real.sin θ ≠ 0 := hs.ne'
  congr 2
  · rw [mul_inv_eq_iff_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperHalfPlaneElt, ellipticElt, Mp, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero] <;> field_simp <;> ring
  · rw [mul_inv_eq_iff_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperHalfPlaneElt, ellipticElt, Mm, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Real.sin_neg, Real.cos_neg] <;> field_simp <;> ring

def Ψ (s : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (s / q.1, q.2 / q.1)

def Ψ' (s : ℝ) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![-(s / q.1 ^ 2), 0; -(q.2 / q.1 ^ 2), 1 / q.1]).toContinuousLinearMap

theorem hasFDerivAt_Ψ (s : ℝ) (q : ℝ × ℝ) (hq : 0 < q.1) : HasFDerivAt (Ψ s) (Ψ' s q) q := by
  unfold Ψ' Ψ
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1⁻¹) ((-(q.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    (hasDerivAt_inv hq.ne').comp_hasFDerivAt q hasFDerivAt_fst
  have hA : HasFDerivAt (fun q : ℝ × ℝ => s / q.1) (s • ((-(q.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ)) q := by
    simpa only [div_eq_mul_inv] using h1.const_mul s
  have hB : HasFDerivAt (fun q : ℝ × ℝ => q.2 / q.1)
      (q.2 • ((-(q.1 ^ 2)⁻¹) • ContinuousLinearMap.fst ℝ ℝ ℝ) + q.1⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) q := by
    have := hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := q) |>.fun_mul h1
    simp only [div_eq_mul_inv]
    exact this
  convert hA.prodMk hB using 1 <;> try rfl
  ext <;> simp <;> ring

theorem det_Ψ' (s : ℝ) (q : ℝ × ℝ) : (Ψ' s q).det = -(s / q.1 ^ 3) := by
  unfold Ψ'
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin, Matrix.det_fin_two_of]
  ring

theorem injOn_Ψ (s : ℝ) (hs : 0 < s) : InjOn (Ψ s) (Ioi (0 : ℝ) ×ˢ univ) := by
  rintro ⟨u, v⟩ hu ⟨u', v'⟩ hu' h
  simp only [Ψ, Prod.mk.injEq] at h
  have hu0 : (0 : ℝ) < u := hu.1
  have hu0' : (0 : ℝ) < u' := hu'.1
  obtain ⟨h₁, h₂⟩ := h
  have : u = u' := by
    have := congrArg (fun t => s / t) h₁
    simpa [div_div_cancel₀, hs.ne', hu0.ne', hu0'.ne'] using this
  subst this
  have : v = v' := by
    have := congrArg (fun t => t * u) h₂
    simpa [div_mul_cancel₀, hu0.ne'] using this
  simp [this]

theorem image_Ψ (s : ℝ) (hs : 0 < s) : Ψ s '' (Ioi (0 : ℝ) ×ˢ univ) = Ioi (0 : ℝ) ×ˢ univ := by
  ext ⟨y, x⟩
  simp only [mem_image, mem_prod, mem_Ioi, mem_univ, and_true, Prod.exists, Ψ, Prod.mk.injEq]
  constructor
  · rintro ⟨u, v, hu, rfl, rfl⟩
    exact div_pos hs hu
  · intro hy
    refine ⟨s / y, x * s / y, div_pos hs hy, ?_, ?_⟩
    · rw [div_div_cancel₀ hs.ne']
    · field_simp

theorem continuous_chartP (r θ : ℝ) (hr : 0 < r) :
    Continuous fun q : ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) =>
      Matrix.GeneralLinearGroup.mkOfDetNeZero (Mp r θ q.1)
        (by rw [det_Mp _ _ _ (q.2.1 : (0 : ℝ) < q.1.1).ne']; positivity) := by
  have hne : ∀ q : ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), (q.1.1 : ℝ) ≠ 0 := fun q => (q.2.1 : (0 : ℝ) < q.1.1).ne'
  have hdet : ∀ q : ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), (Mp r θ q.1).det = r ^ 2 :=
    fun q => det_Mp _ _ _ (hne q)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Mp] <;>
      fun_prop (disch := exact hne)
  · simp only [Matrix.coe_units_inv, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.inv_def, hdet,
      Ring.inverse_eq_inv']
    refine Continuous.fun_const_smul (continuous_matrix fun i j => ?_) _
    fin_cases i <;> fin_cases j <;>
      simp [Mp, Matrix.adjugate_fin_two_of] <;>
      fun_prop (disch := exact hne)

theorem continuous_chartM (r θ : ℝ) (hr : 0 < r) :
    Continuous fun q : ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) =>
      Matrix.GeneralLinearGroup.mkOfDetNeZero (Mm r θ q.1)
        (by rw [det_Mm _ _ _ (q.2.1 : (0 : ℝ) < q.1.1).ne']; positivity) := by
  have hne : ∀ q : ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), (q.1.1 : ℝ) ≠ 0 := fun q => (q.2.1 : (0 : ℝ) < q.1.1).ne'
  have hdet : ∀ q : ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), (Mm r θ q.1).det = r ^ 2 :=
    fun q => det_Mm _ _ _ (hne q)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Mm] <;>
      fun_prop (disch := exact hne)
  · simp only [Matrix.coe_units_inv, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.inv_def, hdet,
      Ring.inverse_eq_inv']
    refine Continuous.fun_const_smul (continuous_matrix fun i j => ?_) _
    fin_cases i <;> fin_cases j <;>
      simp [Mm, Matrix.adjugate_fin_two_of] <;>
      fun_prop (disch := exact hne)

theorem continuousOn_G (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (r θ : ℝ) (hr : 0 < r) :
    ContinuousOn (G f r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  rw [continuousOn_iff_continuous_restrict]
  have hN : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)).domRestrict (G f r θ) = fun q =>
      (f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mp r θ q.1)
          (by rw [det_Mp _ _ _ (q.2.1 : (0 : ℝ) < q.1.1).ne']; positivity)) +
        f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mm r θ q.1)
          (by rw [det_Mm _ _ _ (q.2.1 : (0 : ℝ) < q.1.1).ne']; positivity))) / (q.1.1 : ℂ) := by
    funext q
    simp only [Set.domRestrict_apply, G, Nf_of_pos f r θ hr q.1 q.2.1]
  rw [hN]
  refine Continuous.div ((hf.comp (continuous_chartP r θ hr)).add (hf.comp (continuous_chartM r θ hr)))
    (Complex.continuous_ofReal.comp (continuous_fst.comp continuous_subtype_val)) fun q => ?_
  exact_mod_cast (q.2.1 : (0 : ℝ) < q.1.1).ne'

theorem exists_box (f : GL (Fin 2) ℝ → ℂ) (hfc : HasCompactSupport f) (r θ : ℝ) (hr : 0 < r)
    (hs : 0 < Real.sin θ) :
    ∃ B : ℝ, 0 < B ∧ ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), G f r θ q ≠ 0 →
      q ∈ Icc (r * Real.sin θ ^ 2 / B) (B / r) ×ˢ Icc (-(B / r)) (B / r) := by
  set K := tsupport f with hK_def
  have hK : IsCompact K := hfc
  have h10 : Continuous fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 :=
    (Continuous.matrix_elem continuous_id 1 0).comp Units.continuous_val
  have h01 : Continuous fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 :=
    (Continuous.matrix_elem continuous_id 0 1).comp Units.continuous_val
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn h10.continuousOn
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn h01.continuousOn
  set B := max (max B1 B2) 1 with hB_def
  have hB0 : 0 < B := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB1' : B1 ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB2' : B2 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨B, hB0, ?_⟩
  rintro ⟨u, v⟩ hq hG
  have hu : 0 < u := hq.1

  have key : ∃ g : GL (Fin 2) ℝ, g ∈ K ∧ |(g : Matrix (Fin 2) (Fin 2) ℝ) 1 0| = r * u ∧
      |(g : Matrix (Fin 2) (Fin 2) ℝ) 0 1| = r * ((Real.sin θ ^ 2 + v ^ 2) / u) := by
    have hN : Nf f r θ (u, v) ≠ 0 := by
      intro h; apply hG; simp [G, h]
    rw [Nf_of_pos f r θ hr (u, v) hu] at hN
    by_cases hP : f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mp r θ (u, v))
        (by rw [det_Mp _ _ _ hu.ne']; positivity)) ≠ 0
    · refine ⟨_, subset_tsupport _ hP, ?_, ?_⟩ <;>
        simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Mp, abs_of_pos hr, abs_of_pos hu, abs_mul,
          abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sin θ ^ 2 + v ^ 2)]
    · push Not at hP
      rw [hP, zero_add] at hN
      refine ⟨_, subset_tsupport _ hN, ?_, ?_⟩ <;>
        simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Mm, abs_of_pos hr, abs_of_pos hu, abs_mul,
          abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sin θ ^ 2 + v ^ 2)]
  obtain ⟨g, hgK, hg10, hg01⟩ := key
  have i1 : r * u ≤ B := by
    have := hB1 g hgK; rw [Real.norm_eq_abs, hg10] at this; exact this.trans hB1'
  have i2 : r * ((Real.sin θ ^ 2 + v ^ 2) / u) ≤ B := by
    have := hB2 g hgK; rw [Real.norm_eq_abs, hg01] at this; exact this.trans hB2'
  have i2' : r * (Real.sin θ ^ 2 + v ^ 2) ≤ B * u := by
    rw [mul_div_assoc'] at i2
    rwa [div_le_iff₀ hu] at i2
  simp only [mem_prod, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [div_le_iff₀ hB0]
    nlinarith [sq_nonneg v]
  · rw [le_div_iff₀ hr]; linarith
  · have hv2 : v ^ 2 ≤ (B / r) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      have : r * v ^ 2 ≤ B * u := by nlinarith [sq_nonneg (Real.sin θ)]
      nlinarith
    have hBr : 0 ≤ B / r := by positivity
    constructor <;> nlinarith [sq_nonneg (v + B / r), sq_nonneg (v - B / r)]

theorem integrableOn_G (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (r θ : ℝ) (hr : 0 < r) (hs : 0 < Real.sin θ) :
    IntegrableOn (G f r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  obtain ⟨B, hB0, hbox⟩ := exists_box f hfc r θ hr hs
  set k : Set (ℝ × ℝ) := Icc (r * Real.sin θ ^ 2 / B) (B / r) ×ˢ Icc (-(B / r)) (B / r)
  have hk : IsCompact k := isCompact_Icc.prod isCompact_Icc
  have hkS : k ⊆ Ioi (0 : ℝ) ×ˢ univ := by
    rintro ⟨u, v⟩ ⟨⟨hu, -⟩, -⟩
    exact ⟨lt_of_lt_of_le (by positivity) hu, mem_univ _⟩
  have hcont : ContinuousOn (G f r θ) k := (continuousOn_G f hf r θ hr).mono hkS
  refine (hcont.integrableOn_compact hk).of_forall_diff_eq_zero
    (measurableSet_Ioi.prod MeasurableSet.univ) fun q hq => ?_
  by_contra h
  exact hq.2 (hbox q hq.1 h)

theorem main_of_integrable (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f)
    (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ) (hθπ : θ < Real.pi)
    (hG : IntegrableOn (G f r θ) (Ioi (0 : ℝ) ×ˢ univ)) :
    ellipticTransform f r θ / (2 * Real.sin θ : ℂ) = 2 * ∫ q in Ioi (0 : ℝ) ×ˢ univ, G f r θ q := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  set s := Real.sin θ with hs_def

  set H : ℝ × ℝ → ℂ := fun z => (s : ℂ)⁻¹ • (((z.1 : ℂ) ^ 2)⁻¹ • Nf f r θ (s / z.1, z.2 * s / z.1)) with hH
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ

  have step1 : ellipticTransform f r θ / (2 * Real.sin θ : ℂ) =
      2 * (s : ℂ) ^ 2 * ∫ y in Ioi (0 : ℝ), ∫ x : ℝ, H (y, x) := by
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    unfold ellipticTransform
    rw [dif_pos hr]
    simp only [← hs_def]
    have hcongr : (∫ y in Ioi (0 : ℝ), ∫ x : ℝ,
        (if hy : 0 < y then
          (f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) +
              f (upperHalfPlaneElt x y hy * ellipticElt r (-θ) hr * (upperHalfPlaneElt x y hy)⁻¹)) /
            ((y : ℂ) ^ 2)
        else 0)) = ∫ y in Ioi (0 : ℝ), ∫ x : ℝ, (s : ℂ) • H (y, x) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
      have hy' : 0 < y := hy
      have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy'.ne'
      simp only [dif_pos hy', conj_ellipticElt_eq f r θ _ y hr hy' hs, hH, smul_eq_mul, ← hs_def]
      congr 1
      funext x
      field_simp
    rw [hcongr]
    simp only [smul_eq_mul, integral_const_mul]
    field_simp
    ring

  have step3 : ∫ z in Ioi (0 : ℝ) ×ˢ univ, H z =
      ∫ q in Ioi (0 : ℝ) ×ˢ univ, |(Ψ' s q).det| • H (Ψ s q) := by
    have := integral_image_eq_integral_abs_det_fderiv_smul volume hS
      (fun q hq => (hasFDerivAt_Ψ s q hq.1).hasFDerivWithinAt) (injOn_Ψ s hs) H
    rwa [image_Ψ s hs] at this

  have step4 : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ),
      |(Ψ' s q).det| • H (Ψ s q) = ((s : ℂ) ^ 2)⁻¹ • G f r θ q := by
    rintro ⟨u, v⟩ hq
    have hu : 0 < u := hq.1
    rw [det_Ψ', abs_neg, abs_of_pos (by positivity : 0 < s / (u, v).1 ^ 3)]
    have e1 : s / (s / u) = u := div_div_cancel₀ hs.ne'
    have e2 : v / u * s / (s / u) = v := by field_simp
    simp only [hH, Ψ, G, e1, e2]
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [Complex.real_smul]
    simp only [smul_eq_mul]
    push_cast
    field_simp

  have hHint : IntegrableOn H (Ioi (0 : ℝ) ×ˢ univ) := by
    rw [← image_Ψ s hs, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS
      (fun q hq => (hasFDerivAt_Ψ s q hq.1).hasFDerivWithinAt) (injOn_Ψ s hs)]
    have h1 : IntegrableOn (((s : ℂ) ^ 2)⁻¹ • G f r θ) (Ioi (0 : ℝ) ×ˢ univ) := hG.smul _
    exact IntegrableOn.congr_fun h1 (fun q hq => (step4 q hq).symm) hS

  have step2 : ∫ y in Ioi (0 : ℝ), ∫ x : ℝ, H (y, x) = ∫ z in Ioi (0 : ℝ) ×ˢ univ, H z := by
    have hHint' : IntegrableOn H (Ioi (0 : ℝ) ×ˢ univ) ((volume : Measure ℝ).prod volume) := by
      rwa [← Measure.volume_eq_prod]
    have := setIntegral_prod H hHint'
    rw [← Measure.volume_eq_prod] at this
    rw [this]
    simp only [Measure.restrict_univ]
  rw [step1, step2, step3, setIntegral_congr_fun hS step4, integral_smul, smul_eq_mul]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp

theorem main (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    IntegrableOn (G f r θ) (Ioi (0 : ℝ) ×ˢ univ) ∧
    ellipticTransform f r θ / (2 * Real.sin θ : ℂ) = 2 * ∫ q in Ioi (0 : ℝ) ×ˢ univ, G f r θ q :=
  have hG := integrableOn_G f hf hfc r θ hr (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)
  ⟨hG, main_of_integrable f hf r θ hr hθ hθπ hG⟩

end AutomorphicForm.GL2Real.RCoord

namespace AutomorphicForm
p2m_export "AutomorphicForm" "GL2Real.tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "upperHalfPlaneElt ellipticElt ellipticTransform entrySlice tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero"
namespace RLim
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

open AutomorphicForm.GL2Real.RCoord

def Mp0 (r : ℝ) (q : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r * (1 - q.2), r * (q.2 ^ 2 / q.1); -(r * q.1), r * (1 + q.2)]

def Mm0 (r : ℝ) (q : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r * (1 + q.2), -(r * (q.2 ^ 2 / q.1)); r * q.1, r * (1 - q.2)]

theorem Mp_zero (r : ℝ) (q : ℝ × ℝ) : Mp r 0 q = Mp0 r q := by
  simp [Mp, Mp0]

theorem Mm_zero (r : ℝ) (q : ℝ × ℝ) : Mm r 0 q = Mm0 r q := by
  simp [Mm, Mm0]

def G0 (f : GL (Fin 2) ℝ → ℂ) (r : ℝ) (q : ℝ × ℝ) : ℂ :=
  ((if h : (Mp0 r q).det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) +
    (if h : (Mm0 r q).det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0)) / (q.1 : ℂ)

theorem G_zero (f : GL (Fin 2) ℝ → ℂ) (r : ℝ) : G f r 0 = G0 f r := by
  funext q
  simp only [G, Nf, G0, Mp_zero, Mm_zero]

theorem continuous_chartP₂ (r : ℝ) (hr : 0 < r) :
    Continuous fun p : ℝ × ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) =>
      Matrix.GeneralLinearGroup.mkOfDetNeZero (Mp r p.1 p.2.1)
        (by rw [det_Mp _ _ _ (p.2.2.1 : (0 : ℝ) < p.2.1.1).ne']; positivity) := by
  have hne : ∀ p : ℝ × ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), (p.2.1.1 : ℝ) ≠ 0 := fun p => (p.2.2.1 : (0 : ℝ) < p.2.1.1).ne'
  have hdet : ∀ p : ℝ × ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), (Mp r p.1 p.2.1).det = r ^ 2 := fun p => det_Mp _ _ _ (hne p)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Mp] <;>
      fun_prop (disch := exact hne)
  · simp only [Matrix.coe_units_inv, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.inv_def, hdet,
      Ring.inverse_eq_inv']
    refine Continuous.fun_const_smul (continuous_matrix fun i j => ?_) _
    fin_cases i <;> fin_cases j <;>
      simp [Mp, Matrix.adjugate_fin_two_of] <;>
      fun_prop (disch := exact hne)

theorem continuous_chartM₂ (r : ℝ) (hr : 0 < r) :
    Continuous fun p : ℝ × ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) =>
      Matrix.GeneralLinearGroup.mkOfDetNeZero (Mm r p.1 p.2.1)
        (by rw [det_Mm _ _ _ (p.2.2.1 : (0 : ℝ) < p.2.1.1).ne']; positivity) := by
  have hne : ∀ p : ℝ × ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), (p.2.1.1 : ℝ) ≠ 0 := fun p => (p.2.2.1 : (0 : ℝ) < p.2.1.1).ne'
  have hdet : ∀ p : ℝ × ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), (Mm r p.1 p.2.1).det = r ^ 2 := fun p => det_Mm _ _ _ (hne p)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Mm] <;>
      fun_prop (disch := exact hne)
  · simp only [Matrix.coe_units_inv, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.inv_def, hdet,
      Ring.inverse_eq_inv']
    refine Continuous.fun_const_smul (continuous_matrix fun i j => ?_) _
    fin_cases i <;> fin_cases j <;>
      simp [Mm, Matrix.adjugate_fin_two_of] <;>
      fun_prop (disch := exact hne)

theorem tendsto_G (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (r : ℝ) (hr : 0 < r)
    (q : ℝ × ℝ) (hq : q ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) (θ₀ : ℝ) :
    Tendsto (fun θ => G f r θ q) (nhds θ₀) (nhds (G f r θ₀ q)) := by
  have hu : 0 < q.1 := hq.1
  have hfun : (fun θ => G f r θ q) = fun θ =>
      (f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mp r θ q)
          (by rw [det_Mp _ _ _ hu.ne']; positivity)) +
        f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mm r θ q)
          (by rw [det_Mm _ _ _ hu.ne']; positivity))) / (q.1 : ℂ) := by
    funext θ; simp only [G, Nf_of_pos f r θ hr q hu]
  rw [hfun]
  have hι : Continuous fun θ : ℝ => ((θ, ⟨q, hq⟩) : ℝ × ↥(Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by fun_prop
  have hc : Continuous fun θ =>
      (f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mp r θ q)
          (by rw [det_Mp _ _ _ hu.ne']; positivity)) +
        f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mm r θ q)
          (by rw [det_Mm _ _ _ hu.ne']; positivity))) / (q.1 : ℂ) :=
    (((hf.comp (continuous_chartP₂ r hr)).comp hι).add
      ((hf.comp (continuous_chartM₂ r hr)).comp hι)).div_const _
  convert hc.tendsto θ₀ using 2
  exact congrFun hfun θ₀

theorem support_bound (f : GL (Fin 2) ℝ → ℂ) (hfc : HasCompactSupport f) (r : ℝ) (hr : 0 < r) :
    ∃ B : ℝ, 0 < B ∧ ∀ θ : ℝ, ∀ q ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), Nf f r θ q ≠ 0 →
      r * q.1 ≤ B ∧ r * (Real.sin θ ^ 2 + q.2 ^ 2) ≤ B * q.1 := by
  set K := tsupport f with hK_def
  have hK : IsCompact K := hfc
  have h10 : Continuous fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 :=
    (Continuous.matrix_elem continuous_id 1 0).comp Units.continuous_val
  have h01 : Continuous fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 :=
    (Continuous.matrix_elem continuous_id 0 1).comp Units.continuous_val
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn h10.continuousOn
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn h01.continuousOn
  set B := max (max B1 B2) 1 with hB_def
  have hB0 : 0 < B := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB1' : B1 ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB2' : B2 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨B, hB0, ?_⟩
  rintro θ ⟨u, v⟩ hq hN
  have hu : 0 < u := hq.1
  have key : ∃ g : GL (Fin 2) ℝ, g ∈ K ∧ |(g : Matrix (Fin 2) (Fin 2) ℝ) 1 0| = r * u ∧
      |(g : Matrix (Fin 2) (Fin 2) ℝ) 0 1| = r * ((Real.sin θ ^ 2 + v ^ 2) / u) := by
    rw [Nf_of_pos f r θ hr (u, v) hu] at hN
    by_cases hP : f (Matrix.GeneralLinearGroup.mkOfDetNeZero (Mp r θ (u, v))
        (by rw [det_Mp _ _ _ hu.ne']; positivity)) ≠ 0
    · refine ⟨_, subset_tsupport _ hP, ?_, ?_⟩ <;>
        simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Mp, abs_of_pos hr, abs_of_pos hu, abs_mul,
          abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sin θ ^ 2 + v ^ 2)]
    · push Not at hP
      rw [hP, zero_add] at hN
      refine ⟨_, subset_tsupport _ hN, ?_, ?_⟩ <;>
        simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Mm, abs_of_pos hr, abs_of_pos hu, abs_mul,
          abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sin θ ^ 2 + v ^ 2)]
  obtain ⟨g, hgK, hg10, hg01⟩ := key
  have i1 : r * u ≤ B := by
    have := hB1 g hgK; rw [Real.norm_eq_abs, hg10] at this; exact this.trans hB1'
  have i2 : r * ((Real.sin θ ^ 2 + v ^ 2) / u) ≤ B := by
    have := hB2 g hgK; rw [Real.norm_eq_abs, hg01] at this; exact this.trans hB2'
  refine ⟨i1, ?_⟩
  rw [mul_div_assoc'] at i2
  rwa [div_le_iff₀ hu] at i2

theorem div_le_rpow_mul_rpow (M K u v : ℝ) (hM : 0 ≤ M) (hK : 0 < K) (hu : 0 < u) (hv : v ≠ 0)
    (h : v ^ 2 ≤ K * u) :
    M / u ≤ M * K ^ (1 / 4 : ℝ) * (u ^ (-(3 / 4 : ℝ)) * |v| ^ (-(1 / 2 : ℝ))) := by
  have hv' : 0 < |v| := abs_pos.2 hv
  have h1 : |v| ^ (1 / 2 : ℝ) ≤ K ^ (1 / 4 : ℝ) * u ^ (1 / 4 : ℝ) := by
    have e : |v| ^ (1 / 2 : ℝ) = (v ^ 2) ^ (1 / 4 : ℝ) := by
      rw [← sq_abs, ← Real.rpow_natCast |v| 2, ← Real.rpow_mul (abs_nonneg v)]
      norm_num
    rw [e, ← Real.mul_rpow hK.le hu.le]
    exact Real.rpow_le_rpow (sq_nonneg _) h (by norm_num)
  have h2 : (K ^ (1 / 4 : ℝ) * u ^ (1 / 4 : ℝ))⁻¹ ≤ (|v| ^ (1 / 2 : ℝ))⁻¹ :=
    inv_anti₀ (Real.rpow_pos_of_pos hv' _) h1
  have hK4 : 0 < K ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hK _
  have hu4 : 0 < u ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hu _
  have e2 : M / u = M * K ^ (1 / 4 : ℝ) * (u ^ (-(3 / 4 : ℝ)) * (K ^ (1 / 4 : ℝ) * u ^ (1 / 4 : ℝ))⁻¹) := by
    have e3 : u ^ (-(3 / 4 : ℝ)) * (u ^ (1 / 4 : ℝ))⁻¹ = u⁻¹ := by
      rw [← Real.rpow_neg hu.le, ← Real.rpow_add hu, ← Real.rpow_neg_one]
      norm_num
    rw [mul_inv, show u ^ (-(3 / 4 : ℝ)) * ((K ^ (1 / 4 : ℝ))⁻¹ * (u ^ (1 / 4 : ℝ))⁻¹) =
      (K ^ (1 / 4 : ℝ))⁻¹ * (u ^ (-(3 / 4 : ℝ)) * (u ^ (1 / 4 : ℝ))⁻¹) by ring, e3]
    field_simp
  rw [e2, Real.rpow_neg (abs_nonneg v)]
  have : 0 ≤ u ^ (-(3 / 4 : ℝ)) := (Real.rpow_pos_of_pos hu _).le
  gcongr

def bound (C c : ℝ) : ℝ × ℝ → ℝ :=
  (Ioc (0 : ℝ) c ×ˢ Icc (-c) c).indicator fun q => C * (q.1 ^ (-(3 / 4 : ℝ)) * |q.2| ^ (-(1 / 2 : ℝ)))

theorem bound_nonneg (C c : ℝ) (hC : 0 ≤ C) (q : ℝ × ℝ) : 0 ≤ bound C c q := by
  unfold bound
  apply Set.indicator_nonneg
  intro q hq
  have : 0 ≤ q.1 ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hq.1.1.le _
  have : 0 ≤ |q.2| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
  positivity

theorem integrableOn_abs_rpow (c : ℝ) (hc : 0 ≤ c) :
    IntegrableOn (fun v : ℝ => |v| ^ (-(1 / 2 : ℝ))) (Icc (-c) c) := by
  have hexp : (-1 : ℝ) < -(1 / 2 : ℝ) := by norm_num
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 c :=
    intervalIntegral.intervalIntegrable_rpow' hexp
  have h2 : IntervalIntegrable (fun x : ℝ => (-x) ^ (-(1 / 2 : ℝ))) volume (-c) 0 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hexp).comp_mul_left (c := -1)
    simp only [neg_mul, one_mul, div_neg, div_one, neg_zero] at this
    exact this.symm
  have h1' : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Icc 0 c) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hc).1 h1
  have h2' : IntegrableOn (fun x : ℝ => (-x) ^ (-(1 / 2 : ℝ))) (Icc (-c) 0) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 h2
  have hunion : Icc (-c) c = Icc (-c) 0 ∪ Icc 0 c := (Icc_union_Icc_eq_Icc (by linarith) hc).symm
  rw [hunion]
  refine IntegrableOn.union ?_ ?_
  · exact h2'.congr_fun (fun x hx => by rw [abs_of_nonpos hx.2]) measurableSet_Icc
  · exact h1'.congr_fun (fun x hx => by rw [abs_of_nonneg hx.1]) measurableSet_Icc

theorem integrable_bound (C c : ℝ) (hc : 0 ≤ c) : Integrable (bound C c) (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  have hR : MeasurableSet (Ioc (0 : ℝ) c ×ˢ Icc (-c) c) := measurableSet_Ioc.prod measurableSet_Icc
  refine Integrable.integrableOn ?_
  rw [bound, integrable_indicator_iff hR]
  have hu : IntegrableOn (fun u : ℝ => C * u ^ (-(3 / 4 : ℝ))) (Ioc 0 c) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) (r := -(3 / 4 : ℝ)) (by norm_num))
    exact this.const_mul C
  have hv := integrableOn_abs_rpow c hc
  have := Integrable.mul_prod hu hv
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at this
  simpa [IntegrableOn, mul_assoc] using this

private theorem _root_.AutomorphicForm.GL2Real.RLim.main (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (G0 f r) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∧
    Tendsto (fun θ : ℝ => ellipticTransform f r θ / (2 * Real.sin θ : ℂ)) (nhdsWithin 0 (Ioi 0))
      (nhds (2 * ∫ q in (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), G0 f r q)) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ

  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ g, ‖f g‖ ≤ M₀ := by
    obtain ⟨M₀, hM₀⟩ := (hf.norm.bddAbove_range_of_hasCompactSupport hfc.norm)
    exact ⟨M₀, fun g => hM₀ ⟨g, rfl⟩⟩
  have hM₀' : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 1)
  obtain ⟨B, hB0, hB⟩ := support_bound f hfc r hr
  set c := B / r with hc_def
  have hc : 0 ≤ c := by positivity
  set C := 2 * M₀ * (B / r) ^ (1 / 4 : ℝ) with hC_def
  have hC : 0 ≤ C := by positivity

  have hnull : volume {q : ℝ × ℝ | q.2 = 0} = 0 := by
    have : {q : ℝ × ℝ | q.2 = 0} = (univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
      ext q; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hae : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))), q ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∧ q.2 ≠ 0 := by
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)] with q h1 h2
    exact ⟨h1, h2⟩

  have hdom : ∀ θ : ℝ, ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))), ‖G f r θ q‖ ≤ bound C c q := by
    intro θ
    filter_upwards [hae] with q hq
    obtain ⟨hqS, hv⟩ := hq
    have hu : 0 < q.1 := hqS.1
    by_cases hN : Nf f r θ q = 0
    · simp only [G, hN, zero_div, norm_zero]
      exact bound_nonneg C c hC q
    obtain ⟨i1, i2⟩ := hB θ q hqS hN
    have hv2 : q.2 ^ 2 ≤ (B / r) * q.1 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      nlinarith [sq_nonneg (Real.sin θ)]
    have hqR : q ∈ Ioc (0 : ℝ) c ×ˢ Icc (-c) c := by
      refine ⟨⟨hu, ?_⟩, ?_⟩
      · rw [hc_def, le_div_iff₀ hr]; linarith
      · have hv2' : q.2 ^ 2 ≤ (B / r) ^ 2 := by
          have hq1 : q.1 ≤ B / r := by rw [le_div_iff₀ hr]; linarith
          calc q.2 ^ 2 ≤ B / r * q.1 := hv2
            _ ≤ B / r * (B / r) := mul_le_mul_of_nonneg_left hq1 (by positivity)
            _ = (B / r) ^ 2 := (sq _).symm
        have hBr : 0 ≤ B / r := by positivity
        rw [mem_Icc, hc_def]
        constructor <;> nlinarith [sq_nonneg (q.2 + B / r), sq_nonneg (q.2 - B / r)]
    rw [bound, indicator_of_mem hqR]
    have hNle : ‖Nf f r θ q‖ ≤ 2 * M₀ := by
      rw [Nf_of_pos f r θ hr q hu]
      exact (norm_add_le _ _).trans ((add_le_add (hM₀ _) (hM₀ _)).trans_eq (two_mul M₀).symm)
    have hGle : ‖G f r θ q‖ ≤ 2 * M₀ / q.1 := by
      rw [G, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
      exact div_le_div_of_nonneg_right hNle hu.le
    exact hGle.trans (div_le_rpow_mul_rpow (2 * M₀) (B / r) q.1 q.2 (by positivity) (by positivity) hu hv hv2)
  have hbi : Integrable (bound C c) (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := integrable_bound C c hc
  have hmeas : ∀ θ : ℝ, AEStronglyMeasurable (G f r θ) (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := fun θ =>
    (continuousOn_G f hf r θ hr).aestronglyMeasurable hS

  have hint0 : IntegrableOn (G0 f r) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rw [← G_zero]
    exact hbi.mono' (hmeas 0) (hdom 0)
  refine ⟨hint0, ?_⟩

  have hlim : Tendsto (fun θ : ℝ => ∫ q in (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), G f r θ q) (nhdsWithin 0 (Ioi 0)) (nhds (∫ q in (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)), G0 f r q)) := by
    rw [← G_zero]
    refine tendsto_integral_filter_of_dominated_convergence (bound C c)
      (Eventually.of_forall hmeas) (Eventually.of_forall hdom) hbi ?_
    filter_upwards [ae_restrict_mem hS] with q hq
    exact (tendsto_G f hf r hr q hq 0).mono_left nhdsWithin_le_nhds
  have hlim2 := hlim.const_mul (2 : ℂ)
  refine hlim2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with θ hθ
  exact ((RCoord.main f hf hfc r θ hr hθ.1 hθ.2).2).symm

p2m_export "AutomorphicForm.GL2Real.RLim" "main"
end AutomorphicForm.GL2Real.RLim

namespace AutomorphicForm
p2m_export "AutomorphicForm" "GL2Real.tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "upperHalfPlaneElt ellipticElt ellipticTransform entrySlice tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero"
namespace RHead
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

open AutomorphicForm.GL2Real.RCoord AutomorphicForm.GL2Real.RLim

abbrev E22 := Fin 2 → Fin 2 → ℝ

def eI : E22 := Matrix.of.symm !![1, 0; 0, 1]
def e01 : E22 := Matrix.of.symm !![0, 1; 0, 0]
def e10 : E22 := Matrix.of.symm !![0, 0; 1, 0]

theorem Mp_decomp (r θ : ℝ) (q : ℝ × ℝ) :
    (Matrix.of.symm (Mp r θ q) : E22) =
      (r * Real.cos θ) • eI + (r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1)) • e01 + (-(r * q.1)) • e10 +
        Matrix.of.symm !![-(r * q.2), 0; 0, r * q.2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mp, eI, e01, e10] <;> ring

theorem Mm_decomp (r θ : ℝ) (q : ℝ × ℝ) :
    (Matrix.of.symm (Mm r θ q) : E22) =
      (r * Real.cos θ) • eI + (-(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1))) • e01 + (r * q.1) • e10 +
        Matrix.of.symm !![r * q.2, 0; 0, -(r * q.2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mm, eI, e01, e10] <;> ring

def dθMp (r θ : ℝ) (q : ℝ × ℝ) : E22 :=
  Matrix.of.symm !![-(r * Real.sin θ), r * (2 * Real.sin θ * Real.cos θ / q.1); 0, -(r * Real.sin θ)]
def dθMm (r θ : ℝ) (q : ℝ × ℝ) : E22 :=
  Matrix.of.symm !![-(r * Real.sin θ), -(r * (2 * Real.sin θ * Real.cos θ / q.1)); 0, -(r * Real.sin θ)]

theorem dθMp_eq (r θ : ℝ) (q : ℝ × ℝ) :
    dθMp r θ q = (-(r * Real.sin θ)) • eI + (r * (2 * Real.sin θ * Real.cos θ / q.1)) • e01 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dθMp, eI, e01]

theorem dθMm_eq (r θ : ℝ) (q : ℝ × ℝ) :
    dθMm r θ q = (-(r * Real.sin θ)) • eI + (-(r * (2 * Real.sin θ * Real.cos θ / q.1))) • e01 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dθMm, eI, e01]

def duMp (r θ : ℝ) (q : ℝ × ℝ) : E22 :=
  (-(r * (Real.sin θ ^ 2 + q.2 ^ 2) / q.1 ^ 2)) • e01 + (-r) • e10
def duMm (r θ : ℝ) (q : ℝ × ℝ) : E22 :=
  (r * (Real.sin θ ^ 2 + q.2 ^ 2) / q.1 ^ 2) • e01 + r • e10

theorem hasDerivAt_Mp_θ (r θ : ℝ) (q : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Mp r t q) : E22)) (dθMp r θ q) θ := by
  rw [dθMp_eq]
  simp only [Mp_decomp]
  have h1 : HasDerivAt (fun t => (r * Real.cos t) • eI) ((r * -Real.sin θ) • eI) θ :=
    ((Real.hasDerivAt_cos θ).const_mul r).smul_const eI
  have h2 : HasDerivAt (fun t => (r * ((Real.sin t ^ 2 + q.2 ^ 2) / q.1)) • e01)
      ((r * ((2 * Real.sin θ * Real.cos θ) / q.1)) • e01) θ := by
    have hs : HasDerivAt (fun t => Real.sin t ^ 2 + q.2 ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
      have := ((Real.hasDerivAt_sin θ).fun_pow 2).add_const (q.2 ^ 2)
      convert this using 1 <;> first | rfl | (push_cast; ring)
    exact ((hs.div_const q.1).const_mul r).smul_const e01
  have h3 : HasDerivAt (fun _ : ℝ => (-(r * q.1)) • e10 + Matrix.of.symm !![-(r * q.2), 0; 0, r * q.2])
      (0 : E22) θ := hasDerivAt_const _ _
  convert (h1.add h2).add h3 using 1 <;> try rfl
  · funext t; simp only [Pi.add_apply]; abel
  · simp only [add_zero]; congr 1; ring_nf

theorem hasDerivAt_Mm_θ (r θ : ℝ) (q : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Mm r t q) : E22)) (dθMm r θ q) θ := by
  rw [dθMm_eq]
  simp only [Mm_decomp]
  have h1 : HasDerivAt (fun t => (r * Real.cos t) • eI) ((r * -Real.sin θ) • eI) θ :=
    ((Real.hasDerivAt_cos θ).const_mul r).smul_const eI
  have h2 : HasDerivAt (fun t => (-(r * ((Real.sin t ^ 2 + q.2 ^ 2) / q.1))) • e01)
      (-(r * ((2 * Real.sin θ * Real.cos θ) / q.1)) • e01) θ := by
    have hs : HasDerivAt (fun t => Real.sin t ^ 2 + q.2 ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
      have := ((Real.hasDerivAt_sin θ).fun_pow 2).add_const (q.2 ^ 2)
      convert this using 1 <;> first | rfl | (push_cast; ring)
    exact ((hs.div_const q.1).const_mul r).neg.smul_const e01
  have h3 : HasDerivAt (fun _ : ℝ => (r * q.1) • e10 + Matrix.of.symm !![r * q.2, 0; 0, -(r * q.2)])
      (0 : E22) θ := hasDerivAt_const _ _
  convert (h1.add h2).add h3 using 1 <;> try rfl
  · funext t; simp only [Pi.add_apply]; abel
  · simp only [add_zero]; congr 1; ring_nf

theorem hasDerivAt_Mp_u (r θ v u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Mp r θ (t, v)) : E22)) (duMp r θ (u, v)) u := by
  simp only [Mp_decomp]
  have h1 : HasDerivAt (fun t : ℝ => (r * ((Real.sin θ ^ 2 + v ^ 2) / t)) • e01)
      ((r * ((Real.sin θ ^ 2 + v ^ 2) * (-(u ^ 2)⁻¹))) • e01) u := by
    have := ((hasDerivAt_inv hu).const_mul (Real.sin θ ^ 2 + v ^ 2)).const_mul r
    simpa only [div_eq_mul_inv] using this.smul_const e01
  have h2 : HasDerivAt (fun t : ℝ => (-(r * t)) • e10) ((-(r * 1)) • e10) u :=
    (((hasDerivAt_id u).const_mul r).neg).smul_const e10
  have h3 : HasDerivAt (fun _ : ℝ => (r * Real.cos θ) • eI) (0 : E22) u := hasDerivAt_const _ _
  have h4 : HasDerivAt (fun _ : ℝ => (Matrix.of.symm !![-(r * v), 0; 0, r * v] : E22)) (0 : E22) u :=
    hasDerivAt_const _ _
  convert ((h3.add h1).add h2).add h4 using 1 <;> try rfl
  simp only [duMp, zero_add, add_zero, mul_one]; congr 1; field_simp

theorem hasDerivAt_Mm_u (r θ v u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Mm r θ (t, v)) : E22)) (duMm r θ (u, v)) u := by
  simp only [Mm_decomp]
  have h1 : HasDerivAt (fun t : ℝ => (-(r * ((Real.sin θ ^ 2 + v ^ 2) / t))) • e01)
      (-(r * ((Real.sin θ ^ 2 + v ^ 2) * (-(u ^ 2)⁻¹))) • e01) u := by
    have := (((hasDerivAt_inv hu).const_mul (Real.sin θ ^ 2 + v ^ 2)).const_mul r).fun_neg
    simpa only [div_eq_mul_inv] using this.smul_const e01
  have h2 : HasDerivAt (fun t : ℝ => (r * t) • e10) ((r * 1) • e10) u :=
    ((hasDerivAt_id u).const_mul r).smul_const e10
  have h3 : HasDerivAt (fun _ : ℝ => (r * Real.cos θ) • eI) (0 : E22) u := hasDerivAt_const _ _
  have h4 : HasDerivAt (fun _ : ℝ => (Matrix.of.symm !![r * v, 0; 0, -(r * v)] : E22)) (0 : E22) u :=
    hasDerivAt_const _ _
  convert ((h3.add h1).add h2).add h4 using 1 <;> try rfl
  simp only [duMm, zero_add, add_zero, mul_one]; congr 1; field_simp

theorem dθMp_identity (r θ : ℝ) (q : ℝ × ℝ) (hq : q.1 ≠ 0) (hsv : Real.sin θ ^ 2 + q.2 ^ 2 ≠ 0) :
    (q.1)⁻¹ • dθMp r θ q =
      (-(r * Real.sin θ / q.1)) • eI +
        (-(2 * Real.sin θ * Real.cos θ / (Real.sin θ ^ 2 + q.2 ^ 2))) • (duMp r θ q + r • e10) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dθMp, duMp, eI, e01, e10] <;> field_simp <;> ring

theorem dθMm_identity (r θ : ℝ) (q : ℝ × ℝ) (hq : q.1 ≠ 0) (hsv : Real.sin θ ^ 2 + q.2 ^ 2 ≠ 0) :
    (q.1)⁻¹ • dθMm r θ q =
      (-(r * Real.sin θ / q.1)) • eI +
        (-(2 * Real.sin θ * Real.cos θ / (Real.sin θ ^ 2 + q.2 ^ 2))) • (duMm r θ q + (-r) • e10) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dθMm, duMm, eI, e01, e10] <;> field_simp <;> ring

structure TestFn (ψ : E22 → ℂ) : Prop where
  smooth : ContDiff ℝ 1 ψ
  cpt : HasCompactSupport ψ

namespace TestFn

variable {ψ : E22 → ℂ} (hψ : TestFn ψ)
include hψ

theorem differentiable : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)

theorem continuous : Continuous ψ := hψ.smooth.continuous

theorem continuous_fderiv : Continuous (fderiv ℝ ψ) := hψ.smooth.continuous_fderiv (by simp)

theorem hasCompactSupport_fderiv : HasCompactSupport (fderiv ℝ ψ) := hψ.cpt.fderiv ℝ

theorem exists_compact : ∃ K : Set E22, IsCompact K ∧ (∀ M, ψ M ≠ 0 → M ∈ K) ∧
    ∀ M, fderiv ℝ ψ M ≠ 0 → M ∈ K :=
  ⟨tsupport ψ, hψ.cpt, fun M hM => subset_tsupport _ hM, fun M hM => support_fderiv_subset ℝ hM⟩

theorem exists_bound : ∃ C : ℝ, 0 ≤ C ∧ (∀ M, ‖ψ M‖ ≤ C) ∧ ∀ M, ‖fderiv ℝ ψ M‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hψ.cpt.norm
  obtain ⟨C₂, hC₂⟩ := hψ.continuous_fderiv.norm.bddAbove_range_of_hasCompactSupport
    hψ.hasCompactSupport_fderiv.norm
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun M => ?_, fun M => ?_⟩
  · exact (hC₁ ⟨M, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hC₂ ⟨M, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem exists_entry_bound : ∃ B : ℝ, 0 < B ∧ ∀ M : E22, (ψ M ≠ 0 ∨ fderiv ℝ ψ M ≠ 0) →
    |M 1 0| ≤ B ∧ |M 0 1| ≤ B := by
  obtain ⟨K, hK, h1, h2⟩ := hψ.exists_compact
  have h10 : Continuous fun M : E22 => M 1 0 := by fun_prop
  have h01 : Continuous fun M : E22 => M 0 1 := by fun_prop
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn h10.continuousOn
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn h01.continuousOn
  refine ⟨max (max B1 B2) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun M hM => ?_⟩
  have hMK : M ∈ K := hM.elim (h1 M) (h2 M)
  refine ⟨?_, ?_⟩
  · have := hB1 M hMK; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have := hB2 M hMK; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))

end TestFn

section Phi

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def φ (Φ : E22 × P → ℂ) (p : P) : E22 → ℂ := fun M => Φ (M, p)

theorem testFn_φ (Φ : E22 × P → ℂ) (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P) :
    TestFn (φ Φ p) where
  smooth := (hΦs.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).comp
    (contDiff_id.prodMk contDiff_const)
  cpt := by
    refine HasCompactSupport.intro (hΦc.image continuous_fst) fun M hM => ?_
    have : (M, p) ∉ tsupport Φ := fun h => hM ⟨(M, p), h, rfl⟩
    exact image_eq_zero_of_notMem_tsupport (f := Φ) this

theorem G_entrySlice (Φ : E22 × P → ℂ) (p : P) (r θ : ℝ) (hr : 0 < r) (q : ℝ × ℝ) (hq : 0 < q.1) :
    G (entrySlice Φ p) r θ q =
      (φ Φ p (Matrix.of.symm (Mp r θ q)) + φ Φ p (Matrix.of.symm (Mm r θ q))) / (q.1 : ℂ) := by
  rw [G, Nf_of_pos _ r θ hr q hq]
  simp [entrySlice, φ, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

end Phi

section Deriv

variable {ψ : E22 → ℂ}

def Gψ (ψ : E22 → ℂ) (r θ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (ψ (Matrix.of.symm (Mp r θ q)) + ψ (Matrix.of.symm (Mm r θ q))) / (q.1 : ℂ)

def dG (ψ : E22 → ℂ) (r θ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) (dθMp r θ q) +
    fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) (dθMm r θ q)) / (q.1 : ℂ)

theorem hasDerivAt_Gψ (hψ : TestFn ψ) (r θ : ℝ) (q : ℝ × ℝ) :
    HasDerivAt (fun t => Gψ ψ r t q) (dG ψ r θ q) θ := by
  have h1 := (hψ.differentiable _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_Mp_θ r θ q)
  have h2 := (hψ.differentiable _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_Mm_θ r θ q)
  exact (h1.add h2).div_const _

theorem continuousOn_Mp (r θ : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => (Matrix.of.symm (Mp r θ q) : E22)) (Ioi (0 : ℝ) ×ˢ univ) := by
  simp only [Mp_decomp]
  have : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), q.1 ≠ 0 := fun q hq => (hq.1 : (0:ℝ) < q.1).ne'
  apply ContinuousOn.add
  · apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact continuousOn_const
      · exact ContinuousOn.fun_smul (by fun_prop (disch := exact this)) continuousOn_const
    · exact ContinuousOn.fun_smul (by fun_prop) continuousOn_const
  · refine (continuous_matrix fun i j => ?_).continuousOn
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuousOn_Mm (r θ : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => (Matrix.of.symm (Mm r θ q) : E22)) (Ioi (0 : ℝ) ×ˢ univ) := by
  simp only [Mm_decomp]
  have : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), q.1 ≠ 0 := fun q hq => (hq.1 : (0:ℝ) < q.1).ne'
  apply ContinuousOn.add
  · apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact continuousOn_const
      · exact ContinuousOn.fun_smul (by fun_prop (disch := exact this)) continuousOn_const
    · exact ContinuousOn.fun_smul (by fun_prop) continuousOn_const
  · refine (continuous_matrix fun i j => ?_).continuousOn
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuousOn_dθMp (r θ : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => dθMp r θ q) (Ioi (0 : ℝ) ×ˢ univ) := by
  have : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), q.1 ≠ 0 := fun q hq => (hq.1 : (0:ℝ) < q.1).ne'
  simp only [dθMp_eq]
  exact (continuousOn_const).fun_add (ContinuousOn.fun_smul (by fun_prop (disch := exact this)) continuousOn_const)

theorem continuousOn_dθMm (r θ : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => dθMm r θ q) (Ioi (0 : ℝ) ×ˢ univ) := by
  have : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), q.1 ≠ 0 := fun q hq => (hq.1 : (0:ℝ) < q.1).ne'
  simp only [dθMm_eq]
  exact (continuousOn_const).fun_add (ContinuousOn.fun_smul (by fun_prop (disch := exact this)) continuousOn_const)

theorem continuousOn_Gψ (hψ : TestFn ψ) (r θ : ℝ) : ContinuousOn (Gψ ψ r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  unfold Gψ
  refine ContinuousOn.div ((hψ.continuous.comp_continuousOn (continuousOn_Mp r θ)).add
    (hψ.continuous.comp_continuousOn (continuousOn_Mm r θ)))
    (Complex.continuous_ofReal.comp_continuousOn continuousOn_fst) fun q hq => ?_
  exact_mod_cast (hq.1 : (0:ℝ) < q.1).ne'

theorem continuousOn_dG (hψ : TestFn ψ) (r θ : ℝ) : ContinuousOn (dG ψ r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  unfold dG
  have hA : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) (dθMp r θ q))
      (Ioi (0 : ℝ) ×ˢ univ) :=
    ContinuousOn.clm_apply (hψ.continuous_fderiv.comp_continuousOn (continuousOn_Mp r θ))
      (continuousOn_dθMp r θ)
  have hB : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) (dθMm r θ q))
      (Ioi (0 : ℝ) ×ˢ univ) :=
    ContinuousOn.clm_apply (hψ.continuous_fderiv.comp_continuousOn (continuousOn_Mm r θ))
      (continuousOn_dθMm r θ)
  refine ContinuousOn.div (hA.add hB) (Complex.continuous_ofReal.comp_continuousOn continuousOn_fst)
    fun q hq => ?_
  exact_mod_cast (hq.1 : (0:ℝ) < q.1).ne'

end Deriv

section Support

variable {ψ : E22 → ℂ}

theorem Mp_entries (r θ : ℝ) (q : ℝ × ℝ) :
    (Matrix.of.symm (Mp r θ q) : E22) 1 0 = -(r * q.1) ∧
      (Matrix.of.symm (Mp r θ q) : E22) 0 1 = r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1) := by
  simp [Mp]

theorem Mm_entries (r θ : ℝ) (q : ℝ × ℝ) :
    (Matrix.of.symm (Mm r θ q) : E22) 1 0 = r * q.1 ∧
      (Matrix.of.symm (Mm r θ q) : E22) 0 1 = -(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1)) := by
  simp [Mm]

theorem chart_support (hψ : TestFn ψ) (r : ℝ) (hr : 0 < r) :
    ∃ B : ℝ, 0 < B ∧ ∀ θ : ℝ, ∀ q : ℝ × ℝ, 0 < q.1 →
      ((ψ (Matrix.of.symm (Mp r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) ≠ 0) ∨
        (ψ (Matrix.of.symm (Mm r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) ≠ 0)) →
      r * q.1 ≤ B ∧ r * (Real.sin θ ^ 2 + q.2 ^ 2) ≤ B * q.1 := by
  obtain ⟨B, hB0, hB⟩ := hψ.exists_entry_bound
  refine ⟨B, hB0, fun θ q hu h => ?_⟩
  have hsv : 0 ≤ Real.sin θ ^ 2 + q.2 ^ 2 := by positivity
  rcases h with h | h
  · obtain ⟨h10, h01⟩ := hB _ h
    rw [(Mp_entries r θ q).1, abs_neg, abs_of_pos (by positivity)] at h10
    rw [(Mp_entries r θ q).2, abs_of_nonneg (by positivity), mul_div_assoc', div_le_iff₀ hu] at h01
    exact ⟨h10, h01⟩
  · obtain ⟨h10, h01⟩ := hB _ h
    rw [(Mm_entries r θ q).1, abs_of_pos (by positivity)] at h10
    rw [(Mm_entries r θ q).2, abs_neg, abs_of_nonneg (by positivity), mul_div_assoc', div_le_iff₀ hu] at h01
    exact ⟨h10, h01⟩

theorem box_of_bound {r B u v s : ℝ} (hr : 0 < r) (hB : 0 < B) (hu : 0 < u)
    (h1 : r * u ≤ B) (h2 : r * (s ^ 2 + v ^ 2) ≤ B * u) :
    u ≤ B / r ∧ r * s ^ 2 / B ≤ u ∧ |v| ≤ B / r ∧ v ^ 2 ≤ B / r * u := by
  have i1 : u ≤ B / r := by rw [le_div_iff₀ hr]; linarith
  have i2 : r * s ^ 2 / B ≤ u := by
    rw [div_le_iff₀ hB]; nlinarith [sq_nonneg v]
  have i4 : v ^ 2 ≤ B / r * u := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]; nlinarith [sq_nonneg s]
  have i3 : |v| ≤ B / r := by
    have hv2 : v ^ 2 ≤ (B / r) ^ 2 := by
      calc v ^ 2 ≤ B / r * u := i4
        _ ≤ B / r * (B / r) := mul_le_mul_of_nonneg_left i1 (by positivity)
        _ = (B / r) ^ 2 := (sq _).symm
    have hBr : 0 ≤ B / r := by positivity
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (v + B / r), sq_nonneg (v - B / r)]
  exact ⟨i1, i2, i3, i4⟩

theorem norm_eI_le : ‖(eI : E22)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [eI]

theorem norm_e01_le : ‖(e01 : E22)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [e01]

theorem norm_e10_le : ‖(e10 : E22)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [e10]

theorem norm_dθMp_le (r θ : ℝ) (hr : 0 < r) (q : ℝ × ℝ) (u₀ : ℝ) (hu₀ : 0 < u₀) (hq : u₀ ≤ q.1) :
    ‖dθMp r θ q‖ ≤ r + 2 * r / u₀ := by
  rw [dθMp_eq]
  have hu : 0 < q.1 := lt_of_lt_of_le hu₀ hq
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    refine (mul_le_mul_of_nonneg_left norm_eI_le (norm_nonneg _)).trans ?_
    rw [mul_one, norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le (Real.abs_sin_le_one θ)
  · rw [norm_smul]
    refine (mul_le_mul_of_nonneg_left norm_e01_le (norm_nonneg _)).trans ?_
    rw [mul_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr, abs_div, abs_of_pos hu]
    have : |2 * Real.sin θ * Real.cos θ| ≤ 2 := by
      rw [abs_mul, abs_mul, abs_two]
      nlinarith [Real.abs_sin_le_one θ, Real.abs_cos_le_one θ, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
    calc r * (|2 * Real.sin θ * Real.cos θ| / q.1) ≤ r * (2 / u₀) := by
          gcongr
      _ = 2 * r / u₀ := by ring

theorem norm_dθMm_le (r θ : ℝ) (hr : 0 < r) (q : ℝ × ℝ) (u₀ : ℝ) (hu₀ : 0 < u₀) (hq : u₀ ≤ q.1) :
    ‖dθMm r θ q‖ ≤ r + 2 * r / u₀ := by
  rw [dθMm_eq]
  have hu : 0 < q.1 := lt_of_lt_of_le hu₀ hq
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    refine (mul_le_mul_of_nonneg_left norm_eI_le (norm_nonneg _)).trans ?_
    rw [mul_one, norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le (Real.abs_sin_le_one θ)
  · rw [norm_smul]
    refine (mul_le_mul_of_nonneg_left norm_e01_le (norm_nonneg _)).trans ?_
    rw [mul_one, norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr, abs_div,
      abs_of_pos hu]
    have : |2 * Real.sin θ * Real.cos θ| ≤ 2 := by
      rw [abs_mul, abs_mul, abs_two]
      nlinarith [Real.abs_sin_le_one θ, Real.abs_cos_le_one θ, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
    calc r * (|2 * Real.sin θ * Real.cos θ| / q.1) ≤ r * (2 / u₀) := by
          gcongr
      _ = 2 * r / u₀ := by ring

end Support

section DerivIntegral

variable {ψ : E22 → ℂ}

theorem integrableOn_of_box (g : ℝ × ℝ → ℂ) (hg : ContinuousOn g (Ioi (0 : ℝ) ×ˢ univ))
    (a b c : ℝ) (ha : 0 < a)
    (h0 : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), g q ≠ 0 → q ∈ Icc a b ×ˢ Icc (-c) c) :
    IntegrableOn g (Ioi (0 : ℝ) ×ˢ univ) := by
  set k : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-c) c
  have hk : IsCompact k := isCompact_Icc.prod isCompact_Icc
  have hkS : k ⊆ Ioi (0 : ℝ) ×ˢ univ := by
    rintro ⟨u, v⟩ ⟨⟨hu, -⟩, -⟩; exact ⟨lt_of_lt_of_le ha hu, mem_univ _⟩
  refine ((hg.mono hkS).integrableOn_compact hk).of_forall_diff_eq_zero
    (measurableSet_Ioi.prod MeasurableSet.univ) fun q hq => ?_
  by_contra h
  exact hq.2 (h0 q hq.1 h)

theorem integrableOn_Gψ (hψ : TestFn ψ) (r θ : ℝ) (hr : 0 < r) (hs : 0 < Real.sin θ) :
    IntegrableOn (Gψ ψ r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  obtain ⟨B, hB0, hB⟩ := chart_support hψ r hr
  refine integrableOn_of_box _ (continuousOn_Gψ hψ r θ) (r * Real.sin θ ^ 2 / B) (B / r) (B / r)
    (by positivity) fun q hq hne => ?_
  have hu : 0 < q.1 := hq.1
  have h : (ψ (Matrix.of.symm (Mp r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) ≠ 0) ∨
      (ψ (Matrix.of.symm (Mm r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) ≠ 0) := by
    by_contra hcon
    push Not at hcon
    apply hne
    simp [Gψ, hcon.1.1, hcon.2.1]
  obtain ⟨i1, i2⟩ := hB θ q hu h
  obtain ⟨j1, j2, j3, -⟩ := box_of_bound hr hB0 hu i1 i2
  exact ⟨⟨j2, j1⟩, abs_le.1 j3⟩

theorem hasDerivAt_integral_Gψ (hψ : TestFn ψ) (r : ℝ) (hr : 0 < r) (θ₁ : ℝ)
    (hs₁ : 0 < Real.sin θ₁) :
    IntegrableOn (dG ψ r θ₁) (Ioi (0 : ℝ) ×ˢ univ) ∧
    HasDerivAt (fun θ => ∫ q in Ioi (0 : ℝ) ×ˢ univ, Gψ ψ r θ q)
      (∫ q in Ioi (0 : ℝ) ×ˢ univ, dG ψ r θ₁ q) θ₁ := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  obtain ⟨B, hB0, hB⟩ := chart_support hψ r hr
  obtain ⟨C, hC0, -, hC⟩ := hψ.exists_bound
  set σ := Real.sin θ₁ / 2 with hσ_def
  have hσ : 0 < σ := by positivity
  set U : Set ℝ := {θ | σ < Real.sin θ} with hU_def
  have hU : U ∈ nhds θ₁ := by
    refine (isOpen_lt continuous_const Real.continuous_sin).mem_nhds ?_
    show σ < Real.sin θ₁
    rw [hσ_def]; linarith
  set u₀ := r * σ ^ 2 / B with hu₀_def
  have hu₀ : 0 < u₀ := by positivity
  set Cb := 2 * (C * (r + 2 * r / u₀)) / u₀ with hCb_def
  have hCb : 0 ≤ Cb := by positivity
  set box : Set (ℝ × ℝ) := Icc u₀ (B / r) ×ˢ Icc (-(B / r)) (B / r) with hbox_def
  have hboxm : MeasurableSet box := measurableSet_Icc.prod measurableSet_Icc
  set bound : ℝ × ℝ → ℝ := box.indicator fun _ => Cb with hbound_def

  have hsupp : ∀ θ ∈ U, ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), dG ψ r θ q ≠ 0 → q ∈ box := by
    intro θ hθ q hq hne
    have hu : 0 < q.1 := hq.1
    have h : (ψ (Matrix.of.symm (Mp r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) ≠ 0) ∨
        (ψ (Matrix.of.symm (Mm r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) ≠ 0) := by
      by_contra hcon
      push Not at hcon
      apply hne
      simp [dG, hcon.1.2, hcon.2.2]
    obtain ⟨i1, i2⟩ := hB θ q hu h
    obtain ⟨j1, j2, j3, -⟩ := box_of_bound hr hB0 hu i1 i2
    have hθ' : σ < Real.sin θ := hθ
    have hsin : σ ^ 2 ≤ Real.sin θ ^ 2 := by
      exact pow_le_pow_left₀ hσ.le hθ'.le 2
    refine ⟨⟨?_, j1⟩, abs_le.1 j3⟩
    calc u₀ = r * σ ^ 2 / B := rfl
      _ ≤ r * Real.sin θ ^ 2 / B := by gcongr
      _ ≤ q.1 := j2

  have hbd : ∀ θ ∈ U, ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ‖dG ψ r θ q‖ ≤ bound q := by
    intro θ hθ q hq
    by_cases hne : dG ψ r θ q = 0
    · rw [hne, norm_zero, hbound_def]
      exact Set.indicator_nonneg (fun _ _ => hCb) _
    have hqb := hsupp θ hθ q hq hne
    rw [hbound_def, indicator_of_mem hqb]
    have hu : u₀ ≤ q.1 := hqb.1.1
    have hu' : 0 < q.1 := lt_of_lt_of_le hu₀ hu
    rw [dG, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu', div_le_iff₀ hu']
    have hnum : ‖fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) (dθMp r θ q) +
        fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) (dθMm r θ q)‖ ≤ 2 * (C * (r + 2 * r / u₀)) := by
      refine (norm_add_le _ _).trans ?_
      have a1 : ‖fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) (dθMp r θ q)‖ ≤ C * (r + 2 * r / u₀) :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hC _) (norm_dθMp_le r θ hr q u₀ hu₀ hu) (norm_nonneg _) hC0)
      have a2 : ‖fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) (dθMm r θ q)‖ ≤ C * (r + 2 * r / u₀) :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hC _) (norm_dθMm_le r θ hr q u₀ hu₀ hu) (norm_nonneg _) hC0)
      linarith
    calc ‖fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) (dθMp r θ q) +
          fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) (dθMm r θ q)‖
        ≤ 2 * (C * (r + 2 * r / u₀)) := hnum
      _ = Cb * u₀ := by rw [hCb_def]; field_simp
      _ ≤ Cb * q.1 := by gcongr
  have hbi : Integrable bound (volume.restrict (Ioi (0 : ℝ) ×ˢ univ)) := by
    rw [hbound_def]
    refine Integrable.integrableOn ?_
    rw [integrable_indicator_iff hboxm]
    have : volume box < ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    exact integrableOn_const this.ne
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ) ×ˢ univ))
    (F := fun θ q => Gψ ψ r θ q) (F' := fun θ q => dG ψ r θ q) (x₀ := θ₁) (bound := bound) hU
    (Eventually.of_forall fun θ => (continuousOn_Gψ hψ r θ).aestronglyMeasurable hS)
    (integrableOn_Gψ hψ r θ₁ hr hs₁)
    ((continuousOn_dG hψ r θ₁).aestronglyMeasurable hS)
    (by
      filter_upwards [ae_restrict_mem hS] with q hq θ hθ
      exact hbd θ hθ q hq)
    hbi
    (by
      filter_upwards [] with q θ _
      exact hasDerivAt_Gψ hψ r θ q)
  exact key

end DerivIntegral

section Slice

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem continuous_entrySlice (Φ : E22 × P → ℂ) (hΦ : Continuous Φ) (p : P) :
    Continuous (entrySlice Φ p) := by
  unfold entrySlice
  have h1 : Continuous fun g : GL (Fin 2) ℝ => (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ) : E22) :=
    continuous_pi fun i => continuous_pi fun j =>
      (Continuous.matrix_elem continuous_id i j).comp Units.continuous_val
  exact hΦ.comp (h1.prodMk continuous_const)

theorem ellipticTransform_entrySlice_eq (Φ : E22 × P → ℂ) (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦc : HasCompactSupport Φ) (p : P) (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ) =
      2 * ∫ q in Ioi (0 : ℝ) ×ˢ univ, Gψ (φ Φ p) r θ q := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have hψ := testFn_φ Φ hΦs hΦc p
  have heq : EqOn (G (entrySlice Φ p) r θ) (Gψ (φ Φ p) r θ) (Ioi (0 : ℝ) ×ˢ univ) :=
    fun q hq => G_entrySlice Φ p r θ hr q hq.1
  have hG : IntegrableOn (G (entrySlice Φ p) r θ) (Ioi (0 : ℝ) ×ˢ univ) :=
    (integrableOn_Gψ hψ r θ hr (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)).congr_fun heq.symm hS
  rw [main_of_integrable (entrySlice Φ p) (continuous_entrySlice Φ hΦs.continuous p) r θ hr hθ hθπ hG,
    setIntegral_congr_fun hS heq]

theorem deriv_main (Φ : E22 × P → ℂ) (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (p : P) (r : ℝ) (hr : 0 < r) (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    IntegrableOn (dG (φ Φ p) r θ) (Ioi (0 : ℝ) ×ˢ univ) ∧
    HasDerivAt (fun t : ℝ => ellipticTransform (entrySlice Φ p) r t / (2 * Real.sin t : ℂ))
      (2 * ∫ q in Ioi (0 : ℝ) ×ˢ univ, dG (φ Φ p) r θ q) θ := by
  have hψ := testFn_φ Φ hΦs hΦc p
  obtain ⟨hint, hder⟩ := hasDerivAt_integral_Gψ hψ r hr θ (Real.sin_pos_of_pos_of_lt_pi hθ hθπ)
  refine ⟨hint, ?_⟩
  have hev : (fun t : ℝ => ellipticTransform (entrySlice Φ p) r t / (2 * Real.sin t : ℂ)) =ᶠ[nhds θ]
      fun t => 2 * ∫ q in Ioi (0 : ℝ) ×ˢ univ, Gψ (φ Φ p) r t q := by
    filter_upwards [Ioo_mem_nhds hθ hθπ] with t ht
    exact ellipticTransform_entrySlice_eq Φ hΦs hΦc p r t hr ht.1 ht.2
  exact (hder.const_mul 2).congr_of_eventuallyEq hev

end Slice

section IBP

variable {ψ : E22 → ℂ}

def I1int (ψ : E22 → ℂ) (r θ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) eI + fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) eI) / (q.1 : ℂ)

def Jint (ψ : E22 → ℂ) (r θ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (((Real.sin θ ^ 2 + q.2 ^ 2)⁻¹ : ℝ) : ℂ) *
    (fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) e10 - fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) e10)

def Kint (ψ : E22 → ℂ) (r θ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (((Real.sin θ ^ 2 + q.2 ^ 2)⁻¹ : ℝ) : ℂ) *
    (fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) (duMp r θ q) + fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) (duMm r θ q))

theorem dG_eq (ψ : E22 → ℂ) (r θ : ℝ) (q : ℝ × ℝ) (hq : q.1 ≠ 0) (hsv : Real.sin θ ^ 2 + q.2 ^ 2 ≠ 0) :
    dG ψ r θ q =
      -((r * Real.sin θ : ℝ) : ℂ) * I1int ψ r θ q - ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) * Kint ψ r θ q -
        ((2 * Real.sin θ * Real.cos θ * r : ℝ) : ℂ) * Jint ψ r θ q := by
  unfold dG I1int Jint Kint
  set Dp := fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) with hDp
  set Dm := fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) with hDm
  have hp : (q.1)⁻¹ • Dp (dθMp r θ q) =
      (-(r * Real.sin θ / q.1)) • Dp eI +
        (-(2 * Real.sin θ * Real.cos θ / (Real.sin θ ^ 2 + q.2 ^ 2))) • (Dp (duMp r θ q) + r • Dp e10) := by
    rw [← map_smul, dθMp_identity r θ q hq hsv]
    simp only [map_add, map_smul]
  have hm : (q.1)⁻¹ • Dm (dθMm r θ q) =
      (-(r * Real.sin θ / q.1)) • Dm eI +
        (-(2 * Real.sin θ * Real.cos θ / (Real.sin θ ^ 2 + q.2 ^ 2))) • (Dm (duMm r θ q) + (-r) • Dm e10) := by
    rw [← map_smul, dθMm_identity r θ q hq hsv]
    simp only [map_add, map_smul]
  simp only [Complex.real_smul] at hp hm
  have hu0 : (q.1 : ℂ) ≠ 0 := by exact_mod_cast hq
  have hsv0 : ((Real.sin θ ^ 2 + q.2 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsv
  have e1 : (Dp (dθMp r θ q) + Dm (dθMm r θ q)) / (q.1 : ℂ) =
      ((q.1⁻¹ : ℝ) : ℂ) * Dp (dθMp r θ q) + ((q.1⁻¹ : ℝ) : ℂ) * Dm (dθMm r θ q) := by
    push_cast
    field_simp
  rw [e1, hp, hm]
  push_cast
  field_simp
  ring

theorem continuousOn_duMp (r θ : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => duMp r θ q) (Ioi (0 : ℝ) ×ˢ univ) := by
  have : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), q.1 ≠ 0 := fun q hq => (hq.1 : (0:ℝ) < q.1).ne'
  unfold duMp
  have h1 : ContinuousOn (fun q : ℝ × ℝ => -(r * (Real.sin θ ^ 2 + q.2 ^ 2) / q.1 ^ 2))
      (Ioi (0 : ℝ) ×ˢ univ) :=
    fun q hq => by
      have hq0 : q.1 ^ 2 ≠ 0 := pow_ne_zero 2 (this q hq)
      have : ContinuousAt (fun q : ℝ × ℝ => -(r * (Real.sin θ ^ 2 + q.2 ^ 2) / q.1 ^ 2)) q := by
        fun_prop (disch := exact hq0)
      exact this.continuousWithinAt
  exact (h1.smul continuousOn_const).add continuousOn_const

theorem continuousOn_duMm (r θ : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => duMm r θ q) (Ioi (0 : ℝ) ×ˢ univ) := by
  have : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), q.1 ≠ 0 := fun q hq => (hq.1 : (0:ℝ) < q.1).ne'
  unfold duMm
  have h1 : ContinuousOn (fun q : ℝ × ℝ => r * (Real.sin θ ^ 2 + q.2 ^ 2) / q.1 ^ 2)
      (Ioi (0 : ℝ) ×ˢ univ) :=
    fun q hq => by
      have hq0 : q.1 ^ 2 ≠ 0 := pow_ne_zero 2 (this q hq)
      have : ContinuousAt (fun q : ℝ × ℝ => r * (Real.sin θ ^ 2 + q.2 ^ 2) / q.1 ^ 2) q := by
        fun_prop (disch := exact hq0)
      exact this.continuousWithinAt
  exact (h1.smul continuousOn_const).add continuousOn_const

theorem continuousOn_I1int (hψ : TestFn ψ) (r θ : ℝ) :
    ContinuousOn (I1int ψ r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  unfold I1int
  have hA : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) eI) (Ioi (0 : ℝ) ×ˢ univ) :=
    ContinuousOn.clm_apply (hψ.continuous_fderiv.comp_continuousOn (continuousOn_Mp r θ)) continuousOn_const
  have hB : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) eI) (Ioi (0 : ℝ) ×ˢ univ) :=
    ContinuousOn.clm_apply (hψ.continuous_fderiv.comp_continuousOn (continuousOn_Mm r θ)) continuousOn_const
  refine ContinuousOn.div (hA.add hB) (Complex.continuous_ofReal.comp_continuousOn continuousOn_fst)
    fun q hq => ?_
  exact_mod_cast (hq.1 : (0:ℝ) < q.1).ne'

theorem continuousOn_weight (θ : ℝ) (hs : 0 < Real.sin θ) :
    ContinuousOn (fun q : ℝ × ℝ => (((Real.sin θ ^ 2 + q.2 ^ 2)⁻¹ : ℝ) : ℂ)) (Ioi (0 : ℝ) ×ˢ univ) := by
  refine (Complex.continuous_ofReal.comp ?_).continuousOn
  refine Continuous.inv₀ (by fun_prop) fun q => ?_
  positivity

theorem continuousOn_Jint (hψ : TestFn ψ) (r θ : ℝ) (hs : 0 < Real.sin θ) :
    ContinuousOn (Jint ψ r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  unfold Jint
  have hA : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) e10) (Ioi (0 : ℝ) ×ˢ univ) :=
    ContinuousOn.clm_apply (hψ.continuous_fderiv.comp_continuousOn (continuousOn_Mp r θ)) continuousOn_const
  have hB : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) e10) (Ioi (0 : ℝ) ×ˢ univ) :=
    ContinuousOn.clm_apply (hψ.continuous_fderiv.comp_continuousOn (continuousOn_Mm r θ)) continuousOn_const
  exact (continuousOn_weight θ hs).mul (hA.sub hB)

theorem continuousOn_Kint (hψ : TestFn ψ) (r θ : ℝ) (hs : 0 < Real.sin θ) :
    ContinuousOn (Kint ψ r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  unfold Kint
  have hA : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) (duMp r θ q))
      (Ioi (0 : ℝ) ×ˢ univ) :=
    ContinuousOn.clm_apply (hψ.continuous_fderiv.comp_continuousOn (continuousOn_Mp r θ))
      (continuousOn_duMp r θ)
  have hB : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) (duMm r θ q))
      (Ioi (0 : ℝ) ×ˢ univ) :=
    ContinuousOn.clm_apply (hψ.continuous_fderiv.comp_continuousOn (continuousOn_Mm r θ))
      (continuousOn_duMm r θ)
  exact (continuousOn_weight θ hs).mul (hA.add hB)

theorem box_of_fderiv_ne (hψ : TestFn ψ) (r : ℝ) (hr : 0 < r) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ θ : ℝ, ∀ q : ℝ × ℝ, 0 < q.1 →
      ((ψ (Matrix.of.symm (Mp r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) ≠ 0) ∨
        (ψ (Matrix.of.symm (Mm r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) ≠ 0)) →
      r * q.1 ≤ B ∧ r * (Real.sin θ ^ 2 + q.2 ^ 2) ≤ B * q.1)
    (θ : ℝ) (q : ℝ × ℝ) (hu : 0 < q.1)
    (h : fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) ≠ 0) :
    q ∈ Icc (r * Real.sin θ ^ 2 / B) (B / r) ×ˢ Icc (-(B / r)) (B / r) := by
  have h' : (ψ (Matrix.of.symm (Mp r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mp r θ q)) ≠ 0) ∨
      (ψ (Matrix.of.symm (Mm r θ q)) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mm r θ q)) ≠ 0) :=
    h.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))
  obtain ⟨i1, i2⟩ := hB θ q hu h'
  obtain ⟨j1, j2, j3, -⟩ := box_of_bound hr hB0 hu i1 i2
  exact ⟨⟨j2, j1⟩, abs_le.1 j3⟩

theorem integrableOn_I1int (hψ : TestFn ψ) (r θ : ℝ) (hr : 0 < r) (hs : 0 < Real.sin θ) :
    IntegrableOn (I1int ψ r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  obtain ⟨B, hB0, hB⟩ := chart_support hψ r hr
  refine integrableOn_of_box _ (continuousOn_I1int hψ r θ) (r * Real.sin θ ^ 2 / B) (B / r) (B / r)
    (by positivity) fun q hq hne => box_of_fderiv_ne hψ r hr hB0 hB θ q hq.1 ?_
  by_contra hcon; push Not at hcon; apply hne; simp [I1int, hcon.1, hcon.2]

theorem integrableOn_Jint (hψ : TestFn ψ) (r θ : ℝ) (hr : 0 < r) (hs : 0 < Real.sin θ) :
    IntegrableOn (Jint ψ r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  obtain ⟨B, hB0, hB⟩ := chart_support hψ r hr
  refine integrableOn_of_box _ (continuousOn_Jint hψ r θ hs) (r * Real.sin θ ^ 2 / B) (B / r) (B / r)
    (by positivity) fun q hq hne => box_of_fderiv_ne hψ r hr hB0 hB θ q hq.1 ?_
  by_contra hcon; push Not at hcon; apply hne; simp [Jint, hcon.1, hcon.2]

theorem integrableOn_Kint (hψ : TestFn ψ) (r θ : ℝ) (hr : 0 < r) (hs : 0 < Real.sin θ) :
    IntegrableOn (Kint ψ r θ) (Ioi (0 : ℝ) ×ˢ univ) := by
  obtain ⟨B, hB0, hB⟩ := chart_support hψ r hr
  refine integrableOn_of_box _ (continuousOn_Kint hψ r θ hs) (r * Real.sin θ ^ 2 / B) (B / r) (B / r)
    (by positivity) fun q hq hne => box_of_fderiv_ne hψ r hr hB0 hB θ q hq.1 ?_
  by_contra hcon; push Not at hcon; apply hne; simp [Kint, hcon.1, hcon.2]

theorem integral_u_deriv_eq_zero (hψ : TestFn ψ) (r θ : ℝ) (hr : 0 < r) (hs : 0 < Real.sin θ) (v : ℝ) :
    ∫ u in Ioi (0 : ℝ), (fderiv ℝ ψ (Matrix.of.symm (Mp r θ (u, v))) (duMp r θ (u, v)) +
      fderiv ℝ ψ (Matrix.of.symm (Mm r θ (u, v))) (duMm r θ (u, v))) = 0 := by
  obtain ⟨B, hB0, hB⟩ := chart_support hψ r hr
  set F : ℝ → ℂ := fun u => ψ (Matrix.of.symm (Mp r θ (u, v))) + ψ (Matrix.of.symm (Mm r θ (u, v))) with hF
  set F' : ℝ → ℂ := fun u => fderiv ℝ ψ (Matrix.of.symm (Mp r θ (u, v))) (duMp r θ (u, v)) +
      fderiv ℝ ψ (Matrix.of.symm (Mm r θ (u, v))) (duMm r θ (u, v)) with hF'
  set a₀ := r * Real.sin θ ^ 2 / (2 * B) with ha₀
  have ha₀pos : 0 < a₀ := by positivity

  have hderiv : ∀ u : ℝ, u ≠ 0 → HasDerivAt F (F' u) u := by
    intro u hu
    have h1 := (hψ.differentiable _).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_Mp_u r θ v u hu)
    have h2 := (hψ.differentiable _).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_Mm_u r θ v u hu)
    exact h1.add h2

  have hsuppF : ∀ u : ℝ, 0 < u → F u ≠ 0 → r * Real.sin θ ^ 2 / B ≤ u ∧ u ≤ B / r := by
    intro u hu hne
    have h : (ψ (Matrix.of.symm (Mp r θ (u, v))) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mp r θ (u, v))) ≠ 0) ∨
        (ψ (Matrix.of.symm (Mm r θ (u, v))) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mm r θ (u, v))) ≠ 0) := by
      by_contra hcon; push Not at hcon; apply hne; simp [hF, hcon.1.1, hcon.2.1]
    obtain ⟨i1, i2⟩ := hB θ (u, v) hu h
    obtain ⟨j1, j2, -, -⟩ := box_of_bound hr hB0 hu i1 i2
    exact ⟨j2, j1⟩
  have hsuppF' : ∀ u : ℝ, 0 < u → F' u ≠ 0 → r * Real.sin θ ^ 2 / B ≤ u ∧ u ≤ B / r := by
    intro u hu hne
    have h : fderiv ℝ ψ (Matrix.of.symm (Mp r θ (u, v))) ≠ 0 ∨ fderiv ℝ ψ (Matrix.of.symm (Mm r θ (u, v))) ≠ 0 := by
      by_contra hcon; push Not at hcon; apply hne; simp [hF', hcon.1, hcon.2]
    have := box_of_fderiv_ne hψ r hr hB0 hB θ (u, v) hu h
    exact ⟨this.1.1, this.1.2⟩
  have hlt : a₀ < r * Real.sin θ ^ 2 / B := by
    rw [ha₀];
    have : 0 < r * Real.sin θ ^ 2 := by positivity
    rw [div_lt_div_iff_of_pos_left this (by positivity) hB0]; linarith

  have hzero : ∀ u ∈ Ioi (0 : ℝ) \ Ioi a₀, F' u = 0 := by
    intro u hu
    by_contra hne
    have := (hsuppF' u hu.1 hne).1
    exact hu.2 (lt_of_lt_of_le hlt this)
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi ha₀pos.le) hzero]

  have hcont : ContinuousWithinAt F (Ici a₀) a₀ :=
    ((hderiv a₀ ha₀pos.ne').continuousAt).continuousWithinAt
  have hFa₀ : F a₀ = 0 := by
    by_contra hne
    have := (hsuppF a₀ ha₀pos hne).1
    linarith
  have hint : IntegrableOn F' (Ioi a₀) := by

    have hc : ContinuousOn F' (Icc a₀ (B / r + 1)) := by
      intro u hu
      have hu0 : u ≠ 0 := (lt_of_lt_of_le ha₀pos hu.1).ne'
      refine ContinuousAt.continuousWithinAt ?_
      have hq : ContinuousAt (fun t : ℝ => ((t, v) : ℝ × ℝ)) u := by fun_prop
      have hS' : Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) ∈ nhds ((u, v) : ℝ × ℝ) :=
        (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨lt_of_lt_of_le ha₀pos hu.1, mem_univ _⟩
      have hA : ContinuousAt (fun t : ℝ => Kint ψ r θ (t, v)) u :=
        ContinuousAt.comp (g := Kint ψ r θ) (f := fun t : ℝ => ((t, v) : ℝ × ℝ))
          ((continuousOn_Kint hψ r θ hs).continuousAt hS') hq

      have hw : (((Real.sin θ ^ 2 + v ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
        have : (0 : ℝ) < Real.sin θ ^ 2 + v ^ 2 := by positivity
        exact_mod_cast (inv_pos.2 this).ne'
      have : F' = fun t => ((((Real.sin θ ^ 2 + v ^ 2)⁻¹ : ℝ) : ℂ))⁻¹ * Kint ψ r θ (t, v) := by
        funext t
        simp only [hF', Kint]
        rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul]
      rw [this]
      exact (continuousAt_const.mul hA)
    refine (hc.integrableOn_compact isCompact_Icc).of_forall_diff_eq_zero measurableSet_Ioi ?_
    intro u hu
    by_contra hne
    have h1 := hsuppF' u (lt_trans ha₀pos hu.1) hne
    exact hu.2 ⟨hu.1.le, by linarith [h1.2]⟩
  have hlim : Tendsto F atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (B / r)] with u hu
    by_contra hne
    have := (hsuppF u (lt_trans (by positivity) hu) (Ne.symm hne)).2
    linarith
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun u hu => hderiv u (lt_trans ha₀pos hu).ne') hint hlim,
    hFa₀, sub_zero]

theorem restrict_S_eq :
    ((volume : Measure ℝ).restrict (Ioi 0)).prod (volume : Measure ℝ) =
      (volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
  rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]

theorem integral_Kint_eq_zero (hψ : TestFn ψ) (r θ : ℝ) (hr : 0 < r) (hs : 0 < Real.sin θ) :
    ∫ q in Ioi (0 : ℝ) ×ˢ univ, Kint ψ r θ q = 0 := by
  have hK := integrableOn_Kint hψ r θ hr hs
  have hK' : Integrable (Kint ψ r θ) (((volume : Measure ℝ).restrict (Ioi 0)).prod (volume : Measure ℝ)) := by
    rw [restrict_S_eq]; exact hK
  have e1 : ∫ q in Ioi (0 : ℝ) ×ˢ univ, Kint ψ r θ q =
      ∫ q, Kint ψ r θ q ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod (volume : Measure ℝ)) := by
    rw [restrict_S_eq]
  rw [e1, integral_prod_symm _ hK']
  refine integral_eq_zero_of_ae (Eventually.of_forall fun v => ?_)
  show (∫ u in Ioi (0 : ℝ), Kint ψ r θ (u, v)) = 0
  simp only [Kint]
  rw [integral_const_mul, integral_u_deriv_eq_zero hψ r θ hr hs v, mul_zero]

theorem integral_dG_eq (hψ : TestFn ψ) (r θ : ℝ) (hr : 0 < r) (hs : 0 < Real.sin θ) :
    ∫ q in Ioi (0 : ℝ) ×ˢ univ, dG ψ r θ q =
      -((r * Real.sin θ : ℝ) : ℂ) * (∫ q in Ioi (0 : ℝ) ×ˢ univ, I1int ψ r θ q) -
        ((2 * Real.sin θ * Real.cos θ * r : ℝ) : ℂ) * (∫ q in Ioi (0 : ℝ) ×ˢ univ, Jint ψ r θ q) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  have heq : EqOn (dG ψ r θ) (fun q => -((r * Real.sin θ : ℝ) : ℂ) * I1int ψ r θ q -
      ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) * Kint ψ r θ q -
        ((2 * Real.sin θ * Real.cos θ * r : ℝ) : ℂ) * Jint ψ r θ q) (Ioi (0 : ℝ) ×ˢ univ) := by
    intro q hq
    have hu : (0 : ℝ) < q.1 := hq.1
    exact dG_eq ψ r θ q hu.ne' (by positivity)
  rw [setIntegral_congr_fun hS heq]
  have h1 := (integrableOn_I1int hψ r θ hr hs).const_mul (-((r * Real.sin θ : ℝ) : ℂ))
  have h2 := (integrableOn_Kint hψ r θ hr hs).const_mul (((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ))
  have h3 := (integrableOn_Jint hψ r θ hr hs).const_mul (((2 * Real.sin θ * Real.cos θ * r : ℝ) : ℂ))
  have h12 : Integrable (fun q => -((r * Real.sin θ : ℝ) : ℂ) * I1int ψ r θ q -
      ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) * Kint ψ r θ q) (volume.restrict (Ioi (0 : ℝ) ×ˢ univ)) :=
    h1.sub h2
  rw [integral_sub h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_Kint_eq_zero hψ r θ hr hs, mul_zero, sub_zero]

end IBP

section GLsupport

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hasCompactSupport_entrySlice (Φ : E22 × P → ℂ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (p : P) :
    HasCompactSupport (entrySlice Φ p) := by
  set K₁ : Set E22 := Prod.fst '' tsupport Φ with hK₁_def
  have hK₁ : IsCompact K₁ := hΦc.image continuous_fst
  have hK₁U : ∀ M ∈ K₁, (Matrix.of M).det ≠ 0 := by
    rintro M ⟨q, hq, rfl⟩; exact (hΦU hq).ne_zero

  set σ : E22 → GL (Fin 2) ℝ := fun M =>
    if h : (Matrix.of M).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1 with hσ_def
  have hσ : ContinuousOn σ {M : E22 | (Matrix.of M).det ≠ 0} := by
    rw [continuousOn_iff_continuous_restrict]
    have hres : ({M : E22 | (Matrix.of M).det ≠ 0}).domRestrict σ =
        fun M => Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of M.1) M.2 := by
      funext M
      simp only [Set.domRestrict_apply, hσ_def]
      rw [dif_pos (show (Matrix.of (M : E22)).det ≠ 0 from M.2)]
    rw [hres]
    have hval : Continuous fun M : ↥({M : E22 | (Matrix.of M).det ≠ 0}) => (Matrix.of M.1 : Matrix (Fin 2) (Fin 2) ℝ) :=
      continuous_matrix fun i j =>
        ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · simpa [Function.comp_def, Matrix.GeneralLinearGroup.val_mkOfDetNeZero] using hval
    · simp only [Matrix.coe_units_inv, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.inv_def,
        Ring.inverse_eq_inv']
      exact Continuous.fun_smul (hval.matrix_det.inv₀ fun M => M.2) hval.matrix_adjugate
  have hK₂ : IsCompact (σ '' K₁) := hK₁.image_of_continuousOn (hσ.mono fun M hM => hK₁U M hM)
  refine HasCompactSupport.intro hK₂ fun g hg => ?_
  by_contra hne
  apply hg
  have hM : (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ) : E22) ∈ K₁ :=
    ⟨(_, p), subset_tsupport _ hne, rfl⟩
  refine ⟨_, hM, ?_⟩
  have hdet := hK₁U _ hM
  simp only [hσ_def, dif_pos hdet]
  ext i j
  simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

end GLsupport

section Assembly

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem tendsto_sub_div_of_hasDerivAt (g g' : ℝ → ℂ) (L ℓ : ℂ) (b : ℝ) (hb : 0 < b)
    (hder : ∀ t ∈ Ioo 0 b, HasDerivAt g (g' t) t)
    (hg : Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds L))
    (hg' : Tendsto g' (nhdsWithin 0 (Ioi 0)) (nhds ℓ)) :
    Tendsto (fun t : ℝ => (g t - L) / (t : ℂ)) (nhdsWithin 0 (Ioi 0)) (nhds ℓ) := by
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioo 0 b := Ioo_mem_nhdsGT hb

  have hre : Tendsto (fun t : ℝ => (g t - L).re / t) (nhdsWithin 0 (Ioi 0)) (nhds ℓ.re) := by
    refine HasDerivAt.lhopital_zero_nhdsGT (f' := fun t => (g' t).re) (g := fun t => t) (g' := fun _ => (1 : ℝ))
      ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hev] with t ht
      exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hder t ht).sub_const L)
    · exact Eventually.of_forall fun t => hasDerivAt_id t
    · exact Eventually.of_forall fun _ => one_ne_zero
    · have : Tendsto (fun t => g t - L) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        simpa using hg.sub_const L
      simpa [Function.comp_def] using (Complex.continuous_re.tendsto 0).comp this
    · exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    · simpa [Function.comp_def] using (Complex.continuous_re.tendsto ℓ).comp hg'
  have him : Tendsto (fun t : ℝ => (g t - L).im / t) (nhdsWithin 0 (Ioi 0)) (nhds ℓ.im) := by
    refine HasDerivAt.lhopital_zero_nhdsGT (f' := fun t => (g' t).im) (g := fun t => t) (g' := fun _ => (1 : ℝ))
      ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hev] with t ht
      exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t ((hder t ht).sub_const L)
    · exact Eventually.of_forall fun t => hasDerivAt_id t
    · exact Eventually.of_forall fun _ => one_ne_zero
    · have : Tendsto (fun t => g t - L) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        simpa using hg.sub_const L
      simpa [Function.comp_def] using (Complex.continuous_im.tendsto 0).comp this
    · exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    · simpa [Function.comp_def] using (Complex.continuous_im.tendsto ℓ).comp hg'
  have hsum := (hre.ofReal).add ((him.ofReal).mul_const Complex.I)
  rw [Complex.re_add_im] at hsum
  refine hsum.congr fun t => ?_
  rw [← Complex.div_ofReal_re, ← Complex.div_ofReal_im, Complex.re_add_im]

theorem head_main (Φ : E22 × P → ℂ) (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (p : P) (r : ℝ) (hr : 0 < r) :
    ∃ L : ℂ,
      Tendsto (fun θ : ℝ => ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ))
        (nhdsWithin 0 (Ioi 0)) (nhds L) ∧
      Tendsto (fun θ : ℝ => (ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ) - L) / (θ : ℂ))
        (nhdsWithin 0 (Ioi 0))
        (nhds (((-(8 * Real.pi) : ℝ) : ℂ) * Φ (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)), p))) := by
  have hψ := testFn_φ Φ hΦs hΦc p

  obtain ⟨-, hL⟩ := AutomorphicForm.GL2Real.tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero
    (entrySlice Φ p) (continuous_entrySlice Φ hΦs.continuous p) (hasCompactSupport_entrySlice Φ hΦc hΦU p) r hr
  set L := (2 * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.univ,
        ((if h : Matrix.det !![r * (1 - q.2), r * (q.2 ^ 2 / q.1); -(r * q.1), r * (1 + q.2)] ≠ 0 then
            entrySlice Φ p (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) +
          (if h : Matrix.det !![r * (1 + q.2), -(r * (q.2 ^ 2 / q.1)); r * q.1, r * (1 - q.2)] ≠ 0 then
            entrySlice Φ p (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0)) / (q.1 : ℂ)) with hL_def
  refine ⟨L, hL, ?_⟩

  have hT1 : Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Ioi (0 : ℝ) ×ˢ univ, I1int (φ Φ p) r θ q)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    AutomorphicForm.GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero
      P Φ hΦs hΦc p r hr
  have hT2 : Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Ioi (0 : ℝ) ×ˢ univ, Jint (φ Φ p) r θ q)
      (nhdsWithin 0 (Ioi 0)) (nhds (((2 * Real.pi / r : ℝ) : ℂ) * Φ (Matrix.of.symm (r • 1), p))) :=
    AutomorphicForm.GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero
      P Φ hΦs hΦc p r hr

  set G' : ℝ → ℂ := fun θ =>
    2 * (-(r : ℂ) * ((Real.sin θ : ℂ) * ∫ q in Ioi (0 : ℝ) ×ˢ univ, I1int (φ Φ p) r θ q) -
      ((2 * r * Real.cos θ : ℝ) : ℂ) * ((Real.sin θ : ℂ) * ∫ q in Ioi (0 : ℝ) ×ˢ univ, Jint (φ Φ p) r θ q))
    with hG'_def
  have hder : ∀ θ ∈ Ioo 0 Real.pi, HasDerivAt
      (fun t : ℝ => ellipticTransform (entrySlice Φ p) r t / (2 * Real.sin t : ℂ)) (G' θ) θ := by
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have h := (deriv_main Φ hΦs hΦc p r hr θ hθ.1 hθ.2).2
    rw [integral_dG_eq hψ r θ hr hs] at h
    convert h using 1
    rw [hG'_def]
    push_cast
    ring

  have hcos : Tendsto (fun θ : ℝ => ((2 * r * Real.cos θ : ℝ) : ℂ)) (nhdsWithin 0 (Ioi 0))
      (nhds ((2 * r : ℝ) : ℂ)) := by
    have : Tendsto (fun θ : ℝ => 2 * r * Real.cos θ) (nhds 0) (nhds (2 * r)) := by
      have h := ((Real.continuous_cos.tendsto 0).const_mul (2 * r))
      simpa using h
    exact (this.mono_left nhdsWithin_le_nhds).ofReal
  have hlimG' : Tendsto G' (nhdsWithin 0 (Ioi 0))
      (nhds (2 * (-(r : ℂ) * 0 - ((2 * r : ℝ) : ℂ) * (((2 * Real.pi / r : ℝ) : ℂ) * Φ (Matrix.of.symm (r • 1), p))))) :=
    ((hT1.const_mul _).sub (hcos.mul hT2)).const_mul 2
  have hval : (2 * (-(r : ℂ) * 0 - ((2 * r : ℝ) : ℂ) * (((2 * Real.pi / r : ℝ) : ℂ) * Φ (Matrix.of.symm (r • 1), p)))) =
      ((-(8 * Real.pi) : ℝ) : ℂ) * Φ (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)), p) := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp
    ring
  rw [hval] at hlimG'
  exact tendsto_sub_div_of_hasDerivAt _ G' L _ Real.pi Real.pi_pos hder hL hlimG'

end Assembly

end AutomorphicForm.GL2Real.RHead

end
open MeasureTheory _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi.AutomorphicForm _root_.AutomorphicForm.GL2Real _root_.P2MW.S_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi.AutomorphicForm.GL2Real in
theorem solution :
    ∃ C : ℝ, C ≠ 0 ∧
      ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} →
        ∀ (p : P) (r : ℝ), 0 < r →
          ∃ L : ℂ,
            Filter.Tendsto (fun θ : ℝ => ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
            Filter.Tendsto
              (fun θ : ℝ => (ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ) - L) / (θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds ((C : ℂ) * Φ (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)), p))) := by
  refine ⟨-(8 * Real.pi), neg_ne_zero.mpr (by positivity), ?_⟩
  intro P _ _ Φ hΦs hΦc hΦU p r hr
  exact AutomorphicForm.GL2Real.RHead.head_main Φ hΦs hΦc hΦU p r hr

end S_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi (solution)
