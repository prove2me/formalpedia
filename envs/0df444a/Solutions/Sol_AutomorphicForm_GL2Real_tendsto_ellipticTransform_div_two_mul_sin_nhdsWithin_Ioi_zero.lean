-- Prove2me | solution 1 for AutomorphicForm.GL2Real.tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e7d63c98-4a01-5398-972d-ce0cd1bcdb60

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero

set_option autoImplicit false

open MeasureTheory Set Filter

noncomputable section

namespace AutomorphicForm
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "upperHalfPlaneElt ellipticElt ellipticTransform"
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
    have := hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := q) |>.mul h1
    simp only [div_eq_mul_inv] at this ⊢
    exact this
  convert hA.prodMk hB using 1
  all_goals first | rfl | skip
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
    refine continuous_const.fun_smul (continuous_matrix fun i j => ?_)
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
    refine continuous_const.fun_smul (continuous_matrix fun i j => ?_)
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

private theorem _root_.AutomorphicForm.GL2Real.RCoord.main (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    IntegrableOn (G f r θ) (Ioi (0 : ℝ) ×ˢ univ) ∧
    ellipticTransform f r θ / (2 * Real.sin θ : ℂ) = 2 * ∫ q in Ioi (0 : ℝ) ×ˢ univ, G f r θ q := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  set s := Real.sin θ with hs_def
  have hG := integrableOn_G f hf hfc r θ hr hs
  refine ⟨hG, ?_⟩

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

p2m_export "AutomorphicForm.GL2Real.RCoord" "main"
end AutomorphicForm.GL2Real.RCoord

namespace AutomorphicForm
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "upperHalfPlaneElt ellipticElt ellipticTransform"
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
    refine continuous_const.fun_smul (continuous_matrix fun i j => ?_)
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
    refine continuous_const.fun_smul (continuous_matrix fun i j => ?_)
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

end

open MeasureTheory _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero.AutomorphicForm _root_.AutomorphicForm.GL2Real _root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero.AutomorphicForm.GL2Real in
theorem solution
    (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun q : ℝ × ℝ =>
        ((if h : Matrix.det !![r * (1 - q.2), r * (q.2 ^ 2 / q.1); -(r * q.1), r * (1 + q.2)] ≠ 0 then
            f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) +
          (if h : Matrix.det !![r * (1 + q.2), -(r * (q.2 ^ 2 / q.1)); r * q.1, r * (1 - q.2)] ≠ 0 then
            f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0)) / (q.1 : ℂ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) ∧
    Filter.Tendsto (fun θ : ℝ => ellipticTransform f r θ / (2 * Real.sin θ : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.univ,
        ((if h : Matrix.det !![r * (1 - q.2), r * (q.2 ^ 2 / q.1); -(r * q.1), r * (1 + q.2)] ≠ 0 then
            f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0) +
          (if h : Matrix.det !![r * (1 + q.2), -(r * (q.2 ^ 2 / q.1)); r * q.1, r * (1 - q.2)] ≠ 0 then
            f (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) else 0)) / (q.1 : ℂ))) :=
  AutomorphicForm.GL2Real.RLim.main f hf hfc r hr

end S_AutomorphicForm_GL2Real_tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_tendsto_ellipticTransform_div_two_mul_sin_nhdsWithin_Ioi_zero (solution)
