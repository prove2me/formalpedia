-- Prove2me | solution 1 for AutomorphicForm.exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e8c98b0d-043a-59b9-bdb0-9a93fb015d75

import Mathlib
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous

set_option autoImplicit false

open scoped Classical
open NumberField AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain

noncomputable section

namespace CircleCharacterClassification

theorem exists_eq_exp_of_continuous_mul (f : ℝ → ℂ) (hf : Continuous f) (h0 : f 0 = 1)
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) :
    ∃ α : ℂ, ∀ t : ℝ, f t = Complex.exp (α * t) := by
  set Φ : ℝ → ℂ := fun t => ∫ x in (0 : ℝ)..t, f x with hΦ
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (f t) t := fun t =>
    (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := fun a b =>
    hf.intervalIntegrable a b

  have htrans : ∀ s t : ℝ, Φ (t + s) = Φ t + f t * Φ s := by
    intro s t
    have h1 : Φ (t + s) = (∫ x in (0 : ℝ)..t, f x) + ∫ x in t..t + s, f x :=
      (intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + s))).symm
    have h2 : (∫ x in t..t + s, f x) = ∫ x in (0 : ℝ)..s, f (x + t) := by
      rw [intervalIntegral.integral_comp_add_right f t, zero_add, add_comm s t]
    have h3 : (fun x : ℝ => f (x + t)) = fun x => f t * f x := by
      funext x
      rw [add_comm, hmul]
    rw [h1, h2, h3, intervalIntegral.integral_const_mul]
  by_cases hzero : ∀ s : ℝ, Φ s = 0
  · exfalso
    have hΦ0 : Φ = fun _ => (0 : ℂ) := funext hzero
    have hd := hΦderiv 0
    rw [hΦ0] at hd
    have : f 0 = 0 := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at this
    exact one_ne_zero this
  · push Not at hzero
    obtain ⟨s, hs⟩ := hzero
    set c : ℂ := (f s - 1) / Φ s with hc
    have hf_eq : ∀ t : ℝ, f t = 1 + c * Φ t := by
      intro t
      have h1 := htrans s t
      have h2 := htrans t s
      rw [add_comm t s] at h1
      have key : f t * Φ s = Φ s + (f s - 1) * Φ t := by
        linear_combination h1.symm.trans h2
      calc f t = f t * Φ s / Φ s := by field_simp
        _ = 1 + c * Φ t := by
          rw [key, hc]
          field_simp
    have hfderiv : ∀ t : ℝ, HasDerivAt f (c * f t) t := by
      intro t
      have h := ((hΦderiv t).const_mul c).const_add 1
      have hfun : (fun x : ℝ => 1 + c * Φ x) = f := (funext hf_eq).symm
      rw [hfun] at h
      exact h
    refine ⟨c, fun t => ?_⟩

    have hexp : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-(c * y)))
        (Complex.exp (-(c * x)) * (-(c * 1))) x := by
      intro x
      have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(c * z)))
          (Complex.exp (-(c * (x : ℂ))) * (-(c * 1))) (x : ℂ) :=
        ((hasDerivAt_id (x : ℂ)).const_mul c).neg.cexp
      exact h1.comp_ofReal
    have hg : ∀ x y : ℝ, Complex.exp (-(c * x)) * f x = Complex.exp (-(c * y)) * f y := by
      apply is_const_of_deriv_eq_zero
      · intro x
        exact ((hexp x).mul (hfderiv x)).differentiableAt
      · intro x
        change deriv ((fun y : ℝ => Complex.exp (-(c * y))) * f) x = 0
        rw [((hexp x).mul (hfderiv x)).deriv]
        ring
    have h1 := hg t 0
    rw [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, h0] at h1
    calc f t = Complex.exp (c * t) * (Complex.exp (-(c * t)) * f t) := by
          rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
      _ = Complex.exp (c * t) := by rw [h1, mul_one]

def rotMat (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

@[scoped simp] theorem rotMat_apply_00 (θ : ℝ) : rotMat θ 0 0 = Real.cos θ := rfl
@[scoped simp] theorem rotMat_apply_01 (θ : ℝ) : rotMat θ 0 1 = Real.sin θ := rfl
@[scoped simp] theorem rotMat_apply_10 (θ : ℝ) : rotMat θ 1 0 = -Real.sin θ := rfl
@[scoped simp] theorem rotMat_apply_11 (θ : ℝ) : rotMat θ 1 1 = Real.cos θ := rfl

theorem det_rotMat (θ : ℝ) : (rotMat θ).det = 1 := by
  rw [Matrix.det_fin_two, rotMat_apply_00, rotMat_apply_01, rotMat_apply_10, rotMat_apply_11]
  nlinarith [Real.cos_sq_add_sin_sq θ]

theorem continuous_rotMat_apply (i j : Fin 2) : Continuous fun θ : ℝ => rotMat θ i j := by
  fin_cases i <;> fin_cases j
  · simpa using Real.continuous_cos
  · simpa using Real.continuous_sin
  · simp
    exact Real.continuous_sin.neg
  · simpa using Real.continuous_cos

def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat θ) (by rw [det_rotMat]; exact one_ne_zero)

theorem rotGL_coe (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat θ := rfl

theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_rotMat θ, ?_, ?_⟩
  · rw [rotGL_coe, det_rotMat, norm_one]
  · intro x y
    rw [rotGL_coe, rotMat_apply_00, rotMat_apply_01, rotMat_apply_10, rotMat_apply_11,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      sq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

def rotSO (θ : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL θ, rotGL_mem θ⟩

theorem rotSO_coe_apply (θ : ℝ) (i j : Fin 2) :
    (((rotSO θ : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      rotMat θ i j := rfl

theorem rotSO_add (a b : ℝ) : rotSO (a + b) = rotSO a * rotSO b := by
  apply Subtype.ext
  apply Units.ext
  change rotMat (a + b) = rotMat a * rotMat b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem rotSO_zero : rotSO 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change rotMat 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rotSO_two_pi : rotSO (2 * Real.pi) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change rotMat (2 * Real.pi) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem archWeightOneℝ_rotSO (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := rfl

theorem archWeightOneℝ_rotSO_eq_exp (θ : ℝ) :
    ((archWeightOneℝ (rotSO θ) : ℂˣ) : ℂ) = Complex.exp (θ * Complex.I) := by
  rw [archWeightOneℝ_rotSO, Complex.exp_mul_I]
  apply Complex.ext <;>
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im]

theorem rotSO_surjective : Function.Surjective rotSO := by
  intro k
  obtain ⟨h10, h11, hab⟩ := entries_of_mem_rowIsometrySubgroup₀ k.2
  set a : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 with ha
  set b : ℝ := ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 with hb
  set z : ℂ := ⟨a, b⟩ with hz
  have hnorm : ‖z‖ = 1 := by
    have : Complex.normSq z = 1 := by
      rw [hz, Complex.normSq_mk]
      nlinarith [hab]
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact this
    have h3 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [h2, h3]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨Complex.arg z, ?_⟩
  have hc : Real.cos (Complex.arg z) = a := by rw [Complex.cos_arg hz0, hnorm, div_one]
  have hs : Real.sin (Complex.arg z) = b := by rw [Complex.sin_arg, hnorm, div_one]
  apply Subtype.ext
  apply Units.ext
  change rotMat (Complex.arg z) = ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.eta_fin_two ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), ← ha, ← hb, h10, h11,
    rotMat, hc, hs]

section Adelic

variable (F : Type) [Field F] [NumberField F]

def rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm he (rotSO θ)

omit [NumberField F] in
theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

variable {F}

omit [NumberField F] in
theorem rotAt_coe_apply {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) (i j : Fin 2) :
    (((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) i j = (ringEquivRealOfIsReal hw).symm (rotMat θ i j) :=
  rfl

omit [NumberField F] in

theorem rowIsometrySubgroup₀Map_rotAt {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) :
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (rotAt F hw he θ) = rotSO θ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (ringEquivRealOfIsReal hw) ((ringEquivRealOfIsReal hw).symm (rotMat θ i j)) = rotMat θ i j
  exact RingEquiv.apply_symm_apply _ _

omit [NumberField F] in
theorem rotAt_add {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (a b : ℝ) :
    rotAt F hw he (a + b) = rotAt F hw he a * rotAt F hw he b := by
  rw [rotAt, rotSO_add, map_mul]
  rfl

omit [NumberField F] in
theorem rotAt_zero {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) : rotAt F hw he 0 = 1 := by
  rw [rotAt, rotSO_zero, map_one]

def adelicRot {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) : AdelicGL2 (𝓞 F) F :=
  adelicArchGLInclAt F w
    ((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)

theorem adelicRot_add {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (a b : ℝ) :
    adelicRot hw he (a + b) = adelicRot hw he a * adelicRot hw he b := by
  rw [adelicRot, rotAt_add, Subgroup.coe_mul, map_mul]
  rfl

theorem adelicRot_zero {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) : adelicRot hw he 0 = 1 := by
  rw [adelicRot, rotAt_zero, OneMemClass.coe_one, map_one]

theorem adelicRot_neg {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (a : ℝ) :
    adelicRot hw he (-a) = (adelicRot hw he a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← adelicRot_add, neg_add_cancel, adelicRot_zero]

theorem adelicRot_coe_apply {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) (θ : ℝ) (i j : Fin 2) :
    ((adelicRot hw he θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((fun v : InfinitePlace F =>
          (Function.update (1 : ∀ v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w
            (((rotAt F hw he θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion) v) i j : InfiniteAdeleRing F),
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :=
  rfl

theorem continuous_adelicRot {w : InfinitePlace F} (hw : w.IsReal)
    (he : ∀ x : ℝ, ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖) :
    Continuous fun θ : ℝ => adelicRot hw he θ := by
  have hval : Continuous fun θ : ℝ =>
      ((adelicRot hw he θ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [adelicRot_coe_apply]
    refine Continuous.prodMk ?_ continuous_const
    apply continuous_pi
    intro v
    by_cases hv : v = w
    · subst hv
      simp only [Function.update_self, rotAt_coe_apply]
      exact (isometryEquivRealOfIsReal hw).symm.continuous.comp (continuous_rotMat_apply i j)
    · simp only [Function.update_of_ne hv]
      exact continuous_const
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have : (fun θ : ℝ => (((adelicRot hw he θ)⁻¹ : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
      fun θ : ℝ => ((adelicRot hw he (-θ) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    funext θ
    rw [adelicRot_neg]
  rw [this]
  exact hval.comp continuous_neg

end Adelic

theorem main (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφ0 : ∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0)
    (hχ : HasArchCharacterAt₀ F w
      (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))
      φ) :
    ∃ n : ℤ, χ = archWeightCharℝ n := by
  obtain ⟨g₀, hg₀⟩ := hφ0
  have he := norm_symm_ringEquivRealOfIsReal F hw

  set f : ℝ → ℂ := fun θ => ((χ (rotSO θ) : ℂˣ) : ℂ) with hf
  have hmulf : ∀ s t : ℝ, f (s + t) = f s * f t := by
    intro s t
    simp only [hf, rotSO_add, map_mul, Units.val_mul]
  have hf0 : f 0 = 1 := by
    simp only [hf, rotSO_zero, map_one, Units.val_one]

  have hfφ : ∀ θ : ℝ, f θ = φ (g₀ * adelicRot hw he θ) / φ g₀ := by
    intro θ
    have h := hχ (rotAt F hw he θ) g₀
    rw [MonoidHom.comp_apply, rowIsometrySubgroup₀Map_rotAt] at h
    change φ (g₀ * adelicRot hw he θ) = f θ * φ g₀ at h
    rw [h, mul_div_assoc, div_self hg₀, mul_one]
  have hfcont : Continuous f := by
    have hfun : f = fun θ => φ (g₀ * adelicRot hw he θ) / φ g₀ := funext hfφ
    rw [hfun]
    exact (hφ.comp (continuous_const.mul (continuous_adelicRot hw he))).div_const _
  obtain ⟨α, hα⟩ := exists_eq_exp_of_continuous_mul f hfcont hf0 hmulf

  have h2π : f (2 * Real.pi) = 1 := by
    simp only [hf, rotSO_two_pi, map_one, Units.val_one]
  rw [hα] at h2π
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2π
  have hαn : α = n * Complex.I := by
    have h2 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      positivity
    apply mul_right_cancel₀ h2
    rw [hn]
    push_cast
    ring
  refine ⟨n, MonoidHom.ext fun k => ?_⟩
  obtain ⟨θ, rfl⟩ := rotSO_surjective k
  apply Units.ext
  change f θ = ((archWeightCharℝ n (rotSO θ) : ℂˣ) : ℂ)
  rw [hα θ, hαn, archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val, archWeightOneℝ_rotSO_eq_exp, ← Complex.exp_int_mul]
  congr 1
  ring

end CircleCharacterClassification
p2m_reactivate "P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous.CircleCharacterClassification"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous.CircleCharacterClassification"

theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (χ : rowIsometrySubgroup₀ ℝ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφ0 : ∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0)
    (hχ : HasArchCharacterAt₀ F w
      (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)))
      φ) :
    ∃ n : ℤ, χ = archWeightCharℝ n :=
  CircleCharacterClassification.main F w hw χ φ hφ hφ0 hχ

end S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous
end P2MW
export P2MW.S_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous (solution)
