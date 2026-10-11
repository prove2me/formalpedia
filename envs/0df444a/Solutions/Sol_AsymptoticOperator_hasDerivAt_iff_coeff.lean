-- Prove2me | solution 1 for AsymptoticOperator.hasDerivAt_iff_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T00:06:08.088888+00:00
-- url     : https://prove2.me/submissions/2ef4ae0f-8452-48bd-856d-dc94cd69bba8

import Definitions.Def_AsymptoticOperator_Setting
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator

/-- `complexify` as a continuous `ℝ`-linear map. -/
noncomputable def ao12cx (n : ℕ) : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)

lemma ao12cx_apply {n : ℕ} (v : Vec n) : ao12cx n v = complexify v := rfl

lemma ao12_cont_coe : Continuous (fun y : ℝ => (y : UnitAddCircle)) :=
  continuous_quotient_mk'

/-- Fourier coefficients of a continuous loop as an integral over `[0, 1]`. -/
lemma ao12_coeff_eq {n : ℕ} (g : C(UnitAddCircle, Vec n)) (k : ℤ) :
    coeff g k = ∫ x in (0 : ℝ)..1, fourier (-k) (x : UnitAddCircle) • complexify (g x) := by
  rw [coeff, fourierCoeff_eq_intervalIntegral _ k 0]
  simp

lemma ao12_coeff_eq_of {n : ℕ} (g : C(UnitAddCircle, Vec n)) (k : ℤ) :
    coeff g k = ∫ x in (0 : ℝ)..1, fourier (-k) (x : UnitAddCircle) • ao12cx n (g x) :=
  ao12_coeff_eq g k

/-- Forward direction: a classical derivative has the Fourier coefficients `2πik φ̂ₖ`. -/
lemma ao12_fwd {n : ℕ} (φ h : C(UnitAddCircle, Vec n))
    (hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => φ (y : UnitAddCircle)) (h (x : UnitAddCircle)) x)
    (k : ℤ) : coeff h k = ((2 * Real.pi * k : ℝ) * Complex.I) • coeff φ k := by
  set u : ℝ → ℂ := fun x => fourier (-k) (x : UnitAddCircle)
  set d : ℂ := 2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) / (1 : ℝ)
  have hu : ∀ x, HasDerivAt u (d * u x) x := fun x => hasDerivAt_fourier (T := 1) (-k) x
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ao12cx n (φ (y : UnitAddCircle)))
      (ao12cx n (h (x : UnitAddCircle))) x :=
    fun x => (ao12cx n).hasFDerivAt.comp_hasDerivAt x (hd x)
  have hcu : Continuous u := (fourier (-k)).continuous.comp ao12_cont_coe
  have hch : Continuous fun x : ℝ => ao12cx n (h (x : UnitAddCircle)) :=
    (ao12cx n).continuous.comp (h.continuous.comp ao12_cont_coe)
  have hcφ : Continuous fun x : ℝ => ao12cx n (φ (x : UnitAddCircle)) :=
    (ao12cx n).continuous.comp (φ.continuous.comp ao12_cont_coe)
  have ibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul (a := (0 : ℝ)) (b := 1)
    (fun x _ => hu x) (fun x _ => hv x)
    ((continuous_const.mul hcu).intervalIntegrable _ _) (hch.intervalIntegrable _ _)
  have h10 : ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]
  have hb : u 1 • ao12cx n (φ ((1 : ℝ) : UnitAddCircle)) =
      u 0 • ao12cx n (φ ((0 : ℝ) : UnitAddCircle)) := by
    simp only [u, h10]
  rw [hb, sub_self, zero_sub] at ibp
  simp_rw [mul_smul] at ibp
  rw [intervalIntegral.integral_smul] at ibp
  rw [ao12_coeff_eq_of, ao12_coeff_eq_of, ibp, ← neg_smul]
  congr 1
  simp only [d]
  push_cast
  ring

lemma ao12_cx_inj {n : ℕ} {v : Vec n} (h : ao12cx n v = 0) : v = 0 := by
  ext i
  have := congrFun h i
  simpa [ao12cx_apply, complexify] using this

/-- Coordinates of the coefficients of a continuous loop. -/
lemma ao12_coeff_apply {n : ℕ} (g : C(UnitAddCircle, Vec n)) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff g k i = fourierCoeff (fun t => ((g t i : ℝ) : ℂ)) k := by
  have hint : Integrable (fun t => complexify (g t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    ((ao12cx n).continuous.comp g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact eval_integral (integrable_pi_iff.1 (hint.fourier_smul (-k))) i

/-- Continuous loops are determined by their Fourier coefficients. -/
lemma ao12_eq_of_coeff {n : ℕ} (φ ψ : C(UnitAddCircle, Vec n))
    (h : ∀ k, coeff φ k = coeff ψ k) : φ = ψ := by
  ext t i
  let g : C(UnitAddCircle, ℂ) :=
    ⟨fun t => ((φ t i - ψ t i : ℝ) : ℂ), by fun_prop⟩
  have hg : ∀ k, fourierCoeff g k = 0 := by
    intro k
    have hφ := ao12_coeff_apply φ k i
    have hψ := ao12_coeff_apply ψ k i
    have hiφ : Integrable (fun t => ((φ t i : ℝ) : ℂ))
        (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
      (by fun_prop : Continuous fun t => ((φ t i : ℝ) : ℂ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hiψ : Integrable (fun t => ((ψ t i : ℝ) : ℂ))
        (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
      (by fun_prop : Continuous fun t => ((ψ t i : ℝ) : ℂ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have e : (g : UnitAddCircle → ℂ) =
        (fun t => ((φ t i : ℝ) : ℂ)) - fun t => ((ψ t i : ℝ) : ℂ) := by
      funext t; simp [g]
    have hs : fourierCoeff (fun t => ((φ t i : ℝ) : ℂ) - ((ψ t i : ℝ) : ℂ)) k =
        fourierCoeff (fun t => ((φ t i : ℝ) : ℂ)) k - fourierCoeff (fun t => ((ψ t i : ℝ) : ℂ)) k := by
      simp only [fourierCoeff]
      rw [← integral_sub (hiφ.fourier_smul (-k)) (hiψ.fourier_smul (-k))]
      congr 1
      funext t
      rw [smul_sub]
    rw [e]
    change fourierCoeff (fun t => ((φ t i : ℝ) : ℂ) - ((ψ t i : ℝ) : ℂ)) k = 0
    rw [hs, ← hφ, ← hψ, h k, sub_self]
  have h0 : ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ g = 0 := by
    apply fourierBasis.repr.injective
    rw [map_zero]
    ext k
    rw [fourierBasis_repr, fourierCoeff_toLp, hg]
    rfl
  have hg0 : g = 0 := by
    apply ContinuousMap.toLp_injective (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ)
    rw [h0, map_zero]
  have := congrArg (fun F : C(UnitAddCircle, ℂ) => F t) hg0
  simp only [g, ContinuousMap.coe_mk, ContinuousMap.zero_apply, Complex.ofReal_eq_zero,
    sub_eq_zero] at this
  exact this

theorem solution {n : ℕ} (φ h : C(UnitAddCircle, Vec n)) :
    (∀ x : ℝ, HasDerivAt (fun y : ℝ => φ (y : UnitAddCircle)) (h (x : UnitAddCircle)) x) ↔
      ∀ k : ℤ, coeff h k = ((2 * Real.pi * k : ℝ) * Complex.I) • coeff φ k := by
  refine ⟨fun hd k => ao12_fwd φ h hd k, fun hc => ?_⟩
  have hch : Continuous fun x : ℝ => h (x : UnitAddCircle) := h.continuous.comp ao12_cont_coe
  have hcφ : Continuous fun x : ℝ => φ (x : UnitAddCircle) := φ.continuous.comp ao12_cont_coe
  set G : ℝ → Vec n := fun x => ∫ s in (0 : ℝ)..x, h (s : UnitAddCircle)
  have hG : ∀ x : ℝ, HasDerivAt G (h (x : UnitAddCircle)) x := fun x =>
    (hch.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hcG : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  -- the mean of `h` vanishes
  have hper_h : Function.Periodic (fun s : ℝ => h (s : UnitAddCircle)) 1 := by
    intro s; simp only [AddCircle.coe_add_period]
  have hmean : ∫ s in (0 : ℝ)..1, h (s : UnitAddCircle) = 0 := by
    apply ao12_cx_inj
    rw [← (ao12cx n).intervalIntegral_comp_comm (hch.intervalIntegrable _ _)]
    have := hc 0
    rw [ao12_coeff_eq_of] at this
    simpa using this
  have hGper : Function.Periodic G 1 := by
    intro x
    simp only [G]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
      (hch.intervalIntegrable _ _) (hch.intervalIntegrable _ _),
      hper_h.intervalIntegral_add_eq x 0, zero_add, hmean, add_zero]
  set c : Vec n := ∫ x in (0 : ℝ)..1, (φ (x : UnitAddCircle) - G x) with hcdef
  set H : ℝ → Vec n := fun x => c + G x
  have hHper : Function.Periodic H 1 := fun x => by simp only [H, hGper x]
  have hcH : Continuous H := continuous_const.add hcG
  let Hc : C(UnitAddCircle, Vec n) :=
    ⟨hHper.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hcH⟩
  have hHc : ∀ x : ℝ, Hc (x : UnitAddCircle) = H x := fun x => rfl
  have hdH : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Hc (y : UnitAddCircle)) (h (x : UnitAddCircle)) x :=
    fun x => by simpa only [hHc, H] using (hG x).const_add c
  have hcoef : ∀ k, coeff φ k = coeff Hc k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [ao12_coeff_eq_of, ao12_coeff_eq_of]
      simp only [neg_zero, fourier_zero, one_smul, hHc, H]
      have e2 := (ao12cx n).intervalIntegral_comp_comm
        ((continuous_const.add hcG : Continuous fun x => c + G x).intervalIntegrable
          (μ := volume) 0 1)
      rw [(ao12cx n).intervalIntegral_comp_comm (hcφ.intervalIntegrable _ _)]
      refine Eq.trans ?_ e2.symm
      congr 1
      show ∫ x in (0 : ℝ)..1, φ (x : UnitAddCircle) = ∫ x in (0 : ℝ)..1, (c + G x)
      rw [intervalIntegral.integral_add intervalIntegrable_const (hcG.intervalIntegrable _ _),
        intervalIntegral.integral_const, sub_zero, one_smul, hcdef,
        intervalIntegral.integral_sub (hcφ.intervalIntegrable _ _) (hcG.intervalIntegrable _ _)]
      abel
    · have h1 := hc k
      have h2 := ao12_fwd Hc h hdH k
      rw [h1] at h2
      have hne : ((2 * Real.pi * k : ℝ) * Complex.I) ≠ 0 := by
        refine mul_ne_zero ?_ Complex.I_ne_zero
        rw [Complex.ofReal_ne_zero]
        exact mul_ne_zero (by positivity) (by exact_mod_cast hk)
      exact smul_right_injective _ hne h2
  have hφH := ao12_eq_of_coeff φ Hc hcoef
  intro x
  rw [hφH]
  exact hdH x
