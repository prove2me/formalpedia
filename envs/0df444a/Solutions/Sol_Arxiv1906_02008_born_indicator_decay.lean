-- Prove2me | solution 1 for Arxiv1906_02008.born_indicator_decay
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T09:36:20.54549+00:00
-- url     : https://prove2.me/submissions/80afb24e-f74f-4b60-9108-8d664d77fa96

import Mathlib
import Definitions.Def_Arxiv1906_02008_Basic

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section
namespace BI
open Arxiv1906_02008

def P (w k : ℝ) : ℂ := -Complex.I / w * k ^ 2 + 2 / (w : ℂ) ^ 2 * k + 2 * Complex.I / (w : ℂ) ^ 3

lemma G_eq (w km kp : ℝ) (hw : w ≠ 0) :
    ∫ k in km..kp, (k : ℂ) ^ 2 * Complex.exp (Complex.I * k * w) =
      Complex.exp (Complex.I * kp * w) * P w kp - Complex.exp (Complex.I * km * w) * P w km := by
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun k : ℝ => Complex.exp (Complex.I * k * w) * P w k)
    (fun k _ => ?_) (by apply Continuous.intervalIntegrable; fun_prop)
  have h1 : HasDerivAt (fun k : ℝ => Complex.exp (Complex.I * k * w)) (Complex.exp (Complex.I * k * w) * (Complex.I * w)) k := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := k)).const_mul Complex.I).mul_const (w : ℂ)
    simpa using (this.cexp)
  have h2 : HasDerivAt (fun k : ℝ => P w k) (-Complex.I / w * (2 * k) + 2 / (w : ℂ) ^ 2) k := by
    unfold P
    have hk := Complex.ofRealCLM.hasDerivAt (x := k)
    simp only [Complex.ofRealCLM_apply] at hk
    have := ((hk.pow 2).const_mul (-Complex.I / w)).add ((hk.const_mul (2 / (w : ℂ) ^ 2))) |>.add_const (2 * Complex.I / (w : ℂ) ^ 3)
    exact this.congr_deriv (by norm_num <;> ring)
  refine (h1.mul h2).congr_deriv ?_
  unfold P
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

lemma P_bound (w k kp : ℝ) (hw : 1 ≤ |w|) (hk0 : 0 ≤ k) (hk : k ≤ kp) :
    ‖P w k‖ ≤ (kp ^ 2 + 2 * kp + 2) / |w| := by
  have hw0 : 0 < |w| := by linarith
  unfold P
  have e1 : ‖-Complex.I / (w : ℂ) * (k : ℂ) ^ 2‖ = k ^ 2 / |w| := by
    simp [Complex.norm_real]; ring
  have e2 : ‖2 / (w : ℂ) ^ 2 * (k : ℂ)‖ = 2 * k / |w| ^ 2 := by
    simp [norm_mul, norm_div, Complex.norm_real, abs_of_nonneg hk0]; ring
  have e3 : ‖2 * Complex.I / (w : ℂ) ^ 3‖ = 2 / |w| ^ 3 := by
    simp [norm_mul, norm_div, Complex.norm_real]
  calc _ ≤ ‖-Complex.I / (w : ℂ) * (k : ℂ) ^ 2‖ + ‖2 / (w : ℂ) ^ 2 * (k : ℂ)‖ + ‖2 * Complex.I / (w : ℂ) ^ 3‖ :=
        norm_add₃_le
    _ = k ^ 2 / |w| + 2 * k / |w| ^ 2 + 2 / |w| ^ 3 := by rw [e1, e2, e3]
    _ ≤ kp ^ 2 / |w| + 2 * kp / |w| + 2 / |w| := by
        have a1 : k ^ 2 / |w| ≤ kp ^ 2 / |w| := by gcongr
        have a2 : 2 * k / |w| ^ 2 ≤ 2 * kp / |w| := by
          rw [div_le_div_iff₀ (by positivity) hw0]
          have : |w| ≤ |w| ^ 2 := by nlinarith
          nlinarith [mul_le_mul hk this hw0.le (by linarith)]
        have a3 : 2 / |w| ^ 3 ≤ 2 / |w| := by
          apply div_le_div_of_nonneg_left (by norm_num) hw0
          nlinarith [mul_le_mul hw hw zero_le_one hw0.le]
        linarith
    _ = _ := by ring

lemma G_bound (w km kp : ℝ) (hkm : 0 < km) (hk : km < kp) (hw : 1 ≤ |w|) :
    ‖∫ k in km..kp, (k : ℂ) ^ 2 * Complex.exp (Complex.I * k * w)‖ ≤ 2 * (kp ^ 2 + 2 * kp + 2) / |w| := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw; linarith
  rw [G_eq w km kp hw0]
  have n1 : ∀ k : ℝ, ‖Complex.exp (Complex.I * k * w)‖ = 1 := by
    intro k; rw [show Complex.I * k * w = ((k * w : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  calc _ ≤ ‖Complex.exp (Complex.I * kp * w) * P w kp‖ + ‖Complex.exp (Complex.I * km * w) * P w km‖ := norm_sub_le _ _
    _ = ‖P w kp‖ + ‖P w km‖ := by rw [norm_mul, norm_mul, n1, n1, one_mul, one_mul]
    _ ≤ (kp ^ 2 + 2 * kp + 2) / |w| + (kp ^ 2 + 2 * kp + 2) / |w| := by
        gcongr
        · exact P_bound w kp kp hw (by linarith) le_rfl
        · exact P_bound w km kp hw hkm.le hk.le
    _ = _ := by ring

lemma strip_sep {n : ℕ} (D : Set (Rn n)) (hb : Bornology.IsBounded D) (φ : Rn n) (hφ : ‖φ‖ = 1)
    (z y : Rn n) (hy : y ∈ closure D) :
    Metric.infDist z (strip D φ) ≤ |⟪y, φ⟫ - ⟪z, φ⟫| := by
  obtain ⟨Cb, hCb⟩ := hb.exists_norm_le
  have hbdd1 : BddBelow ((fun x => ⟪x, φ⟫) '' D) := ⟨-Cb, by
    rintro _ ⟨x, hx, rfl⟩
    have := abs_real_inner_le_norm x φ; rw [hφ, mul_one] at this
    linarith [abs_le.mp (this.trans (hCb x hx)) |>.1]⟩
  have hbdd2 : BddAbove ((fun x => ⟪x, φ⟫) '' D) := ⟨Cb, by
    rintro _ ⟨x, hx, rfl⟩
    have := abs_real_inner_le_norm x φ; rw [hφ, mul_one] at this
    linarith [abs_le.mp (this.trans (hCb x hx)) |>.2]⟩
  have hcl : IsClosed (strip D φ) := by
    have hci : Continuous (fun x : Rn n => ⟪x, φ⟫) := continuous_id.inner continuous_const
    unfold strip
    exact (isClosed_le continuous_const hci).inter (isClosed_le hci continuous_const)
  have hsub : D ⊆ strip D φ := fun x hx =>
    ⟨csInf_le hbdd1 ⟨x, hx, rfl⟩, le_csSup hbdd2 ⟨x, hx, rfl⟩⟩
  have hys : y ∈ strip D φ := hcl.closure_subset_iff.mpr hsub hy
  set m := sInf ((fun x => ⟪x, φ⟫) '' D)
  set M := sSup ((fun x => ⟪x, φ⟫) '' D)
  set t := ⟪z, φ⟫
  set s := ⟪y, φ⟫
  have hms : m ≤ s := hys.1
  have hsM : s ≤ M := hys.2
  set c := max m (min t M)
  have hc1 : m ≤ c := le_max_left _ _
  have hc2 : c ≤ M := max_le (by linarith) (min_le_right _ _)
  have hz' : z + (c - t) • φ ∈ strip D φ := by
    have : ⟪z + (c - t) • φ, φ⟫ = c := by
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hφ]; ring
    exact ⟨by rw [this]; exact hc1, by rw [this]; exact hc2⟩
  calc Metric.infDist z (strip D φ) ≤ dist z (z + (c - t) • φ) := Metric.infDist_le_dist_of_mem hz'
    _ = |c - t| := by rw [dist_eq_norm]; simp [norm_smul, hφ]
    _ ≤ |s - t| := by
        by_cases h1 : t ≤ m
        · rw [show c = m by simp only [c]; rw [min_eq_left (by linarith), max_eq_left h1]]
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
        · by_cases h2 : M ≤ t
          · rw [show c = M by simp only [c]; rw [min_eq_right h2, max_eq_right (by linarith)]]
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          · rw [show c = t by simp only [c]; rw [min_eq_left (by linarith), max_eq_right (by linarith)]]
            simp

end BI

open Arxiv1906_02008 BI in
theorem solution {n : ℕ} (hn : n = 2 ∨ n = 3)
    (km kp : ℝ) (hkm : 0 < km) (hk : km < kp)
    (xh θ : Rn n) (hxh : ‖xh‖ = 1) (hθ : ‖θ‖ = 1) (hne : xh ≠ θ)
    (q : Rn n → ℝ) (D : Set (Rn n)) (hq : IsMedium q D) :
    ∃ C R : ℝ, ∀ z : Rn n, R ≤ Metric.infDist z (strip D (phiDir xh θ)) →
      indicatorI1 (fun a b k => bornFarField q a b k) km kp xh θ z ≤
        C / Metric.infDist z (strip D (phiDir xh θ)) := by
  obtain ⟨⟨-, hDb, -, -, -⟩, -, hqi, hsupp⟩ := hq
  set v := θ - xh with hv
  have hv0 : v ≠ 0 := sub_ne_zero.mpr hne.symm
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hφ : ‖phiDir xh θ‖ = 1 := by
    unfold phiDir; rw [← hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
  set C0 := 2 * (kp ^ 2 + 2 * kp + 2)
  set Iq := ∫ y, |q y - 1|
  refine ⟨C0 / ‖v‖ * Iq, ‖v‖⁻¹, fun z hz => ?_⟩
  set d := Metric.infDist z (strip D (phiDir xh θ))
  have hd : 0 < d := lt_of_lt_of_le (inv_pos.mpr hvn) hz
  set f : Rn n → ℂ := fun y => ((q y - 1 : ℝ) : ℂ)
  set w : Rn n → ℝ := fun y => ⟪v, y⟫ - ⟪z, v⟫
  set F : ℝ → Rn n → ℂ := fun k y => f y * ((k : ℂ) ^ 2 * Complex.exp (Complex.I * k * (w y)))
  have hstep : (∫ k in km..kp, bornFarField q xh θ k * Complex.exp (-(Complex.I * (k : ℂ) * (⟪z, θ - xh⟫ : ℂ)))) =
      ∫ k in km..kp, ∫ y, F k y := by
    refine intervalIntegral.integral_congr (fun k _ => ?_)
    unfold bornFarField
    rw [← hv, mul_assoc, ← integral_mul_const, ← integral_const_mul]
    congr 1; ext y
    simp only [F, f, w]
    rw [show Complex.I * (k : ℂ) * ((⟪v, y⟫ - ⟪z, v⟫ : ℝ) : ℂ) =
      Complex.I * (k : ℂ) * (⟪v, y⟫ : ℂ) + (-(Complex.I * (k : ℂ) * (⟪z, v⟫ : ℂ))) by push_cast; ring,
      Complex.exp_add]
    ring
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Ioc km kp)).prod volume) := by
    have hg : Integrable (fun p : ℝ × Rn n => p.1 ^ 2 * |q p.2 - 1|) ((volume.restrict (Ioc km kp)).prod volume) :=
      Integrable.mul_prod (f := fun k : ℝ => k ^ 2) (g := fun y => |q y - 1|)
        ((continuous_pow 2).integrableOn_Ioc) hqi.abs
    refine hg.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have h1 : AEStronglyMeasurable (fun p : ℝ × Rn n => f p.2) ((volume.restrict (Ioc km kp)).prod volume) :=
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hqi.1).comp_snd
      have h2 : Continuous (fun p : ℝ × Rn n => ((p.1 : ℂ) ^ 2 * Complex.exp (Complex.I * p.1 * (w p.2)))) := by
        simp only [w]; fun_prop
      exact h1.mul h2.aestronglyMeasurable
    · simp only [Function.uncurry, F, f, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      rw [show Complex.I * (p.1 : ℂ) * ((w p.2 : ℝ) : ℂ) = ((p.1 * w p.2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
      rw [sq_abs]; ring_nf; rfl
  have hswap : (∫ k in km..kp, ∫ y, F k y) = ∫ y, ∫ k in km..kp, F k y := by
    simp only [intervalIntegral.integral_of_le hk.le]
    exact integral_integral_swap hint
  have hF : ∀ y, (∫ k in km..kp, F k y) = f y * ∫ k in km..kp, (k : ℂ) ^ 2 * Complex.exp (Complex.I * k * (w y)) :=
    fun y => intervalIntegral.integral_const_mul _ _
  unfold indicatorI1
  rw [hstep, hswap]
  simp_rw [hF]
  have hbound : ∀ y, ‖f y * ∫ k in km..kp, (k : ℂ) ^ 2 * Complex.exp (Complex.I * k * (w y))‖ ≤
      |q y - 1| * (C0 / (‖v‖ * d)) := by
    intro y
    by_cases hy : y ∈ closure D
    · have hsep := strip_sep D hDb _ hφ z y hy
      have hwy : w y = ‖v‖ * (⟪y, phiDir xh θ⟫ - ⟪z, phiDir xh θ⟫) := by
        simp only [w]; unfold phiDir
        rw [← hv, real_inner_smul_right, real_inner_smul_right, real_inner_comm y v]
        field_simp
      have hw1 : ‖v‖ * d ≤ |w y| := by
        rw [hwy, abs_mul, abs_norm]; exact mul_le_mul_of_nonneg_left hsep hvn.le
      have hge : 1 ≤ ‖v‖ * d := by
        have := mul_le_mul_of_nonneg_left hz hvn.le; rwa [mul_inv_cancel₀ hvn.ne'] at this
      rw [norm_mul]; simp only [f, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (G_bound _ km kp hkm hk (hge.trans hw1)).trans
        (div_le_div_of_nonneg_left (by nlinarith [sq_nonneg (kp + 1)]) (by positivity) hw1)
    · have : q y - 1 = 0 := by
        have h' : y ∉ tsupport (fun y => q y - 1) := by rw [hsupp]; exact hy
        exact image_eq_zero_of_notMem_tsupport (f := fun y => q y - 1) h'
      simp only [f, this, Complex.ofReal_zero, zero_mul, norm_zero, abs_zero]; rfl
  calc _ ≤ ∫ y, |q y - 1| * (C0 / (‖v‖ * d)) :=
        norm_integral_le_of_norm_le (hqi.abs.mul_const _) (Filter.Eventually.of_forall hbound)
    _ = C0 / ‖v‖ * Iq / d := by
      show _ = C0 / ‖v‖ * (∫ y, |q y - 1|) / d
      rw [integral_mul_const]; field_simp
