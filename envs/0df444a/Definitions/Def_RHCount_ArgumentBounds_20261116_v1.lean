-- Prove2me | Definitions.Def_RHCount_ArgumentBounds_20261116_v1
-- name    : RHCount_ArgumentBounds_20261116_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-16T18:32:32.357775+00:00
-- url     : https://prove2.me/theorems/c4255c51-b6d1-4eb4-b6cc-6e372ebf907e
-- title:
--   Integrated zeta argument bounds and phase estimates
-- statement:
--   A support module for unconditional integration bounds on the continuous argument of zeta, phase differentiation and monotonicity of the zero counter. It imports the preceding analytic modules and includes the helper proofs required by the unit-window and eventual-density theorems. It does not assert RH or the complete Branches.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Analytic sources smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe. Partition of the completely checked actual_count_submission.lean into closed source sections. Complete sources, Apache-2.0 licenses and exact source manifest accompany the reproducibility archive. No novelty claim.

import Definitions.Def_RHCount_ZeroCounting_20261116_v1
/- Reduced submission: unused declarations and documentation removed. Retained proofs are complete. Full original sources and licenses accompany the archive. -/
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Maksym Radziwill
-/
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Matteo Cipollina
-/
/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CountPort69
section
open Complex Filter Topology Function Set
open Complex.Stirling
open scoped Real
instance : Countable RiemannXiZerosIndex := by
  have : Countable ↥(MeromorphicOn.divisor riemannXi ⊤).support :=
    ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
      (MeromorphicOn.divisor riemannXi ⊤).discreteSupport).to_subtype
  infer_instance
theorem AnalyticAt.conj_conj {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g (starRingEnd ℂ u)) :
    AnalyticAt ℂ (fun w ↦ starRingEnd ℂ (g (starRingEnd ℂ w))) u := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [Complex.continuous_conj.continuousAt.eventually
    (hg.eventually_analyticAt.mono fun y hy ↦ hy.differentiableAt)] with w hw
  simpa [Function.comp_def] using hw.conj_conj
private theorem analyticAt_riemannXi (w : ℂ) : AnalyticAt ℂ riemannXi w :=
  differentiable_riemannXi.analyticAt w
private theorem analyticOrderAt_riemannXi_ne_top (w : ℂ) :
    analyticOrderAt riemannXi w ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero w analyticAt_riemannXi]
  intro h
  simpa [riemannXi_zero] using congrFun h 0
theorem analyticOrderAt_riemannXi_conj (z : ℂ) :
    analyticOrderAt riemannXi (starRingEnd ℂ z) = analyticOrderAt riemannXi z := by
  set N := analyticOrderNatAt riemannXi z
  obtain ⟨g, hg, hg0, hfac⟩ :=
    (analyticAt_riemannXi z).analyticOrderAt_ne_top.mp (analyticOrderAt_riemannXi_ne_top z)
  have hgconj : AnalyticAt ℂ (fun u ↦ starRingEnd ℂ (g (starRingEnd ℂ u))) (starRingEnd ℂ z) :=
    AnalyticAt.conj_conj (u := starRingEnd ℂ z) (by rw [Complex.conj_conj]; exact hg)
  have hval : (fun u ↦ starRingEnd ℂ (g (starRingEnd ℂ u))) (starRingEnd ℂ z) ≠ 0 := by
    simp only [Complex.conj_conj]
    exact fun h ↦ hg0 (by simpa using congrArg (starRingEnd ℂ) h)
  have hfac2 : riemannXi =ᶠ[𝓝 (starRingEnd ℂ z)]
      fun u ↦ (u - starRingEnd ℂ z) ^ N • (starRingEnd ℂ (g (starRingEnd ℂ u))) := by
    have hc : ContinuousAt (starRingEnd ℂ) (starRingEnd ℂ z) :=
      Complex.continuous_conj.continuousAt
    have hpull : ∀ᶠ u in 𝓝 (starRingEnd ℂ z),
        riemannXi (starRingEnd ℂ u) = (starRingEnd ℂ u - z) ^ N • g (starRingEnd ℂ u) := by
      have hbase : ∀ᶠ y in 𝓝 (starRingEnd ℂ (starRingEnd ℂ z)),
          riemannXi y = (y - z) ^ N • g y := by rw [Complex.conj_conj]; exact hfac
      exact hc.eventually hbase
    filter_upwards [hpull] with u hu
    have h2 := congrArg (starRingEnd ℂ) hu
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, riemannXi_conj, Complex.conj_conj] at h2
    simpa only [smul_eq_mul] using h2
  have hcz : analyticOrderNatAt riemannXi (starRingEnd ℂ z) = N := by
    rw [(analyticAt_riemannXi (starRingEnd ℂ z)).analyticOrderNatAt_eq_iff
      (analyticOrderAt_riemannXi_ne_top _)]
    exact ⟨_, hgconj, hval, hfac2⟩
  rw [← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top (starRingEnd ℂ z)),
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top z), hcz]
theorem analyticOrderAt_riemannXi_one_sub (z : ℂ) :
    analyticOrderAt riemannXi (1 - z) = analyticOrderAt riemannXi z := by
  have hcomp : analyticOrderAt (riemannXi ∘ fun w ↦ 1 - w) z
      = analyticOrderAt riemannXi ((fun w ↦ 1 - w) z) := by
    refine analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_const.sub analyticAt_id) ?_
    have hd : deriv (fun w : ℂ ↦ 1 - w) z = -1 := ((hasDerivAt_id z).const_sub (1 : ℂ)).deriv
    rw [hd]; exact neg_ne_zero.mpr one_ne_zero
  have hfun : (riemannXi ∘ fun w ↦ 1 - w) = riemannXi := by
    funext w; simp only [comp_apply, riemannXi_one_sub]
  rw [hfun] at hcomp
  exact hcomp.symm
theorem analyticOrderAt_riemannXi_one_sub_conj (z : ℂ) :
    analyticOrderAt riemannXi (1 - starRingEnd ℂ z) = analyticOrderAt riemannXi z := by
  rw [analyticOrderAt_riemannXi_one_sub, analyticOrderAt_riemannXi_conj]
theorem divisor_riemannXi_one_sub_conj (z : ℂ) :
    MeromorphicOn.divisor riemannXi ⊤ (1 - starRingEnd ℂ z)
      = MeromorphicOn.divisor riemannXi ⊤ z := by
  have hf : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  rw [divisor_eq_analyticOrderNatAt hf, divisor_eq_analyticOrderNatAt hf]
  simp only [analyticOrderNatAt, analyticOrderAt_riemannXi_one_sub_conj]
theorem exists_equiv_riemannXiZeros_one_sub_conj :
    ∃ e : RiemannXiZerosIndex ≃ RiemannXiZerosIndex,
      ∀ i, riemannXiZeros (e i) = 1 - starRingEnd ℂ (riemannXiZeros i) := by
  let F : (MeromorphicOn.divisor riemannXi ⊤).support →
      (MeromorphicOn.divisor riemannXi ⊤).support :=
    fun a ↦ ⟨1 - starRingEnd ℂ (a : ℂ), by
      rw [mem_support, divisor_riemannXi_one_sub_conj]
      exact mem_support.mp a.2⟩
  have hFinv : Involutive F := by
    intro a
    apply Subtype.ext
    change 1 - starRingEnd ℂ (1 - starRingEnd ℂ (a : ℂ)) = (a : ℂ)
    simp only [map_sub, map_one, Complex.conj_conj]; ring
  let eSupp := hFinv.toPerm F
  have hfib : ∀ a : (MeromorphicOn.divisor riemannXi ⊤).support,
      (MeromorphicOn.divisor riemannXi ⊤ (a : ℂ)).toNat
        = (MeromorphicOn.divisor riemannXi ⊤ (eSupp a : ℂ)).toNat := by
    intro a
    change (MeromorphicOn.divisor riemannXi ⊤ (a : ℂ)).toNat
      = (MeromorphicOn.divisor riemannXi ⊤ (1 - starRingEnd ℂ (a : ℂ))).toNat
    rw [divisor_riemannXi_one_sub_conj]
  refine ⟨Equiv.sigmaCongr eSupp (fun a ↦ finCongr (hfib a)), ?_⟩
  rintro ⟨a, k⟩
  rfl
theorem tsum_riemannXiZeros_one_sub_conj {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (g : ℂ → M) :
    ∑' i, g (riemannXiZeros i) = ∑' i, g (1 - starRingEnd ℂ (riemannXiZeros i)) := by
  obtain ⟨e, hval⟩ := exists_equiv_riemannXiZeros_one_sub_conj
  calc ∑' i, g (riemannXiZeros i)
      = ∑' i, g (riemannXiZeros (e i)) := (e.tsum_eq (fun i ↦ g (riemannXiZeros i))).symm
    _ = ∑' i, g (1 - starRingEnd ℂ (riemannXiZeros i)) := by simp_rw [hval]
theorem summable_riemannXiZeros_one_sub_conj_iff {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (g : ℂ → M) :
    Summable (fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)))
      ↔ Summable (fun i ↦ g (riemannXiZeros i)) := by
  obtain ⟨e, hval⟩ := exists_equiv_riemannXiZeros_one_sub_conj
  have hcomp : (fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)))
      = (fun j ↦ g (riemannXiZeros j)) ∘ e := by
    ext i; simp only [Function.comp_apply, hval i]
  rw [hcomp, Equiv.summable_iff]
theorem riemannXi_riemannXiZeros_eq_zero (i : RiemannXiZerosIndex) :
    riemannXi (riemannXiZeros i) = 0 := by
  have hf : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  have hmem : MeromorphicOn.divisor riemannXi ⊤ (riemannXiZeros i) ≠ 0 := by
    have := i.1.2; rwa [Function.mem_support] at this
  rw [divisor_eq_analyticOrderNatAt hf] at hmem
  have hnat : analyticOrderNatAt riemannXi (riemannXiZeros i) ≠ 0 := by
    intro h; rw [h] at hmem; simp at hmem
  have hAt : AnalyticAt ℂ riemannXi (riemannXiZeros i) := differentiable_riemannXi.analyticAt _
  rw [← hAt.analyticOrderAt_ne_zero]
  intro hz
  exact hnat (by simp [analyticOrderNatAt, hz])
theorem riemannXiZeros_re_pos (i : RiemannXiZerosIndex) : 0 < (riemannXiZeros i).re :=
  (riemannXi_re_mem_Ioo_of_eq_zero (riemannXi_riemannXiZeros_eq_zero i)).1
theorem riemannXiZeros_re_lt_one (i : RiemannXiZerosIndex) : (riemannXiZeros i).re < 1 :=
  (riemannXi_re_mem_Ioo_of_eq_zero (riemannXi_riemannXiZeros_eq_zero i)).2
private lemma abs_re_inv_le_norm_sq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    |(ρ⁻¹).re| ≤ ‖ρ⁻¹‖ ^ 2 := by
  have hne : ρ ≠ 0 := fun h ↦ by rw [h] at h0; simp at h0
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hne
  have hsq : ‖ρ⁻¹‖ ^ 2 = (Complex.normSq ρ)⁻¹ := by rw [norm_inv, inv_pow, Complex.sq_norm]
  rw [Complex.inv_re, hsq, abs_div, abs_of_pos h0, abs_of_pos hns, div_le_iff₀ hns,
    inv_mul_cancel₀ (ne_of_gt hns)]
  exact h1.le
theorem summable_re_inv_riemannXiZeros :
    Summable fun i ↦ ((riemannXiZeros i)⁻¹).re := by
  refine Summable.of_norm_bounded summable_inv_norm_sq_riemannXiZeros (fun i ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_re_inv_le_norm_sq (riemannXiZeros_re_pos i) (riemannXiZeros_re_lt_one i)
private lemma log_norm_one_sub_div {ρ : ℂ} (hρ : ρ ≠ 0) {w : ℂ} (hw : w ≠ ρ) :
    Real.log ‖1 - w / ρ‖ = Real.log ‖w - ρ‖ - Real.log ‖ρ‖ := by
  have hh : (1 : ℂ) - w / ρ = (ρ - w) / ρ := by rw [sub_div, div_self hρ]
  rw [hh, norm_div, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ hw h.symm))
    (norm_ne_zero_iff.mpr hρ), norm_sub_rev]
noncomputable def shiftLogIntegrand (t d : ℝ) (ρ : ℂ) (x : ℝ) : ℝ :=
    Real.log ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - ρ‖
      - Real.log ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - ρ‖
noncomputable def shiftLogIntegral (t d : ℝ) (ρ : ℂ) : ℝ :=
    ∫ x in (0 : ℝ)..d, shiftLogIntegrand t d ρ x
private lemma abs_log_norm_one_sub_add_re_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |Real.log ‖1 - z‖ + z.re| ≤ ‖z‖ ^ 2 := by
  have h : Real.log ‖1 - z‖ + z.re = (Complex.log (1 - z) + z).re := by
    rw [Complex.add_re, Complex.log_re]
  rw [h]
  exact (Complex.abs_re_le_norm _).trans (Complex.norm_log_one_sub_add_self_le hz)
private lemma abs_log_norm_one_sub_div_add_re_le {z ρ : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C)
    (hsmall : C * ‖ρ⁻¹‖ ≤ 1 / 2) :
    |Real.log ‖1 - z / ρ‖ + (z / ρ).re| ≤ C ^ 2 * ‖ρ⁻¹‖ ^ 2 := by
  have hle : ‖z / ρ‖ ≤ C * ‖ρ⁻¹‖ := by
    rw [norm_div, norm_inv, div_eq_mul_inv]; gcongr
  calc |Real.log ‖1 - z / ρ‖ + (z / ρ).re| ≤ ‖z / ρ‖ ^ 2 :=
        abs_log_norm_one_sub_add_re_le (hle.trans hsmall)
    _ ≤ (C * ‖ρ⁻¹‖) ^ 2 := by gcongr
    _ = C ^ 2 * ‖ρ⁻¹‖ ^ 2 := by ring
private lemma sub_ne_zero_of_im_eq {z c : ℂ} {t : ℝ} (hz : z.im = t) (hc : c.im ≠ t) :
    z - c ≠ 0 := fun h ↦ hc (by
  have := congrArg Complex.im h
  rw [Complex.sub_im, hz, Complex.zero_im, sub_eq_zero] at this
  exact this.symm)
private lemma complex_line_im (a b : ℝ) : ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I).im = b := by
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
private lemma complex_line_re (a b : ℝ) :
    ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I).re = 1 / 2 + a := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
private lemma complex_line_add_im (a b c : ℝ) :
    ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I + (c : ℂ)).im = b := by
  rw [Complex.add_im, complex_line_im, Complex.ofReal_im, add_zero]
private lemma shiftLogIntegrand_eq {ρ : ℂ} (hρ : ρ ≠ 0) (t d x : ℝ)
    (h1 : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) ≠ ρ)
    (h2 : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I ≠ ρ) :
    shiftLogIntegrand t d ρ x
      = ((Real.log ‖1 - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ‖
            + (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ).re)
          - (Real.log ‖1 - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ‖
            + (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ).re))
        - d * (ρ⁻¹).re := by
  have ere : (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ).re
      - (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ).re = d * (ρ⁻¹).re := by
    rw [← Complex.sub_re,
      show ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ
          - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ = (d : ℂ) * ρ⁻¹ by
        rw [div_sub_div_same,
          show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)
              - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) = (d : ℂ) by ring,
          div_eq_mul_inv],
      Complex.re_ofReal_mul]
  unfold shiftLogIntegrand
  rw [log_norm_one_sub_div hρ h1, log_norm_one_sub_div hρ h2]
  linear_combination -ere
private lemma continuous_shiftLogIntegrand {ρ : ℂ} (t d : ℝ) (hρt : ρ.im ≠ t) :
    Continuous (shiftLogIntegrand t d ρ) := by
  unfold shiftLogIntegrand
  refine Continuous.sub (Continuous.log (by fun_prop) (fun x ↦ ?_))
    (Continuous.log (by fun_prop) (fun x ↦ ?_))
  · rw [norm_ne_zero_iff]
    exact sub_ne_zero_of_im_eq (z := (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ))
      (complex_line_add_im x t d) hρt
  · rw [norm_ne_zero_iff]
    exact sub_ne_zero_of_im_eq (z := (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I)
      (complex_line_im x t) hρt
private lemma bookerIntegrand_eq_shiftLog (ρ : ℂ) (t d x : ℝ) (hρt : ρ.im ≠ t) :
    Real.log ‖((x : ℂ) + (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
        * ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))
        / (((x : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
            * ((x : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))))‖
      = shiftLogIntegrand t d ρ x + shiftLogIntegrand t d (1 - (starRingEnd ℂ) ρ) x := by
  have hc1 : (x : ℂ) + (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ)
        ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - (1 - (starRingEnd ℂ) ρ)) := by
    apply Complex.ext <;> simp <;> ring
  have hc2 : (x : ℂ) + (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - ρ) := by
    apply Complex.ext <;> simp; ring
  have hc3 : (x : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ)) := by
    apply Complex.ext <;> simp <;> ring
  have hc4 : (x : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - ρ) := by
    apply Complex.ext <;> simp; ring
  have him : ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I).im = t := complex_line_im x t
  have himd : ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)).im = t := complex_line_add_im x t d
  have hρstar : (1 - (starRingEnd ℂ) ρ).im ≠ t := by
    simpa [Complex.sub_im, Complex.one_im, Complex.conj_im] using hρt
  have hA1 := sub_ne_zero_of_im_eq himd hρstar
  have hA2 := sub_ne_zero_of_im_eq himd hρt
  have hA3 := sub_ne_zero_of_im_eq him hρstar
  have hA4 := sub_ne_zero_of_im_eq him hρt
  rw [norm_div, norm_mul, norm_mul, hc1, hc2, hc3, hc4, Complex.norm_conj, Complex.norm_conj,
    Complex.norm_conj, Complex.norm_conj,
    Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr hA1) (norm_ne_zero_iff.mpr hA2))
      (mul_ne_zero (norm_ne_zero_iff.mpr hA3) (norm_ne_zero_iff.mpr hA4)),
    Real.log_mul (norm_ne_zero_iff.mpr hA1) (norm_ne_zero_iff.mpr hA2),
    Real.log_mul (norm_ne_zero_iff.mpr hA3) (norm_ne_zero_iff.mpr hA4)]
  unfold shiftLogIntegrand
  ring
private lemma shiftLogIntegral_add_le_of {ρ : ℂ} (t : ℝ) {d : ℝ} (hd : 1 / 2 < d)
    (hρt : ρ.im ≠ t) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {c : ℝ} (hc : 2 ≤ c) :
    shiftLogIntegral t d ρ + shiftLogIntegral t d (1 - (starRingEnd ℂ) ρ)
      ≤ c * d ^ 2 * ((((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re
          + (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re) := by
  have hwre : |(ρ - (1 / 2 + (t : ℂ) * I)).re| ≤ 1 / 2 := by
    rw [show (ρ - (1 / 2 + (t : ℂ) * I)).re = ρ.re - 1 / 2 by simp]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwim : (ρ - (1 / 2 + (t : ℂ) * I)).im ≠ 0 := by
    rw [show (ρ - (1 / 2 + (t : ℂ) * I)).im = ρ.im - t by simp]
    exact sub_ne_zero.mpr hρt
  have hbk := bookerPairIntegral_le_of hd hwre hwim hc
  have hresPlus : (1 / ((d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re := by
    have hc : (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
        = (starRingEnd ℂ) ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ)) := by
      apply Complex.ext <;> simp <;> ring
    rw [one_div, hc, ← map_inv₀, Complex.conj_re]
  have hresMinus : (1 / ((d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re := by
    have hc : (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
        = (starRingEnd ℂ) ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ) := by
      apply Complex.ext <;> simp; ring
    rw [one_div, hc, ← map_inv₀, Complex.conj_re]
  have hI1 : IntervalIntegrable (shiftLogIntegrand t d ρ) MeasureTheory.volume 0 d :=
    (continuous_shiftLogIntegrand t d hρt).intervalIntegrable 0 d
  have hI2 : IntervalIntegrable (shiftLogIntegrand t d (1 - (starRingEnd ℂ) ρ))
      MeasureTheory.volume 0 d := by
    refine (continuous_shiftLogIntegrand t d ?_).intervalIntegrable 0 d
    simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]
    exact hρt
  have hLHS : bookerPairIntegral d (ρ - (1 / 2 + (t : ℂ) * I))
      = shiftLogIntegral t d ρ + shiftLogIntegral t d (1 - (starRingEnd ℂ) ρ) := by
    rw [bookerPairIntegral, shiftLogIntegral, shiftLogIntegral,
      ← intervalIntegral.integral_add hI1 hI2]
    exact intervalIntegral.integral_congr (fun x _ ↦ bookerIntegrand_eq_shiftLog ρ t d x hρt)
  have hRHS : (1 / ((d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
        + 1 / ((d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re
          + (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re := by
    rw [Complex.add_re, hresPlus, hresMinus]; ring
  rw [hLHS, hRHS] at hbk
  exact hbk
lemma Complex.norm_complex_line_le (a b : ℝ) :
    ‖(1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I‖ ≤ 1 / 2 + |a| + |b| := by
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by rw [norm_div, norm_one, Complex.norm_ofNat]
  calc ‖(1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I‖
      ≤ ‖(1 / 2 : ℂ) + (a : ℂ)‖ + ‖(b : ℂ) * I‖ := norm_add_le _ _
    _ ≤ (‖(1 / 2 : ℂ)‖ + ‖(a : ℂ)‖) + ‖(b : ℂ) * I‖ := by gcongr; exact norm_add_le _ _
    _ = 1 / 2 + |a| + |b| := by
        rw [h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
theorem summable_re_inv_riemannXiZeros_sub {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    Summable (fun i ↦ ((s - riemannXiZeros i)⁻¹).re) := by
  have h2 : Summable (fun i ↦ (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i).re) :=
    (summable_partial_fraction hs).map (Complex.reCLM : ℂ →L[ℝ] ℝ).toAddMonoidHom
      Complex.continuous_re
  refine (h2.sub summable_re_inv_riemannXiZeros).congr (fun i ↦ ?_)
  rw [Complex.add_re, one_div, one_div, add_sub_cancel_right]
theorem exists_forall_riemannXiZeros_im_ne :
    ∃ t₀ : ℝ, ∀ i, (riemannXiZeros i).im ≠ t₀ := by
  have hcount : (Set.range (fun i ↦ (riemannXiZeros i).im)).Countable := Set.countable_range _
  have hne : Set.range (fun i ↦ (riemannXiZeros i).im) ≠ Set.univ := fun h ↦
    Cardinal.not_countable_real (h ▸ hcount)
  obtain ⟨t₀, ht₀⟩ := Set.nonempty_compl.mpr hne
  exact ⟨t₀, fun i h ↦ ht₀ ⟨i, h⟩⟩
theorem tsum_re_inv_riemannXiZeros_sub_critical_eq_zero {s₀ : ℂ}
    (hconj : starRingEnd ℂ s₀ = 1 - s₀) :
    ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re = 0 := by
  have hgpt : ∀ z : ℂ, ((s₀ - (1 - starRingEnd ℂ z))⁻¹).re = -((s₀ - z)⁻¹).re := by
    intro z
    have hid : s₀ - (1 - starRingEnd ℂ z) = -(starRingEnd ℂ (s₀ - z)) := by
      rw [map_sub, hconj]; ring
    rw [hid, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
  have hcalc : (∑' i, ((s₀ - riemannXiZeros i)⁻¹).re)
      = - ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re :=
    calc (∑' i, ((s₀ - riemannXiZeros i)⁻¹).re)
        = ∑' i, ((s₀ - (1 - starRingEnd ℂ (riemannXiZeros i)))⁻¹).re :=
          tsum_riemannXiZeros_one_sub_conj (fun z ↦ ((s₀ - z)⁻¹).re)
      _ = ∑' i, (-((s₀ - riemannXiZeros i)⁻¹).re) := by simp_rw [hgpt]
      _ = - ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re := tsum_neg
  linarith
private lemma deriv_riemannXi_conj (s : ℂ) :
    deriv riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (deriv riemannXi s) := by
  have hsym : starRingEnd ℂ ∘ riemannXi ∘ starRingEnd ℂ = riemannXi := by
    funext z; simp only [Function.comp_apply, riemannXi_conj, Complex.conj_conj]
  have h : starRingEnd ℂ ∘ deriv riemannXi ∘ starRingEnd ℂ = deriv riemannXi := by
    rw [← deriv_conj_conj, hsym]
  simpa using congrArg (starRingEnd ℂ) (congrFun h s)
private lemma deriv_riemannXi_one_sub (s : ℂ) :
    deriv riemannXi (1 - s) = - deriv riemannXi s := by
  have hu : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hcomp : HasDerivAt (riemannXi ∘ fun w ↦ 1 - w) (deriv riemannXi (1 - s) * (-1)) s :=
    ((differentiable_riemannXi (1 - s)).hasDerivAt).comp s hu
  have hfun : (riemannXi ∘ fun w ↦ 1 - w) = riemannXi := by
    funext z; simp only [Function.comp_apply, riemannXi_one_sub]
  rw [hfun] at hcomp
  have hd : HasDerivAt riemannXi (deriv riemannXi s) s := (differentiable_riemannXi s).hasDerivAt
  linear_combination -(hcomp.unique hd)
theorem re_logDeriv_riemannXi_critical_eq_zero {s₀ : ℂ}
    (hconj : starRingEnd ℂ s₀ = 1 - s₀) :
    (logDeriv riemannXi s₀).re = 0 := by
  have ha : logDeriv riemannXi (starRingEnd ℂ s₀) = starRingEnd ℂ (logDeriv riemannXi s₀) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_conj, riemannXi_conj, map_div₀]
  have hb : logDeriv riemannXi (1 - s₀) = - logDeriv riemannXi s₀ := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub, neg_div]
  have hcomb : starRingEnd ℂ (logDeriv riemannXi s₀) = - logDeriv riemannXi s₀ := by
    rw [← ha, hconj, hb]
  have := congrArg Complex.re hcomb
  rw [Complex.conj_re, Complex.neg_re] at this
  linarith
private lemma re_tsum_partialFraction_add {s : ℂ} (hsne : ∀ i, s ≠ riemannXiZeros i)
    (hPair : Summable fun i ↦ ((s - riemannXiZeros i)⁻¹).re) :
    (∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i)).re
      = ∑' i, ((s - riemannXiZeros i)⁻¹).re + ∑' i, ((riemannXiZeros i)⁻¹).re := by
  rw [Complex.re_tsum (summable_partial_fraction hsne),
    tsum_congr (fun i ↦ by rw [Complex.add_re, one_div, one_div]),
    hPair.tsum_add summable_re_inv_riemannXiZeros]
theorem hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero :
    (logDeriv riemannXi 0).re + ∑' i, ((riemannXiZeros i)⁻¹).re = 0 := by
  obtain ⟨t₀, ht₀⟩ := exists_forall_riemannXiZeros_im_ne
  set s₀ : ℂ := (1 / 2 : ℂ) + (t₀ : ℂ) * I with hs₀
  have hs0im : s₀.im = t₀ := by rw [hs₀]; simp
  have hsne : ∀ i, s₀ ≠ riemannXiZeros i := fun i h ↦ ht₀ i (by rw [← h, hs0im])
  have hconj : starRingEnd ℂ s₀ = 1 - s₀ := by
    rw [hs₀]; apply Complex.ext <;> simp; ring
  have hkey := congrArg Complex.re (logDeriv_riemannXi_eq hsne)
  rw [Complex.add_re,
    re_tsum_partialFraction_add hsne (summable_re_inv_riemannXiZeros_sub hsne),
    re_logDeriv_riemannXi_critical_eq_zero hconj,
    tsum_re_inv_riemannXiZeros_sub_critical_eq_zero hconj, zero_add] at hkey
  linarith
theorem tsum_re_inv_riemannXiZeros_sub_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hsne : ∀ i, s ≠ riemannXiZeros i)
    (hPair : Summable (fun i ↦ ((s - riemannXiZeros i)⁻¹).re)) :
    ∑' i, ((s - riemannXiZeros i)⁻¹).re
      = (logDeriv riemannZeta s).re + (1 / s).re + (1 / (s - 1)).re
        - 1 / 2 * Real.log π + 1 / 2 * (Complex.digamma (s / 2)).re := by
  have hkey := logDeriv_riemannZeta_eq hre hs1 hsne
  have hκ := hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hlogpi_re : ((1 / 2 : ℂ) * (Real.log π : ℂ)).re = 1 / 2 * Real.log π := by
    rw [hhalf, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpsi_re : ((1 / 2 : ℂ) * Complex.digamma (s / 2)).re
      = 1 / 2 * (Complex.digamma (s / 2)).re := by rw [hhalf, Complex.re_ofReal_mul]
  have hexp := congrArg Complex.re hkey
  simp only [Complex.add_re, Complex.sub_re, hlogpi_re, hpsi_re] at hexp
  rw [re_tsum_partialFraction_add hsne hPair] at hexp
  linarith [hexp, hκ]
lemma summable_pairDensity {t d : ℝ} (hd : 1 / 2 < d) :
    Summable (fun i ↦ (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re) :=
  summable_re_inv_riemannXiZeros_sub fun i h ↦ by
    have hlt := riemannXiZeros_re_lt_one i
    rw [← h, complex_line_re d t] at hlt; linarith
lemma Real.log_add_le {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    Real.log (u + t) ≤ Real.log t + u / t := by
  have hdiv : Real.log ((t + u) / t) ≤ u / t := by
    calc Real.log ((t + u) / t)
        ≤ (t + u) / t - 1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) ht)
      _ = u / t := by field_simp; ring
  rw [Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < t + u)) ht.ne'] at hdiv
  rw [add_comm u t]
  linarith
lemma Complex.re_one_div_le_norm_inv (w : ℂ) : (1 / w).re ≤ ‖w‖⁻¹ := by
  rw [one_div]; exact (Complex.re_le_norm _).trans_eq (norm_inv w)
lemma shiftedLine_setup {d t : ℝ} (hdlt : 1 / 2 < d) (ht0 : 0 < t) :
    ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re = 1 / 2 + d ∧
      ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).im = t ∧
      0 < ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re ∧
      1 < ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re ∧
      (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I ≠ 1 ∧
      (∀ i, (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I ≠ riemannXiZeros i) ∧
      1 / 2 + d ≤ ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ∧
      0 < ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ∧
      ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ≤ (1 / 2 + d) + t := by
  have hsre : ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re = 1 / 2 + d := complex_line_re d t
  have hsim : ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).im = t := complex_line_im d t
  have hsnorm_lb : 1 / 2 + d ≤ ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ := by
    rw [← hsre]; exact Complex.re_le_norm _
  refine ⟨hsre, hsim, ?_, ?_, ?_, ?_, hsnorm_lb, lt_of_lt_of_le (by linarith) hsnorm_lb, ?_⟩
  · rw [hsre]; linarith
  · rw [hsre]; linarith
  · intro h; rw [h] at hsim; simp at hsim; linarith
  · intro i h
    have hlt := riemannXiZeros_re_lt_one i
    rw [← h, hsre] at hlt; linarith
  · have h := Complex.norm_complex_line_le d t
    rw [abs_of_pos (by linarith : (0 : ℝ) < d), abs_of_pos ht0] at h
    linarith
private lemma abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, le_abs_self b, le_abs_self c],
              by linarith [le_abs_self a, neg_abs_le b, neg_abs_le c]⟩
private lemma exists_eventually_forall_norm_shiftLogIntegrand_le {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in Filter.cofinite, ∀ x ∈ Set.uIoc (0 : ℝ) d,
      ‖shiftLogIntegrand t d (riemannXiZeros i) x‖ ≤ C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
  have hd0 : (0 : ℝ) < d := by linarith
  set C0 : ℝ := 1 / 2 + 2 * d + |t| with hC0
  have hC0pos : 0 ≤ C0 := by rw [hC0]; positivity
  have hsum2 := summable_inv_norm_sq_riemannXiZeros
  have htail : ∀ᶠ i in Filter.cofinite, ‖(riemannXiZeros i)⁻¹‖ ≤ 1 / (2 * (C0 + 1)) := by
    have hlt : (0 : ℝ) < (1 / (2 * (C0 + 1))) ^ 2 := by positivity
    filter_upwards [hsum2.tendsto_cofinite_zero.eventually (eventually_lt_nhds hlt)] with i hi
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hi).le
  refine ⟨2 * C0 ^ 2 + d, by positivity, ?_⟩
  filter_upwards [htail] with i hi
  set ρ := riemannXiZeros i with hρ
  have hρ0 : ρ ≠ 0 := riemannXiZeros_ne_zero i
  have hρre0 : 0 < ρ.re := riemannXiZeros_re_pos i
  have hρre1 : ρ.re < 1 := riemannXiZeros_re_lt_one i
  have hsmall : C0 * ‖ρ⁻¹‖ ≤ 1 / 2 := by
    have hstep : C0 * ‖ρ⁻¹‖ ≤ C0 * (1 / (2 * (C0 + 1))) := mul_le_mul_of_nonneg_left hi hC0pos
    have : C0 * (1 / (2 * (C0 + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hE3 : d * |(ρ⁻¹).re| ≤ d * ‖ρ⁻¹‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (abs_re_inv_le_norm_sq hρre0 hρre1) hd0.le
  intro x hx
  rw [Set.uIoc_of_le hd0.le] at hx
  have hxabs : |x| ≤ d := by rw [abs_of_nonneg hx.1.le]; exact hx.2
  have hs_C0 : ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I‖ ≤ C0 := by
    have := Complex.norm_complex_line_le x t; rw [hC0]; linarith
  have hsd_C0 : ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)‖ ≤ C0 := by
    have h1 := norm_add_le ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) (d : ℂ)
    have h2 : ‖(d : ℂ)‖ = d := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    have := Complex.norm_complex_line_le x t
    rw [hC0]; rw [h2] at h1; linarith
  have h2ne : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I ≠ ρ := fun h ↦
    ht i (by rw [← hρ, ← h, complex_line_im x t])
  have h1ne : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) ≠ ρ := fun h ↦
    ht i (by rw [← hρ, ← h, complex_line_add_im x t d])
  rw [Real.norm_eq_abs, shiftLogIntegrand_eq hρ0 t d x h1ne h2ne]
  refine (abs_sub_sub_le _ _ _).trans ?_
  rw [abs_mul, abs_of_pos hd0]
  refine (add_le_add (add_le_add (abs_log_norm_one_sub_div_add_re_le (ρ := ρ) hsd_C0 hsmall)
    (abs_log_norm_one_sub_div_add_re_le (ρ := ρ) hs_C0 hsmall)) hE3).trans (le_of_eq ?_)
  ring
private lemma summable_shiftLogIntegral {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    Summable (fun i ↦ shiftLogIntegral t d (riemannXiZeros i)) := by
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨C, hC0, hCb⟩ := exists_eventually_forall_norm_shiftLogIntegrand_le hd ht
  refine Summable.of_norm_bounded_eventually
    (summable_inv_norm_sq_riemannXiZeros.mul_left (C * d)) ?_
  filter_upwards [hCb] with i hi
  calc ‖shiftLogIntegral t d (riemannXiZeros i)‖
      = ‖∫ x in (0 : ℝ)..d, shiftLogIntegrand t d (riemannXiZeros i) x‖ := by rw [shiftLogIntegral]
    _ ≤ C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 * |d - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hi
    _ = C * d * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by rw [sub_zero, abs_of_pos hd0]; ring
theorem tsum_shiftLogIntegral_eq_intervalIntegral_tsum {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      = ∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hint : ∀ i, MeasureTheory.IntegrableOn
      (shiftLogIntegrand t d (riemannXiZeros i)) (Set.Ioc 0 d) := fun i ↦
    (continuous_shiftLogIntegrand t d (ht i)).integrableOn_Ioc
  obtain ⟨C, hC0, hCb⟩ := exists_eventually_forall_norm_shiftLogIntegrand_le hd ht
  have hsummint : Summable (fun i ↦
      ∫ x in Set.Ioc (0 : ℝ) d, ‖shiftLogIntegrand t d (riemannXiZeros i) x‖) := by
    refine Summable.of_norm_bounded_eventually
      (summable_inv_norm_sq_riemannXiZeros.mul_left (C * d)) ?_
    filter_upwards [hCb] with i hi
    have hnn : (0 : ℝ) ≤ ∫ x in Set.Ioc (0 : ℝ) d,
        ‖shiftLogIntegrand t d (riemannXiZeros i) x‖ :=
      MeasureTheory.integral_nonneg (fun x ↦ norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    calc ∫ x in Set.Ioc (0 : ℝ) d, ‖shiftLogIntegrand t d (riemannXiZeros i) x‖
        ≤ ∫ _x in Set.Ioc (0 : ℝ) d, C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
          refine MeasureTheory.setIntegral_mono_on (hint i).norm ?_ measurableSet_Ioc ?_
          · exact MeasureTheory.integrableOn_const
              (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
          · intro x hx
            exact hi x (by rw [Set.uIoc_of_le hd0.le]; exact hx)
      _ = C * d * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hd0.le, smul_eq_mul]
          ring
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun i ↦ shiftLogIntegrand t d (riemannXiZeros i))
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) d)) hint hsummint
  calc ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      = ∑' i, ∫ x in Set.Ioc (0 : ℝ) d, shiftLogIntegrand t d (riemannXiZeros i) x := by
        refine tsum_congr (fun i ↦ ?_)
        rw [shiftLogIntegral, intervalIntegral.integral_of_le hd0.le]
    _ = ∫ x in Set.Ioc (0 : ℝ) d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := hswap
    _ = ∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := by
        rw [intervalIntegral.integral_of_le hd0.le]
theorem integral_tsum_log_norm_shift_le_of {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) {c : ℝ} (hc : 2 ≤ c) :
    ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      ≤ c * d ^ 2 * ∑' i,
          (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re := by
  set A : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hA
  set g : ℂ → ℝ := shiftLogIntegral t d with hg
  set f : ℂ → ℝ := fun ρ ↦ ((A - ρ)⁻¹).re with hf
  have hSg : Summable fun i ↦ g (riemannXiZeros i) := summable_shiftLogIntegral hd ht
  have hSh : Summable fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)) :=
    (summable_riemannXiZeros_one_sub_conj_iff g).mpr hSg
  have hSc : Summable fun i ↦ f (riemannXiZeros i) := summable_pairDensity hd
  have hSch : Summable fun i ↦ f (1 - starRingEnd ℂ (riemannXiZeros i)) :=
    (summable_riemannXiZeros_one_sub_conj_iff f).mpr hSc
  have hper : ∀ i, g (riemannXiZeros i) + g (1 - starRingEnd ℂ (riemannXiZeros i))
      ≤ c * d ^ 2 * (f (riemannXiZeros i) + f (1 - starRingEnd ℂ (riemannXiZeros i))) := fun i ↦
    shiftLogIntegral_add_le_of t hd (ht i) (riemannXiZeros_re_pos i)
      (riemannXiZeros_re_lt_one i) hc
  have hreflg := tsum_riemannXiZeros_one_sub_conj g
  have hreflc := tsum_riemannXiZeros_one_sub_conj f
  have key : 2 * ∑' i, g (riemannXiZeros i) ≤ 2 * (c * d ^ 2 * ∑' i, f (riemannXiZeros i)) :=
    calc 2 * ∑' i, g (riemannXiZeros i)
        = ∑' i, (g (riemannXiZeros i) + g (1 - starRingEnd ℂ (riemannXiZeros i))) := by
          rw [hSg.tsum_add hSh, ← hreflg]; ring
      _ ≤ ∑' i, c * d ^ 2 * (f (riemannXiZeros i) + f (1 - starRingEnd ℂ (riemannXiZeros i))) :=
          Summable.tsum_le_tsum hper (hSg.add hSh) ((hSc.add hSch).mul_left _)
      _ = 2 * (c * d ^ 2 * ∑' i, f (riemannXiZeros i)) := by
          rw [tsum_mul_left, hSc.tsum_add hSch, ← hreflc]; ring
  linarith
open scoped LSeries.notation
open ArithmeticFunction
lemma re_logDeriv_riemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    (logDeriv riemannZeta s).re ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := by
  have hsum : Summable (fun n ↦ ‖LSeries.term ↗Λ s n‖) := (LSeriesSummable_vonMangoldt hs).norm
  have hlogD : logDeriv riemannZeta s = -LSeries ↗Λ s := by
    rw [logDeriv_apply, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]; ring
  calc (logDeriv riemannZeta s).re
      ≤ ‖logDeriv riemannZeta s‖ := Complex.re_le_norm _
    _ = ‖LSeries ↗Λ s‖ := by rw [hlogD, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
lemma re_digamma_le {z : ℂ} (hz : 0 < z.re) {C : ℝ}
    (hC : ‖digammaRemainderIoi z 1‖ ≤ C * ‖z‖ ^ (-(1 : ℤ))) :
    (Complex.digamma z).re ≤ Real.log ‖z‖ + (1 / 2 + C) / ‖z‖ := by
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hz
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzne : ‖z‖ ≠ 0 := hznorm.ne'
  have hzpow : ‖z‖ ^ (-(1 : ℤ)) = (‖z‖)⁻¹ := by rw [zpow_neg, zpow_one]
  rw [hzpow] at hC
  have heq := digamma_eq_log_sub z hz 0
  rw [show (2 * 0 + 1) = 1 from rfl,
      show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty_of_lt (by norm_num),
      Finset.sum_empty, sub_zero] at heq
  rw [heq, Complex.sub_re, Complex.sub_re, Complex.log_re]
  have e1 : -((2 * z)⁻¹).re ≤ (2 * ‖z‖)⁻¹ := by
    have hn : ‖(2 * z)⁻¹‖ = (2 * ‖z‖)⁻¹ := by rw [norm_inv, norm_mul, Complex.norm_ofNat]
    calc -((2 * z)⁻¹).re ≤ ‖(2 * z)⁻¹‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ = (2 * ‖z‖)⁻¹ := hn
  have e2 : -(digammaRemainderIoi z 1).re ≤ C * (‖z‖)⁻¹ :=
    le_trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) hC
  have efr : (2 * ‖z‖)⁻¹ + C * (‖z‖)⁻¹ = (1 / 2 + C) / ‖z‖ := by field_simp
  linarith [e1, e2, efr]
end
end CountPort69
section CountPort70
section
open MeasureTheory Metric Real
open scoped ENNReal
private theorem lintegral_ofReal_inv_norm_closedBall {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in closedBall (0 : ℂ) r, ENNReal.ofReal ‖s‖⁻¹ = ENNReal.ofReal (2 * π * r) := by
  rw [← lintegral_indicator measurableSet_closedBall,
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have heqon : Set.EqOn
      (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 •
        (closedBall (0 : ℂ) r).indicator (fun w ↦ ENNReal.ofReal ‖w‖⁻¹)
          (Complex.polarCoord.symm p))
      ((Set.Ioc 0 r ×ˢ Set.Ioo (-π) π).indicator (fun _ ↦ 1))
      (Set.Ioi 0 ×ˢ Set.Ioo (-π) π) := by
    rintro ⟨x, y⟩ ⟨hx : (0 : ℝ) < x, hy₁, hy₂⟩
    have hnorm : ‖(Complex.polarCoord.symm (x, y) : ℂ)‖ = x := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hx]
    by_cases h : x ≤ r <;>
      simp [-Complex.polarCoord_symm_apply, mem_closedBall, dist_zero_right, hnorm, hx, hy₁, hy₂,
        h, ENNReal.mul_inv_cancel (by simp [hx] : ENNReal.ofReal x ≠ 0) ENNReal.ofReal_ne_top]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) heqon,
    setLIntegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo),
    Set.prod_inter_prod, Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self, Set.inter_self,
    setLIntegral_const, one_mul, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioc, Real.volume_Ioo, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ r - 0)]
  congr 1
  ring
private theorem lintegral_ofReal_inv_norm_sub_closedBall (ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in closedBall ρ r, ENNReal.ofReal ‖s - ρ‖⁻¹ = ENNReal.ofReal (2 * π * r) := by
  rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_add_right_eq_self _ ρ,
    ← lintegral_ofReal_inv_norm_closedBall hr, ← lintegral_indicator measurableSet_closedBall]
  refine lintegral_congr fun s ↦ ?_
  simp [Set.indicator, mem_closedBall, dist_eq_norm]
private theorem measurable_inv_norm_sub (ρ : ℂ) : Measurable (fun s : ℂ ↦ ‖s - ρ‖⁻¹) :=
  (continuous_norm.comp (continuous_id.sub continuous_const)).measurable.inv
theorem integrableOn_inv_norm_sub_closedBall (ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℂ ↦ ‖s - ρ‖⁻¹) (closedBall ρ r) := by
  refine ⟨(measurable_inv_norm_sub ρ).aestronglyMeasurable, ?_⟩
  simp_rw [hasFiniteIntegral_iff_norm, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    lintegral_ofReal_inv_norm_sub_closedBall ρ hr]
  exact ENNReal.ofReal_lt_top
end
end CountPort70
section CountPort71
section
open Complex MeasureTheory Metric Set Filter Topology
private theorem analyticOnNhd_riemannZeta_ne_one :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_ne
private theorem analyticOnNhd_deriv_riemannZeta_ne_one :
    AnalyticOnNhd ℂ (deriv riemannZeta) {s : ℂ | s ≠ 1} :=
  fun s hs ↦ (analyticOnNhd_riemannZeta_ne_one s hs).deriv
private theorem analyticOnNhd_riemannZeta_upperHalfPlane :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | 0 < s.im} :=
  DifferentiableOn.analyticOnNhd (fun s hs ↦
    (differentiableAt_riemannZeta (by rintro rfl; simp at hs)).differentiableWithinAt)
    (isOpen_lt continuous_const continuous_im)
private theorem isConnected_upperHalfPlane : IsConnected {s : ℂ | 0 < s.im} :=
  (convex_halfSpace_im_gt 0).isConnected ⟨I, by simp⟩
private theorem im_pos_of_mem_rectangle {z w s : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (hs : s ∈ Rectangle z w) : 0 < s.im := by
  simp only [Rectangle, mem_reProdIm, mem_uIcc] at hs
  rcases hs.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
private theorem continuous_riemannZeta_horizontal {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
  analyticOnNhd_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
    (fun σ h ↦ ht (by simpa using congrArg Complex.im h))
private theorem continuous_riemannZeta_vertical {x : ℝ} (hx : x ≠ 1) :
    Continuous (fun τ : ℝ ↦ riemannZeta ((x : ℂ) + I * (τ : ℂ))) :=
  analyticOnNhd_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
    (fun τ h ↦ hx (by simpa using congrArg Complex.re h))
private theorem ofReal_add_I_mul_ne_one {σ t : ℝ} (ht : t ≠ 0) :
    (σ : ℂ) + I * (t : ℂ) ≠ 1 := fun h ↦ ht (by simpa using congrArg Complex.im h)
theorem finite_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Rectangle z w ∩ {ρ | riemannZeta ρ = 0}).Finite :=
  finite_rectangle_inter_setOf_eq_zero analyticOnNhd_riemannZeta_upperHalfPlane
    isConnected_upperHalfPlane (fun _ hρ ↦ im_pos_of_mem_rectangle hz hw hρ) (z₀ := 2 + I) (by simp)
    (riemannZeta_ne_zero_of_one_le_re (by simp))
theorem finite_re_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Complex.re '' (Rectangle z w ∩ {ρ | riemannZeta ρ = 0})).Finite :=
  (finite_riemannZeta_zeros_rectangle hz hw).image _
theorem finite_im_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Complex.im '' (Rectangle z w ∩ {ρ | riemannZeta ρ = 0})).Finite :=
  (finite_riemannZeta_zeros_rectangle hz hw).image _
private theorem ofReal_add_I_mul_mem_rectangle {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {σ t : ℝ} (hσ : σ ∈ Icc z.re w.re) (ht : t ∈ Icc z.im w.im) :
    ((σ : ℂ) + I * (t : ℂ)) ∈ Rectangle z w := by
  rw [Rectangle, mem_reProdIm, Set.uIcc_of_le hre, Set.uIcc_of_le him]
  exact ⟨by simpa using hσ, by simpa using ht⟩
private theorem ofReal_add_I_mul_mem_rectangle_two {t₁ t₂ σ t : ℝ} (h12 : t₁ ≤ t₂)
    (hσ : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1) (ht : t ∈ Set.Icc t₁ t₂) :
    ((σ : ℂ) + I * (t : ℂ)) ∈ Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ)) :=
  ofReal_add_I_mul_mem_rectangle (by norm_num) (by simpa using h12)
    (by simp only [mem_Icc]; norm_num; constructor <;> linarith) (by simpa using ht)
private theorem re_le_one_of_riemannZeta_eq_zero {σ t : ℝ}
    (hz : riemannZeta ((σ : ℂ) + I * t) = 0) : σ ≤ 1 :=
  not_lt.mp fun h ↦ riemannZeta_ne_zero_of_one_le_re (by simpa using h.le) hz
private theorem riemannZeta_ray_ne_zero_of_not_mem_im_zeros {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) {t : ℝ}
    (ht : t ∈ Set.Icc t₁ t₂)
    (htbad : t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
      ∩ {ρ | riemannZeta ρ = 0})) :
    ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0 := fun σ hσ hzero ↦
  htbad ⟨(σ : ℂ) + I * (t : ℂ),
    ⟨ofReal_add_I_mul_mem_rectangle_two h12 hσ (re_le_one_of_riemannZeta_eq_zero hzero) ht,
      hzero⟩, by simp⟩
private theorem not_eventually_riemannZeta_eq_zero {x : ℂ} (hx : 0 < x.im) :
    ¬ ∀ᶠ z in 𝓝 x, riemannZeta z = 0 := fun hev ↦
  riemannZeta_ne_zero_of_one_le_re (s := 2 + I) (by simp)
    (analyticOnNhd_riemannZeta_upperHalfPlane.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isConnected_upperHalfPlane.isPreconnected hx hev (by simp))
private theorem integrableOn_const_div_sub_closedBall (c ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℂ ↦ c / (s - ρ)) (closedBall ρ r) := by
  refine Integrable.mono' ((integrableOn_inv_norm_sub_closedBall ρ hr).const_mul ‖c‖)
    (measurable_const.div (measurable_id.sub measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s ↦ ?_)
  rw [norm_div, div_eq_mul_inv]
private theorem exists_integrableOn_logDeriv_riemannZeta_closedBall {x : ℂ} (hx : 0 < x.im) :
    ∃ r > 0, IntegrableOn (logDeriv riemannZeta) (closedBall x r) := by
  have hax : AnalyticAt ℂ riemannZeta x :=
    analyticOnNhd_riemannZeta_ne_one x (by rintro rfl; simp at hx)
  by_cases hzero : riemannZeta x = 0
  ·
    obtain ⟨n, g, -, -, -, hlogg, heq⟩ :=
      meromorphicOrderAt_eq_residue_logDeriv hax (not_eventually_riemannZeta_eq_zero hx)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      ((eventually_nhdsWithin_iff.mp heq).and hlogg.eventually_analyticAt)
    have hlt : ∀ {z : ℂ}, z ∈ closedBall x (ε / 2) → dist z x < ε := fun {z} hz ↦
      lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)
    refine ⟨ε / 2, half_pos hε, Integrable.congr
      ((integrableOn_const_div_sub_closedBall (n : ℂ) x (half_pos hε).le).add
        (ContinuousOn.integrableOn_compact (isCompact_closedBall x (ε / 2))
          fun _ hz ↦ (hball (hlt hz)).2.continuousAt.continuousWithinAt)) ?_⟩
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton x)),
      ae_restrict_mem measurableSet_closedBall] with z hzne hzmem
    exact ((hball (hlt hzmem)).1 hzne).symm
  ·
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      (hax.eventually_analyticAt.and (hax.continuousAt.eventually_ne hzero))
    refine ⟨ε / 2, half_pos hε, ContinuousOn.integrableOn_compact
      (isCompact_closedBall x (ε / 2)) fun z hz ↦ ?_⟩
    obtain ⟨haz, hzne⟩ := hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
    exact (haz.deriv.div haz hzne).continuousAt.continuousWithinAt
theorem integrableOn_logDeriv_riemannZeta_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (logDeriv riemannZeta) (Rectangle z w) := by
  refine LocallyIntegrableOn.integrableOn_isCompact ?_ (isCompact_uIcc.reProdIm isCompact_uIcc)
  intro x hx
  obtain ⟨r, hr, hint⟩ :=
    exists_integrableOn_logDeriv_riemannZeta_closedBall (im_pos_of_mem_rectangle hz hw hx)
  exact ⟨closedBall x r, nhdsWithin_le_nhds (closedBall_mem_nhds x hr), hint⟩
theorem log_norm_riemannZeta_sub_eq_neg_im_integral {σ t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) (ht1 : 0 < t₁)
    (hne : ∀ t ∈ Icc t₁ t₂, riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖ - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖
      = -(∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hpathcont : Continuous (fun t : ℝ ↦ (σ : ℂ) + I * t) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ ↦ (σ : ℂ) + I * t) (Icc t₁ t₂) {s : ℂ | s ≠ 1} :=
    fun t ht ↦ ofReal_add_I_mul_ne_one (ht1.trans_le ht.1).ne'
  have hderiv : ∀ t ∈ Ioo t₁ t₂,
      HasDerivAt (fun t : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))
        (deriv riemannZeta ((σ : ℂ) + I * t) * I) t := fun t ht ↦
    ((analyticOnNhd_riemannZeta_ne_one _
      (ofReal_add_I_mul_ne_one (ht1.trans_le ht.1.le).ne')).differentiableAt.hasDerivAt).comp t
      (by simpa using ((ofRealCLM.hasDerivAt (x := t)).const_mul I).const_add (σ : ℂ))
  have hφcont : ContinuousOn (fun t : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) (Icc t₁ t₂) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp hpathcont.continuousOn hmaps
  have heq : (fun t : ℝ ↦ deriv riemannZeta ((σ : ℂ) + I * t) * I / riemannZeta ((σ : ℂ) + I * t))
      = fun t : ℝ ↦ logDeriv riemannZeta ((σ : ℂ) + I * t) * I :=
    funext fun t ↦ by rw [logDeriv_apply, mul_div_right_comm]
  have h := re_integral_div_eq_log_norm_sub h12 hφcont hne hderiv
    (((analyticOnNhd_deriv_riemannZeta_ne_one.continuousOn.comp hpathcont.continuousOn hmaps).mul
      continuousOn_const).div hφcont hne)
  rw [heq, intervalIntegral.integral_mul_const, mul_I_re] at h
  linarith
theorem argVariation_riemannZeta_horizontal_eq_im_integral {a X t : ℝ} (hX : a ≤ X) (ht : t ≠ 0)
    (hne : ∀ σ ∈ Icc a X, riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    argVariation a X (fun σ ↦ riemannZeta ((σ : ℂ) + I * t))
      = (∫ σ in a..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hφcont : ContinuousOn (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) (Icc a X) :=
    (continuous_riemannZeta_horizontal ht).continuousOn
  have hdcont : Continuous (fun σ : ℝ ↦ deriv riemannZeta ((σ : ℂ) + I * t)) :=
    analyticOnNhd_deriv_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
      (fun _ ↦ ofReal_add_I_mul_ne_one ht)
  have hderiv : ∀ σ ∈ Ioo a X,
      HasDerivAt (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))
        (deriv riemannZeta ((σ : ℂ) + I * t)) σ := fun σ _ ↦ by
    have h1 : HasDerivAt (fun σ : ℝ ↦ (σ : ℂ) + I * t) 1 σ := by
      simpa using (ofRealCLM.hasDerivAt (x := σ)).add_const (I * (t : ℂ))
    have hd := ((analyticOnNhd_riemannZeta_ne_one _
      (ofReal_add_I_mul_ne_one ht)).differentiableAt.hasDerivAt).comp σ h1
    rw [mul_one] at hd; exact hd
  rw [argVariation_eq_im_integral hX hφcont hne hderiv (hdcont.continuousOn.div hφcont hne)]
  simp only [logDeriv_apply]
theorem tendsto_argVariation_riemannZeta_vertical_atTop {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun X : ℝ ↦ argVariation 0 t (fun τ : ℝ ↦ riemannZeta ((X : ℂ) + I * (τ : ℂ))))
      atTop (𝓝 0) := by
  have key : Tendsto (fun X : ℝ ↦ (riemannZeta ((X : ℂ) + I * (t : ℂ))).arg
      - (riemannZeta ((X : ℂ) + I * ((0 : ℝ) : ℂ))).arg) atTop (𝓝 0) := by
    simpa using (tendsto_arg_riemannZeta_atTop t).sub (tendsto_arg_riemannZeta_atTop 0)
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  rw [argVariation_eq_arg_sub_arg ht
    (continuous_riemannZeta_vertical (by linarith)).continuousOn
    (fun τ _ ↦ riemannZeta_mem_slitPlane_of_two_le_re (by simpa using hX))]
private theorem arg_riemannZeta_ofReal_eq_zero {σ : ℝ} (hσ : 2 ≤ σ) :
    (riemannZeta (σ : ℂ)).arg = 0 := by
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (σ : ℂ)
      = (((1 / ((n : ℝ) + 1) ^ σ : ℝ)) : ℂ) := fun n ↦ by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have him : (riemannZeta (σ : ℂ)).im = 0 := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using (by linarith : (1 : ℝ) < σ)),
      tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_im]
  have hsp := Complex.mem_slitPlane_iff.mp
    (riemannZeta_mem_slitPlane_of_two_le_re (s := (σ : ℂ)) (by simpa using hσ))
  exact Complex.arg_eq_zero_iff.mpr ⟨hsp.elim le_of_lt (absurd him), him⟩
private theorem mem_Icc_affine {a b u : ℝ} (hab : a ≤ b) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    a + u * (b - a) ∈ Set.Icc a b :=
  Set.uIcc_of_le hab ▸ add_mul_sub_mem_uIcc hu
private theorem argVariation_riemannZeta_lineSeg_comp {a b : ℝ} (hab : a ≤ b) {P Q : ℂ}
    {g : ℝ → ℂ} (hg : ∀ u : ℝ, lineSeg P Q u = g (a + u * (b - a)))
    (hcont : ContinuousOn (fun x : ℝ ↦ riemannZeta (g x)) (Set.Icc a b))
    (hne : ∀ x ∈ Set.Icc a b, riemannZeta (g x) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg P Q u))
      = argVariation a b (fun x : ℝ ↦ riemannZeta (g x)) := by
  rw [show (fun u : ℝ ↦ riemannZeta (lineSeg P Q u))
      = fun u : ℝ ↦ (fun x : ℝ ↦ riemannZeta (g x)) (a + u * (b - a)) from
    funext fun u ↦ by rw [hg u]]
  exact argVariation_comp hab zero_le_one (by fun_prop) (fun u hu ↦ mem_Icc_affine hab hu)
    (by ring) (by ring) hcont hne
private theorem argVariation_riemannZeta_lineSeg_symm {z₀ z₁ : ℂ}
    (hcont : ContinuousOn (fun u : ℝ ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc (0 : ℝ) 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannZeta (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₁ z₀ u))
      = - argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) := by
  have hfun : (fun u : ℝ ↦ riemannZeta (lineSeg z₁ z₀ u))
      = (fun u : ℝ ↦ (fun v : ℝ ↦ riemannZeta (lineSeg z₀ z₁ v)) (0 + 1 - u)) := by
    funext u; simp only; congr 1; simp only [lineSeg]; push_cast; ring
  rw [hfun]
  exact argVariation_reverse zero_le_one hcont hne
private theorem argVariation_riemannZeta_lineSeg_horizontal_rev {a b t : ℝ} (hab : a ≤ b)
    (ht : t ≠ 0) (hrowcont : Continuous fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
    (hne : ∀ σ ∈ Set.Icc a b, riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0) :
    argVariation 0 1
        (fun u ↦ riemannZeta (lineSeg ((b : ℂ) + I * (t : ℂ)) ((a : ℂ) + I * (t : ℂ)) u))
      = - argVariation a b (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
  have heq : ∀ u : ℝ, lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u
      = (((a + u * (b - a) : ℝ)) : ℂ) + I * (t : ℂ) := fun u ↦ by
    simp only [lineSeg]; push_cast; ring
  have hcont : ContinuousOn
      (fun u : ℝ ↦ riemannZeta (lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u))
      (Set.Icc 0 1) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp (continuous_lineSeg _ _).continuousOn
      (fun u _ ↦ by rw [heq u]; exact ofReal_add_I_mul_ne_one ht)
  have hne01 : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannZeta (lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u) ≠ 0 := fun u hu ↦ by
    rw [heq u]; exact hne _ (mem_Icc_affine hab hu)
  rw [argVariation_riemannZeta_lineSeg_symm hcont hne01,
    argVariation_riemannZeta_lineSeg_comp (g := fun σ : ℝ ↦ (σ : ℂ) + I * (t : ℂ)) hab heq
      hrowcont.continuousOn hne]
private theorem argVariation_riemannZeta_lineSeg_of_two_le_re {z₀ z₁ : ℂ}
    (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, 2 ≤ (lineSeg z₀ z₁ u).re) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u))
      = (riemannZeta z₁).arg - (riemannZeta z₀).arg := by
  have hcont : ContinuousOn (fun u : ℝ ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc 0 1) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp (continuous_lineSeg _ _).continuousOn
      fun u hu h1 ↦ by simpa [h1] using h u hu
  rw [argVariation_eq_arg_sub_arg zero_le_one hcont
    fun u hu ↦ riemannZeta_mem_slitPlane_of_two_le_re (h u hu), lineSeg_one, lineSeg_zero]
theorem tendsto_argVariation_riemannZeta_horizontal_atTop {t : ℝ} (ht : 0 < t)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0) :
    Tendsto (fun X : ℝ ↦ argVariation (1 / 2) X
        (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))))
      atTop (𝓝 (-(Real.pi * argZeta t))) := by
  have hrowcont : Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
    continuous_riemannZeta_horizontal ht.ne'
  have hpi : Real.pi * argZeta t = argVariationContourL riemannZeta t := by
    rw [argZeta, ← mul_assoc, mul_one_div, div_self Real.pi_ne_zero, one_mul]
  have hlim := (tendsto_argVariation_riemannZeta_vertical_atTop ht.le).sub_const
    (Real.pi * argZeta t)
  rw [zero_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  have hzero :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (2 : ℂ) (X : ℂ) u))
        + argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (X : ℂ) ((X : ℂ) + I * (t : ℂ)) u))
        + argVariation 0 1 (fun u ↦
            riemannZeta (lineSeg ((X : ℂ) + I * (t : ℂ)) ((2 : ℂ) + I * (t : ℂ)) u))
        + argVariation 0 1 (fun u ↦
            riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) (2 : ℂ) u)) = 0 := by
    have hsub : Rectangle (2 : ℂ) ((X : ℂ) + I * (t : ℂ)) ⊆ {s : ℂ | 1 < s.re} := fun ρ hρ ↦ by
      simp only [Rectangle, mem_reProdIm, mem_uIcc, show (2 : ℂ).re = 2 from by norm_num,
        show ((X : ℂ) + I * (t : ℂ)).re = X from by simp] at hρ
      rcases hρ.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact Set.mem_ofPred.mpr (by linarith)
    have hz0 := rectangleArgVariation_eq_zero_of_analyticOnNhd
      (fun s hs ↦ analyticOnNhd_riemannZeta_ne_one s (by rintro rfl; simp at hs))
      (fun _ hs ↦ riemannZeta_ne_zero_of_one_le_re hs.le) hsub
    rw [rectangleArgVariation] at hz0
    simpa [Complex.re_add_im, mul_comm] using hz0
  have hEb : argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (2 : ℂ) (X : ℂ) u)) = 0 := by
    rw [argVariation_riemannZeta_lineSeg_of_two_le_re (fun u hu ↦ by
        simp only [lineSeg_re, Complex.re_ofNat, Complex.ofReal_re]
        nlinarith [mul_nonneg hu.1 (by linarith : (0 : ℝ) ≤ X - 2)]),
      arg_riemannZeta_ofReal_eq_zero hX,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
      arg_riemannZeta_ofReal_eq_zero (le_refl 2), sub_self]
  have hEr0 :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (X : ℂ) ((X : ℂ) + I * (t : ℂ)) u))
      = argVariation 0 t (fun τ : ℝ ↦ riemannZeta ((X : ℂ) + I * (τ : ℂ))) :=
    argVariation_riemannZeta_lineSeg_comp (g := fun τ : ℝ ↦ (X : ℂ) + I * (τ : ℂ)) ht.le
      (fun u ↦ by simp only [lineSeg]; push_cast; ring)
      (continuous_riemannZeta_vertical (by rintro rfl; norm_num at hX)).continuousOn
      (fun τ _ ↦ riemannZeta_ne_zero_of_one_le_re (by simpa using (by linarith : (1 : ℝ) ≤ X)))
  have hEt0 :
      argVariation 0 1
          (fun u ↦ riemannZeta (lineSeg ((X : ℂ) + I * (t : ℂ)) ((2 : ℂ) + I * (t : ℂ)) u))
      = - argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
    rw [show ((2 : ℂ) + I * (t : ℂ)) = (((2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num]
    exact argVariation_riemannZeta_lineSeg_horizontal_rev hX ht.ne' hrowcont
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  have hEl0 :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) (2 : ℂ) u))
      = - argVariation 0 1
          (fun u ↦ riemannZeta (lineSeg (2 : ℂ) ((2 : ℂ) + I * (t : ℂ)) u)) := by
    rw [argVariation_riemannZeta_lineSeg_of_two_le_re (fun u _ ↦ by norm_num [lineSeg_re]),
      argVariation_riemannZeta_lineSeg_of_two_le_re (fun u _ ↦ by norm_num [lineSeg_re]), neg_sub]
  have hAsplit : argVariation (1 / 2) X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
      = argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
        + argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
    argVariation_trans (by norm_num) hX hrowcont.continuousOn
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  have hAlow :
      argVariation 0 1
          (fun u ↦
            riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) ((1 / 2 : ℂ) + I * (t : ℂ)) u))
      = - argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
    rw [show ((2 : ℂ) + I * (t : ℂ)) = (((2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num,
      show ((1 / 2 : ℂ) + I * (t : ℂ)) = (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num]
    exact argVariation_riemannZeta_lineSeg_horizontal_rev (by norm_num) ht.ne' hrowcont
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  rw [hEb, hEr0, hEt0, hEl0] at hzero
  rw [hpi, argVariationContourL]
  linarith [hzero, hAsplit, hAlow]
private theorem abs_arg_le_arcsin_of_norm_sub_one_le {w : ℂ} {δ : ℝ}
    (hw : ‖w - 1‖ ≤ δ) (hδ : δ < 1) : |w.arg| ≤ Real.arcsin δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hw
  have hre1 : |(w - 1).re| ≤ δ := (Complex.abs_re_le_norm _).trans hw
  rw [Complex.sub_re, Complex.one_re, abs_le] at hre1
  have hre : 0 < w.re := by linarith [hre1.1]
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr (by rintro rfl; simp at hre)
  have e3 : (w.re - 1) ^ 2 + w.im ^ 2 ≤ δ ^ 2 := by
    have he : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]; ring
    linarith [pow_le_pow_left₀ (norm_nonneg _) hw 2, he]
  have e1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1d : (0 : ℝ) ≤ 1 - δ ^ 2 := by nlinarith [hδ0, hδ]
  have habs : -(δ * ‖w‖) ≤ w.im ∧ w.im ≤ δ * ‖w‖ :=
    abs_le_of_sq_le_sq' (by
      rw [mul_pow, e1]
      nlinarith [e3, h1d, sq_nonneg (w.re - 1 + δ ^ 2), mul_nonneg h1d
        (by nlinarith [e3] : (0 : ℝ) ≤ δ ^ 2 - (w.re - 1) ^ 2 - w.im ^ 2)]) (by positivity)
  rw [Complex.arg_of_re_nonneg hre.le, abs_le, ← Real.arcsin_neg]
  exact ⟨Real.arcsin_le_arcsin (by rw [le_div_iff₀ hnorm]; linarith [habs.1]),
    Real.arcsin_le_arcsin (by rw [div_le_iff₀ hnorm]; linarith [habs.2])⟩
private theorem integrable_logDeriv_riemannZeta_box {a b c d : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hcd : c ≤ d) :
    Integrable (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ)))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))) := by
  have hfun : (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ))) ∘
      ⇑Complex.measurableEquivRealProd = logDeriv riemannZeta := funext fun z ↦ by
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply]
    rw [mul_comm I (z.im : ℂ), Complex.re_add_im]
  have hset : Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d)
      = Rectangle ((a : ℂ) + I * (c : ℂ)) ((b : ℂ) + I * (d : ℂ)) := by
    ext z
    simp [Rectangle, Complex.mem_reProdIm, Set.uIcc_of_le hab, Set.uIcc_of_le hcd,
      and_and_and_comm]
  rw [Measure.prod_restrict]
  change IntegrableOn (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ)))
    (Set.Icc a b ×ˢ Set.Icc c d) volume
  rw [← Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
        Complex.measurableEquivRealProd.measurableEmbedding, hfun, hset]
  exact integrableOn_logDeriv_riemannZeta_rectangle (by simpa using hc)
    (by simpa using hc.trans_le hcd)
theorem abs_argVariation_riemannZeta_horizontal_le {X t : ℝ} (hX : 2 ≤ X) (ht : t ≠ 0)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    |argVariation (1 / 2) X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  have hrowcont : Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) :=
    continuous_riemannZeta_horizontal ht
  have hhead : |argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
    rw [argVariation_riemannZeta_horizontal_eq_im_integral (by norm_num) ht
      (fun σ hσ ↦ hne σ hσ.1)]
    exact (Complex.abs_im_le_norm _).trans
      (intervalIntegral.norm_integral_le_integral_norm (by norm_num))
  have htail : |argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1) := by
    have hb : ∀ σ : ℝ, 2 ≤ σ →
        |(riemannZeta ((σ : ℂ) + I * t)).arg| ≤ Real.arcsin (Real.pi ^ 2 / 6 - 1) :=
      fun σ hσ ↦ abs_arg_le_arcsin_of_norm_sub_one_le
        (norm_riemannZeta_sub_one_le_of_two_le_re (by simpa using hσ))
        (by nlinarith [Real.pi_lt_d2, Real.pi_pos])
    rw [argVariation_eq_arg_sub_arg hX hrowcont.continuousOn (fun σ hσ ↦
      riemannZeta_mem_slitPlane_of_two_le_re (by simpa using hσ.1))]
    exact (abs_sub _ _).trans (by linarith [hb X (by linarith), hb 2 le_rfl])
  rw [argVariation_trans (by norm_num) hX hrowcont.continuousOn (fun σ hσ ↦ hne σ hσ.1)]
  exact (abs_add_le _ _).trans (by linarith [hhead, htail])
theorem integrableOn_argVariation_riemannZeta_horizontal_bound {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) :
    IntegrableOn (fun t : ℝ ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
      + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖) (Icc t₁ t₂) := by
  have hbox := integrable_logDeriv_riemannZeta_box (by norm_num : (1 / 2 : ℝ) ≤ 2) ht1 h12
  refine continuous_const.continuousOn.integrableOn_Icc.add
    ((hbox.swap.integral_norm_prod_left).congr (Filter.Eventually.of_forall fun t ↦ ?_))
  simp only [Function.comp_apply, Prod.swap_prod_mk,
    intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2),
    MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem tendsto_im_integral_logDeriv_row_atTop {t : ℝ} (ht : 0 < t)
    (hray : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    Tendsto (fun X : ℝ ↦ (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im)
      atTop (𝓝 (-(Real.pi * argZeta t))) := by
  refine (tendsto_argVariation_riemannZeta_horizontal_atTop ht hray).congr' ?_
  filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
  exact argVariation_riemannZeta_horizontal_eq_im_integral hX ht.ne' fun σ hσ ↦ hray σ hσ.1
private theorem abs_im_integral_logDeriv_row_le {X t : ℝ} (hX : 2 ≤ X) (ht : t ≠ 0)
    (hray : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    |(∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  rw [← argVariation_riemannZeta_horizontal_eq_im_integral (by linarith) ht
    fun σ hσ ↦ hray σ hσ.1]
  exact abs_argVariation_riemannZeta_horizontal_le hX ht hray
private theorem integrable_integral_logDeriv_riemannZeta_row {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    Integrable (fun t : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t))
      (volume.restrict (Set.Icc t₁ t₂)) := by
  have hbox := integrable_logDeriv_riemannZeta_box hX ht1 h12
  refine (hbox.swap.integral_prod_left).congr (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [Function.comp_apply, Prod.swap_prod_mk, intervalIntegral.integral_of_le hX,
    MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem integrable_integral_logDeriv_riemannZeta_col {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    Integrable (fun σ : ℝ ↦ ∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t))
      (volume.restrict (Set.Icc (1 / 2 : ℝ) X)) := by
  have hbox := integrable_logDeriv_riemannZeta_box hX ht1 h12
  refine (hbox.integral_prod_left).congr (Filter.Eventually.of_forall fun σ ↦ ?_)
  simp only [intervalIntegral.integral_of_le h12, MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem intervalIntegral_im {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℂ}
    (hF : Integrable F (volume.restrict (Icc a b))) :
    (∫ x in a..b, (F x).im) = (∫ x in a..b, F x).im := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_im (hF.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))
private theorem intervalIntegral₂_eq_setIntegral₂ {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (F : ℝ → ℝ → ℂ) :
    (∫ x in a..b, ∫ y in c..d, F x y) = ∫ x in Icc a b, ∫ y in Icc c d, F x y := by
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Icc fun x _ ↦ by
    rw [intervalIntegral.integral_of_le hcd, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
private theorem integral_log_norm_riemannZeta_sub_eq {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    (∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖))
      = -∫ t in t₁..t₂,
          (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hcongr : (∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖))
      = ∫ σ in (1 / 2 : ℝ)..X,
          -(∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr ((finite_re_riemannZeta_zeros_rectangle
      (z := (1 / 2 : ℂ) + I * (t₁ : ℂ)) (w := (X : ℂ) + I * (t₂ : ℂ)) (by simpa using ht1)
      (by simpa using ht1.trans_le h12)).measure_zero volume)] with σ hσ hσI
    rw [Set.uIoc_of_le hX] at hσI
    refine log_norm_riemannZeta_sub_eq_neg_im_integral h12 ht1 fun t ht hzero ↦
      hσ ⟨(σ : ℂ) + I * (t : ℂ), ⟨ofReal_add_I_mul_mem_rectangle (by simpa using hX)
        (by simpa using h12) (by simpa using (⟨hσI.1.le, hσI.2⟩ : σ ∈ Icc (1 / 2 : ℝ) X))
        (by simpa using ht), hzero⟩, by simp⟩
  have hpullσ := intervalIntegral_im hX (integrable_integral_logDeriv_riemannZeta_col ht1 h12 hX)
  have hpullt := intervalIntegral_im h12 (integrable_integral_logDeriv_riemannZeta_row ht1 h12 hX)
  have hswap : (∫ σ in (1 / 2 : ℝ)..X, ∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t))
      = ∫ t in t₁..t₂, ∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t) := by
    rw [intervalIntegral₂_eq_setIntegral₂ hX h12, intervalIntegral₂_eq_setIntegral₂ h12 hX]
    exact integral_integral_swap (integrable_logDeriv_riemannZeta_box hX ht1 h12)
  rw [hcongr, intervalIntegral.integral_neg]
  congr 1
  rw [hpullσ, hswap, ← hpullt]
private theorem ae_not_mem_im_riemannZeta_zeros {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (ht2 : 0 < t₂) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
        ∩ {ρ | riemannZeta ρ = 0}) :=
  compl_mem_ae_iff.mpr ((finite_im_riemannZeta_zeros_rectangle (by simpa using ht1)
    (by simpa using ht2)).measure_zero volume)
private theorem pos_and_ray_ne_zero_of_not_mem_im_zeros {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {t : ℝ} (htI : t ∈ Set.uIoc t₁ t₂)
    (htbad : t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
      ∩ {ρ | riemannZeta ρ = 0})) :
    0 < t ∧ ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0 := by
  rw [Set.uIoc_of_le h12] at htI
  have htIcc : t ∈ Set.Icc t₁ t₂ := Set.Ioc_subset_Icc_self htI
  exact ⟨by linarith [htIcc.1], riemannZeta_ray_ne_zero_of_not_mem_im_zeros h12 htIcc htbad⟩
private theorem aestronglyMeasurable_im_integral_row {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im)
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) :=
  ((integrable_integral_logDeriv_riemannZeta_row ht1 h12 hX).im).aestronglyMeasurable.mono_measure
    (Measure.restrict_mono (Set.uIoc_of_le h12 ▸ Set.Ioc_subset_Icc_self) le_rfl)
theorem intervalIntegrable_argZeta {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂) :
    IntervalIntegrable argZeta volume t₁ t₂ := by
  have ht2 : 0 < t₂ := lt_of_lt_of_le ht1 h12
  have h0T := ae_not_mem_im_riemannZeta_zeros ht1 ht2
  set bound : ℝ → ℝ := fun t ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
      + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
  set F : ℕ → ℝ → ℝ := fun n t ↦
    (∫ σ in (1 / 2 : ℝ)..((n : ℝ) + 1), logDeriv riemannZeta ((σ : ℂ) + I * t)).im
  have hFmeas : ∀ n, AEStronglyMeasurable (F n)
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) := fun n ↦
    aestronglyMeasurable_im_integral_row ht1 h12
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc t₁ t₂ →
      Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (-(Real.pi * argZeta t)))
        ∧ ‖-(Real.pi * argZeta t)‖ ≤ bound t := by
    filter_upwards [h0T] with t htbad htI
    obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12 htI htbad
    have htend : Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (-(Real.pi * argZeta t))) :=
      (tendsto_im_integral_logDeriv_row_atTop htpos hray).comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    refine ⟨htend, le_of_tendsto htend.norm ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact abs_im_integral_logDeriv_row_le
      (by exact_mod_cast Nat.add_one_le_iff.mpr (by lia)) htpos.ne' hray
  have hmeas : AEStronglyMeasurable (fun t ↦ -(Real.pi * argZeta t))
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop hFmeas ?_
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t ht htI using (ht htI).1
  have hbound_int : IntegrableOn bound (Set.uIoc t₁ t₂) volume :=
    Set.uIoc_of_le h12 ▸ (integrableOn_argVariation_riemannZeta_horizontal_bound ht1
      h12).mono_set Set.Ioc_subset_Icc_self
  have hdom : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)),
      ‖-(Real.pi * argZeta t)‖ ≤ bound t := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t ht htI using (ht htI).2
  have hfun : (fun t ↦ -(1 / Real.pi) * -(Real.pi * argZeta t)) = argZeta := funext fun t ↦ by
    rw [neg_mul_neg, ← mul_assoc, one_div_mul_cancel Real.pi_ne_zero, one_mul]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h12, ← Set.uIoc_of_le h12]
  exact hfun ▸ (Integrable.mono' hbound_int hmeas hdom).const_mul (-(1 / Real.pi))
theorem finite_setOf_riemannZeta_zero_ray_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    {t : ℝ | (∃ σ : ℝ, (1 / 2 : ℝ) ≤ σ ∧ riemannZeta ((σ : ℂ) + I * t) = 0)
      ∧ t ∈ Set.Icc a b}.Finite := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  refine Set.Finite.subset (finite_im_riemannZeta_zeros_rectangle
    (show (0 : ℝ) < ((1 / 2 : ℂ) + I * (a : ℂ)).im by simpa using ha)
    (show (0 : ℝ) < ((2 : ℂ) + I * (b : ℂ)).im by simpa using hb)) ?_
  rintro t ⟨⟨σ, hσ, hz⟩, htab⟩
  exact ⟨(σ : ℂ) + I * (t : ℂ), ⟨ofReal_add_I_mul_mem_rectangle_two hab hσ
    (re_le_one_of_riemannZeta_eq_zero hz) htab, hz⟩, by simp⟩
theorem pi_mul_integral_argZeta_eq_sub {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (ht1 : 0 < t₁)
    (hne1 : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0)
    (hne2 : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) :
    Real.pi * ∫ t in t₁..t₂, argZeta t
      = logNormZetaIntegral t₂ - logNormZetaIntegral t₁ := by
  have h12' : t₁ ≤ t₂ := h12.le
  have ht2 : 0 < t₂ := lt_trans ht1 h12
  have htr : ∀ t : ℝ, t ≠ 0 → (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      Tendsto (fun X : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X, Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖)
        atTop (𝓝 (logNormZetaIntegral t)) := fun t ht hne ↦ by
    simpa [logNormZetaIntegral] using intervalIntegral_tendsto_integral_Ioi (1 / 2)
      (integrableOn_log_norm_riemannZeta_Ioi ht hne) tendsto_id
  have hii : ∀ t : ℝ, t ≠ 0 → (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      ∀ X : ℝ, (1 / 2 : ℝ) ≤ X → IntervalIntegrable
        (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖) volume (1 / 2) X :=
    fun t ht hne X hX ↦ (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr
      ((integrableOn_log_norm_riemannZeta_Ioi ht hne).mono_set Set.Ioc_subset_Ioi_self)
  have hDtend : Tendsto (fun X : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖)) atTop
      (𝓝 (logNormZetaIntegral t₂ - logNormZetaIntegral t₁)) := by
    refine ((htr t₂ ht2.ne' hne2).sub (htr t₁ ht1.ne' hne1)).congr' ?_
    filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
    rw [intervalIntegral.integral_sub (hii t₂ ht2.ne' hne2 X hX) (hii t₁ ht1.ne' hne1 X hX)]
  have h0T := ae_not_mem_im_riemannZeta_zeros ht1 ht2
  have hDCT : Tendsto (fun X : ℝ ↦ ∫ t in t₁..t₂,
        (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im) atTop
      (𝓝 (∫ t in t₁..t₂, -(Real.pi * argZeta t))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
      exact aestronglyMeasurable_im_integral_row ht1 h12' hX
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
      filter_upwards [h0T] with t htbad htI
      obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12' htI htbad
      rw [Real.norm_eq_abs]
      exact abs_im_integral_logDeriv_row_le hX htpos.ne' hray
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h12').mpr
        ((integrableOn_argVariation_riemannZeta_horizontal_bound ht1 h12').mono_set
          Set.Ioc_subset_Icc_self)
    · filter_upwards [h0T] with t htbad htI
      obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12' htI htbad
      exact tendsto_im_integral_logDeriv_row_atTop htpos hray
  have huniq : logNormZetaIntegral t₂ - logNormZetaIntegral t₁
      = -∫ t in t₁..t₂, -(Real.pi * argZeta t) :=
    tendsto_nhds_unique (hDtend.congr' (by
      filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
      exact integral_log_norm_riemannZeta_sub_eq ht1 h12' hX)) hDCT.neg
  rw [huniq, intervalIntegral.integral_neg, neg_neg, intervalIntegral.integral_const_mul]
end
end CountPort71
section CountPort72
section
open Complex Filter Topology MeasureTheory Set
theorem Real.sum_range_rpow_neg_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (1 - σ) / (1 - σ) + 1 := by
  have h1mσ : 0 < 1 - σ := by linarith
  have hcmp := (Real.antitoneOn_rpow_neg_Icc (a := 1) (b := 1 + (↑(N - 1) : ℝ)) hσ0.le
    one_pos).sum_le_integral
  have hcast : (1 : ℝ) + (↑(N - 1) : ℝ) = (N : ℝ) := by
    rw [Nat.cast_sub hN]; push_cast; ring
  rw [hcast] at hcmp
  have hint : ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ) = ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -σ)), Real.one_rpow,
      show -σ + 1 = 1 - σ by ring]
  rw [hint] at hcmp
  rw [Finset.sum_range_succ', Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσ0.ne'), add_zero]
  have inner : ∑ i ∈ Finset.range N, ((↑(i + 1) : ℝ)) ^ (-σ)
      = (∑ i ∈ Finset.range (N - 1), ((1 : ℝ) + ↑(i + 1)) ^ (-σ)) + 1 := by
    conv_lhs => rw [show N = (N - 1) + 1 by lia]
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      congr 1; push_cast; ring
    · norm_num
  rw [inner]
  calc (∑ i ∈ Finset.range (N - 1), ((1 : ℝ) + ↑(i + 1)) ^ (-σ)) + 1
      ≤ ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) + 1 := by linarith [hcmp]
    _ ≤ (N : ℝ) ^ (1 - σ) / (1 - σ) + 1 := by gcongr; linarith
private theorem add_mul_I_ne_one {σ t : ℝ} (ht : t ≠ 0) : (σ : ℂ) + (t : ℂ) * I ≠ 1 :=
  fun h ↦ ht (by simpa using congrArg Complex.im h)
private theorem abs_floor_bundle {t : ℝ} (ht : 3 < |t|) :
    0 < |t| ∧ 0 < ⌊|t|⌋₊ ∧ (⌊|t|⌋₊ : ℝ) ≤ |t| :=
  have htpos : (0 : ℝ) < |t| := by linarith
  ⟨htpos, Nat.floor_pos.mpr (by linarith), Nat.floor_le htpos.le⟩
private theorem norm_sum_one_div_cpow_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ |t| ^ (1 - σ) / (1 - σ) + |t| ^ (1 - σ) := by
  have σpos : 0 < σ := by linarith [hσ.1]
  have h1mσ : 0 < 1 - σ := by linarith [hσ.2]
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    rw [show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp]; exact σpos
  have hs_ne : (σ : ℂ) + (t : ℂ) * I ≠ 0 := fun h ↦ by rw [h] at hre; simp at hre
  have hsum_norm : ‖∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), (n : ℝ) ^ (-σ) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ ?_))
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.cast_zero]
      rw [Complex.zero_cpow hs_ne, div_zero, norm_zero, Real.zero_rpow (neg_ne_zero.mpr σpos.ne')]
    · rw [norm_div, norm_one, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  refine hsum_norm.trans ((Real.sum_range_rpow_neg_le σpos hσ.2 Npos).trans ?_)
  have hdiv : (⌊|t|⌋₊ : ℝ) ^ (1 - σ) / (1 - σ) ≤ |t| ^ (1 - σ) / (1 - σ) := by gcongr
  have h1L : (1 : ℝ) ≤ |t| ^ (1 - σ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ |t|) h1mσ.le
  linarith
private theorem norm_neg_cpow_one_sub_div_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1)
    (ht : 3 < |t|) :
    ‖-(⌊|t|⌋₊ : ℂ) ^ (1 - ((σ : ℂ) + (t : ℂ) * I)) / (1 - ((σ : ℂ) + (t : ℂ) * I))‖
      ≤ |t| ^ (1 - σ) * 2 := by
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  rw [norm_div, norm_neg, norm_natCast_cpow_of_pos Npos,
    show ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)).re = 1 - σ by simp]
  exact (UpperBnd_aux6 ht ⟨hσ.1, by linarith [hσ.2]⟩ (add_mul_I_ne_one (abs_pos.mp htpos))
    Npos N_le_t).1
private theorem norm_neg_cpow_neg_div_two_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1)
    (ht : 3 < |t|) :
    ‖-(⌊|t|⌋₊ : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) / 2‖ ≤ |t| ^ (1 - σ) := by
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  rw [norm_div, norm_neg, norm_natCast_cpow_of_pos Npos, RCLike.norm_ofNat,
    show (-((σ : ℂ) + (t : ℂ) * I)).re = -σ by simp]
  exact (UpperBnd_aux6 ht ⟨hσ.1, by linarith [hσ.2]⟩ (add_mul_I_ne_one (abs_pos.mp htpos))
    Npos N_le_t).2.1
private theorem norm_riemannZeta0_tail_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖((σ : ℂ) + (t : ℂ) * I) * ∫ x in Ioi (⌊|t|⌋₊ : ℝ),
        (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) + 1)‖ ≤ 16 * |t| ^ (1 - σ) := by
  have σpos : 0 < σ := by linarith [hσ.1]
  have hσ2 : σ ≤ 2 := by linarith [hσ.2]
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  have hpow : |t| * |t| ^ (-σ) = |t| ^ (1 - σ) := by
    rw [show (1 - σ : ℝ) = 1 + (-σ) by ring, Real.rpow_add htpos, Real.rpow_one]
  refine (ZetaBnd_aux1 ⌊|t|⌋₊ Npos ⟨σpos, hσ2⟩ (by linarith : (2 : ℝ) ≤ |t|)).trans ?_
  rw [mul_div_assoc]
  refine (mul_le_mul_of_nonneg_left
    (UpperBnd_aux6 ht ⟨hσ.1, hσ2⟩ (add_mul_I_ne_one (abs_pos.mp htpos)) Npos N_le_t).2.2
    (by positivity)).trans (le_of_eq ?_)
  rw [show |t| ^ (1 - σ) = |t| * |t| ^ (-σ) from hpow.symm]; ring
theorem norm_riemannZeta_le_of_mem_strip {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ 11 / (1 - σ) * |t| ^ (1 - σ) := by
  rw [mul_comm Complex.I (t : ℂ)]
  have h1mσ : 0 < 1 - σ := by linarith [hσ.2]
  have σpos : 0 < σ := by linarith [hσ.1]
  obtain ⟨htpos, Npos, -⟩ := abs_floor_bundle ht
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    rw [show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp]; exact σpos
  have hL : (0 : ℝ) < |t| ^ (1 - σ) := Real.rpow_pos_of_pos htpos _
  rw [← Zeta0EqZeta Npos hre (add_mul_I_ne_one (abs_pos.mp htpos))]
  refine le_trans (norm_add₄_le ..) ?_
  refine le_trans (add_le_add (add_le_add (add_le_add (norm_sum_one_div_cpow_le hσ ht)
    (norm_neg_cpow_one_sub_div_le hσ ht)) (norm_neg_cpow_neg_div_two_le hσ ht))
    (norm_riemannZeta0_tail_le hσ ht)) ?_
  have hscalar : 1 / (1 - σ) + 20 ≤ 11 / (1 - σ) := by
    rw [← sub_nonneg, show 11 / (1 - σ) - (1 / (1 - σ) + 20) = (20 * σ - 10) / (1 - σ) by
      field_simp; ring]
    exact div_nonneg (by linarith [hσ.1]) h1mσ.le
  calc |t| ^ (1 - σ) / (1 - σ) + |t| ^ (1 - σ) + |t| ^ (1 - σ) * 2 + |t| ^ (1 - σ)
        + 16 * |t| ^ (1 - σ)
      = (1 / (1 - σ) + 20) * |t| ^ (1 - σ) := by ring
    _ ≤ 11 / (1 - σ) * |t| ^ (1 - σ) := mul_le_mul_of_nonneg_right hscalar hL.le
private theorem intervalIntegrable_log_one_sub :
    IntervalIntegrable (fun σ : ℝ ↦ Real.log (1 - σ)) volume (1 / 2) 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := (1 / 2 : ℝ)) (b := 0)).comp_sub_left 1
  norm_num at h; exact h
private theorem intervalIntegrable_log_sub_one :
    IntervalIntegrable (fun σ : ℝ ↦ Real.log (σ - 1)) volume 1 2 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)).comp_sub_right 1
  norm_num at h; exact h
private theorem integral_strip_majorant (L : ℝ) :
    ∫ σ in (1 / 2 : ℝ)..1, (Real.log 11 + (1 - σ) * L - Real.log (1 - σ))
      = 1 / 2 * Real.log 11 + L / 8 + (1 / 2 * Real.log 2 + 1 / 2) := by
  have ii_const : IntervalIntegrable (fun _ : ℝ ↦ Real.log 11) volume (1 / 2) 1 :=
    intervalIntegrable_const
  have ii_lin : IntervalIntegrable (fun σ : ℝ ↦ (1 - σ) * L) volume (1 / 2) 1 :=
    Continuous.intervalIntegrable (by fun_prop) (1 / 2) 1
  have ii_log := intervalIntegrable_log_one_sub
  have hlin : ∫ σ in (1 / 2 : ℝ)..1, (1 - σ) * L = L / 8 := by
    rw [intervalIntegral.integral_mul_const]
    have hone : ∫ σ in (1 / 2 : ℝ)..1, (1 - σ) = 1 / 8 := by
      rw [intervalIntegral.integral_comp_sub_left (fun x ↦ x) 1, integral_id]
      norm_num
    rw [hone]; ring
  have hlog : ∫ σ in (1 / 2 : ℝ)..1, Real.log (1 - σ) = -(1 / 2 * Real.log 2) - 1 / 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun x ↦ Real.log x) 1, integral_log]
    rw [show (1 : ℝ) - 1 = 0 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      Real.log_div one_ne_zero two_ne_zero, Real.log_one]
    simp
  rw [intervalIntegral.integral_sub (ii_const.add ii_lin) ii_log,
    intervalIntegral.integral_add ii_const ii_lin, intervalIntegral.integral_const, hlin, hlog]
  simp only [smul_eq_mul]
  ring
theorem norm_riemannZeta_le_div_sub_one {σ t : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ σ / (σ - 1) := by
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * t with hs
  have hsre : s.re = σ := by simp [hs]
  have htail : ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    have h := norm_riemannZeta_sub_one_le (s := s) (by rw [hsre]; exact hσ)
    rwa [hsre] at h
  have hsum := Real.tsum_one_div_nat_add_two_rpow_le_inv_sub_one hσ
  have hnorm := norm_le_insert (1 : ℂ) (riemannZeta s)
  rw [norm_one, norm_sub_rev] at hnorm
  refine (by linarith [htail, hsum] : ‖riemannZeta s‖ ≤ 1 + 1 / (σ - 1)).trans (le_of_eq ?_)
  rw [eq_div_iff hσ1.ne']; field_simp; ring
private theorem integral_log_sub_log_sub_one :
    ∫ σ in (1 : ℝ)..2, (Real.log σ - Real.log (σ - 1)) = 2 * Real.log 2 := by
  have iiA : IntervalIntegrable (fun σ : ℝ ↦ Real.log σ) volume 1 2 :=
    intervalIntegral.intervalIntegrable_log'
  rw [intervalIntegral.integral_sub iiA intervalIntegrable_log_sub_one]
  have hA : ∫ σ in (1 : ℝ)..2, Real.log σ = 2 * Real.log 2 - 1 := by
    rw [integral_log, Real.log_one]; ring
  have hB : ∫ σ in (1 : ℝ)..2, Real.log (σ - 1) = -1 := by
    rw [intervalIntegral.integral_comp_sub_right (fun x ↦ Real.log x) 1]
    norm_num [integral_log, Real.log_one]
  rw [hA, hB]; ring
private theorem integrableOn_log_norm_riemannZeta_subset {t : ℝ} {S : Set ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (hS : S ⊆ Ioi (1 / 2 : ℝ)) :
    IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S :=
  (integrableOn_log_norm_riemannZeta_Ioi ht hzero).mono_set hS
private theorem logNormZetaIntegral_eq_add {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t
      = (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + ∫ σ in Ioi (4 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ := by
  have ig : ∀ {S : Set ℝ}, S ⊆ Ioi (1 / 2 : ℝ) →
      IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S :=
    fun hS ↦ integrableOn_log_norm_riemannZeta_subset ht hzero hS
  have ig_a := ig (S := Ioc (1 / 2 : ℝ) 1) Ioc_subset_Ioi_self
  have ig_Ioi1 := ig (S := Ioi (1 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  have ig_Ioi2 := ig (S := Ioi (2 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  have ig_b := ig (S := Ioc (1 : ℝ) 2) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_c := ig (S := Ioc (2 : ℝ) 4) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_d := ig (S := Ioi (4 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  rw [logNormZetaIntegral, ← Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 1 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_a ig_Ioi1,
    ← Ioc_union_Ioi_eq_Ioi (show (1 : ℝ) ≤ 2 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_b ig_Ioi2,
    ← Ioc_union_Ioi_eq_Ioi (show (2 : ℝ) ≤ 4 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_c ig_d]
  ring
private theorem integral_log_norm_riemannZeta_Ioc_half_one_le {t : ℝ} (ht : 3 < t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 1 / 2 * Real.log 11 + Real.log t / 8 + (1 / 2 * Real.log 2 + 1 / 2) := by
  have htpos : 0 < t := by linarith
  have ht3 : 3 < |t| := by rwa [abs_of_pos htpos]
  have hpos : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
    fun σ hσ ↦ norm_pos_iff.mpr (hzero σ hσ)
  have ig_a := integrableOn_log_norm_riemannZeta_subset (S := Ioc (1 / 2 : ℝ) 1) htpos.ne' hzero
    Ioc_subset_Ioi_self
  have hmaj : IntegrableOn
      (fun σ : ℝ ↦ Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ))
      (Ioc (1 / 2 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_const).add
      (Continuous.intervalIntegrable (by fun_prop) (1 / 2) 1)).sub intervalIntegrable_log_one_sub
  calc (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioc (1 / 2 : ℝ) 1, (Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ)) := by
        refine setIntegral_mono_on_ae ig_a hmaj measurableSet_Ioc ?_
        have hne1 : ∀ᵐ σ : ℝ, σ ≠ 1 := by rw [ae_iff]; simp
        filter_upwards [hne1] with σ hσ1 hσmem
        have hσIoo : σ ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hσmem.1, lt_of_le_of_ne hσmem.2 hσ1⟩
        have h1mσ : 0 < 1 - σ := by linarith [hσIoo.2]
        have hstrip := norm_riemannZeta_le_of_mem_strip hσIoo ht3
        rw [abs_of_pos htpos] at hstrip
        have hzpos := hpos σ (le_of_lt hσmem.1)
        have hlogexp : Real.log (11 / (1 - σ) * t ^ (1 - σ))
            = Real.log 11 - Real.log (1 - σ) + (1 - σ) * Real.log t := by
          rw [Real.log_mul (ne_of_gt (div_pos (by norm_num) h1mσ))
              (ne_of_gt (Real.rpow_pos_of_pos htpos _)),
            Real.log_div (by norm_num) (ne_of_gt h1mσ), Real.log_rpow htpos]
        calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
            ≤ Real.log (11 / (1 - σ) * t ^ (1 - σ)) := Real.log_le_log hzpos hstrip
          _ = Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ) := by rw [hlogexp]; ring
    _ = ∫ σ in (1 / 2 : ℝ)..1, (Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ)) :=
        (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = 1 / 2 * Real.log 11 + Real.log t / 8 + (1 / 2 * Real.log 2 + 1 / 2) :=
        integral_strip_majorant _
private theorem integral_log_norm_riemannZeta_Ioc_two_four_le {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 2 * Real.log (Real.pi ^ 2 / 6) := by
  have hpos : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
    fun σ hσ ↦ norm_pos_iff.mpr (hzero σ hσ)
  have ig_c := integrableOn_log_norm_riemannZeta_subset (S := Ioc (2 : ℝ) 4) ht hzero
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_m3 : IntegrableOn (fun _ : ℝ ↦ Real.log (Real.pi ^ 2 / 6)) (Ioc (2 : ℝ) 4) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    exact intervalIntegrable_const
  calc (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioc (2 : ℝ) 4, Real.log (Real.pi ^ 2 / 6) := by
        refine setIntegral_mono_on ig_c ig_m3 measurableSet_Ioc ?_
        intro σ hσmem
        have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
        have hb := norm_riemannZeta_sub_one_le_of_two_le_re
          (s := (σ : ℂ) + Complex.I * t) (by rw [hre]; linarith [hσmem.1])
        have hzle : ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ Real.pi ^ 2 / 6 := by
          have h := norm_sub_norm_le (riemannZeta ((σ : ℂ) + Complex.I * t)) 1
          rw [norm_one] at h
          linarith
        have hzpos := hpos σ (by linarith [hσmem.1])
        exact Real.log_le_log hzpos hzle
    _ = 2 * Real.log (Real.pi ^ 2 / 6) := by
        rw [← intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 4),
          intervalIntegral.integral_const]; norm_num
private theorem integral_log_norm_riemannZeta_Ioi_four_le {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioi (4 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ig_d := integrableOn_log_norm_riemannZeta_subset (S := Ioi (4 : ℝ)) ht hzero
    (Ioi_subset_Ioi (by norm_num))
  have ig_maj : IntegrableOn
      (fun σ : ℝ ↦ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))) (Ioi (4 : ℝ)) :=
    (Real.integrableOn_exp_neg_mul_Ioi hl2 4).const_mul _
  refine setIntegral_mono_on ig_d ig_maj measurableSet_Ioi ?_
  intro σ hσmem
  calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
      ≤ |Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖| := le_abs_self _
    _ ≤ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) :=
        abs_log_norm_riemannZeta_le_exp (le_of_lt hσmem)
theorem logNormZetaIntegral_le_of_middle {M₂ β₂ : ℝ} {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (hmid : (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        ≤ M₂ + β₂ * Real.log t) :
    logNormZetaIntegral t ≤
      (1 / 2 * Real.log 11 + (1 / 2 * Real.log 2 + 1 / 2) + M₂
        + (2 * Real.log (Real.pi ^ 2 / 6)
          + ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))))
        + (1 / 8 + β₂) * Real.log t := by
  have htpos : 0 < t := by nlinarith [Real.pi_pos]
  have ht3 : 3 < t := by nlinarith [Real.pi_gt_three]
  rw [logNormZetaIntegral_eq_add htpos.ne' hzero]
  linarith [integral_log_norm_riemannZeta_Ioc_half_one_le ht3 hzero, hmid,
    integral_log_norm_riemannZeta_Ioc_two_four_le htpos.ne' hzero,
    integral_log_norm_riemannZeta_Ioi_four_le htpos.ne' hzero]
theorem logNormZetaIntegral_le_elem {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤
      (1 / 2 * Real.log 11 + (1 / 2 * Real.log 2 + 1 / 2) + 2 * Real.log 2
        + (2 * Real.log (Real.pi ^ 2 / 6)
          + ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))))
        + 1 / 8 * Real.log t := by
  have htpos : 0 < t := by nlinarith [Real.pi_pos]
  have ig_b := integrableOn_log_norm_riemannZeta_subset (S := Ioc (1 : ℝ) 2) htpos.ne' hzero
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have hmid : (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 2 * Real.log 2 + 0 * Real.log t := by
    have hmaj : IntegrableOn (fun σ : ℝ ↦ Real.log σ - Real.log (σ - 1)) (Ioc (1 : ℝ) 2) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      exact intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_log_sub_one
    calc (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        ≤ ∫ σ in Ioc (1 : ℝ) 2, (Real.log σ - Real.log (σ - 1)) := by
          refine setIntegral_mono_on ig_b hmaj measurableSet_Ioc (fun σ hσmem ↦ ?_)
          have hσ1 : 1 < σ := hσmem.1
          have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
          have hzpos : 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
            norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact hσ1.le))
          have hζle := norm_riemannZeta_le_div_sub_one (t := t) hσ1
          calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
              ≤ Real.log (σ / (σ - 1)) := Real.log_le_log hzpos hζle
            _ = Real.log σ - Real.log (σ - 1) := Real.log_div (by linarith) (by linarith)
      _ = ∫ σ in (1 : ℝ)..2, (Real.log σ - Real.log (σ - 1)) :=
          (intervalIntegral.integral_of_le (by norm_num)).symm
      _ = 2 * Real.log 2 := integral_log_sub_log_sub_one
      _ = 2 * Real.log 2 + 0 * Real.log t := by ring
  linarith [logNormZetaIntegral_le_of_middle ht hzero hmid]
private theorem integral_exp_tail_eq :
    (∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
      = (Real.pi ^ 2 / 6 - 1) / (2 * Real.log 2) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have key : (∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
      = 8 * (Real.pi ^ 2 / 6 - 1) * ∫ σ in Ioi (4 : ℝ), Real.exp ((-Real.log 2) * σ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun σ _ ↦ ?_)
    simp only [neg_mul]
  rw [key, integral_exp_mul_Ioi (by linarith : -Real.log 2 < 0) 4]
  have hexp : Real.exp ((-Real.log 2) * 4) = 1 / 16 := by
    rw [show (-Real.log 2) * 4 = -(4 * Real.log 2) by ring, Real.exp_neg,
      show (4 : ℝ) * Real.log 2 = Real.log (2 ^ 4) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
    norm_num
  rw [hexp]; field_simp; ring
private theorem pi_sq_lt_d4 : Real.pi ^ 2 < 9.8697 := by
  nlinarith [Real.pi_lt_d6, Real.pi_pos]
private theorem log_eleven_le : Real.log 11 ≤ 3 * Real.log 2 + 3 / 8 := by
  have he : Real.log 11 = Real.log (2 ^ 3) + Real.log (11 / 8) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; norm_num
  rw [he, Real.log_pow]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 8 by norm_num)
  push_cast; linarith
private theorem log_pi_sq_div_six_lt : Real.log (Real.pi ^ 2 / 6) < 1 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have hsq : (Real.pi ^ 2 / 6) ^ 2 < Real.exp (1 / 2) ^ 2 := by
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [pow_two, ← Real.exp_add]; norm_num
    rw [h1]; nlinarith [pi_sq_lt_d4, Real.exp_one_gt_d9]
  exact lt_of_pow_lt_pow_left₀ 2 (Real.exp_pos _).le hsq
private theorem exp_tail_lt_half : (Real.pi ^ 2 / 6 - 1) / (2 * Real.log 2) < 1 / 2 := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pi_sq_lt_d4, Real.log_two_gt_d9]
theorem logNormZetaIntegral_le_five {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤ 5 + 1 / 8 * Real.log t := by
  refine (logNormZetaIntegral_le_elem ht hzero).trans ?_
  rw [integral_exp_tail_eq]
  linarith [log_eleven_le, log_pi_sq_div_six_lt, exp_tail_lt_half, Real.log_two_lt_d9]
end
end CountPort72
section CountPort73
section
open Complex Filter Topology Set MeasureTheory
open scoped Real
noncomputable def logNormGammaArchimedean (t σ : ℝ) : ℝ :=
  Real.log ‖(1 / 2 : ℂ) * (((σ : ℂ) + Complex.I * t) * (((σ : ℂ) + Complex.I * t) - 1)) *
    Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖
private lemma norm_ofReal_add_I_mul (a t : ℝ) :
    ‖(a : ℂ) + Complex.I * t‖ = Real.sqrt (a ^ 2 + t ^ 2) := by
  rw [mul_comm, Complex.norm_add_mul_I]
lemma archLine_ne_zero {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    (σ : ℂ) + Complex.I * t ≠ 0 := by
  intro h
  exact ht (by simpa using congrArg Complex.im h)
lemma archLine_sub_one_ne_zero {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    (σ : ℂ) + Complex.I * t - 1 ≠ 0 := by
  intro h
  exact ht (by simpa using congrArg Complex.im h)
private lemma Gammaℝ_archLine_ne_zero {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    Complex.Gammaℝ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_im_ne_zero (by simpa using ht)
private lemma archLine_div_two (σ t : ℝ) :
    ((σ : ℂ) + Complex.I * t) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring
private lemma archLine_div_two_ne_neg_natCast {t : ℝ} (ht : t ≠ 0) (σ : ℝ) (m : ℕ) :
    ((σ : ℂ) + Complex.I * t) / 2 ≠ -m := by
  intro hm
  rw [archLine_div_two] at hm
  apply ht
  have him := congrArg Complex.im hm
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.ofReal_re, Complex.neg_im, Complex.natCast_im, mul_one, mul_zero, zero_add,
    add_zero] at him
  linarith
private lemma norm_Gammaℝ_archLine (σ t : ℝ) :
    ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖ =
      Real.pi ^ (-σ / 2) * ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  simp [neg_div]
private lemma log_norm_Gammaℝ_archLine {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖ =
      -(σ / 2) * Real.log Real.pi + Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ := by
  have hpole := archLine_div_two_ne_neg_natCast ht σ
  rw [norm_Gammaℝ_archLine,
    Real.log_mul (by positivity) (norm_ne_zero_iff.2 (Complex.Gamma_ne_zero hpole)),
    Real.log_rpow Real.pi_pos]
  ring
private lemma logNormGammaArchimedean_eq {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    logNormGammaArchimedean t σ =
      Real.log (1 / 2) + Real.log ‖(σ : ℂ) + Complex.I * t‖ +
        Real.log ‖(σ : ℂ) + Complex.I * t - 1‖ +
        Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖ := by
  unfold logNormGammaArchimedean
  set z : ℂ := (σ : ℂ) + Complex.I * t with hz
  have hz_ne : ‖z‖ ≠ 0 := by rw [hz]; exact norm_ne_zero_iff.2 (archLine_ne_zero ht σ)
  have hz1_ne : ‖z - 1‖ ≠ 0 := by rw [hz]; exact norm_ne_zero_iff.2 (archLine_sub_one_ne_zero ht σ)
  have hG_ne : ‖Complex.Gammaℝ z‖ ≠ 0 := by
    rw [hz]; exact norm_ne_zero_iff.2 (Gammaℝ_archLine_ne_zero ht σ)
  have e : (1 / 2 : ℂ) * (z * (z - 1)) * Complex.Gammaℝ z =
      (1 / 2 : ℂ) * z * (z - 1) * Complex.Gammaℝ z := by ring
  rw [e, norm_mul, norm_mul, norm_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_ofNat]
  rw [h12, Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num) hz_ne) hz1_ne) hG_ne,
    Real.log_mul (mul_ne_zero (by norm_num) hz_ne) hz1_ne,
    Real.log_mul (by norm_num) hz_ne]
private lemma continuous_archFactor {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ (1 / 2 : ℂ) * (((σ : ℂ) + Complex.I * t) *
      (((σ : ℂ) + Complex.I * t) - 1)) * Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)) := by
  have hline : Continuous (fun σ : ℝ ↦ (σ : ℂ) + Complex.I * t) := by fun_prop
  have hdiv : Continuous (fun σ : ℝ ↦ ((σ : ℂ) + Complex.I * t) / 2) := hline.div_const 2
  have hndiv : Continuous (fun σ : ℝ ↦ -((σ : ℂ) + Complex.I * t) / 2) := hline.neg.div_const 2
  have hG : Continuous (fun σ : ℝ ↦ Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)) := by
    rw [continuous_iff_continuousAt]
    intro σ
    have hcpow : ContinuousAt
        (fun σ : ℝ ↦ (Real.pi : ℂ) ^ (-((σ : ℂ) + Complex.I * t) / 2)) σ :=
      (continuousAt_const_cpow (by exact_mod_cast Real.pi_ne_zero)).comp hndiv.continuousAt
    have hGamma : ContinuousAt
        (fun σ : ℝ ↦ Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)) σ :=
      ContinuousAt.comp (g := Complex.Gamma)
        (f := fun σ : ℝ ↦ ((σ : ℂ) + Complex.I * t) / 2)
        (Complex.differentiableAt_Gamma _ (archLine_div_two_ne_neg_natCast ht σ)).continuousAt
        hdiv.continuousAt
    simp only [Complex.Gammaℝ_def]
    exact hcpow.mul hGamma
  exact (continuous_const.mul (hline.mul (hline.sub continuous_const))).mul hG
lemma continuous_logNormGammaArchimedean {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ logNormGammaArchimedean t σ) := by
  rw [continuous_iff_continuousAt]
  intro σ
  have hne : (1 / 2 : ℂ) * (((σ : ℂ) + Complex.I * t) * (((σ : ℂ) + Complex.I * t) - 1)) *
      Complex.Gammaℝ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
    prefactor_ne_zero_of (archLine_ne_zero ht σ)
      (sub_ne_zero.mp (archLine_sub_one_ne_zero ht σ)) (Gammaℝ_archLine_ne_zero ht σ)
  exact (Real.continuousAt_log (by simpa using hne)).comp
    ((continuous_norm.comp (continuous_archFactor ht)).continuousAt)
lemma intervalIntegrable_logNormGammaArchimedean {t : ℝ} (ht : t ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun σ : ℝ ↦ logNormGammaArchimedean t σ) volume a b :=
  (continuous_logNormGammaArchimedean ht).intervalIntegrable a b
lemma intervalIntegral.Ioo_eq_comp_add_right (f : ℝ → ℝ) {a b s : ℝ} (hab : a ≤ b) :
    (∫ σ in Set.Ioo (a + s) (b + s), f σ) = ∫ x in a..b, f (x + s) := by
  rw [intervalIntegral.integral_comp_add_right f s,
    intervalIntegral.integral_of_le (by linarith : a + s ≤ b + s),
    integral_Ioc_eq_integral_Ioo]
private lemma hasDerivAt_log_norm_Gamma_archLine_half {t : ℝ} (_ht : t ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun u : ℝ ↦ Real.log ‖Complex.Gamma (((u : ℂ) + Complex.I * t) / 2)‖)
      (1 / 2 * (Complex.digamma (((σ : ℂ) + Complex.I * t) / 2)).re) σ := by
  have hpath : HasDerivAt (fun u : ℝ ↦ ((u : ℂ) + Complex.I * t) / 2) (1 / 2 : ℂ) σ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := σ)).add_const (Complex.I * t)).div_const 2
  have hzpos : 0 < (((σ : ℂ) + Complex.I * t) / 2).re := by
    rw [Complex.div_ofNat_re, show ((σ : ℂ) + Complex.I * t).re = σ by simp]; linarith
  simpa [Complex.mul_re] using Complex.hasDerivAt_log_norm_Gamma_comp hpath hzpos
private lemma half_re_digamma_archLine_ge {t : ℝ} (ht : 168 * Real.pi ≤ t)
    {u : ℝ} (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 9 / 2) :
    1 / 2 * Real.log (t / 2) - 1 / 10000 ≤
      1 / 2 * (Complex.digamma (((u : ℂ) + Complex.I * t) / 2)).re := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht504 : (504 : ℝ) ≤ t := by nlinarith
  have ht0 : 0 < t := by linarith
  set z : ℂ := ((u : ℂ) + Complex.I * t) / 2 with hz
  have hzre : z.re = u / 2 := by rw [hz, Complex.div_ofNat_re]; simp
  have h2z : 2 * z = (u : ℂ) + Complex.I * t := by rw [hz]; ring
  have hnorm_ge : t / 2 ≤ ‖z‖ := by
    have h : t ≤ Real.sqrt (u ^ 2 + t ^ 2) := by
      have := Real.sqrt_le_sqrt (show t ^ 2 ≤ u ^ 2 + t ^ 2 by nlinarith [sq_nonneg u])
      rwa [Real.sqrt_sq ht0.le] at this
    rw [hz, norm_div, Complex.norm_ofNat, le_div_iff₀ (by norm_num),
      mul_comm (Complex.I) (t : ℂ), Complex.norm_add_mul_I]
    linarith
  have hznpos : 0 < ‖z‖ := by linarith
  have hlogz : Real.log (t / 2) ≤ (Complex.log z).re := by
    rw [Complex.log_re]; exact Real.log_le_log (by linarith) hnorm_ge
  have hpole_le : ((2 * z)⁻¹).re ≤ u / t ^ 2 := by
    rw [h2z, show ((u : ℂ) + Complex.I * t) = ((u : ℂ) + (t : ℂ) * Complex.I) by ring,
      Complex.inv_re, Complex.normSq_add_mul_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    gcongr
    nlinarith [sq_nonneg u]
  set E : ℂ := Complex.digamma z - Complex.log z + (2 * z)⁻¹ with hE
  have hEbound := Complex.Stirling.norm_digamma_sub_log_le' (a := 1 / 4) (by norm_num) z
    (by rw [hzre]; linarith)
  rw [← hE, show ‖z‖ ^ (-(2 : ℤ)) = (‖z‖ ^ 2)⁻¹ by rw [zpow_neg]; norm_cast] at hEbound
  have hC₀ : 3 / (2 * π ^ 2 * (1 / 4)) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hzn2_le : (‖z‖ ^ 2)⁻¹ ≤ 4 / t ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hEre : -(3 / t ^ 2) ≤ E.re := by
    have h3 : (1 / 12 + 3 / (2 * π ^ 2 * (1 / 4))) * (‖z‖ ^ 2)⁻¹ ≤ 3 / t ^ 2 := by
      calc (1 / 12 + 3 / (2 * π ^ 2 * (1 / 4))) * (‖z‖ ^ 2)⁻¹
          ≤ 3 / 4 * (4 / t ^ 2) := mul_le_mul (by linarith) hzn2_le (by positivity) (by norm_num)
        _ = 3 / t ^ 2 := by ring
    linarith [neg_abs_le E.re, Complex.abs_re_le_norm E, hEbound, h3]
  have hψre : (Complex.digamma z).re = (Complex.log z).re - ((2 * z)⁻¹).re + E.re := by
    rw [hE]; simp only [Complex.add_re, Complex.sub_re]; ring
  have htail : u / t ^ 2 + 3 / t ^ 2 ≤ 2 * (1 / 10000) := by
    rw [show u / t ^ 2 + 3 / t ^ 2 = (u + 3) / t ^ 2 by ring, div_le_iff₀ (by positivity)]
    nlinarith [ht504, hu2]
  linarith [hlogz, hpole_le, hEre, hψre, htail]
private lemma logNormGamma_half_diff_ge {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2) {t : ℝ}
    (ht : 168 * Real.pi ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    (d / 2) * Real.log (t / 2) - d / 10000 ≤
      Real.log ‖Complex.Gamma ((((σ + d : ℝ) : ℂ) + Complex.I * t) / 2)‖ -
        Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htne : t ≠ 0 := by nlinarith
  have hσd : σ ≤ σ + d := by linarith
  have hderiv : ∀ u ∈ Set.Icc σ (σ + d),
      HasDerivAt (fun v : ℝ ↦ Real.log ‖Complex.Gamma (((v : ℂ) + Complex.I * t) / 2)‖)
        (1 / 2 * (Complex.digamma (((u : ℂ) + Complex.I * t) / 2)).re) u :=
    fun u hu ↦ hasDerivAt_log_norm_Gamma_archLine_half htne (by linarith [hu.1])
  have hmvt := (convex_Icc σ (σ + d)).mul_sub_le_image_sub_of_le_deriv
    (f := fun v : ℝ ↦ Real.log ‖Complex.Gamma (((v : ℂ) + Complex.I * t) / 2)‖)
    (C := 1 / 2 * Real.log (t / 2) - 1 / 10000)
    (fun u hu ↦ (hderiv u hu).continuousAt.continuousWithinAt)
    (fun u hu ↦ (hderiv u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ by
      rw [interior_Icc, Set.mem_Ioo] at hu
      rw [(hderiv u ⟨hu.1.le, hu.2.le⟩).deriv]
      exact half_re_digamma_archLine_ge ht (by linarith [hu.1]) (by linarith [hu.2]))
    σ (Set.left_mem_Icc.2 hσd) (σ + d) (Set.right_mem_Icc.2 hσd) hσd
  beta_reduce at hmvt
  push_cast at hmvt ⊢
  nlinarith [hmvt]
lemma logNormGammaArchimedean_line_log_norm_diff_ge {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2)
    {t : ℝ} (ht : 2 ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    Real.log ‖(σ : ℂ) + Complex.I * t‖ ≤ Real.log ‖((σ : ℂ) + (d : ℂ)) + Complex.I * t‖ ∧
    -(1 / 2 * Real.log 2) ≤
      Real.log ‖((σ : ℂ) + (d : ℂ)) + Complex.I * t - 1‖ -
        Real.log ‖(σ : ℂ) + Complex.I * t - 1‖ := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht2pos : (0 : ℝ) < t ^ 2 := pow_pos ht0 2
  refine ⟨?_, ?_⟩
  ·
    rw [show ((σ : ℂ) + (d : ℂ)) + Complex.I * t = ((σ + d : ℝ) : ℂ) + Complex.I * t by
        push_cast; ring, norm_ofReal_add_I_mul, norm_ofReal_add_I_mul]
    apply Real.log_le_log (Real.sqrt_pos.2 (by nlinarith [sq_nonneg σ]))
    apply Real.sqrt_le_sqrt
    nlinarith
  ·
    rw [show ((σ : ℂ) + (d : ℂ)) + Complex.I * t - 1 = ((σ + d - 1 : ℝ) : ℂ) + Complex.I * t by
        push_cast; ring,
      show (σ : ℂ) + Complex.I * t - 1 = ((σ - 1 : ℝ) : ℂ) + Complex.I * t by push_cast; ring,
      norm_ofReal_add_I_mul, norm_ofReal_add_I_mul, Real.log_sqrt (by positivity),
      Real.log_sqrt (by positivity)]
    have hlow : Real.log (t ^ 2) ≤ Real.log ((σ + d - 1) ^ 2 + t ^ 2) :=
      Real.log_le_log ht2pos (by nlinarith [sq_nonneg (σ + d - 1)])
    have hhigh : Real.log ((σ - 1) ^ 2 + t ^ 2) ≤ Real.log (2 * t ^ 2) := by
      apply Real.log_le_log (by nlinarith [sq_nonneg (σ - 1)])
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - (σ - 1))
          (by linarith : (0 : ℝ) ≤ 2 + (σ - 1)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ t - 2) (by linarith : (0 : ℝ) ≤ t + 2)]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hhigh
    rw [Real.log_pow] at hlow
    push_cast at hlow hhigh
    nlinarith [hlow, hhigh]
lemma logNormGammaArchimedean_diff_ge_tight {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2)
    {t : ℝ} (ht : 168 * Real.pi ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    (d / 2) * Real.log (t / 2) - (d / 2) * Real.log Real.pi - 1 / 2 * Real.log 2 - d / 10000 ≤
      logNormGammaArchimedean t (σ + d) - logNormGammaArchimedean t σ := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht2 : (2 : ℝ) ≤ t := by nlinarith
  have htne : t ≠ 0 := by nlinarith
  rw [logNormGammaArchimedean_eq htne (σ + d), logNormGammaArchimedean_eq htne σ,
    log_norm_Gammaℝ_archLine htne (σ + d), log_norm_Gammaℝ_archLine htne σ]
  push_cast
  obtain ⟨hE1, hE2⟩ := logNormGammaArchimedean_line_log_norm_diff_ge hd hd' ht2 hσ1 hσ2
  have hGamma := logNormGamma_half_diff_ge hd hd' ht hσ1 hσ2
  push_cast at hGamma
  nlinarith [hE1, hE2, hGamma]
private lemma logNormGammaArchimedean_strip_diff_ge_of_pointwise {d G : ℝ} (hd : 1 / 2 < d)
    {t : ℝ} (htne : t ≠ 0)
    (hpt : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 / 2 + d →
      G ≤ logNormGammaArchimedean t (σ + d) - logNormGammaArchimedean t σ) :
    d * G ≤
      (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
        ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ := by
  have hab : (1 / 2 : ℝ) ≤ 1 / 2 + d := by linarith
  have hshift : (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + d), logNormGammaArchimedean t (σ + d) := by
    rw [show (1 / 2 + 2 * d : ℝ) = (1 / 2 + d) + d by ring]
    exact intervalIntegral.Ioo_eq_comp_add_right
      (fun σ ↦ logNormGammaArchimedean t σ) (a := 1 / 2) (b := 1 / 2 + d) (s := d) hab
  have h1 : (∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), logNormGammaArchimedean t σ) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + d), logNormGammaArchimedean t σ := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Ioc_eq_integral_Ioo]
  rw [hshift, h1]
  have hint1 : IntervalIntegrable (fun σ : ℝ ↦ logNormGammaArchimedean t (σ + d)) volume
      (1 / 2) (1 / 2 + d) :=
    ((continuous_logNormGammaArchimedean htne).comp (by fun_prop)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun σ : ℝ ↦ logNormGammaArchimedean t σ) volume
      (1 / 2) (1 / 2 + d) := intervalIntegrable_logNormGammaArchimedean htne _ _
  rw [← intervalIntegral.integral_sub hint1 hint2]
  have hmono : (∫ _σ in (1 / 2 : ℝ)..(1 / 2 + d), G) ≤
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + d), (logNormGammaArchimedean t (σ + d) -
        logNormGammaArchimedean t σ) := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const (hint1.sub hint2)
    intro σ hσ
    rw [Set.mem_Icc] at hσ
    exact hpt σ hσ.1 hσ.2
  rwa [intervalIntegral.integral_const, smul_eq_mul,
    show (1 / 2 + d - 1 / 2 : ℝ) = d by ring] at hmono
theorem logNormGammaArchimedean_strip_diff_ge_tight {d : ℝ} (hd : 1 / 2 < d) (hd' : d ≤ 2) :
    ∀ t : ℝ, 168 * Real.pi ≤ t →
      (d ^ 2 / 2) * Real.log t -
          ((d ^ 2 / 2) * (Real.log 2 + Real.log Real.pi) + (d / 2) * Real.log 2 + d ^ 2 / 10000) ≤
        (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ := by
  intro t ht
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht504 : (504 : ℝ) ≤ t := by nlinarith
  have htne : t ≠ 0 := by linarith
  have key := logNormGammaArchimedean_strip_diff_ge_of_pointwise hd htne
    (fun σ hσ1 hσ2 ↦ logNormGammaArchimedean_diff_ge_tight (by linarith) hd' ht hσ1 hσ2)
  have hlogt : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div htne (by norm_num)]
  rw [hlogt] at key
  nlinarith [key]
end
end CountPort73
section CountPort74
section
open Complex Filter Topology MeasureTheory Set
open scoped Real
private lemma riemannXiZeros_im_ne_of_forall_riemannZeta_ne {t : ℝ}
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (i : RiemannXiZerosIndex) : (riemannXiZeros i).im ≠ t := by
  intro hi
  have key : ∀ ρ : ℂ, riemannXi ρ = 0 → ρ.im = t → (1 / 2 : ℝ) ≤ ρ.re → False :=
    fun ρ hξ hρ hge ↦ hzero ρ.re hge (by
      rw [show ((ρ.re : ℝ) : ℂ) + Complex.I * t = ρ from Complex.ext (by simp) (by simp [hρ])]
      exact riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)
  set ρ := riemannXiZeros i
  have hξ : riemannXi ρ = 0 := riemannXi_riemannXiZeros_eq_zero i
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with hge | hlt
  · exact key ρ hξ hi hge
  ·
    refine key (1 - starRingEnd ℂ ρ) (by rw [riemannXi_one_sub, riemannXi_conj, hξ, map_zero])
      (by simp [hi]) ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
private lemma log_norm_riemannXi_eq {t σ : ℝ} (htne : t ≠ 0) (hσ : 0 < σ)
    (hζ : riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    Real.log ‖riemannXi ((σ : ℂ) + Complex.I * t)‖
      = logNormGammaArchimedean t σ + Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ := by
  have hz0 : (σ : ℂ) + Complex.I * t ≠ 0 := archLine_ne_zero htne σ
  have hz1 : (σ : ℂ) + Complex.I * t ≠ 1 := sub_ne_zero.mp (archLine_sub_one_ne_zero htne σ)
  have hΓ : Complex.Gammaℝ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hσ)
  rw [riemannXi_eq_prefactor_mul hz0 hz1 hΓ, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr (prefactor_ne_zero_of hz0 hz1 hΓ))
      (norm_ne_zero_iff.mpr hζ)]
  rfl
private lemma continuousOn_log_norm_riemannZeta_Ici {t : ℝ} (htne : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    ContinuousOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      (Set.Ici (1 / 2)) := by
  refine continuousOn_log_norm_riemannZeta (fun σ _ h ↦ ?_) hzero
  have him : ((σ : ℂ) + Complex.I * t).im = t := by simp
  rw [h] at him; simp only [Complex.one_im] at him; exact htne him.symm
private lemma intervalIntegral_zero_shift_eq_Ioo (f : ℝ → ℝ) {s d b : ℝ} (hd : 0 ≤ d)
    (hb : s + d = b) : (∫ x in (0 : ℝ)..d, f (x + s)) = ∫ σ in Set.Ioo s b, f σ := by
  have h := intervalIntegral.Ioo_eq_comp_add_right f (a := 0) (b := d) (s := s) hd
  rw [zero_add, show d + s = b from by rw [← hb]; ring] at h
  exact h.symm
theorem le_logNormZetaIntegral_of_le {d κ Ca Cψ Ct : ℝ} (hd : 1 / 2 < d)
    (hκ : ∀ s : ℂ, (∀ i, s ≠ riemannXiZeros i) → (∀ i, s + d ≠ riemannXiZeros i) →
        ∑' i, (Real.log ‖s + ↑d - riemannXiZeros i‖ - Real.log ‖s - riemannXiZeros i‖)
          = Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖ - ↑d * κ)
    (hCa : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (d ^ 2 / 2) * Real.log t - Ca ≤
        (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ)
    (hCψ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      ∑' i, (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
        ≤ 1 / 2 * Real.log t + Cψ)
    (hCt : ∀ t : ℝ,
      (-Ct ≤ ∫ σ in Set.Ioi (1 / 2 + d), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) ∧
      (-Ct ≤ ∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d),
              Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖))
    {c : ℝ} (hc : 2 ≤ c) :
    ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤
        (c * d ^ 2 * Cψ + d ^ 2 * κ + 2 * Ct + Ca) + (c - 1) / 2 * d ^ 2 * Real.log t := by
  intro t ht hzero
  have hd0 : (0 : ℝ) < d := by linarith
  have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) ht)
  have ht_im : ∀ i, (riemannXiZeros i).im ≠ t :=
    riemannXiZeros_im_ne_of_forall_riemannZeta_ne hzero
  have hZc := continuousOn_log_norm_riemannZeta_Ici htne hzero
  have hg := integrableOn_log_norm_riemannZeta_Ioi htne hzero
  have hCa' := hCa t ht
  have hCt1 := (hCt t).1
  have hCt2 := (hCt t).2
  set Z : ℝ → ℝ := fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ with hZdef
  set A : ℝ → ℝ := fun σ : ℝ ↦ logNormGammaArchimedean t σ with hAdef
  have hsplit : Set.EqOn (fun x ↦ ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x)
      (fun x ↦ A (x + (1 / 2 + d)) + Z (x + (1 / 2 + d)) - (A (x + 1 / 2) + Z (x + 1 / 2))
        - d * κ) (Set.uIcc 0 d) := by
    intro x hx
    rw [Set.uIcc_of_le hd0.le, Set.mem_Icc] at hx
    have hne : ∀ y : ℂ, y.im = t → ∀ i, y ≠ riemannXiZeros i := fun y hy i h ↦ ht_im i (h ▸ hy)
    have key : ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x
        = Real.log ‖riemannXi ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ))‖
          - Real.log ‖riemannXi ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I)‖ - d * κ := by
      rw [← hκ _ (hne _ (by simp)) (hne _ (by simp))]
      exact tsum_congr fun i ↦ by rw [shiftLogIntegrand]
    simp only [hZdef, hAdef]
    rw [key,
      show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)
          = (((x + (1 / 2 + d) : ℝ) : ℂ) + Complex.I * t) from by push_cast; ring,
      show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I = (((x + 1 / 2 : ℝ) : ℂ) + Complex.I * t) from by
        push_cast; ring,
      log_norm_riemannXi_eq htne (by linarith [hx.1] : (0 : ℝ) < x + (1 / 2 + d))
        (hzero _ (by linarith [hx.1])),
      log_norm_riemannXi_eq htne (by linarith [hx.1] : (0 : ℝ) < x + 1 / 2)
        (hzero _ (by linarith [hx.1]))]
  have iA : ∀ s : ℝ, IntervalIntegrable (fun x ↦ A (x + s)) volume 0 d := fun s ↦
    ((continuous_logNormGammaArchimedean htne).comp (by fun_prop)).intervalIntegrable 0 d
  have iZ : ∀ s : ℝ, 1 / 2 ≤ s → IntervalIntegrable (fun x ↦ Z (x + s)) volume 0 d := fun s hs ↦ by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hd0.le]
    exact hZc.comp (by fun_prop) fun x hx ↦ by
      simp only [Set.mem_Icc] at hx; simp only [Set.mem_Ici]; linarith [hx.1]
  have eA1 := intervalIntegral_zero_shift_eq_Ioo A (s := 1 / 2) hd0.le rfl
  have eA2 := intervalIntegral_zero_shift_eq_Ioo A (s := 1 / 2 + d) (b := 1 / 2 + 2 * d) hd0.le
    (by ring)
  have eZ1 := intervalIntegral_zero_shift_eq_Ioo Z (s := 1 / 2) hd0.le rfl
  have eZ2 := intervalIntegral_zero_shift_eq_Ioo Z (s := 1 / 2 + d) (b := 1 / 2 + 2 * d) hd0.le
    (by ring)
  have hIeq : (∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x)
      = ((∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), A σ)
            - ∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), A σ)
        + ((∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), Z σ)
            - ∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), Z σ) - d ^ 2 * κ := by
    have j1 := (iA (1 / 2)).add (iZ (1 / 2) le_rfl)
    have j2 := (iA (1 / 2 + d)).add (iZ (1 / 2 + d) (by linarith))
    rw [intervalIntegral.integral_congr hsplit,
      intervalIntegral.integral_sub (j2.sub j1) intervalIntegrable_const,
      intervalIntegral.integral_sub j2 j1,
      intervalIntegral.integral_add (iA (1 / 2 + d)) (iZ (1 / 2 + d) (by linarith)),
      intervalIntegral.integral_add (iA (1 / 2)) (iZ (1 / 2) le_rfl),
      intervalIntegral.integral_const, eA2, eZ2, eA1, eZ1]
    simp only [smul_eq_mul, sub_zero]
    ring
  have hSb : ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      ≤ c / 2 * d ^ 2 * Real.log t + c * d ^ 2 * Cψ := by
    have h := (integral_tsum_log_norm_shift_le_of hd ht_im hc).trans
      (mul_le_mul_of_nonneg_left (hCψ t ht) (mul_nonneg (by linarith : (0 : ℝ) ≤ c) (sq_nonneg d)))
    linarith [h]
  rw [tsum_shiftLogIntegral_eq_intervalIntegral_tsum hd ht_im, hIeq] at hSb
  have hIt : logNormZetaIntegral t
      = (∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), Z σ) + ∫ σ in Set.Ioi (1 / 2 + d), Z σ := by
    simp only [hZdef, logNormZetaIntegral]
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 1 / 2 + d by linarith),
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hg.mono_set Set.Ioc_subset_Ioi_self) (hg.mono_set (Set.Ioi_subset_Ioi (by linarith))),
      integral_Ioc_eq_integral_Ioo]
  rw [hIt]
  nlinarith [hSb, hCa', hCt1, hCt2]
end
end CountPort74
section CountPort75
section
open Complex Filter Topology MeasureTheory Set
open scoped Real
theorem norm_integral_argZeta_le_of_bounds' {a₁ a₂ b₁ b₂ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb : b₁ + b₂ ≤ 0.128 * Real.pi)
    (ha₁ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      logNormZetaIntegral t ≤ a₁ + b₁ * Real.log t)
    (ha₂ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ a₂ + b₂ * Real.log t) :
    ∀ t₁ t₂ : ℝ, 168 * Real.pi < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t|
        ≤ ((a₁ + a₂) + (b₁ + b₂) * Real.log (2 * Real.pi)) / Real.pi
          + 0.128 * Real.log (t₂ / (2 * Real.pi)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  intro t₁ t₂ ht1 h12 hne1 hne2
  have ht1pos : 0 < t₁ := lt_trans (by positivity) ht1
  have ht2' : 168 * Real.pi ≤ t₂ := ht1.le.trans h12.le
  have hlogeq : Real.log t₂ = Real.log (t₂ / (2 * Real.pi)) + Real.log (2 * Real.pi) := by
    rw [Real.log_div (ht1pos.trans h12).ne' (by positivity)]; ring
  have hLpos : 0 ≤ Real.log (t₂ / (2 * Real.pi)) :=
    Real.log_nonneg <| (one_le_div (by positivity)).2 <| by nlinarith
  have hlogmono := Real.log_le_log ht1pos h12.le
  have hm₁ := mul_le_mul_of_nonneg_left hlogmono hb₁
  have hm₂ := mul_le_mul_of_nonneg_left hlogmono hb₂
  have hmul := mul_le_mul_of_nonneg_right hb hLpos
  have e1 : Real.pi * |∫ t in t₁..t₂, argZeta t|
      = |logNormZetaIntegral t₂ - logNormZetaIntegral t₁| := by
    rw [← pi_mul_integral_argZeta_eq_sub h12 ht1pos hne1 hne2, abs_mul, abs_of_pos hπ]
  refine le_of_mul_le_mul_left ?_ hπ
  rw [e1, mul_add, mul_div_cancel₀ _ hπ.ne', abs_le]
  constructor <;>
    nlinarith [ha₁ t₁ ht1.le hne1, ha₁ t₂ ht2' hne2, ha₂ t₁ ht1.le hne1, ha₂ t₂ ht2' hne2]
end
end CountPort75
section CountPort76
section
open Complex Filter Topology Function Set
private lemma summable_and_riemannZeta_ofReal_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-σ)) ∧
      riemannZeta (σ : ℂ) = ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
  have hneg : (-σ : ℝ) < -1 := by linarith
  refine ⟨?_, ?_⟩
  · refine ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hneg)).congr (fun n ↦ ?_)
    rw [Nat.cast_add, Nat.cast_one]
  · rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hσ), Complex.ofReal_tsum]
    refine tsum_congr (fun n ↦ ?_)
    have hbase : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.rpow_neg hbase, Complex.ofReal_inv, Complex.ofReal_cpow hbase, one_div]
    push_cast
    ring
private lemma integral_Ioi_rpow_le_tsum_shift {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    ((k : ℝ) + 1) ^ (1 - σ) / (σ - 1) ≤ ∑' n : ℕ, (((n + k : ℕ) : ℝ) + 1) ^ (-σ) := by
  have hneg : (-σ : ℝ) < -1 := by linarith
  have hb : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  obtain ⟨hsum, -⟩ := summable_and_riemannZeta_ofReal_eq_tsum hσ
  set a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) ^ (-σ) with ha
  have hintval : ∫ x in Set.Ioi ((k : ℝ) + 1), x ^ (-σ) = ((k : ℝ) + 1) ^ (1 - σ) / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt hneg hb, show (-σ + 1 : ℝ) = -(σ - 1) by ring, neg_div_neg_eq,
      show (-(σ - 1) : ℝ) = 1 - σ by ring]
  rw [← hintval]
  refine Real.integral_Ioi_le_tsum_of_window k hsum (integrableOn_Ioi_rpow_of_lt hneg hb)
    fun N ↦ (Real.antitoneOn_rpow_neg_Icc (a := (k : ℝ) + 1) (b := (k : ℝ) + 1 + (N : ℝ))
      (by linarith) hb).integral_le_sum.trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
  show ((k : ℝ) + 1 + (i : ℝ)) ^ (-σ) = a (i + k)
  simp only [ha]; congr 1; push_cast; ring
theorem one_div_sub_one_le_riemannZeta_ofReal {σ : ℝ} (hσ : 1 < σ) :
    1 / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re := by
  obtain ⟨-, hzeq⟩ := summable_and_riemannZeta_ofReal_eq_tsum hσ
  rw [hzeq, Complex.ofReal_re]
  simpa using integral_Ioi_rpow_le_tsum_shift hσ 0
theorem riemannZeta_ofReal_ge_sharp {σ : ℝ} (hσ : 1 < σ) :
    1 + 2 ^ (-σ) + 3 ^ (-σ) + 4 ^ (1 - σ) / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re := by
  obtain ⟨hsum, hzeq⟩ := summable_and_riemannZeta_ofReal_eq_tsum hσ
  set a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) ^ (-σ) with ha
  rw [hzeq, Complex.ofReal_re]
  have htail : (4 : ℝ) ^ (1 - σ) / (σ - 1) ≤ ∑' n, a (n + 3) := by
    have h := integral_Ioi_rpow_le_tsum_shift hσ 3
    rw [show ((3 : ℕ) : ℝ) + 1 = 4 by norm_num] at h
    simpa [ha] using h
  have hfirst : (∑ i ∈ Finset.range 3, a i) = 1 + 2 ^ (-σ) + 3 ^ (-σ) := by
    simp only [ha, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Real.one_rpow]
  rw [(hsum.sum_add_tsum_nat_add 3).symm, hfirst]
  linarith [htail]
section Digamma
open Complex.Stirling MeasureTheory
open scoped Nat Real
end Digamma
open scoped LSeries.notation
open ArithmeticFunction
open scoped Real
private noncomputable def negZetaDerivAntideriv (σ x : ℝ) : ℝ :=
  -(1 / (σ - 1)) * (x ^ (1 - σ) * Real.log x) - (1 / (σ - 1) ^ 2) * x ^ (1 - σ)
private lemma hasDerivAt_negZetaDerivAntideriv {σ : ℝ} (hσ : 1 < σ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (negZetaDerivAntideriv σ) (Real.log x * x ^ (-σ)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hc : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
  have hA : HasDerivAt (fun y : ℝ ↦ y ^ (1 - σ)) ((1 - σ) * x ^ (1 - σ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have h1 : HasDerivAt (fun y : ℝ ↦ y ^ (1 - σ) * Real.log y)
      ((1 - σ) * x ^ (1 - σ - 1) * Real.log x + x ^ (1 - σ) * x⁻¹) x := hA.mul hlog
  have p1 : x ^ (1 - σ - 1) = x ^ (-σ) := by rw [show (1 - σ - 1) = -σ by ring]
  have p2 : x ^ (1 - σ) * x⁻¹ = x ^ (-σ) := by
    rw [show x⁻¹ = x ^ (-1 : ℝ) from (Real.rpow_neg_one x).symm, ← Real.rpow_add hx,
      show (1 - σ + -1 : ℝ) = -σ by ring]
  rw [show Real.log x * x ^ (-σ)
      = -(1 / (σ - 1)) * ((1 - σ) * x ^ (1 - σ - 1) * Real.log x + x ^ (1 - σ) * x⁻¹)
        - 1 / (σ - 1) ^ 2 * ((1 - σ) * x ^ (1 - σ - 1)) from by rw [p1, p2]; field_simp; ring]
  exact (h1.const_mul (-(1 / (σ - 1)))).sub (hA.const_mul (1 / (σ - 1) ^ 2))
private lemma tendsto_negZetaDerivAntideriv {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (negZetaDerivAntideriv σ) atTop (𝓝 0) := by
  have hc : (0 : ℝ) < σ - 1 := by linarith
  have h1 : Tendsto (fun x : ℝ ↦ x ^ (1 - σ)) atTop (𝓝 0) := by
    simpa [show -(σ - 1) = 1 - σ by ring] using tendsto_rpow_neg_atTop hc
  have h2 : Tendsto (fun x : ℝ ↦ x ^ (1 - σ) * Real.log x) atTop (𝓝 0) := by
    refine ((isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show (1 - σ) = -(σ - 1) by ring, Real.rpow_neg hx.le, div_eq_mul_inv, mul_comm]
  have hcomb := (h2.const_mul (-(1 / (σ - 1)))).sub (h1.const_mul (1 / (σ - 1) ^ 2))
  rw [show (fun x : ℝ ↦ -(1 / (σ - 1)) * (x ^ (1 - σ) * Real.log x)
    - 1 / (σ - 1) ^ 2 * x ^ (1 - σ)) = negZetaDerivAntideriv σ from rfl] at hcomb
  simpa using hcomb
theorem neg_deriv_riemannZeta_ofReal_le {σ : ℝ} (hσ : 1 < σ) :
    (- deriv riemannZeta (σ : ℂ)).re ≤
      Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ)
        + 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) := by
  set f : ℝ → ℝ := fun x ↦ Real.log x * x ^ (-σ) with hf
  set b : ℕ → ℝ := fun n ↦ Real.log n * (n : ℝ) ^ (-σ) with hb
  have habs : LSeries.abscissaOfAbsConv 1 < ((σ : ℂ)).re := by
    rw [LSeries.abscissaOfAbsConv_one, Complex.ofReal_re]; exact_mod_cast hσ
  have hEv : riemannZeta =ᶠ[𝓝 (σ : ℂ)] LSeries 1 := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 < ((σ : ℂ)).re by rwa [Complex.ofReal_re])] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  have h1 : HasSum b (- deriv riemannZeta (σ : ℂ)).re := by
    have h0 : HasSum (LSeries.term (LSeries.logMul 1) (σ : ℂ)) (- deriv riemannZeta (σ : ℂ)) := by
      rw [hEv.deriv_eq, LSeries_deriv habs, neg_neg]
      exact (LSeriesSummable_logMul_of_lt_re habs).hasSum
    refine (Complex.hasSum_re h0).congr_fun fun n ↦ Eq.symm ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hb, LSeries.term]
    · have hnpos : 0 < (n : ℝ) := by positivity
      rw [LSeries.term_of_ne_zero hn]
      simp only [hb, LSeries.logMul, Pi.one_apply, mul_one]
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
          ← Complex.ofReal_log hnpos.le, ← Complex.ofReal_cpow hnpos.le,
          ← Complex.ofReal_div, Complex.ofReal_re, Real.rpow_neg hnpos.le, div_eq_mul_inv]
  have hbsum : Summable b := h1.summable
  rw [← h1.tsum_eq]
  have hlog3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hderivf : ∀ {x : ℝ}, 0 < x →
      HasDerivAt f (x⁻¹ * x ^ (-σ) + Real.log x * (-σ * x ^ (-σ - 1))) x := fun hx ↦
    (Real.hasDerivAt_log hx.ne').mul (Real.hasDerivAt_rpow_const (Or.inl hx.ne'))
  have hdf : ∀ x ∈ Set.Ici (3 : ℝ), DifferentiableAt ℝ f x := fun x hx ↦
    (hderivf (by simp only [Set.mem_Ici] at hx; linarith)).differentiableAt
  have hderiv_np : ∀ x ∈ Set.Ioi (3 : ℝ), deriv f x ≤ 0 := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hlogx : (1 : ℝ) < Real.log x := hlog3.trans_le (Real.log_le_log (by norm_num) hx.le)
    rw [(hderivf hxpos).deriv, show x⁻¹ * x ^ (-σ) = x ^ (-σ - 1) by
      rw [show x⁻¹ = x ^ (-1 : ℝ) from (Real.rpow_neg_one x).symm, ← Real.rpow_add hxpos,
        show (-1 + -σ : ℝ) = -σ - 1 by ring]]
    nlinarith [Real.rpow_pos_of_pos hxpos (-σ - 1), hlogx, hσ,
      mul_nonneg (by linarith : (0 : ℝ) ≤ σ - 1) (by linarith : (0 : ℝ) ≤ Real.log x - 1)]
  have hanti : AntitoneOn f (Set.Ici (3 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 3)
      (fun x hx ↦ (hdf x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hdf x (interior_subset hx)).differentiableWithinAt) ?_
    rw [interior_Ici]; exact hderiv_np
  have hcont : ContinuousWithinAt (negZetaDerivAntideriv σ) (Set.Ici 3) 3 :=
    (hasDerivAt_negZetaDerivAntideriv hσ (by norm_num)).continuousAt.continuousWithinAt
  have hderivF : ∀ x ∈ Set.Ioi (3 : ℝ), HasDerivAt (negZetaDerivAntideriv σ) (f x) x :=
    fun x hx ↦ hasDerivAt_negZetaDerivAntideriv hσ (by simp only [Set.mem_Ioi] at hx; linarith)
  have hfpos : ∀ x ∈ Set.Ioi (3 : ℝ), 0 ≤ f x := fun x hx ↦
    mul_nonneg (Real.log_nonneg (by simp only [Set.mem_Ioi] at hx; linarith))
      (Real.rpow_nonneg (by simp only [Set.mem_Ioi] at hx; linarith) _)
  have hlim := tendsto_negZetaDerivAntideriv hσ
  have htail : ∑' k, b (k + 4) ≤ (0 : ℝ) - negZetaDerivAntideriv σ 3 := by
    refine (Real.tsum_le_integral_Ioi_of_window 4 hbsum
        (MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderivF hfpos hlim)
        (fun N ↦ le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
          (hanti.mono Set.Icc_subset_Ici_self).sum_le_integral)).trans_eq
      (MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderivF hfpos hlim)
    simp only [hb, hf]
    rw [show ((i + 4 : ℕ) : ℝ) = 3 + ((i + 1 : ℕ) : ℝ) by push_cast; ring]
  have hfirst : (∑ i ∈ Finset.range 4, b i) = Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ) := by
    simp only [hb, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Real.log_zero]
  have hFval : (0 : ℝ) - negZetaDerivAntideriv σ 3
      = 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) := by
    simp only [negZetaDerivAntideriv]; ring
  rw [(hbsum.sum_add_tsum_nat_add 4).symm, hfirst]
  linarith [hFval ▸ htail]
private lemma log_three_le : Real.log 3 ≤ 1099 / 1000 := by
  linarith [Real.log_three_lt_d9]
private lemma tsum_norm_term_vonMangoldt_eq_and_pos {σ : ℝ} (hσ : 1 < σ) :
    ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖
        = (- deriv riemannZeta (σ : ℂ)).re * ((riemannZeta (σ : ℂ)).re)⁻¹ ∧
      0 < (riemannZeta (σ : ℂ)).re ∧ 0 ≤ (- deriv riemannZeta (σ : ℂ)).re := by
  set s : ℂ := (σ : ℂ) with hsdef
  have hs : 1 < s.re := by rw [hsdef, Complex.ofReal_re]; exact hσ
  have hnorm_re : ∀ n : ℕ, (LSeries.term ↗Λ s n).re = ‖LSeries.term ↗Λ s n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hnpos : 0 < (n : ℝ) := by positivity
      rw [show LSeries.term ↗Λ s n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) from by
            rw [LSeries.term_of_ne_zero hn, hsdef,
              show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
              ← Complex.ofReal_cpow hnpos.le, ← Complex.ofReal_div],
          Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg hnpos.le σ))]
  have hD : ∑' n, ‖LSeries.term ↗Λ s n‖ = (LSeries ↗Λ s).re :=
    ((Complex.hasSum_re (LSeriesSummable_vonMangoldt hs).hasSum).congr_fun
      (fun n ↦ (hnorm_re n).symm)).tsum_eq
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ s = (((1 / ((n : ℝ) + 1) ^ σ : ℝ)) : ℂ) := by
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one, hsdef, Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have hζim : (riemannZeta s).im = 0 := by
    rw [hsdef, zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [Complex.ofReal_re]; exact hσ),
        tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_im]
  have hσ1pos : (0 : ℝ) < σ - 1 := by linarith
  have hζpos : 0 < (riemannZeta s).re :=
    lt_of_lt_of_le (by positivity) (one_div_sub_one_le_riemannZeta_ofReal hσ)
  set r : ℝ := (riemannZeta s).re with hrdef
  have hζeq : riemannZeta s = (r : ℂ) :=
    Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im, hζim])
  have hDeq : ∑' n, ‖LSeries.term ↗Λ s n‖ = (- deriv riemannZeta s).re * r⁻¹ := by
    rw [hD, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hζeq, div_eq_mul_inv,
      ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  refine ⟨hDeq, hζpos, ?_⟩
  nlinarith [hDeq ▸ tsum_nonneg (fun n ↦ norm_nonneg (LSeries.term ↗Λ s n)), inv_pos.mpr hζpos]
private lemma rpow_pow_25 {x e : ℝ} (hx : 0 ≤ x) {k : ℕ} (he : e * (25 : ℕ) = -(k : ℕ)) :
    (x ^ e) ^ (25 : ℕ) = (x ^ k)⁻¹ := by
  rw [← Real.rpow_natCast (x ^ e) 25, ← Real.rpow_mul hx, he, Real.rpow_neg hx, Real.rpow_natCast]
private lemma inner_pole_bound_124 :
    Real.log 3 / ((124 / 100 : ℝ) - 1) + 1 / ((124 / 100 : ℝ) - 1) ^ 2 ≤ 439 / 20 := by
  rw [show Real.log 3 / ((124 / 100 : ℝ) - 1) + 1 / ((124 / 100 : ℝ) - 1) ^ 2
    = Real.log 3 * (25 / 6) + 625 / 36 by ring]
  linarith [log_three_le]
private lemma rpow_two_neg_124_ge : (42 / 100 : ℝ) ≤ (2 : ℝ) ^ (-(124 / 100) : ℝ) :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_three_neg_124_ge : (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (-(124 / 100) : ℝ) :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_four_one_sub_124_ge : (71 / 100 : ℝ) ≤ (4 : ℝ) ^ (1 - 124 / 100 : ℝ) :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [rpow_pow_25 (by norm_num)
      (show (1 - 124 / 100 : ℝ) * (25 : ℕ) = -(6 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_two_neg_124_le : (2 : ℝ) ^ (-(124 / 100) : ℝ) ≤ 43 / 100 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_three_neg_124_le : (3 : ℝ) ^ (-(124 / 100) : ℝ) ≤ 27 / 100 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma rpow_three_one_sub_124_le : (3 : ℝ) ^ (1 - 124 / 100 : ℝ) ≤ 77 / 100 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (1 - 124 / 100 : ℝ) * (25 : ℕ) = -(6 : ℕ) by push_cast; norm_num)]; norm_num)
private lemma riemannZeta_ofReal_124_ge :
    (462 / 100 : ℝ) ≤ (riemannZeta ((124 / 100 : ℝ) : ℂ)).re := by
  have h4div : (1775 / 600 : ℝ) ≤ (4 : ℝ) ^ (1 - 124 / 100 : ℝ) / ((124 / 100 : ℝ) - 1) := by
    rw [show ((124 / 100 : ℝ) - 1) = 6 / 25 by norm_num,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 6 / 25)]
    linarith [rpow_four_one_sub_124_ge]
  linarith [riemannZeta_ofReal_ge_sharp (σ := (124 / 100 : ℝ)) (by norm_num),
    rpow_two_neg_124_ge, rpow_three_neg_124_ge, h4div]
private lemma neg_deriv_riemannZeta_124_le :
    (- deriv riemannZeta ((124 / 100 : ℝ) : ℂ)).re ≤ 35 / 2 := by
  refine (neg_deriv_riemannZeta_ofReal_le (by norm_num : (1 : ℝ) < 124 / 100)).trans ?_
  have ht1 : Real.log 2 * 2 ^ (-(124 / 100) : ℝ) ≤ (6932 / 10000) * (43 / 100) :=
    mul_le_mul (by linarith [Real.log_two_lt_d9]) rpow_two_neg_124_le
      (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  have ht2 : Real.log 3 * 3 ^ (-(124 / 100) : ℝ) ≤ (1099 / 1000) * (27 / 100) :=
    mul_le_mul log_three_le rpow_three_neg_124_le (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  have ht3 : 3 ^ (1 - 124 / 100 : ℝ)
      * (Real.log 3 / ((124 / 100 : ℝ) - 1) + 1 / ((124 / 100 : ℝ) - 1) ^ 2)
      ≤ (77 / 100) * (439 / 20) :=
    mul_le_mul rpow_three_one_sub_124_le inner_pole_bound_124 (by positivity) (by norm_num)
  linarith [ht1, ht2, ht3]
theorem tsum_vonMangoldt_norm_le_124_sharp :
    ∑' n, ‖LSeries.term ↗Λ ((124 / 100 : ℝ) : ℂ) n‖ ≤ 379 / 100 := by
  obtain ⟨hDeq, hζpos, -⟩ :=
    tsum_norm_term_vonMangoldt_eq_and_pos (show (1 : ℝ) < 124 / 100 by norm_num)
  set A : ℝ := (- deriv riemannZeta ((124 / 100 : ℝ) : ℂ)).re with hAdef
  set r : ℝ := (riemannZeta ((124 / 100 : ℝ) : ℂ)).re with hrdef
  have hinvle : r⁻¹ ≤ 100 / 462 := by
    rw [show (100 / 462 : ℝ) = (462 / 100)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) riemannZeta_ofReal_124_ge
  rw [hDeq]
  calc A * r⁻¹ ≤ (35 / 2) * (100 / 462) :=
        mul_le_mul neg_deriv_riemannZeta_124_le hinvle (inv_pos.mpr hζpos).le (by norm_num)
    _ ≤ 379 / 100 := by norm_num
private lemma le_norm_of_im_eq {z : ℂ} {t : ℝ} (ht : 0 < t) (h : z.im = t) : t ≤ ‖z‖ := by
  simpa [h, abs_of_pos ht] using Complex.abs_im_le_norm z
private lemma re_digamma_shiftedLine_le {d t : ℝ} (hdlt : 1 / 2 < d) (hd1 : d ≤ 1)
    (ht : 168 * π ≤ t) :
    (Complex.digamma (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I) / 2)).re
      ≤ Real.log t - Real.log 2 + 2 / 100 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  obtain ⟨hsre, hsim, -, -, -, -, -, hsnorm_pos, hsnorm_ub⟩ := shiftedLine_setup hdlt ht0
  set s : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hsdef
  have hs_ge_t : t ≤ ‖s‖ := le_norm_of_im_eq ht0 hsim
  have hz : 0 < (s / 2).re := by rw [Complex.div_ofNat_re, hsre]; linarith
  have hnorm_half : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
  have hdig := re_digamma_le (C := 1) hz
    (by simpa using Complex.Stirling.norm_digammaRemainderIoi_le' (s / 2) hz 1 le_rfl)
  rw [show (1 / 2 + (1 : ℝ)) = 3 / 2 by norm_num] at hdig
  have hlog_half : Real.log ‖s / 2‖ ≤ Real.log t + (1 / 2 + d) / (168 * π) - Real.log 2 := by
    rw [hnorm_half, Real.log_div hsnorm_pos.ne' (by norm_num)]
    have h3 := Real.log_add_le (u := 1 / 2 + d) (t := t) (by linarith) ht0
    have h4 : (1 / 2 + d) / t ≤ (1 / 2 + d) / (168 * π) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) ht
    linarith [Real.log_le_log hsnorm_pos hsnorm_ub]
  have hfrac : (3 / 2 : ℝ) / ‖s / 2‖ ≤ 3 / (168 * π) := by
    rw [hnorm_half]
    calc (3 / 2 : ℝ) / (‖s‖ / 2) ≤ (3 / 2 : ℝ) / (t / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
      _ = 3 / t := by ring
      _ ≤ 3 / (168 * π) := div_le_div_of_nonneg_left (by norm_num) (by positivity) ht
  have htiny : (1 / 2 + d) / (168 * π) + 3 / (168 * π) ≤ 2 / 100 := by
    rw [← add_div, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  linarith
private lemma re_logDeriv_riemannZeta_le_of_re {s : ℂ} {σ D : ℝ} (hσ : 1 < s.re) (hsre : s.re = σ)
    (hVM : ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖ ≤ D) : (logDeriv riemannZeta s).re ≤ D := by
  refine (re_logDeriv_riemannZeta_le hσ).trans ?_
  rw [show (∑' n, ‖LSeries.term ↗Λ s n‖) = ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖ from
    tsum_congr fun n ↦ by rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre, Complex.ofReal_re]]
  exact hVM
theorem tsum_re_inv_riemannXiZeros_sub_le_tight_of {t D : ℝ} (ht : 168 * π ≤ t)
    (hVM : ∑' n, ‖LSeries.term ↗Λ ((124 / 100 : ℝ) : ℂ) n‖ ≤ D) :
    ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
      ≤ 1 / 2 * Real.log t + (D - 3 / 5) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have ht500 : (500 : ℝ) ≤ t := le_trans (by nlinarith [Real.pi_gt_three]) ht
  set d : ℝ := 74 / 100 with hd
  have hdlt : (1 / 2 : ℝ) < d := by rw [hd]; norm_num
  have hPair := summable_pairDensity (d := d) (t := t) hdlt
  obtain ⟨hsre, hsim, hre, hreσ, hs1, hsne, -, -, -⟩ := shiftedLine_setup hdlt ht0
  set s : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hsdef
  have hDir : (logDeriv riemannZeta s).re ≤ D :=
    re_logDeriv_riemannZeta_le_of_re hreσ (by rw [hsre, hd]; norm_num) hVM
  have hinv500 : t⁻¹ ≤ 1 / 500 := by rw [one_div]; exact inv_anti₀ (by norm_num) ht500
  have b2 : (1 / s).re ≤ 1 / 500 := (Complex.re_one_div_le_norm_inv s).trans
    ((inv_anti₀ ht0 (le_norm_of_im_eq ht0 hsim)).trans hinv500)
  have hs1im : (s - 1).im = t := by rw [Complex.sub_im, Complex.one_im, hsim]; ring
  have b3 : (1 / (s - 1)).re ≤ 1 / 500 := (Complex.re_one_div_le_norm_inv _).trans
    ((inv_anti₀ ht0 (le_norm_of_im_eq ht0 hs1im)).trans hinv500)
  have hpsi_bound : 1 / 2 * (Complex.digamma (s / 2)).re
      ≤ 1 / 2 * Real.log t + 1 / 100 - 1 / 2 * Real.log 2 := by
    have hcore := re_digamma_shiftedLine_le hdlt (by rw [hd]; norm_num) ht
    rw [← hsdef] at hcore
    linarith
  have hlogπ_ge : (1 : ℝ) ≤ Real.log π := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1)
      (le_of_lt (lt_trans (lt_trans Real.exp_one_lt_d9 (by norm_num)) Real.pi_gt_three))
  have hlog2_ge := Real.log_two_gt_d9
  rw [tsum_re_inv_riemannXiZeros_sub_eq hre hs1 hsne hPair]
  linarith [b2, b3, hpsi_bound, hDir, hlogπ_ge, hlog2_ge]
theorem tsum_re_inv_riemannXiZeros_sub_le_tight_sharp (t : ℝ) (ht : 168 * π ≤ t) :
    ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
      ≤ 1 / 2 * Real.log t + 319 / 100 := by
  linarith [tsum_re_inv_riemannXiZeros_sub_le_tight_of ht tsum_vonMangoldt_norm_le_124_sharp]
end
end CountPort76
section CountPort77
section
open Complex Filter Topology Function Set
open scoped Real
section Tail
open MeasureTheory
theorem tsum_one_div_nat_add_two_rpow_le_majorant {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ 2 ^ (-σ) + 2 ^ (1 - σ) / (σ - 1) := by
  have hneg : (-σ : ℝ) < -1 := by linarith
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 2) ^ σ) :=
    Real.summable_one_div_nat_add_two_rpow hσ
  rw [hsum.tsum_eq_zero_add]
  have h0 : 1 / (((0 : ℕ) : ℝ) + 2) ^ σ = (2 : ℝ) ^ (-σ) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div]
    norm_num
  have htail : ∑' n : ℕ, 1 / (((n : ℕ) + 1 : ℝ) + 2) ^ σ ≤ 2 ^ (1 - σ) / (σ - 1) := by
    have h := Real.tsum_one_div_nat_add_rpow_le 2 (by norm_num) hσ
    norm_num at h
    refine le_trans (le_of_eq (tsum_congr fun n ↦ ?_)) h
    rw [show ((n : ℕ) + 1 : ℝ) + 2 = (n : ℝ) + 3 by ring, one_div]
  refine add_le_add (le_of_eq ?_) (le_trans (le_of_eq (tsum_congr fun n ↦ ?_)) htail)
  · exact h0
  · push_cast; ring_nf
theorem Real.rpow_two_neg_le_one_sub_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (2 : ℝ) ^ (-u) ≤ 1 - u / 2 := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-Real.log 2))
    (by linarith : (0 : ℝ) ≤ 1 - u) hu0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    show Real.log 2 * -u = u * -Real.log 2 by ring]
  linarith [h]
private lemma two_rpow_one_sub (σ : ℝ) : (2 : ℝ) ^ (1 - σ) = 2 * 2 ^ (-σ) := by
  rw [show (1 - σ : ℝ) = 1 + -σ by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_one]
private lemma integrableOn_two_rpow_neg_Ioi (c : ℝ) :
    IntegrableOn (fun σ : ℝ ↦ (2 : ℝ) ^ (-σ)) (Set.Ioi c) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp : IntegrableOn (fun σ : ℝ ↦ Real.exp (-(Real.log 2 * σ))) (Set.Ioi c) :=
    Real.integrableOn_exp_neg_mul_Ioi hl2 c
  refine hexp.congr_fun (fun σ _ ↦ ?_) measurableSet_Ioi
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring_nf
private lemma integral_two_rpow_neg_Ioi (c : ℝ) :
    ∫ σ in Set.Ioi c, (2 : ℝ) ^ (-σ) = 2 ^ (-c) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcong : ∫ σ in Set.Ioi c, (2 : ℝ) ^ (-σ)
      = ∫ σ in Set.Ioi c, Real.exp (-Real.log 2 * σ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun σ _ ↦ ?_
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  rw [hcong, integral_exp_mul_Ioi (by linarith) c,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [div_eq_div_iff (ne_of_lt (by linarith : -Real.log 2 < 0)) (ne_of_gt hl2)]
  rw [show -Real.log 2 * c = Real.log 2 * -c by ring]
  ring
private lemma integrableOn_tail_majorant_snd {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) / (σ - 1)) (Set.Ioi c) := by
  have hcont : ContinuousOn (fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) / (σ - 1)) (Set.Ioi c) := by
    have h2 : Continuous fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) :=
      (Real.continuous_const_rpow (by norm_num)).comp (continuous_const.sub continuous_id)
    exact h2.continuousOn.div ((continuous_id.sub continuous_const).continuousOn)
      (fun σ hσ ↦ ne_of_gt (by simp only [Set.mem_Ioi] at hσ; linarith))
  refine Integrable.mono' ((integrableOn_two_rpow_neg_Ioi c).const_mul (2 / (c - 1)))
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  simp only [Set.mem_Ioi] at hσ
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.rpow_nonneg (by norm_num) _) hσ1.le), two_rpow_one_sub,
    show 2 / (c - 1) * (2 : ℝ) ^ (-σ) = 2 * (2 : ℝ) ^ (-σ) / (c - 1) by ring]
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
private lemma integrableOn_tail_majorant {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun σ : ℝ ↦ (2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) (Set.Ioi c) :=
  (integrableOn_two_rpow_neg_Ioi _).add (integrableOn_tail_majorant_snd hc)
private lemma integral_tail_majorant_le_core {a : ℝ} (ha : 1 < a) (ha2 : a ≤ 2) :
    ∫ σ in Set.Ioi a, ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1))
      ≤ 0.7214 + (Real.log (a - 1)⁻¹ + a / 2 - 1) + 0.7214 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [integral_add (integrableOn_two_rpow_neg_Ioi _) (integrableOn_tail_majorant_snd ha)]
  have hp1 : ∫ σ in Set.Ioi a, (2 : ℝ) ^ (-σ) ≤ 0.7214 := by
    rw [integral_two_rpow_neg_Ioi, div_le_iff₀ hl2]
    have h2c : (2 : ℝ) ^ (-a) ≤ 1 / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : (-a : ℝ) ≤ -1)
      rwa [Real.rpow_neg_one, ← one_div] at h
    linarith [Real.log_two_gt_d9]
  have hsplit : ∫ σ in Set.Ioi a, (2 : ℝ) ^ (1 - σ) / (σ - 1)
      = (∫ σ in Set.Ioc a 2, (2 : ℝ) ^ (1 - σ) / (σ - 1))
        + ∫ σ in Set.Ioi (2 : ℝ), (2 : ℝ) ^ (1 - σ) / (σ - 1) := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_tail_majorant_snd ha).mono_set Set.Ioc_subset_Ioi_self)
      (integrableOn_tail_majorant_snd (by norm_num : (1 : ℝ) < 2)),
      Set.Ioc_union_Ioi_eq_Ioi ha2]
  have hmid : ∫ σ in Set.Ioc a 2, (2 : ℝ) ^ (1 - σ) / (σ - 1)
      ≤ Real.log (a - 1)⁻¹ + a / 2 - 1 := by
    rw [← intervalIntegral.integral_of_le ha2]
    have hII : IntervalIntegrable (fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) / (σ - 1)) volume a 2 := by
      apply ContinuousOn.intervalIntegrable
      have h2 : Continuous fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) :=
        (Real.continuous_const_rpow (by norm_num)).comp (continuous_const.sub continuous_id)
      refine h2.continuousOn.div ((continuous_id.sub continuous_const).continuousOn)
        fun σ hσ ↦ ne_of_gt ?_
      rw [Set.uIcc_of_le ha2, Set.mem_Icc] at hσ
      linarith [hσ.1]
    have hII' : IntervalIntegrable (fun σ : ℝ ↦ 1 / (σ - 1) - 1 / 2) volume a 2 := by
      apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.sub (ContinuousOn.div continuousOn_const
        ((continuous_id.sub continuous_const).continuousOn) fun σ hσ ↦ ne_of_gt ?_)
        continuousOn_const
      rw [Set.uIcc_of_le ha2, Set.mem_Icc] at hσ
      linarith [hσ.1]
    have hle : ∫ σ in a..2, (2 : ℝ) ^ (1 - σ) / (σ - 1) ≤ ∫ σ in a..2, (1 / (σ - 1) - 1 / 2) := by
      refine intervalIntegral.integral_mono_on ha2 hII hII' fun σ hσ ↦ ?_
      rw [Set.mem_Icc] at hσ
      have hσ1 : (0 : ℝ) < σ - 1 := by linarith [hσ.1]
      have hchord : (2 : ℝ) ^ (1 - σ) ≤ 1 - (σ - 1) / 2 := by
        have h := Real.rpow_two_neg_le_one_sub_half (u := σ - 1) (by linarith [hσ.1])
          (by linarith [hσ.2])
        rwa [show (-(σ - 1) : ℝ) = 1 - σ by ring] at h
      calc (2 : ℝ) ^ (1 - σ) / (σ - 1) ≤ (1 - (σ - 1) / 2) / (σ - 1) := by gcongr
        _ = 1 / (σ - 1) - 1 / 2 := by field_simp
    have hFTC : ∫ σ in a..2, (1 / (σ - 1) - 1 / 2) = Real.log (a - 1)⁻¹ + a / 2 - 1 := by
      have hderiv : ∀ σ ∈ Set.uIcc a 2,
          HasDerivAt (fun x : ℝ ↦ Real.log (x - 1) - x / 2) (1 / (σ - 1) - 1 / 2) σ := by
        intro σ hσ
        rw [Set.uIcc_of_le ha2, Set.mem_Icc] at hσ
        have hne : σ - 1 ≠ 0 := ne_of_gt (by linarith [hσ.1])
        have h1 : HasDerivAt (fun x : ℝ ↦ Real.log (x - 1)) (1 / (σ - 1)) σ := by
          simpa using ((hasDerivAt_id σ).sub_const 1).log hne
        exact h1.sub ((hasDerivAt_id σ).div_const 2)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII',
        show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one, Real.log_inv]
      ring
    exact hle.trans_eq hFTC
  have hp3 : ∫ σ in Set.Ioi (2 : ℝ), (2 : ℝ) ^ (1 - σ) / (σ - 1) ≤ 0.7214 := by
    have hmono : ∫ σ in Set.Ioi (2 : ℝ), (2 : ℝ) ^ (1 - σ) / (σ - 1)
        ≤ ∫ σ in Set.Ioi (2 : ℝ), 2 * (2 : ℝ) ^ (-σ) := by
      refine setIntegral_mono_on (integrableOn_tail_majorant_snd (by norm_num : (1 : ℝ) < 2))
        ((integrableOn_two_rpow_neg_Ioi 2).const_mul 2)
        measurableSet_Ioi fun σ hσ ↦ ?_
      simp only [Set.mem_Ioi] at hσ
      rw [two_rpow_one_sub]
      exact div_le_self (by positivity) (by linarith)
    rw [integral_const_mul, integral_two_rpow_neg_Ioi] at hmono
    have h22 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
      rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rw [h22] at hmono
    refine hmono.trans ?_
    rw [show (2 : ℝ) * (1 / 4 / Real.log 2) = 1 / 2 / Real.log 2 by ring, div_le_iff₀ hl2]
    linarith [Real.log_two_gt_d9]
  rw [hsplit]
  linarith [hp1, hmid, hp3]
private lemma log_25_24_mul_two_pow_le (k : ℕ) :
    Real.log (25 / 24 * 2 ^ k) ≤ 1 / 24 + k * Real.log 2 := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 25 / 24 by norm_num)]
private lemma neg_le_logNormZetaIntegral_of_integral_majorant_le {a B : ℝ} (ha1 : 1 < a)
    (hIN : ∫ σ in Set.Ioi a, ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) ≤ B) (b t : ℝ) :
    (-B ≤ ∫ σ in Set.Ioi a, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-B ≤ ∫ σ in Set.Ioo a b, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  neg_le_logNormZetaIntegral_of_tsum_le ha1 (integrableOn_tail_majorant ha1)
    (fun _ hσ ↦ tsum_one_div_nat_add_two_rpow_le_majorant (lt_trans ha1 hσ)) hIN
theorem integral_tail_majorant_le_124 :
    ∫ σ in Set.Ioi (124 / 100 : ℝ), ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) ≤ 5 / 2 := by
  have h := integral_tail_majorant_le_core (a := 124 / 100) (by norm_num) (by norm_num)
  rw [show ((124 / 100 : ℝ) - 1)⁻¹ = 25 / 6 by norm_num] at h
  have hlog : Real.log (25 / 6) ≤ 1 / 24 + 2 * Real.log 2 := by
    have h2 := log_25_24_mul_two_pow_le 2
    rw [show (25 / 24 * 2 ^ (2 : ℕ) : ℝ) = 25 / 6 by norm_num] at h2
    push_cast at h2; linarith
  linarith [h, hlog, Real.log_two_lt_d9]
theorem logNormZetaIntegral_tail_ge_tight (t : ℝ) :
    (-(5 / 2) ≤ ∫ σ in Set.Ioi (124 / 100 : ℝ),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-(5 / 2) ≤ ∫ σ in Set.Ioo (124 / 100 : ℝ) (198 / 100),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  neg_le_logNormZetaIntegral_of_integral_majorant_le (a := 124 / 100) (by norm_num)
    integral_tail_majorant_le_124 (198 / 100) t
end Tail
end
end CountPort77
section CountPort78
section
open Complex Filter Topology Function Set
open scoped Real
private lemma log_pi_le_two_log_two : Real.log π ≤ 2 * Real.log 2 := by
  rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
  exact Real.log_le_log Real.pi_pos Real.pi_lt_four.le
private lemma log_two_pi_le_three_log_two : Real.log (2 * π) ≤ 3 * Real.log 2 := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne']; linarith [log_pi_le_two_log_two]
private lemma logDeriv_riemannXi_zero_eq {B : ℝ}
    (hB : ∀ s, riemannXi s =
      1 / 2 * Complex.exp (B * s) * riemannXiCanonicalProduct riemannXiZeros s) :
    logDeriv riemannXi 0 = (B : ℂ) := by
  have hrep : ∀ s, riemannXi s = Complex.exp (Complex.log (1 / 2) + B * s) *
      riemannXiCanonicalProduct riemannXiZeros s := fun s ↦ by
    rw [hB s, Complex.exp_add, Complex.exp_log (by norm_num)]
  have hde : HasDerivAt (fun s : ℂ ↦ Complex.log (1 / 2) + (B : ℂ) * s) (B : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (B : ℂ)).const_add (Complex.log (1 / 2))
  rw [logDeriv_riemannXi_zero_eq_deriv (by fun_prop) hrep, hde.deriv]
theorem tsum_log_norm_riemannXiZeros_shift_eq {s : ℂ} {d : ℝ}
    (hs : ∀ i, s ≠ riemannXiZeros i) (hsd : ∀ i, s + d ≠ riemannXiZeros i) :
    ∑' i, (Real.log ‖s + ↑d - riemannXiZeros i‖ - Real.log ‖s - riemannXiZeros i‖)
      = Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖ := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  have hsum : Summable fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2 := summable_inv_norm_sq_riemannXiZeros
  have hresum : Summable fun i ↦ ((riemannXiZeros i)⁻¹).re := summable_re_inv_riemannXiZeros
  have hκ0 : B + ∑' i, ((riemannXiZeros i)⁻¹).re = 0 := by
    have hBre : (logDeriv riemannXi 0).re = B := by
      rw [logDeriv_riemannXi_zero_eq hB, Complex.ofReal_re]
    have h := hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero
    rwa [hBre] at h
  set ρ := riemannXiZeros
  have hzne : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) → ∀ i, z / ρ i ≠ 1 := fun {z} hz i h ↦
    hz i ((div_eq_one_iff_eq (riemannXiZeros_ne_zero i)).mp h)
  have hsummSplit : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) →
      Summable (fun i ↦ Real.log ‖1 - z / ρ i‖ + (z / ρ i).re) := fun {z} hz ↦
    (summable_log_norm_weierstrassE1 ρ hsum z).congr
      (fun i ↦ log_norm_weierstrassE1 (hzne hz i))
  have hlogXi : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) →
      Real.log ‖riemannXi z‖
        = Real.log (1 / 2) + B * z.re + Real.log ‖riemannXiCanonicalProduct ρ z‖ := by
    intro z hz
    have hPne : riemannXiCanonicalProduct ρ z ≠ 0 :=
      riemannXiCanonicalProduct_ne_zero_of_forall_ne ρ hsum hz
    have h12 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
      rw [norm_div, norm_one, Complex.norm_ofNat]
    rw [hB z, norm_mul, norm_mul, Complex.norm_exp, h12,
      show ((B : ℂ) * z).re = B * z.re from by rw [Complex.re_ofReal_mul],
      Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hPne),
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hdiffXi : Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖
      = B * d + (Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖) := by
    rw [hlogXi hsd, hlogXi hs, Complex.add_re, Complex.ofReal_re]; ring
  have hterm : ∀ i,
      (Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re)
        = (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖) + d * ((ρ i)⁻¹).re := by
    intro i
    have hρ0 := riemannXiZeros_ne_zero i
    have elog : ∀ {w : ℂ}, w ≠ ρ i →
        Real.log ‖1 - w / ρ i‖ = Real.log ‖w - ρ i‖ - Real.log ‖ρ i‖ := by
      intro w hw
      have h1 : (1 : ℂ) - w / ρ i = (ρ i - w) / ρ i := by rw [sub_div, div_self hρ0]
      rw [h1, norm_div, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ hw h.symm))
        (norm_ne_zero_iff.mpr hρ0), norm_sub_rev]
    have hsubdiv : (s + ↑d) / ρ i - s / ρ i = (↑d : ℂ) * (ρ i)⁻¹ := by
      rw [div_sub_div_same, add_sub_cancel_left, div_eq_mul_inv]
    have ere : ((s + ↑d) / ρ i).re - (s / ρ i).re = d * ((ρ i)⁻¹).re := by
      rw [← Complex.sub_re, hsubdiv, Complex.re_ofReal_mul]
    rw [elog (hsd i), elog (hs i)]
    linear_combination ere
  have hD : Summable (fun i ↦ Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖) := by
    refine ((hsummSplit hsd).sub (hsummSplit hs)).sub (hresum.mul_left d) |>.congr fun i ↦ ?_
    rw [hterm i]; ring
  have hsplit : ∑' i, ((Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re))
      = ∑' i, (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖)
          + d * ∑' i, ((ρ i)⁻¹).re := by
    rw [funext (fun i ↦ hterm i), hD.tsum_add (hresum.mul_left d), tsum_mul_left]
  have hPsub : ∑' i, ((Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re))
      = Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖ := by
    rw [(hsummSplit hsd).tsum_sub (hsummSplit hs),
      ← log_norm_riemannXiCanonicalProduct_eq_tsum ρ hsum hsd,
      ← log_norm_riemannXiCanonicalProduct_eq_tsum ρ hsum hs]
  rw [hPsub] at hsplit
  have hfinal : ∑' i, (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖)
      = (Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖) - d * ∑' i, ((ρ i)⁻¹).re := by
    linear_combination -hsplit
  rw [hfinal, hdiffXi]
  linear_combination (-(d : ℝ)) * hκ0
section Assembly
open Complex.Stirling MeasureTheory
private lemma le_logNormZetaIntegral_p1_of {Cψ a₂ : ℝ}
    (hCψ : ∀ t : ℝ, 168 * π ≤ t →
      ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
        ≤ 1 / 2 * Real.log t + Cψ)
    (ha₂ : (2 : ℝ) * (74 / 100) ^ 2 * Cψ + 2 * (5 / 2)
        + ((74 / 100) ^ 2 / 2 * (3 * Real.log 2) + (74 / 100) / 2 * Real.log 2
          + (74 / 100) ^ 2 / 10000) ≤ a₂) :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ a₂ + (74 / 100) ^ 2 / 2 * Real.log t := by
  intro t ht hzero
  have hlt := le_logNormZetaIntegral_of_le (d := 74 / 100) (κ := 0)
    (Ca := (74 / 100) ^ 2 / 2 * (Real.log 2 + Real.log π) + (74 / 100) / 2 * Real.log 2
      + (74 / 100) ^ 2 / 10000)
    (Cψ := Cψ) (Ct := 5 / 2) (by norm_num)
    (fun s hs hsd ↦ by rw [tsum_log_norm_riemannXiZeros_shift_eq hs hsd]; ring)
    (logNormGammaArchimedean_strip_diff_ge_tight (by norm_num) (by norm_num))
    hCψ
    (fun t ↦ by
      rw [show (1 / 2 + 74 / 100 : ℝ) = 124 / 100 by norm_num,
        show (1 / 2 + 2 * (74 / 100) : ℝ) = 198 / 100 by norm_num]
      exact logNormZetaIntegral_tail_ge_tight t)
    (c := 2) (by norm_num) t ht hzero
  have h1 : (74 / 100 : ℝ) ^ 2 / 2 * (Real.log 2 + Real.log π)
      ≤ (74 / 100) ^ 2 / 2 * (3 * Real.log 2) :=
    mul_le_mul_of_nonneg_left (by linarith [log_pi_le_two_log_two]) (by positivity)
  nlinarith [hlt, ha₂, h1]
theorem le_logNormZetaIntegral_five :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ 933 / 100 + (74 / 100) ^ 2 / 2 * Real.log t :=
  le_logNormZetaIntegral_p1_of tsum_re_inv_riemannXiZeros_sub_le_tight_sharp
    (by nlinarith [Real.log_two_lt_d9, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
theorem norm_integral_argZeta_le_five :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 5 + 0.128 * Real.log (t₂ / (2 * π)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds' (b₁ := 1 / 8) (b₂ := (74 / 100) ^ 2 / 2)
    (by norm_num) (by positivity) (by nlinarith [Real.pi_gt_d2])
    (fun t ht hzero ↦ logNormZetaIntegral_le_five ht hzero)
    (fun t ht hzero ↦ le_logNormZetaIntegral_five t ht hzero)
      t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  have hπpos : 0 < π := Real.pi_pos
  have hconst :
      (5 + 933 / 100 + (1 / 8 + (74 / 100) ^ 2 / 2) * Real.log (2 * π)) / π ≤ 5 := by
    rw [div_le_iff₀ hπpos]
    nlinarith [log_two_pi_le_three_log_two, Real.log_two_lt_d9, Real.pi_gt_d2]
  linarith [hconst]
end Assembly
section Unconditional
open MeasureTheory
private lemma exists_zeroFree_Ioo {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ t : ℝ, t ∈ Set.Ioo c (c + ε) ∧
      ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0 := by
  have hcε : c < c + ε := by linarith
  have hfin := finite_setOf_riemannZeta_zero_ray_Icc hc hcε.le
  obtain ⟨t, htd⟩ := ((Set.Ioo_infinite hcε).sdiff hfin).nonempty
  rw [Set.mem_sdiff] at htd
  exact ⟨t, htd.1, fun σ hσ hz ↦ htd.2 ⟨⟨σ, hσ, hz⟩, Set.Ioo_subset_Icc_self htd.1⟩⟩
private lemma norm_integral_argZeta_le_unconditional_of {A : ℝ}
    (hbnd : ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ A + 0.128 * Real.log (t₂ / (2 * π)))
    {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁) (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ A + 0.128 * Real.log (t₂ / (2 * π)) := by
  have hπ : 0 < π := Real.pi_pos
  have ht1pos : 0 < t₁ := lt_trans (by positivity) ht1
  have ht2pos : 0 < t₂ := lt_trans ht1pos h12
  have ht1gt1 : (1 : ℝ) < t₁ := by nlinarith [Real.pi_gt_three]
  set m : ℝ := min 1 (t₂ - t₁) with hm
  have hm0 : 0 < m := lt_min one_pos (by linarith)
  have hmlt : m ≤ t₂ - t₁ := min_le_right _ _
  set d : ℕ → ℝ := fun n ↦ min (1 / ((n : ℝ) + 1)) m with hd
  have hd0 : ∀ n, 0 < d n := fun n ↦ lt_min (by positivity) hm0
  have hdm : ∀ n, d n ≤ m := fun n ↦ min_le_right _ _
  have hdinv : ∀ n, d n ≤ 1 / ((n : ℝ) + 1) := fun n ↦ min_le_left _ _
  have hdtend : Tendsto d atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ (hd0 n).le) hdinv tendsto_one_div_add_atTop_nhds_zero_nat
  choose a hamem hafree using fun n ↦ exists_zeroFree_Ioo ht1pos (hd0 n)
  choose b hbmem hbfree using fun n ↦ exists_zeroFree_Ioo ht2pos (hd0 n)
  have halt : ∀ n, t₁ < a n := fun n ↦ (hamem n).1
  have hault : ∀ n, a n < t₁ + d n := fun n ↦ (hamem n).2
  have hblt : ∀ n, t₂ < b n := fun n ↦ (hbmem n).1
  have hbult : ∀ n, b n < t₂ + d n := fun n ↦ (hbmem n).2
  have hab : ∀ n, a n < b n := fun n ↦ by
    have := hault n; have := hdm n; have := hblt n; linarith
  have hII : IntervalIntegrable argZeta volume (t₁ - 1) (t₂ + 1) :=
    intervalIntegrable_argZeta (by linarith) (by linarith)
  have hle : t₁ - 1 ≤ t₂ + 1 := by linarith
  have hcontOn : ContinuousOn (fun x ↦ ∫ s in t₁..x, argZeta s) (Set.Icc (t₁ - 1) (t₂ + 1)) := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := t₁) hII
      (by rw [Set.uIcc_of_le hle]; exact ⟨by linarith, by linarith⟩)
    rwa [Set.uIcc_of_le hle] at this
  have hcatT1 : ContinuousAt (fun x ↦ ∫ s in t₁..x, argZeta s) t₁ :=
    hcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcatT2 : ContinuousAt (fun x ↦ ∫ s in t₁..x, argZeta s) t₂ :=
    hcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have haup : Tendsto (fun n ↦ t₁ + d n) atTop (𝓝 t₁) := by
    simpa using tendsto_const_nhds.add hdtend
  have hbup : Tendsto (fun n ↦ t₂ + d n) atTop (𝓝 t₂) := by
    simpa using tendsto_const_nhds.add hdtend
  have hatend : Tendsto a atTop (𝓝 t₁) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds haup
      (fun n ↦ (halt n).le) (fun n ↦ (hault n).le)
  have hbtend : Tendsto b atTop (𝓝 t₂) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbup
      (fun n ↦ (hblt n).le) (fun n ↦ (hbult n).le)
  have hsplit : ∀ n, ∫ s in (a n)..(b n), argZeta s
      = (∫ s in t₁..(b n), argZeta s) - ∫ s in t₁..(a n), argZeta s := fun n ↦ by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_argZeta ht1pos (halt n).le)
      (intervalIntegrable_argZeta (lt_trans ht1pos (halt n)) (hab n).le)]
    ring
  have hIb : Tendsto (fun n ↦ ∫ s in t₁..(b n), argZeta s) atTop
      (𝓝 (∫ s in t₁..t₂, argZeta s)) := hcatT2.tendsto.comp hbtend
  have hIa : Tendsto (fun n ↦ ∫ s in t₁..(a n), argZeta s) atTop
      (𝓝 (∫ s in t₁..t₁, argZeta s)) := hcatT1.tendsto.comp hatend
  rw [intervalIntegral.integral_same] at hIa
  have hlhs : Tendsto (fun n ↦ ∫ s in (a n)..(b n), argZeta s) atTop
      (𝓝 (∫ s in t₁..t₂, argZeta s)) := by
    have hd := hIb.sub hIa
    rw [sub_zero] at hd
    exact hd.congr (fun n ↦ (hsplit n).symm)
  have hrhs : Tendsto (fun n ↦ A + 0.128 * Real.log (b n / (2 * π))) atTop
      (𝓝 (A + 0.128 * Real.log (t₂ / (2 * π)))) := by
    have hlog : Tendsto (fun n ↦ Real.log (b n / (2 * π))) atTop
        (𝓝 (Real.log (t₂ / (2 * π)))) :=
      (Real.continuousAt_log (by positivity)).tendsto.comp (hbtend.div_const (2 * π))
    exact tendsto_const_nhds.add (hlog.const_mul 0.128)
  have hbound : ∀ n, |∫ s in (a n)..(b n), argZeta s| ≤ A + 0.128 * Real.log (b n / (2 * π)) :=
    fun n ↦ hbnd (a n) (b n)
      (by have := halt n; linarith) (hab n) (hafree n) (hbfree n)
  exact le_of_tendsto_of_tendsto' hlhs.abs hrhs hbound
theorem norm_integral_argZeta_le_five_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 5 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_five ht1 h12
end Unconditional
end
end CountPort78
section CountPort79
section
open scoped Real
namespace Complex
end Complex
end
end CountPort79
section CountPort80
section
open Filter Topology Set
open scoped ComplexConjugate Real Nat
namespace Complex
noncomputable def logGammaAux : ℂ → ℂ :=
  Classical.choose (Convex.exists_forall_hasDerivWithinAt (convex_halfSpace_re_gt 0)
    differentiableOn_digamma_re_pos)
private lemma logGammaAux_hasDerivWithinAt {w : ℂ} (hw : 0 < w.re) :
    HasDerivWithinAt logGammaAux (Complex.digamma w) {z : ℂ | 0 < z.re} w :=
  Classical.choose_spec (Convex.exists_forall_hasDerivWithinAt (convex_halfSpace_re_gt 0)
    differentiableOn_digamma_re_pos) w hw
noncomputable def logGamma (w : ℂ) : ℂ := logGammaAux w - logGammaAux 1
@[simp]
theorem logGamma_one : logGamma 1 = 0 := sub_self _
theorem hasDerivAt_logGamma {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt logGamma (Complex.digamma w) w :=
  ((logGammaAux_hasDerivWithinAt hw).hasDerivAt ((isOpen_re_gt 0).mem_nhds hw)).sub_const
    (logGammaAux 1)
theorem cexp_logGamma {w : ℂ} (hw : 0 < w.re) :
    Complex.exp (logGamma w) = Complex.Gamma w := by
  have hf : DifferentiableOn ℂ (fun z ↦ Complex.exp (logGamma z)) {z : ℂ | 0 < z.re} :=
    fun z hz ↦ ((hasDerivAt_logGamma hz).cexp).differentiableAt.differentiableWithinAt
  have hfn : ∀ z ∈ {z : ℂ | 0 < z.re}, Complex.exp (logGamma z) ≠ 0 :=
    fun z _ ↦ Complex.exp_ne_zero _
  have hlog : EqOn (logDeriv (fun z ↦ Complex.exp (logGamma z)))
      (logDeriv Complex.Gamma) {z : ℂ | 0 < z.re} := by
    intro z hz
    have hd : deriv (fun z ↦ Complex.exp (logGamma z)) z
        = Complex.exp (logGamma z) * Complex.digamma z :=
      ((hasDerivAt_logGamma hz).cexp).deriv
    rw [logDeriv_apply, logDeriv_apply, hd, mul_comm, mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one, Complex.digamma_def, logDeriv_apply]
  obtain ⟨c, -, hce⟩ := (logDeriv_eqOn_iff hf differentiableOn_Gamma_re_pos (isOpen_re_gt 0)
    isPreconnected_re_pos (fun _ hz ↦ Complex.Gamma_ne_zero_of_re_pos hz) hfn).mp hlog
  have hc1 : c = 1 := by
    simpa [logGamma_one, Complex.Gamma_one, Pi.smul_apply, smul_eq_mul]
      using (hce (by simp : (1 : ℂ) ∈ {z : ℂ | 0 < z.re})).symm
  simpa [Pi.smul_apply, smul_eq_mul, hc1] using hce (show w ∈ {z : ℂ | 0 < z.re} from hw)
theorem digamma_conj (s : ℂ) :
    Complex.digamma (conj s) = conj (Complex.digamma s) := by
  have hΓeq : (conj ∘ Complex.Gamma ∘ conj) = Complex.Gamma := by
    funext z; simp [Function.comp, Complex.Gamma_conj]
  have hderiv : deriv Complex.Gamma (conj s) = conj (deriv Complex.Gamma s) := by
    simpa using congrArg conj (congrFun (by rw [← deriv_conj_conj, hΓeq] :
      conj ∘ deriv Complex.Gamma ∘ conj = deriv Complex.Gamma) s)
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, hderiv, Complex.Gamma_conj, map_div₀]
theorem logGamma_im_ofReal {x : ℝ} (hx : 0 < x) :
    (logGamma (x : ℂ)).im = 0 := by
  have hψderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ (logGamma (u : ℂ)).im) 0 t := by
    intro t ht
    have htre : 0 < ((t : ℂ)).re := by simpa using ht
    have hc : HasDerivAt (fun u : ℝ ↦ logGamma (u : ℂ)) (Complex.digamma (t : ℂ)) t :=
      (hasDerivAt_logGamma htre).comp_ofReal
    have him : HasDerivAt (fun u : ℝ ↦ Complex.imCLM (logGamma (u : ℂ)))
        (Complex.imCLM (Complex.digamma (t : ℂ))) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hc
    have hreal : (Complex.digamma (t : ℂ)).im = 0 :=
      Complex.conj_eq_iff_im.mp <| by
        simpa [Complex.conj_ofReal] using (digamma_conj (t : ℂ)).symm
    simpa only [Complex.imCLM_apply, hreal] using him
  simpa [Complex.ofReal_one] using isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun u hu ↦ (hψderiv u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ (hψderiv u hu).deriv) hx (mem_Ioi.mpr one_pos)
end Complex
end
end CountPort80
section CountPort81
section
open MeasureTheory Filter
open scoped Topology Nat Real
namespace Complex.Stirling
noncomputable def logGammaStirling (M : ℕ) (w : ℂ) : ℂ :=
  (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ)
    + ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ))
end Complex.Stirling
namespace Real.Stirling
end Real.Stirling
end
end CountPort81
section CountPort82
section
open MeasureTheory Filter
open scoped Topology Nat Real
namespace Complex.Stirling
end Complex.Stirling
end
end CountPort82
section CountPort83
section
open Complex
open scoped Nat
theorem continuous_logGamma_curve :
    Continuous fun u : ℝ ↦ logGamma (1 / 4 + Complex.I * ((u : ℂ) / 2)) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hre : (0 : ℝ) < (1 / 4 + Complex.I * ((u : ℂ) / 2)).re := by simp
  exact ContinuousAt.comp (f := fun u : ℝ => (1 / 4 : ℂ) + Complex.I * ((u : ℂ) / 2))
    (hasDerivAt_logGamma hre).continuousAt (by fun_prop)
theorem riemannSiegelTheta_eq_im_logGamma {T : ℝ} (hT : 0 ≤ T) :
    riemannSiegelTheta T
      = (logGamma (1 / 4 + Complex.I * (T / 2))).im - T / 2 * Real.log Real.pi := by
  have hre : ∀ u : ℝ, (0 : ℝ) < (1 / 4 + Complex.I * ((u : ℂ) / 2)).re := fun u => by simp
  have hcontlog : IsContLog 0 T (fun u => Complex.Gamma (1 / 4 + Complex.I * (u / 2)))
      (fun u ↦ logGamma (1 / 4 + Complex.I * (u / 2))) :=
    ⟨continuous_logGamma_curve.continuousOn, fun u _ ↦ cexp_logGamma (hre u)⟩
  rw [riemannSiegelTheta, argVariation_eq_of_isContLog hT hcontlog]
  have hg0 : (logGamma (1 / 4 + Complex.I * (((0 : ℝ) : ℂ) / 2))).im = 0 := by
    rw [show (1 : ℂ) / 4 + Complex.I * (((0 : ℝ) : ℂ) / 2) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring]
    exact logGamma_im_ofReal (by norm_num)
  simp only [hg0, sub_zero]
namespace Complex
end Complex
open Complex.Stirling
noncomputable abbrev riemannSiegelThetaStirlingErrorBound (M N : ℕ) : ℝ :=
  ((2 * M + 1)! : ℝ) / (2 * M * (2 * Real.pi) ^ (2 * M)) * (1 / 4 + N : ℝ) ^ (-(2 * M : ℤ))
noncomputable abbrev riemannSiegelThetaStirlingErrorBound' (M N : ℕ) (t : ℝ) : ℝ :=
  ((2 * M + 1)! : ℝ) * 2 ^ (2 * M + 1) / (2 * M * (2 * Real.pi) ^ (2 * M))
    * ((1 / 4 + N) ^ 2 + (t / 2) ^ 2 : ℝ) ^ (-(M : ℤ))
noncomputable abbrev riemannSiegelThetaApproximant (M N : ℕ) (t : ℝ) : ℝ :=
  ((logGammaStirling M (1 / 4 + Complex.I * (t / 2) + N)
        - ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * (t / 2) + j)).im
      - t / 2 * Real.log Real.pi : ℝ)
def thetaShift (M : ℕ) : ℕ := 2 * M
noncomputable abbrev hardyZApproximantEM (M N : ℕ) (t : ℝ) : ℝ :=
  (Complex.exp (Complex.I * ((riemannSiegelThetaApproximant M (thetaShift M) t : ℝ) : ℂ))
      * zetaApproximant (1 / 2 + Complex.I * t) M N).re
noncomputable abbrev hardyZErrorBoundEM (M N : ℕ) (t : ℝ) : ℝ :=
  riemannSiegelThetaStirlingErrorBound M (thetaShift M)
      * ‖zetaApproximant (1 / 2 + Complex.I * t) M N‖
    + ‖zetaRemainder (1 / 2 + Complex.I * t) M N‖
end
end CountPort83
section CountPort84
section
namespace Complex
theorem deriv_digamma_add_one {s : ℂ} (hs : 0 < s.re) :
    deriv Complex.digamma (s + 1) = deriv Complex.digamma s - (s ^ 2)⁻¹ := by
  have hs1 : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hL : HasDerivAt (fun z ↦ Complex.digamma (z + 1)) (deriv Complex.digamma (s + 1)) s := by
    simpa [Function.comp_def] using
      (differentiableAt_digamma hs1).hasDerivAt.comp s ((hasDerivAt_id s).add_const 1)
  have heq : (fun z ↦ Complex.digamma (z + 1)) =ᶠ[nhds s] fun z ↦ Complex.digamma z + z⁻¹ := by
    filter_upwards [(isOpen_re_gt 0).mem_nhds hs] with z (hz : 0 < z.re)
    exact Complex.digamma_apply_add_one z (ne_neg_natCast_of_re_pos hz)
  rw [hL.unique <| ((differentiableAt_digamma hs).hasDerivAt.add
    (hasDerivAt_inv (Complex.ne_zero_of_re_pos hs))).congr_of_eventuallyEq heq]
  ring
theorem im_inv_sq_nonpos {w : ℂ} (hre : 0 ≤ w.re) (him : 0 ≤ w.im) : ((w ^ 2)⁻¹).im ≤ 0 := by
  rw [Complex.inv_im, neg_div, neg_nonpos, sq, Complex.mul_im]
  exact div_nonneg (by nlinarith [mul_nonneg hre him]) (Complex.normSq_nonneg _)
end Complex
end
end CountPort84
section CountPort85
section
open Complex Filter
open scoped Topology Nat Real
namespace Complex
open Complex.Stirling
theorem norm_digamma_le {z : ℂ} (hz : 0 < z.re) (h1 : 1 ≤ ‖z‖) :
    ‖Complex.digamma z‖ ≤ Real.log ‖z‖ + (Real.pi + 3) := by
  have hlogpos : 0 ≤ Real.log ‖z‖ := Real.log_nonneg h1
  have hLog : ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im, abs_of_nonneg hlogpos]
    linarith [Complex.abs_arg_le_pi z]
  have hinv : ‖(2 * z)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, Complex.norm_ofNat]
    exact inv_le_one_of_one_le₀ (by nlinarith [h1])
  have hsum : ‖∑ k ∈ Finset.Icc 1 1, (bernoulli (2 * k) : ℂ) / (2 * k) * z ^ (-(2 * k : ℤ))‖
      ≤ 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton, norm_mul]
    have hb : ‖(bernoulli (2 * 1) : ℂ) / (2 * (1 : ℕ))‖ ≤ 1 := by
      norm_num [bernoulli_two, Complex.norm_div]
    have hz2 : ‖z ^ (-(2 * (1 : ℕ) : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]; exact zpow_le_one_of_nonpos₀ h1 (by norm_num)
    exact mul_le_one₀ hb (norm_nonneg _) hz2
  have hrem : ‖digammaRemainderIoi z (2 * 1 + 1)‖ ≤ 1 := by
    have hb := norm_digammaRemainderIoi_le' z hz (2 * 1 + 1) (by norm_num)
    have hzp : ‖z‖ ^ (-(2 * 1 + 1 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ h1 (by norm_num)
    have hcoef : ((2 * 1 + 1)! : ℝ) / (2 * Real.pi) ^ ((2 * 1 + 1) - 1) ≤ 1 := by
      rw [show (2 * 1 + 1 : ℕ) = 3 from rfl, show (3 - 1 : ℕ) = 2 from rfl,
        show (3 ! : ℝ) = 6 from by norm_num, div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    exact hb.trans (mul_le_one₀ hcoef (zpow_nonneg (norm_nonneg _) _) hzp)
  rw [digamma_eq_log_sub z hz 1]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans ?_
  linarith [hLog, hinv, hsum, hrem]
private lemma re_sub_dist_le_re {c z : ℂ} {r : ℝ} (h : dist z c ≤ r) : c.re - r ≤ z.re := by
  have hab := Complex.abs_re_le_norm (c - z)
  rw [Complex.sub_re, show ‖c - z‖ = dist z c by rw [Complex.dist_eq, norm_sub_rev]] at hab
  linarith [(le_abs_self (c.re - z.re)).trans hab]
theorem tendsto_deriv_digamma_add_nat {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ ↦ deriv Complex.digamma (s + n)) atTop (𝓝 0) := by
  set L : ℝ := Real.pi + 3 with hL
  set K : ℝ := Real.log (2 * (‖s‖ + 1)) + L with hK
  have he : Tendsto (fun n : ℕ ↦ (2 * Real.log ↑n + 2 * K) / ↑n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ 2 * Real.log ↑n / ↑n) atTop (𝓝 0) := by
      have h0 := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop).const_mul 2
      simp only [Function.comp_def, id_eq, mul_zero] at h0
      exact h0.congr fun n ↦ by rw [mul_div_assoc]
    have h2 : Tendsto (fun n : ℕ ↦ 2 * K / ↑n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (2 * K)
    simpa [add_div] using h1.add h2
  refine squeeze_zero_norm' ?_ he
  filter_upwards [eventually_ge_atTop (max 1 ⌈2 - s.re⌉₊)] with n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hnpos : 0 < (n : ℝ) := by linarith
  set c : ℂ := s + ↑n with hc
  have hcre : c.re = s.re + ↑n := by rw [hc, Complex.add_re, Complex.natCast_re]
  have hcre2 : 2 ≤ c.re := by
    rw [hcre]
    have hle : (⌈2 - s.re⌉₊ : ℝ) ≤ ↑n := by exact_mod_cast le_trans (le_max_right _ _) hn
    linarith [Nat.le_ceil (2 - s.re), hle]
  set R : ℝ := c.re / 2 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hR1 : 1 ≤ R := by rw [hR]; linarith
  have hbound : ‖deriv Complex.digamma c‖ ≤ (Real.log (2 * (‖s‖ + ↑n)) + L) / R := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos
    · apply DifferentiableOn.diffContOnCl
      intro z hz
      have hzc : dist z c ≤ R :=
        Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hz)
      exact (differentiableAt_digamma (by linarith [re_sub_dist_le_re hzc])).differentiableWithinAt
    · intro z hz
      have hzc : dist z c = R := Metric.mem_sphere.mp hz
      have hzre : R ≤ z.re := by linarith [re_sub_dist_le_re hzc.le]
      have hznorm1 : 1 ≤ ‖z‖ := le_trans hR1 (hzre.trans (Complex.re_le_norm z))
      have hznorm : ‖z‖ ≤ 2 * (‖s‖ + ↑n) := by
        have hcn : ‖c‖ ≤ ‖s‖ + ↑n := by
          rw [hc]
          simpa [Complex.norm_natCast] using norm_add_le s (↑n : ℂ)
        have hzc' : ‖z - c‖ = R := by rw [← Complex.dist_eq]; exact hzc
        have hz1 : ‖z‖ ≤ ‖c‖ + R := hzc' ▸ norm_le_norm_add_norm_sub' z c
        have hRle : R ≤ ‖s‖ + ↑n := by
          rw [hR, hcre]; linarith [Complex.re_le_norm s, norm_nonneg s]
        linarith
      calc ‖Complex.digamma z‖ ≤ Real.log ‖z‖ + L := norm_digamma_le (by linarith [hzre]) hznorm1
        _ ≤ Real.log (2 * (‖s‖ + ↑n)) + L := by gcongr
  refine hbound.trans ?_
  have hnum : Real.log (2 * (‖s‖ + ↑n)) + L ≤ Real.log ↑n + K := by
    have hmul : (2 : ℝ) * (‖s‖ + ↑n) ≤ 2 * (‖s‖ + 1) * ↑n := by nlinarith [norm_nonneg s, hn1]
    have hlog : Real.log (2 * (‖s‖ + ↑n)) ≤ Real.log (2 * (‖s‖ + 1)) + Real.log ↑n := by
      rw [← Real.log_mul (by positivity) (by linarith)]
      exact Real.log_le_log (by positivity) hmul
    rw [hK]; linarith
  have hnum0 : 0 ≤ Real.log (2 * (‖s‖ + ↑n)) + L := by
    have : 0 ≤ Real.log (2 * (‖s‖ + ↑n)) := Real.log_nonneg (by nlinarith [norm_nonneg s, hn1])
    rw [hL]; linarith [Real.pi_pos]
  rw [hR]
  calc (Real.log (2 * (‖s‖ + ↑n)) + L) / (c.re / 2)
      ≤ (Real.log (2 * (‖s‖ + ↑n)) + L) / (↑n / 2) :=
        div_le_div_of_nonneg_left hnum0 (by positivity) (by rw [hcre]; linarith)
    _ = (Real.log (2 * (‖s‖ + ↑n)) + L) * 2 / ↑n := by rw [div_div_eq_mul_div]
    _ ≤ (2 * Real.log ↑n + 2 * K) / ↑n := by gcongr; linarith [hnum]
theorem im_deriv_digamma_nonpos {s : ℂ} (hs : 0 < s.re) (him : 0 ≤ s.im) :
    (deriv Complex.digamma s).im ≤ 0 := by
  have htel : ∀ n : ℕ, deriv Complex.digamma s
      = deriv Complex.digamma (s + ↑n) + ∑ k ∈ Finset.range n, ((s + ↑k) ^ 2)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have hsm : 0 < (s + ↑m).re := by
        simp only [Complex.add_re, Complex.natCast_re]
        linarith [Nat.cast_nonneg (α := ℝ) m]
      rw [show (s : ℂ) + ↑(m + 1) = (s + ↑m) + 1 by push_cast; ring, deriv_digamma_add_one hsm,
        Finset.sum_range_succ, ih]
      ring
  have hle : ∀ n : ℕ, (deriv Complex.digamma s).im ≤ (deriv Complex.digamma (s + ↑n)).im := by
    intro n
    rw [htel n, Complex.add_im, Complex.im_sum]
    have hsum : (∑ k ∈ Finset.range n, (((s + (k : ℂ)) ^ 2)⁻¹).im) ≤ 0 :=
      Finset.sum_nonpos fun k _ ↦ im_inv_sq_nonpos
        (by simp only [Complex.add_re, Complex.natCast_re];
            linarith [Nat.cast_nonneg (α := ℝ) k, hs.le])
        (by simp only [Complex.add_im, Complex.natCast_im, add_zero]; exact him)
    linarith
  have hlim : Tendsto (fun n : ℕ ↦ (deriv Complex.digamma (s + ↑n)).im) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_im.tendsto 0).comp (tendsto_deriv_digamma_add_nat hs)
  exact ge_of_tendsto' hlim hle
theorem monotoneOn_re_digamma_quarter_vertical :
    MonotoneOn (fun T : ℝ ↦ (Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).re)
      (Set.Ici 0) := by
  have hre : ∀ T : ℝ, 0 < (1 / 4 + Complex.I * ((T : ℂ) / 2)).re := fun T ↦ by
    rw [show (1 / 4 + Complex.I * ((T : ℂ) / 2)).re = 1 / 4 by simp]; norm_num
  have hderiv : ∀ T : ℝ,
      HasDerivAt (fun t : ℝ ↦ (Complex.digamma (1 / 4 + Complex.I * ((t : ℂ) / 2))).re)
        (-(1 / 2) * (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).im) T := by
    intro T
    have haff : HasDerivAt (fun z : ℂ ↦ (1 / 4 : ℂ) + Complex.I * (z / 2)) (Complex.I * (1 / 2))
        (T : ℂ) := (((hasDerivAt_id (T : ℂ)).div_const 2).const_mul Complex.I).const_add (1 / 4)
    have hcomp := ((differentiableAt_digamma (hre T)).hasDerivAt.comp (T : ℂ) haff).comp_ofReal
    have hg := Complex.reCLM.hasFDerivAt.comp_hasDerivAt T hcomp
    simp only [Complex.reCLM_apply, Function.comp_apply] at hg
    rw [show (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2)) * (Complex.I * (1 / 2))).re
        = -(1 / 2) * (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).im by
      simp [Complex.mul_re]; ring] at hg
    exact hg
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr fun T ↦ (hderiv T).continuousAt).continuousOn
  · exact fun T _ ↦ (hderiv T).differentiableAt.differentiableWithinAt
  · intro T hT
    rw [interior_Ici] at hT
    rw [(hderiv T).deriv]
    have him : (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).im ≤ 0 := by
      refine im_deriv_digamma_nonpos (hre T) ?_
      have hval : (1 / 4 + Complex.I * ((T : ℂ) / 2)).im = T / 2 := by simp
      rw [hval]; linarith [Set.mem_Ioi.mp hT]
    linarith
end Complex
end
end CountPort85
section CountPort86
section
open MeasureTheory Filter
open scoped Topology Real
open Complex
theorem hasDerivAt_riemannSiegelTheta {T : ℝ} (hT : 0 < T) :
    HasDerivAt riemannSiegelTheta
      (1 / 2 * (Complex.digamma (1 / 4 + Complex.I * (T / 2))).re
        - 1 / 2 * Real.log Real.pi) T := by
  set w : ℂ := 1 / 4 + Complex.I * ((T : ℂ) / 2) with hw
  have hre : 0 < w.re := by rw [show w.re = 1 / 4 by rw [hw]; simp]; norm_num
  have hcurve := ((hasDerivAt_logGamma hre).comp (T : ℂ)
    ((((hasDerivAt_id (T : ℂ)).div_const 2).const_mul Complex.I).const_add (1 / 4))).comp_ofReal
  have hg := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt T hcurve).sub
    (((hasDerivAt_id T).div_const 2).mul_const (Real.log Real.pi))
  simp only [Complex.imCLM_apply, Function.comp_apply] at hg
  rw [show (Complex.digamma w * (Complex.I * (1 / 2))).im - 1 / 2 * Real.log Real.pi
      = 1 / 2 * (Complex.digamma w).re - 1 / 2 * Real.log Real.pi by
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      show ((1 : ℂ) / 2).re = 1 / 2 by simp, show ((1 : ℂ) / 2).im = 0 by simp]
    ring] at hg
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hT] with s (hs : (0 : ℝ) < s)
  exact riemannSiegelTheta_eq_im_logGamma hs.le
theorem continuousOn_riemannSiegelTheta : ContinuousOn riemannSiegelTheta (Set.Ici 0) := by
  have hline : Continuous fun T : ℝ ↦ (1 / 4 : ℂ) + Complex.I * ((T : ℂ) / 2) :=
    ((Complex.continuous_ofReal.div_const 2).const_mul Complex.I).const_add (1 / 4)
  have hcurve : Continuous fun T : ℝ ↦ logGamma (1 / 4 + Complex.I * ((T : ℂ) / 2)) :=
    continuous_iff_continuousAt.2 fun T ↦ ContinuousAt.comp
      (f := fun T : ℝ ↦ (1 / 4 : ℂ) + Complex.I * ((T : ℂ) / 2))
      (hasDerivAt_logGamma (show 0 < (1 / 4 + Complex.I * ((T : ℂ) / 2)).re by
        rw [show (1 / 4 + Complex.I * ((T : ℂ) / 2)).re = 1 / 4 by simp]; norm_num)).continuousAt
      hline.continuousAt
  exact ((Complex.continuous_im.comp hcurve).sub
    ((continuous_id.div_const 2).mul continuous_const)).continuousOn.congr
      fun T hT ↦ riemannSiegelTheta_eq_im_logGamma hT
open Set
abbrev gramDomain : Set ℝ := Ici 7
private theorem log_pi_lt_re_digamma_quarter_seven :
    Real.log Real.pi < (Complex.digamma (1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2))).re := by
  set s : ℂ := 1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2) with hs_def
  have hsre : s.re = 1 / 4 := by rw [hs_def]; simp
  have hsim : s.im = 7 / 2 := by rw [hs_def]; simp
  have hnormSq : Complex.normSq s = 197 / 16 := by
    rw [Complex.normSq_apply, hsre, hsim]; norm_num
  have hnorm_pos : 0 < ‖s‖ :=
    norm_pos_iff.mpr (Complex.ne_zero_of_re_pos (by rw [hsre]; norm_num))
  have hnorm_sq : ‖s‖ ^ 2 = 197 / 16 := by rw [Complex.sq_norm]; exact hnormSq
  have hnorm_lo : (3.5088 : ℝ) < ‖s‖ := by
    nlinarith [hnorm_sq, hnorm_pos, sq_nonneg (‖s‖ - 3.5088)]
  have hDbound : ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      ≤ (1 / 12 + 3 / (2 * π ^ 2 * (1 / 4))) * ‖s‖ ^ (-(2 : ℤ)) :=
    Complex.Stirling.norm_digamma_sub_log_le' (by norm_num) s (by rw [hsre])
  have hinv_re : ((2 * s)⁻¹).re = 2 / 197 := by
    rw [Complex.inv_re, Complex.normSq_mul, Complex.mul_re]
    simp only [hsre, hsim, hnormSq]
    norm_num
  have hdecomp : (Complex.digamma s).re = Real.log ‖s‖ - 2 / 197
      + (Complex.digamma s - Complex.log s + (2 * s)⁻¹).re := by
    rw [Complex.add_re, Complex.sub_re, Complex.log_re, hinv_re]; ring
  have hDre : -‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      ≤ (Complex.digamma s - Complex.log s + (2 * s)⁻¹).re :=
    (abs_le.1 (Complex.abs_re_le_norm _)).1
  have hπ2 : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d6, Real.pi_pos]
  have hDbound2 : ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖ ≤ 0.06 := by
    refine hDbound.trans ?_
    rw [show ‖s‖ ^ (-(2 : ℤ)) = 16 / 197 by
      rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hnorm_sq]; norm_num]
    have hv : 3 / (2 * π ^ 2 * (1 / 4)) < 0.6080 := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [hπ2]
    nlinarith [hv]
  have hlogdiff : 1 - π / ‖s‖ ≤ Real.log ‖s‖ - Real.log π := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ‖s‖ / π by positivity)
    rwa [Real.log_div hnorm_pos.ne' Real.pi_pos.ne', inv_div] at h
  have hu : π / ‖s‖ < 0.8954 := by
    rw [div_lt_iff₀ hnorm_pos]; nlinarith [Real.pi_lt_d4, hnorm_lo]
  linarith [hdecomp, hDre, hDbound2, hlogdiff, hu]
private theorem le_deriv_riemannSiegelTheta {x : ℝ} (hx : 7 < x) :
    ((Complex.digamma (1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2))).re - Real.log π) / 2
      ≤ deriv riemannSiegelTheta x := by
  rw [(hasDerivAt_riemannSiegelTheta (by linarith : (0 : ℝ) < x)).deriv]
  have hmono := Complex.monotoneOn_re_digamma_quarter_vertical
    (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 7)) (Set.mem_Ici.mpr (by linarith : (0:ℝ) ≤ x)) hx.le
  simp only at hmono
  linarith
theorem strictMonoOn_riemannSiegelTheta_gramDomain :
    StrictMonoOn riemannSiegelTheta gramDomain := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 7)
    (continuousOn_riemannSiegelTheta.mono (Ici_subset_Ici.mpr (by norm_num))) fun x hx ↦ ?_
  rw [interior_Ici] at hx
  linarith [le_deriv_riemannSiegelTheta (Set.mem_Ioi.mp hx), log_pi_lt_re_digamma_quarter_seven]
theorem tendsto_riemannSiegelTheta_atTop : atTop.Tendsto riemannSiegelTheta atTop := by
  set c := ((Complex.digamma (1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2))).re - Real.log π) / 2
    with hc
  have hc_pos : 0 < c := by rw [hc]; linarith [log_pi_lt_re_digamma_quarter_seven]
  have hcont := continuousOn_riemannSiegelTheta.mono (Ici_subset_Ici.mpr (by norm_num : (0:ℝ) ≤ 7))
  have hdiff : DifferentiableOn ℝ riemannSiegelTheta (interior (Ici (7 : ℝ))) := by
    rw [interior_Ici]
    exact fun x hx ↦ (hasDerivAt_riemannSiegelTheta (by linarith [Set.mem_Ioi.mp hx] :
      (0 : ℝ) < x)).differentiableAt.differentiableWithinAt
  have hlin : ∀ x ∈ Ici (7 : ℝ), c * (x - 7) ≤ riemannSiegelTheta x - riemannSiegelTheta 7 :=
    fun x hx ↦ Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici 7) hcont hdiff
      (fun x hx ↦ hc ▸ le_deriv_riemannSiegelTheta (by rwa [interior_Ici] at hx))
      7 Set.self_mem_Ici x hx (Set.mem_Ici.mp hx)
  have hg : Tendsto (fun x : ℝ ↦ riemannSiegelTheta 7 + c * (x - 7)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (Tendsto.const_mul_atTop hc_pos (tendsto_atTop_add_const_right atTop (-7) tendsto_id))
  refine tendsto_atTop_mono' atTop ?_ hg
  filter_upwards [eventually_ge_atTop (7 : ℝ)] with x hx
  linarith [hlin x (Set.mem_Ici.mpr hx)]
end
end CountPort86
section CountPort87
section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f g : 𝕜 → F}
end
end CountPort87
section CountPort88
section
open MeasureTheory Real
open scoped Nat
namespace Real
end Real
section Moments
variable {b : ℝ}
end Moments
end
end CountPort88
section CountPort89
section
open scoped Real
namespace Complex
end Complex
end
end CountPort89
section CountPort90
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def line (a w : ℝ) : ℂ := (a + w : ℝ) + (w : ℝ) * I
@[simp]
theorem line_re (a w : ℝ) : (line a w).re = a + w := by simp [line]
@[simp]
theorem line_im (a w : ℝ) : (line a w).im = w := by simp [line]
@[fun_prop]
theorem continuous_line (a : ℝ) : Continuous (line a) := by
  unfold line; fun_prop
end Zeta.RiemannSiegel
end
end CountPort90
section CountPort91
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
end Zeta.RiemannSiegel
end
end CountPort91
section CountPort92
section
open Complex Filter Topology
open scoped Real
namespace Zeta.RiemannSiegel
end Zeta.RiemannSiegel
end
end CountPort92
section CountPort93
section
open scoped Real
namespace Complex
end Complex
end
end CountPort93
section CountPort94
section
open scoped Real
namespace Complex
end Complex
end
end CountPort94
section CountPort95
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel
end Zeta.RiemannSiegel
end
end CountPort95
section CountPort96
section
open Complex MeasureTheory
open scoped Real
namespace Complex
end Complex
namespace Zeta.RiemannSiegel
end Zeta.RiemannSiegel
end
end CountPort96
section CountPort97
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def modelFun (p x : ℂ) : ℂ :=
  exp (2 * π * I * (x - p) ^ 2) / (exp (π * I * x) - exp (-(π * I * x)))
noncomputable def modelIntegrand (p : ℂ) (a w : ℝ) : ℂ :=
  modelFun p (line a w)
noncomputable def modelIntegral (p : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, modelIntegrand p a w
end Zeta.RiemannSiegel
end
end CountPort97
section CountPort98
section
open Complex MeasureTheory
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def modelMomentIntegrand (n : ℕ) (p : ℂ) (a w : ℝ) : ℂ :=
  (line a w - p) ^ n * modelIntegrand p a w
noncomputable def modelMoment (n : ℕ) (p : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, modelMomentIntegrand n p a w
end Zeta.RiemannSiegel
end
end CountPort98
section CountPort99
section
open Complex
open scoped Real
namespace Zeta.RiemannSiegel
noncomputable def mainSumOfPhase (θ t : ℝ) (ν : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ν, Real.cos (θ - t * Real.log n) / Real.sqrt n
noncomputable def correction (p : ℝ) : ℝ :=
  2 * (exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2)).re
noncomputable def correctionLinear (p : ℝ) : ℝ :=
  2 * (exp (-((π / 8 : ℝ) * I)) *
    (-(1 / 2) * modelMoment 1 (p : ℂ) (1 / 2) - 2 * π * I / 3 * modelMoment 3 (p : ℂ) (1 / 2))).re
end Zeta.RiemannSiegel
open Zeta.RiemannSiegel
noncomputable abbrev hardyZApproximantRS (t : ℝ) : ℝ :=
  mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
    - (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
        * (correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
          + correctionLinear (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
              / Real.sqrt (t / (2 * π)))
noncomputable abbrev hardyZErrorBoundRS (t : ℝ) : ℝ :=
  25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ) + 1 / 32 * (t / (2 * π)) ^ (-(15 / 4) : ℝ)
noncomputable abbrev hardyZApproximantRS₀ (t : ℝ) : ℝ :=
  mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
    - (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
        * correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
noncomputable abbrev hardyZErrorBoundRS₀ (t : ℝ) : ℝ :=
  hardyZErrorBoundRS t + 13 / 10 * (t / (2 * π)) ^ (-(3 / 4) : ℝ)
end
end CountPort99
section CountPort100
section
namespace Zeta.Certificates
structure ZIntervalEM extends NonemptyInterval ℝ where
  fstCutoff : ℕ
  sndCutoff : ℕ
  fstBernoulli : ℕ
  sndBernoulli : ℕ
abbrev ZIntervalRS := NonemptyInterval ℝ
noncomputable abbrev ZIntervalEM.fstVal (I : ZIntervalEM) : ℝ :=
  hardyZApproximantEM I.fstBernoulli I.fstCutoff I.fst
noncomputable abbrev ZIntervalEM.sndVal (I : ZIntervalEM) : ℝ :=
  hardyZApproximantEM I.sndBernoulli I.sndCutoff I.snd
noncomputable abbrev ZIntervalRS.fstVal (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS I.fst
noncomputable abbrev ZIntervalRS.sndVal (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS I.snd
noncomputable abbrev ZIntervalRS.fstVal₀ (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS₀ I.fst
noncomputable abbrev ZIntervalRS.sndVal₀ (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS₀ I.snd
structure ZIntervalEM.Certificate (I : ZIntervalEM) where
  fst_nonneg : 0 ≤ I.fst
  fstBernoulli_pos : 0 < I.fstBernoulli
  fstCutoff_pos : 0 < I.fstCutoff
  sndBernoulli_pos : 0 < I.sndBernoulli
  sndCutoff_pos : 0 < I.sndCutoff
  is_sign_change : I.fstVal * I.sndVal < 0
  fst_error : ‖I.fstVal‖ > hardyZErrorBoundEM I.fstBernoulli I.fstCutoff I.fst
  snd_error : ‖I.sndVal‖ > hardyZErrorBoundEM I.sndBernoulli I.sndCutoff I.snd
structure ZIntervalRS.Certificate (I : ZIntervalRS) where
  le_fst : 32 * Real.pi ≤ I.fst
  is_sign_change : I.fstVal * I.sndVal < 0
  fst_error : ‖I.fstVal‖ > hardyZErrorBoundRS I.fst
  snd_error : ‖I.sndVal‖ > hardyZErrorBoundRS I.snd
namespace ZIntervalRS.Certificate
variable {I : ZIntervalRS}
theorem fst_nonneg (h : I.Certificate) : 0 ≤ I.fst :=
  le_trans (by positivity) h.le_fst
end ZIntervalRS.Certificate
structure ZIntervalRS.Certificate₀ (I : ZIntervalRS) where
  le_fst : 32 * Real.pi ≤ I.fst
  is_sign_change : I.fstVal₀ * I.sndVal₀ < 0
  fst_error : ‖I.fstVal₀‖ > hardyZErrorBoundRS₀ I.fst
  snd_error : ‖I.sndVal₀‖ > hardyZErrorBoundRS₀ I.snd
namespace ZIntervalRS.Certificate₀
variable {I : ZIntervalRS}
theorem fst_nonneg (h : I.Certificate₀) : 0 ≤ I.fst :=
  le_trans (by positivity) h.le_fst
end ZIntervalRS.Certificate₀
structure CertifiedZeroIntervals where
  intervals : List (NonemptyInterval ℝ)
  fst_nonneg : ∀ I ∈ intervals, 0 ≤ I.fst
  has_zero : ∀ I ∈ intervals, ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1/2 + Complex.I * t) = 0
  disj : intervals.IsChain fun I J ↦ I.snd ≤ J.fst
@[simp]
noncomputable def CertifiedZeroIntervals.height (C : CertifiedZeroIntervals) : ℝ :=
  if h : C.intervals = [] then 0 else (C.intervals.maxOn (fun I ↦ I.snd) h).snd
end Zeta.Certificates
open Zeta.Certificates
namespace Zeta.Certificates
open Complex Set
noncomputable def CertifiedZeroIntervals.zeros (C : CertifiedZeroIntervals) : List ℂ :=
  (C.intervals.pmap (fun I hI ↦ (C.has_zero I hI).choose) (by simp)).map
      fun t : ℝ ↦ 1/2 + I * t
end Zeta.Certificates
end
end CountPort100
section CountPort101
section
namespace Zeta.Certificates
open Real Set
structure GramPoint extends NonemptyInterval ℝ where
  idx : ℕ
  fstCutoff : ℕ
  fstBernoulli : ℕ
  sndCutoff : ℕ
  sndBernoulli : ℕ
noncomputable abbrev GramPoint.fstVal (G : GramPoint) : ℝ :=
  riemannSiegelThetaApproximant G.fstBernoulli G.fstCutoff G.fst
noncomputable abbrev GramPoint.sndVal (G : GramPoint) : ℝ :=
  riemannSiegelThetaApproximant G.sndBernoulli G.sndCutoff G.snd
structure GramPoint.Certificate (G : GramPoint) where
  fst_nonneg : 0 ≤ G.fst
  snd_nonneg : 0 ≤ G.snd
  fstBernoulli_pos : 0 < G.fstBernoulli
  sndBernoulli_pos : 0 < G.sndBernoulli
  fst_bound : G.idx * π - G.fstVal >
    riemannSiegelThetaStirlingErrorBound' G.fstBernoulli G.fstCutoff G.fst
  snd_bound : G.sndVal - G.idx * π >
    riemannSiegelThetaStirlingErrorBound' G.sndBernoulli G.sndCutoff G.snd
structure GramBlock where
  left : GramPoint
  right : GramPoint
  zeros : List (NonemptyInterval ℝ)
  seq : left.idx + 1 = right.idx
  separated : left.snd ≤ right.fst
structure GramBlock.Certificate (G : GramBlock) where
  left_certificate : G.left.Certificate
  right_certificate : G.right.Certificate
  has_zero : ∀ z ∈ G.zeros, ∃ t ∈ Set.Ioo z.fst z.snd, riemannZeta (1 / 2 + Complex.I * t) = 0
  contains_zero : ∃ z ∈ G.zeros, z.fst ∈ Icc G.left.snd G.right.fst ∧
    z.snd ∈ Icc G.left.snd G.right.fst
structure CertifiedGramBlockSeq where
  blocks : List GramBlock
  seq : blocks.IsChain fun a b ↦ a.right.idx = b.left.idx
  cert : ∀ b ∈ blocks, b.Certificate
  non_empty : blocks ≠ []
  wide : (5 + (0.128 : ℝ) * ((blocks.getLast non_empty).right.snd / (2 * π)).log) <
    ((blocks.getLast non_empty).right.fst - (blocks.head non_empty).left.snd) / 2
  high : 168 * π < (blocks.head non_empty).left.fst
end Zeta.Certificates
end
end CountPort101
section CountPort102
section
open Real Set Filter Zeta.Certificates Complex MeasureTheory
noncomputable instance {T : ℝ} : Fintype (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :=
  (Kadiri.zeroes_rect_univ_positive_height_finite T).fintype
lemma riemannZeta.N_eq_sum (T : ℝ) :
    riemannZeta.N T = ∑ ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset,
      (riemannZeta.order ρ : ℝ) := by
  rw [riemannZeta.N, riemannZeta.zeroes_sum, tsum_fintype, ← Finset.sum_set_coe]
  exact Finset.sum_congr rfl fun _ _ ↦ one_mul _
private lemma riemannZeta.order_nonneg_of_mem_toFinset {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset) :
    (0 : ℝ) ≤ (riemannZeta.order ρ : ℝ) := by
  exact_mod_cast (Kadiri.riemannZeta_order_pos_positiveHeightZero
    ⟨ρ, Set.mem_toFinset.1 hρ⟩).le
private theorem riemannZeta.zeroes_rect_Ioo_subset {τ t : ℝ} (h : τ ≤ t) :
    riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 τ) ⊆
      riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 t) :=
  fun _ hz ↦ ⟨hz.1, Set.Ioo_subset_Ioo_right h hz.2.1, hz.2.2⟩
theorem riemannZeta.N_mono : Monotone riemannZeta.N := fun τ t hτt ↦ by
  rw [riemannZeta.N_eq_sum, riemannZeta.N_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun _ hz ↦ Set.mem_toFinset.2 (zeroes_rect_Ioo_subset hτt (Set.mem_toFinset.1 hz)))
    fun _ hρ _ ↦ riemannZeta.order_nonneg_of_mem_toFinset hρ
namespace Zeta.Certificates
end Zeta.Certificates
end
end CountPort102


