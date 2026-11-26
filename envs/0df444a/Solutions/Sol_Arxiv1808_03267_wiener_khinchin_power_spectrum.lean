-- Prove2me | solution 1 for Arxiv1808_03267.wiener_khinchin_power_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T10:34:14.74636+00:00
-- url     : https://prove2.me/submissions/975d5207-b2b3-44bc-b866-51979d453966

import Mathlib
import Definitions.Def_Arxiv1808_03267_Basic

open MeasureTheory Filter Topology Metric Set SchwartzMap
open scoped FourierTransform RealInnerProductSpace ComplexInnerProductSpace ContDiff SchwartzMap

noncomputable section
set_option maxHeartbeats 400000

namespace WK
open Arxiv1808_03267

/-- Translation identity for the Fourier transform. -/
lemma fourier_comp_add (E : Plane → ℂ) (x u : Plane) :
    𝓕 (fun z : Plane => E (z + x)) u = 𝐞 (⟪x, u⟫) * 𝓕 E u := by
  have h := congr_fun (VectorFourier.fourierIntegral_comp_add_right
      (e := Real.fourierChar) (μ := volume) (innerₗ Plane) E x) u
  have h' :
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ Plane) (E ∘ fun v => v + x) u =
        𝐞 (⟪x, u⟫) * VectorFourier.fourierIntegral 𝐞 volume (innerₗ Plane) E u := by
    simpa [Circle.smul_def] using h
  exact h'

lemma integrable_normSq_fourier (f : 𝓢(Plane, ℂ)) :
    Integrable (fun u : Plane => ((‖𝓕 (f : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ)) := by
  have hmem : MemLp (𝓕 (f : Plane → ℂ)) 2 volume := by
    rw [← SchwartzMap.fourier_coe f]
    exact (𝓕 f).memLp 2 volume
  have hr : Integrable (fun u : Plane => ‖𝓕 (f : Plane → ℂ) u‖ ^ 2) := by
    have := hmem.integrable_norm_rpow (by norm_num : (2 : ENNReal) ≠ 0) (by simp : (2 : ENNReal) ≠ ⊤)
    simpa using this
  exact Integrable.ofReal (𝕜 := ℂ) hr

def translate_schwartz (f : 𝓢(Plane, ℂ)) (x : Plane) : 𝓢(Plane, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz (K := 1) ℂ
    (Function.HasTemperateGrowth.id.add (Function.HasTemperateGrowth.const x))
    (AntilipschitzWith.of_le_mul_dist (K := 1) (fun a b => by
      simp [dist_eq_norm, add_sub_add_right_eq_sub])) f

lemma translate_schwartz_apply (f : 𝓢(Plane, ℂ)) (x y : Plane) :
    translate_schwartz f x y = f (y + x) := rfl

lemma normSq_coe (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) z * z := by
  rw [← RCLike.normSq_eq_def' (K := ℂ)]
  exact Complex.normSq_eq_conj_mul_self

/-- Wiener–Khinchin for Schwartz functions. -/
lemma wk_schwartz (f : 𝓢(Plane, ℂ)) (x : Plane) :
    𝓕⁻ (fun u : Plane => ((‖𝓕 (f : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ)) x =
      autocorrelation (f : Plane → ℂ) x := by
  let fτ := translate_schwartz f x
  have hcoe : ∀ u : Plane, 𝓕 fτ u = 𝓕 (fun z : Plane => (f : Plane → ℂ) (z + x)) u := by
    intro u
    have hfτ : ⇑fτ = fun z : Plane => (f : Plane → ℂ) (z + x) := by
      ext y; exact translate_schwartz_apply f x y
    rw [SchwartzMap.fourier_coe fτ, hfτ]
  have hshift : ∀ u : Plane,
      𝓕 (fun z : Plane => (f : Plane → ℂ) (z + x)) u =
        𝐞 (⟪u, x⟫) * 𝓕 (f : Plane → ℂ) u := by
    intro u
    rw [fourier_comp_add, real_inner_comm]
  have h1 :
      𝓕⁻ (fun u : Plane => ((‖𝓕 (f : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ)) x =
        ∫ u : Plane, 𝐞 (⟪u, x⟫) • ((‖𝓕 (f : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ) :=
    Real.fourierInv_eq _ _
  have h1' :
      ∫ u : Plane, 𝐞 (⟪u, x⟫) • ((‖𝓕 (f : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ) =
        ∫ u : Plane, 𝐞 (⟪u, x⟫) * ((‖𝓕 (f : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp [Circle.smul_def]
  have h2 :
      ∫ u : Plane, 𝐞 (⟪u, x⟫) * ((‖𝓕 (f : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ) =
        ∫ u : Plane, (starRingEnd ℂ) (𝓕 (f : Plane → ℂ) u) *
          𝓕 (fun z : Plane => (f : Plane → ℂ) (z + x)) u := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [normSq_coe, hshift]
    ring
  have h3 :
      ∫ u : Plane, (starRingEnd ℂ) (𝓕 (f : Plane → ℂ) u) *
          𝓕 (fun z : Plane => (f : Plane → ℂ) (z + x)) u =
        ∫ u : Plane, (starRingEnd ℂ) (𝓕 f u) * 𝓕 fτ u := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [SchwartzMap.fourier_coe f, hcoe u]
  have h4 :
      ∫ u : Plane, (starRingEnd ℂ) (𝓕 f u) * 𝓕 fτ u =
        inner ℂ ((𝓕 f).toLp 2) ((𝓕 fτ).toLp 2) := by
    rw [inner_toL2_toL2_eq (𝓕 f) (𝓕 fτ) volume]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [RCLike.inner_apply, mul_comm]
  have h5 :
      inner ℂ ((𝓕 f).toLp 2) ((𝓕 fτ).toLp 2) =
        inner ℂ (f.toLp 2) (fτ.toLp 2) := by
    rw [← toLp_fourier_eq, ← toLp_fourier_eq, Lp.inner_fourier_eq]
  have h6 :
      inner ℂ (f.toLp 2) (fτ.toLp 2) =
        ∫ y : Plane, (starRingEnd ℂ) (f y) * f (y + x) := by
    rw [inner_toL2_toL2_eq f fτ volume]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [RCLike.inner_apply, mul_comm, translate_schwartz_apply]
  have h7 :
      ∫ y : Plane, (starRingEnd ℂ) (f y) * f (y + x) =
        autocorrelation (f : Plane → ℂ) x := by
    unfold autocorrelation
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [add_comm]
  exact (h1.trans (h1'.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))))


lemma iUnion_closedBall_nat : ⋃ n : ℕ, closedBall (0 : Plane) (n : ℝ) = (univ : Set Plane) := by
  ext x
  simp only [mem_iUnion, mem_closedBall, dist_zero_right, mem_univ, iff_true]
  exact exists_nat_ge ‖x‖

lemma exists_nat_ball_tail (f : Plane → ℂ) {p : ENNReal} (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hf : MemLp f p volume) {ε : ENNReal} (hε : 0 < ε) :
    ∃ N : ℕ, eLpNorm ((closedBall (0 : Plane) (N : ℝ))ᶜ.indicator f) p volume < ε := by
  have hdir : Directed (· ⊆ ·) fun n : ℕ => closedBall (0 : Plane) (n : ℝ) :=
    directed_of_isDirected_le fun a b hab =>
      closedBall_subset_closedBall (Nat.cast_le.mpr hab)
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hunion :
      ∫⁻ x, ‖f x‖ₑ ^ p.toReal =
        ⨆ n : ℕ, ∫⁻ x in closedBall (0 : Plane) (n : ℝ), ‖f x‖ₑ ^ p.toReal := by
    have := setLIntegral_iUnion_of_directed (μ := volume)
      (fun x : Plane => ‖f x‖ₑ ^ p.toReal) hdir
    rwa [iUnion_closedBall_nat, Measure.restrict_univ] at this
  have hmono : Monotone fun n : ℕ =>
      ∫⁻ x in closedBall (0 : Plane) (n : ℝ), ‖f x‖ₑ ^ p.toReal := by
    intro a b hab
    exact lintegral_mono_set (closedBall_subset_closedBall (Nat.cast_le.mpr hab))
  have htend : Tendsto (fun n : ℕ =>
      ∫⁻ x in closedBall (0 : Plane) (n : ℝ), ‖f x‖ₑ ^ p.toReal) atTop
      (𝓝 (∫⁻ x, ‖f x‖ₑ ^ p.toReal)) := by
    rw [hunion]
    exact tendsto_atTop_iSup hmono
  have hsum : ∀ n,
      (∫⁻ x in closedBall (0 : Plane) (n : ℝ), ‖f x‖ₑ ^ p.toReal) +
        ∫⁻ x in (closedBall (0 : Plane) (n : ℝ))ᶜ, ‖f x‖ₑ ^ p.toReal =
      ∫⁻ x, ‖f x‖ₑ ^ p.toReal := fun n =>
    lintegral_add_compl _ measurableSet_closedBall
  have hfin : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ≠ ⊤ :=
    ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt).1 hf.eLpNorm_lt_top).ne
  have hcompl : Tendsto (fun n : ℕ =>
      ∫⁻ x in (closedBall (0 : Plane) (n : ℝ))ᶜ, ‖f x‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ =>
        (∫⁻ x, ‖f x‖ₑ ^ p.toReal) -
          ∫⁻ x in closedBall (0 : Plane) (n : ℝ), ‖f x‖ₑ ^ p.toReal) atTop (𝓝 0) := by
      simpa [tsub_self] using
        ENNReal.Tendsto.sub (tendsto_const_nhds (x := ∫⁻ x, ‖f x‖ₑ ^ p.toReal)) htend (Or.inl hfin)
    apply this.congr
    intro n
    exact ENNReal.sub_eq_of_eq_add_rev
      (ne_top_of_le_ne_top hfin (by rw [← hsum n]; exact le_self_add)) (hsum n).symm
  have heq : ∀ n,
      eLpNorm ((closedBall (0 : Plane) (n : ℝ))ᶜ.indicator f) p volume =
        (∫⁻ x in (closedBall (0 : Plane) (n : ℝ))ᶜ, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
    intro n
    have hms : MeasurableSet (closedBall (0 : Plane) (n : ℝ))ᶜ := measurableSet_closedBall.compl
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hms, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hz : (0 : ENNReal) ^ (1 / p.toReal) = 0 := ENNReal.zero_rpow_of_pos (by positivity)
  have hrpow : Tendsto (fun n : ℕ =>
      (∫⁻ x in (closedBall (0 : Plane) (n : ℝ))ᶜ, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal))
      atTop (𝓝 0) := by
    have hto : Tendsto (fun n : ℕ =>
        (∫⁻ x in (closedBall (0 : Plane) (n : ℝ))ᶜ, ‖f x‖ₑ ^ p.toReal).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hcompl
      exact this
    have hr : Tendsto (fun n : ℕ =>
        (∫⁻ x in (closedBall (0 : Plane) (n : ℝ))ᶜ, ‖f x‖ₑ ^ p.toReal).toReal ^
          (p.toReal)⁻¹) atTop (𝓝 0) := by
      have := Filter.Tendsto.rpow_const (p := (p.toReal)⁻¹) hto (Or.inr (by positivity))
      simpa [Real.zero_rpow (show (p.toReal)⁻¹ ≠ 0 by positivity)] using this
    have hof : Tendsto (fun n : ℕ =>
        ENNReal.ofReal
          ((∫⁻ x in (closedBall (0 : Plane) (n : ℝ))ᶜ, ‖f x‖ₑ ^ p.toReal).toReal ^
            (p.toReal)⁻¹)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hr
    refine hof.congr fun n => ?_
    have hne : ∫⁻ x in (closedBall (0 : Plane) (n : ℝ))ᶜ, ‖f x‖ₑ ^ p.toReal ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (by rw [← hsum n]; exact le_add_left le_rfl)
    rw [show 1 / p.toReal = (p.toReal)⁻¹ from one_div _,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
      ENNReal.ofReal_toReal hne]
  have : Tendsto (fun n : ℕ =>
      eLpNorm ((closedBall (0 : Plane) (n : ℝ))ᶜ.indicator f) p volume) atTop (𝓝 0) :=
    hrpow.congr fun n => (heq n).symm
  exact (this.eventually (Iio_mem_nhds hε)).exists

lemma exists_ball_tail (f : Plane → ℂ) (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧
      eLpNorm ((closedBall (0 : Plane) R)ᶜ.indicator f) 1 volume ≤ ENNReal.ofReal ε ∧
      eLpNorm ((closedBall (0 : Plane) R)ᶜ.indicator f) 2 volume ≤ ENNReal.ofReal ε := by
  have hε0 : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  obtain ⟨N1, hN1⟩ := exists_nat_ball_tail f (by simp) (by simp) hf1 hε0
  obtain ⟨N2, hN2⟩ := exists_nat_ball_tail f (by simp) (by simp) hf2 hε0
  let N := max N1 (max N2 1)
  refine ⟨(N : ℝ), ?_, ?_, ?_⟩
  · exact_mod_cast (le_max_right N1 (max N2 1) |>.trans' (le_max_right N2 1))
  · have hsub : closedBall (0 : Plane) (N1 : ℝ) ⊆ closedBall (0 : Plane) (N : ℝ) :=
      closedBall_subset_closedBall (Nat.cast_le.mpr (le_max_left _ _))
    have : eLpNorm ((closedBall (0 : Plane) (N : ℝ))ᶜ.indicator f) 1 volume ≤
        eLpNorm ((closedBall (0 : Plane) (N1 : ℝ))ᶜ.indicator f) 1 volume :=
      eLpNorm_mono fun x => by
        simp only [norm_indicator_eq_indicator_norm]
        exact indicator_le_indicator_of_subset (compl_subset_compl.2 hsub) (fun _ => norm_nonneg _) x
    exact this.trans hN1.le
  · have hsub : closedBall (0 : Plane) (N2 : ℝ) ⊆ closedBall (0 : Plane) (N : ℝ) :=
      closedBall_subset_closedBall (Nat.cast_le.mpr
        ((le_max_left N2 1).trans (le_max_right N1 _)))
    have : eLpNorm ((closedBall (0 : Plane) (N : ℝ))ᶜ.indicator f) 2 volume ≤
        eLpNorm ((closedBall (0 : Plane) (N2 : ℝ))ᶜ.indicator f) 2 volume :=
      eLpNorm_mono fun x => by
        simp only [norm_indicator_eq_indicator_norm]
        exact indicator_le_indicator_of_subset (compl_subset_compl.2 hsub) (fun _ => norm_nonneg _) x
    exact this.trans hN2.le

/-- Simultaneous L¹ and L² approximation by a smooth compactly supported function. -/
lemma exists_smooth_approx (f : Plane → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Plane → ℂ, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (f - g) 1 volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (f - g) 2 volume ≤ ENNReal.ofReal ε := by
  have hf1' : MemLp f 1 volume := memLp_one_iff_integrable.2 hf1
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨R, hR1, htail1, htail2⟩ := exists_ball_tail f hf1' hf2 (ε / 3) hε3
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  let fR : Plane → ℂ := (closedBall (0 : Plane) R).indicator f
  have hfR2 : MemLp fR 2 volume := hf2.indicator measurableSet_closedBall
  have hfR1 : MemLp fR 1 volume := hf1'.indicator measurableSet_closedBall
  have hμ : volume (closedBall (0 : Plane) (R + 1)) < ⊤ :=
    (isCompact_closedBall 0 (R + 1)).measure_lt_top
  let C : ENNReal := volume (closedBall (0 : Plane) (R + 1))
  have hCfin : C ≠ ⊤ := hμ.ne
  have hCsqrt : 0 < C.toReal ^ (2 : ℝ)⁻¹ + 1 := by positivity
  let δ : ℝ := min (ε / 3) ((ε / 3) / (C.toReal ^ (2 : ℝ)⁻¹ + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨g0, hg0s, hg0d, hg0e⟩ :=
    hfR2.exist_eLpNorm_sub_le (p := 2) (by simp) (by simp) hδ
  let bump : ContDiffBump (0 : Plane) := ⟨R, R + 1, hRpos, by linarith⟩
  let g : Plane → ℂ := fun z => (bump z : ℝ) • g0 z
  have hg_cd : ContDiff ℝ ∞ g :=
    (bump.contDiff (n := ⊤)).smul hg0d
  have hg_supp : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Plane) bump.rOut) fun z hz => ?_
    have : z ∉ tsupport bump := by
      rw [bump.tsupport_eq]
      exact hz
    have hz0 : bump z = 0 := image_eq_zero_of_notMem_tsupport this
    simp [g, hz0]
  have hpt : ∀ z, g z = bump z * g0 z := fun z => by simp [g, smul_eq_mul]
  have hident : ∀ z, fR z - g z = bump z * (fR z - g0 z) := by
    intro z
    by_cases hz : z ∈ closedBall (0 : Plane) R
    · have hb : bump z = 1 := bump.one_of_mem_closedBall hz
      simp [hpt, hb]
    · have hfRz : fR z = 0 := Set.indicator_of_notMem hz _
      rw [hpt, hfRz]
      simp
  have hle : ∀ z, ‖fR z - g z‖ ≤ ‖fR z - g0 z‖ := by
    intro z
    have hmul : ‖(bump z : ℂ) * (fR z - g0 z)‖ = |bump z| * ‖fR z - g0 z‖ := by
      simp [norm_mul, Complex.norm_real]
    rw [hident, hmul, abs_of_nonneg bump.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) bump.le_one
  have h2close : eLpNorm (fR - g) 2 volume ≤ ENNReal.ofReal δ :=
    (eLpNorm_mono hle).trans hg0e
  have hsupp_diff : Function.support (fR - g) ⊆ closedBall (0 : Plane) (R + 1) := by
    intro z hz
    have : g z ≠ 0 ∨ fR z ≠ 0 := by
      contrapose! hz
      simp [Pi.sub_apply, hz]
    rcases this with hg | hfR
    · have hb' : bump z ≠ 0 := by
        intro h0; apply hg; simp [hpt, h0]
      have : z ∈ Function.support (fun w : Plane => (bump w : ℝ)) := hb'
      have hsupp := bump.support_eq
      have : z ∈ Metric.ball (0 : Plane) bump.rOut := by
        rw [← hsupp]; exact this
      exact ball_subset_closedBall this
    · have : z ∈ closedBall (0 : Plane) R := by
        contrapose! hfR
        exact Set.indicator_of_notMem hfR _
      exact closedBall_subset_closedBall (le_add_of_nonneg_right zero_le_one) this
  haveI : IsFiniteMeasure (volume.restrict (closedBall (0 : Plane) (R + 1))) :=
    ⟨by simpa [Measure.restrict_apply MeasurableSet.univ] using hμ⟩
  have h1bound :
      eLpNorm (fR - g) 1 volume ≤ eLpNorm (fR - g) 2 volume * C ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
    have hsup : eLpNorm (fR - g) 1 volume =
        eLpNorm (fR - g) 1 (volume.restrict (closedBall (0 : Plane) (R + 1))) := by
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
      refine eLpNorm_congr_ae ?_
      filter_upwards with z
      by_cases hz : z ∈ closedBall (0 : Plane) (R + 1)
      · simp [hz]
      · have : (fR - g) z = 0 := Function.notMem_support.mp (fun h => hz (hsupp_diff h))
        simp [hz, this]
    have hsup2 : eLpNorm (fR - g) 2 volume =
        eLpNorm (fR - g) 2 (volume.restrict (closedBall (0 : Plane) (R + 1))) := by
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
      refine eLpNorm_congr_ae ?_
      filter_upwards with z
      by_cases hz : z ∈ closedBall (0 : Plane) (R + 1)
      · simp [hz]
      · have : (fR - g) z = 0 := Function.notMem_support.mp (fun h => hz (hsupp_diff h))
        simp [hz, this]
    rw [hsup, hsup2]
    have hAe : AEStronglyMeasurable (fR - g)
        (volume.restrict (closedBall (0 : Plane) (R + 1))) :=
      (hfR1.sub (hg_cd.continuous.memLp_of_hasCompactSupport hg_supp)).aestronglyMeasurable.restrict
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict (closedBall (0 : Plane) (R + 1)))
      (p := 1) (q := 2) (by simp) hAe
    convert this using 2
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rfl
  -- convert the product bound into ofReal (ε/3)
  have h1close : eLpNorm (fR - g) 1 volume ≤ ENNReal.ofReal (ε / 3) := by
    refine h1bound.trans ?_
    have : 1 / (1 : ℝ) - 1 / (2 : ℝ) = (2 : ℝ)⁻¹ := by ring
    rw [this]
    have h2le : eLpNorm (fR - g) 2 volume ≤ ENNReal.ofReal δ := h2close
    have : ENNReal.ofReal δ * C ^ (2 : ℝ)⁻¹ ≤ ENNReal.ofReal (ε / 3) := by
      have hδle : δ ≤ (ε / 3) / (C.toReal ^ (2 : ℝ)⁻¹ + 1) := min_le_right _ _
      -- crude bound: ofReal δ * C^{1/2} ≤ ofReal (ε/3)
      have hpos : 0 ≤ C.toReal ^ (2 : ℝ)⁻¹ := by positivity
      have : δ * C.toReal ^ (2 : ℝ)⁻¹ ≤ ε / 3 := by
        have : δ * (C.toReal ^ (2 : ℝ)⁻¹ + 1) ≤ ε / 3 := by
          have hden : 0 < C.toReal ^ (2 : ℝ)⁻¹ + 1 := by positivity
          rw [← le_div_iff₀ hden]
          exact hδle
        linarith
      calc
        ENNReal.ofReal δ * C ^ (2 : ℝ)⁻¹
            = ENNReal.ofReal δ * ENNReal.ofReal (C.toReal ^ (2 : ℝ)⁻¹) := by
              rw [← ENNReal.ofReal_rpow_of_nonneg (ENNReal.toReal_nonneg) (by positivity)]
              rw [ENNReal.ofReal_toReal hCfin]
        _ = ENNReal.ofReal (δ * C.toReal ^ (2 : ℝ)⁻¹) := by
              rw [← ENNReal.ofReal_mul (le_of_lt hδ)]
        _ ≤ ENNReal.ofReal (ε / 3) := ENNReal.ofReal_le_ofReal this
    exact (mul_le_mul_of_nonneg_right h2le (by positivity)).trans this
  have hsplit : f - g = (fun z => (closedBall (0 : Plane) R)ᶜ.indicator f z) + (fR - g) := by
    ext z
    simp only [Pi.add_apply, Pi.sub_apply]
    by_cases hz : z ∈ closedBall (0 : Plane) R
    · simp [fR, hz]
    · simp [fR, hz, sub_eq_add_neg]
  have h3 : ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hε3.le hε3.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨g, hg_supp, hg_cd, ?_, ?_⟩
  · rw [hsplit]
    refine (eLpNorm_add_le ?_ ?_ le_rfl).trans ?_
    · exact (hf1'.indicator measurableSet_closedBall.compl).aestronglyMeasurable
    · exact (hfR1.sub (hg_cd.continuous.memLp_of_hasCompactSupport hg_supp)).aestronglyMeasurable
    · exact (add_le_add htail1 h1close).trans h3
  · rw [hsplit]
    refine (eLpNorm_add_le ?_ ?_ (by simp : (1 : ENNReal) ≤ 2)).trans ?_
    · exact (hf2.indicator measurableSet_closedBall.compl).aestronglyMeasurable
    · exact (hfR2.sub (hg_cd.continuous.memLp_of_hasCompactSupport hg_supp)).aestronglyMeasurable
    · exact (add_le_add htail2
        (h2close.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))).trans h3


lemma exists_schwartz_approx (f : Plane → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : 𝓢(Plane, ℂ),
      eLpNorm (f - (g : Plane → ℂ)) 1 volume ≤ ENNReal.ofReal ε ∧
      eLpNorm (f - (g : Plane → ℂ)) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨g0, hsupp, hcd, h1, h2⟩ := exists_smooth_approx f hf1 hf2 ε hε
  refine ⟨hsupp.toSchwartzMap hcd, ?_, ?_⟩
  · exact h1
  · exact h2

lemma schwartz_fourier_eLpNorm_eq (g : 𝓢(Plane, ℂ)) :
    eLpNorm (𝓕 (g : Plane → ℂ)) 2 volume = eLpNorm (g : Plane → ℂ) 2 volume := by
  let Fg : 𝓢(Plane, ℂ) := 𝓕 g
  have hcoe : 𝓕 (g : Plane → ℂ) = (Fg : Plane → ℂ) := (SchwartzMap.fourier_coe g).symm
  rw [hcoe]
  have htop1 : eLpNorm (Fg : Plane → ℂ) 2 volume ≠ ⊤ := (Fg.memLp 2 volume).eLpNorm_ne_top
  have htop2 : eLpNorm (g : Plane → ℂ) 2 volume ≠ ⊤ := (g.memLp 2 volume).eLpNorm_ne_top
  have e1 : (eLpNorm (Fg : Plane → ℂ) 2 volume).toReal =
      (eLpNorm (g : Plane → ℂ) 2 volume).toReal := by
    have h := Lp.norm_fourier_eq (g.toLp 2 volume)
    rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.norm_toLp, SchwartzMap.norm_toLp] at h
    exact h
  exact (ENNReal.toReal_eq_toReal_iff' htop1 htop2).1 e1

lemma fourier_sub_of_integrable {f g : Plane → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  ext u
  simp only [Pi.sub_apply, Real.fourier_eq]
  rw [← integral_sub]
  · refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp [smul_sub]
  · exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ u).2 hf
  · exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ u).2 hg

lemma schwartz_integrable (g : 𝓢(Plane, ℂ)) : Integrable (g : Plane → ℂ) :=
  memLp_one_iff_integrable.1 (g.memLp 1 volume)

lemma translate_memLp {p : ENNReal} {f : Plane → ℂ} (hf : MemLp f p volume) (x : Plane) :
    MemLp (fun y : Plane => f (y + x)) p volume :=
  hf.comp_measurePreserving (measurePreserving_add_right volume x)

lemma translate_eLpNorm {p : ENNReal} {f : Plane → ℂ} (hf : AEStronglyMeasurable f volume)
    (x : Plane) :
    eLpNorm (fun y : Plane => f (y + x)) p volume = eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_right volume x)

lemma autocorrelation_eq_inner {f : Plane → ℂ} (hf : MemLp f 2 volume) (x : Plane) :
    autocorrelation f x =
      inner ℂ (hf.toLp f) ((translate_memLp hf x).toLp (fun y => f (y + x))) := by
  unfold autocorrelation
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp (translate_memLp hf x)] with
    y hfy hty
  rw [RCLike.inner_apply, hfy, hty, mul_comm, add_comm]

lemma autocorr_diff_norm {f g : Plane → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x : Plane) :
    ‖autocorrelation f x - autocorrelation g x‖ ≤
      (eLpNorm (f - g) 2 volume).toReal *
        ((eLpNorm f 2 volume).toReal + (eLpNorm g 2 volume).toReal) := by
  have hτf := translate_memLp hf x
  have hτg := translate_memLp hg x
  set F := hf.toLp f
  set G := hg.toLp g
  set TF := hτf.toLp (fun y => f (y + x))
  set TG := hτg.toLp (fun y => g (y + x))
  have hsplit : autocorrelation f x - autocorrelation g x =
      inner ℂ (F - G) TF + inner ℂ G (TF - TG) := by
    rw [autocorrelation_eq_inner hf x, autocorrelation_eq_inner hg x, inner_sub_left,
      inner_sub_right]
    ring
  have nFG : ‖F - G‖ = (eLpNorm (f - g) 2 volume).toReal := by
    rw [← MemLp.toLp_sub hf hg, Lp.norm_toLp]
  have nTFG : ‖TF - TG‖ = (eLpNorm (f - g) 2 volume).toReal := by
    rw [← MemLp.toLp_sub hτf hτg, Lp.norm_toLp]
    have : eLpNorm ((fun y => f (y + x)) - fun y => g (y + x)) 2 volume =
        eLpNorm (fun y => (f - g) (y + x)) 2 volume := rfl
    rw [this, translate_eLpNorm (hf.sub hg).1 x]
  have nTF : ‖TF‖ = (eLpNorm f 2 volume).toReal := by
    rw [Lp.norm_toLp, translate_eLpNorm hf.1 x]
  have nG : ‖G‖ = (eLpNorm g 2 volume).toReal := Lp.norm_toLp g hg
  rw [hsplit]
  calc ‖inner ℂ (F - G) TF + inner ℂ G (TF - TG)‖
      ≤ ‖F - G‖ * ‖TF‖ + ‖G‖ * ‖TF - TG‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ = _ := by rw [nFG, nTFG, nTF, nG]; ring

lemma norm_fourier_le (f : Plane → ℂ) (u : Plane) :
    ‖𝓕 f u‖ ≤ ∫ v : Plane, ‖f v‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ Plane) f u

lemma norm_fourierInv_le (f : Plane → ℂ) (u : Plane) :
    ‖𝓕⁻ f u‖ ≤ ∫ v : Plane, ‖f v‖ := by
  show ‖VectorFourier.fourierIntegral 𝐞 volume (-innerₗ Plane) f u‖ ≤ _
  exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (-innerₗ Plane) f u

lemma integral_norm_eq_eLpNorm_one {f : Plane → ℂ} (hf : Integrable f) :
    ∫ v : Plane, ‖f v‖ = (eLpNorm f 1 volume).toReal := by
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable, eLpNorm_one_eq_lintegral_enorm]

lemma eLpNorm_one_toReal_le {f : Plane → ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : eLpNorm f 1 volume ≤ ENNReal.ofReal ε) :
    (eLpNorm f 1 volume).toReal ≤ ε := by
  have := ENNReal.toReal_mono (by simp) h
  simpa [ENNReal.toReal_ofReal hε] using this

lemma eLpNorm_two_toReal_le {f : Plane → ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : eLpNorm f 2 volume ≤ ENNReal.ofReal ε) :
    (eLpNorm f 2 volume).toReal ≤ ε := by
  have := ENNReal.toReal_mono (by simp) h
  simpa [ENNReal.toReal_ofReal hε] using this

lemma fourier_approx_pointwise (f : Plane → ℂ) (hf1 : Integrable f)
    (g : 𝓢(Plane, ℂ)) (u : Plane) :
    ‖𝓕 (g : Plane → ℂ) u - 𝓕 f u‖ ≤ (eLpNorm ((g : Plane → ℂ) - f) 1 volume).toReal := by
  have hgi := schwartz_integrable g
  have hsub := congrFun (fourier_sub_of_integrable hgi hf1) u
  rw [Pi.sub_apply] at hsub
  rw [← hsub]
  exact (norm_fourier_le ((g : Plane → ℂ) - f) u).trans
    (le_of_eq (integral_norm_eq_eLpNorm_one (hgi.sub hf1)))


lemma eLpNorm_sub_comm {p : ENNReal} (f g : Plane → ℂ) :
    eLpNorm (f - g) p volume = eLpNorm (g - f) p volume := by
  simpa [neg_sub] using (eLpNorm_neg (f := f - g) (p := p) (μ := volume)).symm

lemma continuous_of_integrable {f : Plane → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

lemma tendsto_ofReal_inv_succ :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  simpa [one_div, ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat

lemma tendsto_fourier_approx (f : Plane → ℂ) (hf1 : Integrable f)
    (g : ℕ → 𝓢(Plane, ℂ))
    (hg1 : ∀ n, eLpNorm (f - (g n : Plane → ℂ)) 1 volume ≤ ENNReal.ofReal ((n : ℝ) + 1)⁻¹)
    (u : Plane) :
    Tendsto (fun n : ℕ => 𝓕 (g n : Plane → ℂ) u) atTop (𝓝 (𝓕 f u)) := by
  have hnhds : Tendsto (fun n : ℕ => ‖𝓕 (g n : Plane → ℂ) u - 𝓕 f u‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (fourier_approx_pointwise f hf1 (g n) u).trans <|
        eLpNorm_one_toReal_le (by positivity)
          (by simpa [eLpNorm_sub_comm (g n : Plane → ℂ) f] using hg1 n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnhds

lemma tendsto_eLpNorm_of_sub_tendsto {f : Plane → ℂ} {g : ℕ → Plane → ℂ}
    {p : ENNReal} (hp : 1 ≤ p) (hf : AEStronglyMeasurable f volume)
    (hg : ∀ n, AEStronglyMeasurable (g n) volume)
    (hfin : eLpNorm f p volume ≠ ⊤)
    (h : Tendsto (fun n => eLpNorm (g n - f) p volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (g n) p volume) atTop (𝓝 (eLpNorm f p volume)) := by
  have hlo : Tendsto (fun n => eLpNorm f p volume - eLpNorm (g n - f) p volume)
      atTop (𝓝 (eLpNorm f p volume)) := by
    simpa [tsub_zero] using ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl hfin)
  have hhi : Tendsto (fun n => eLpNorm f p volume + eLpNorm (g n - f) p volume)
      atTop (𝓝 (eLpNorm f p volume)) := by
    simpa using Tendsto.add (tendsto_const_nhds (x := eLpNorm f p volume)) h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => ?_) (fun n => ?_)
  · have hc : eLpNorm (g n - f) p volume = eLpNorm (f - g n) p volume := eLpNorm_sub_comm _ _
    rw [hc]
    have heq : f = g n + (f - g n) := by ext; simp
    nth_rw 1 [heq]
    exact tsub_le_iff_right.2 (eLpNorm_add_le (hg n) (hf.sub (hg n)) hp)
  · have heq : g n = f + (g n - f) := by ext; simp
    nth_rw 1 [heq]
    exact eLpNorm_add_le hf ((hg n).sub hf) hp

lemma tendsto_eLpNorm_approx {f : Plane → ℂ}
    {g : ℕ → 𝓢(Plane, ℂ)} (hf : MemLp f 2 volume)
    (hg2 : ∀ n, eLpNorm (f - (g n : Plane → ℂ)) 2 volume ≤ ENNReal.ofReal ((n : ℝ) + 1)⁻¹) :
    Tendsto (fun n : ℕ => eLpNorm (g n : Plane → ℂ) 2 volume) atTop
      (𝓝 (eLpNorm f 2 volume)) :=
  tendsto_eLpNorm_of_sub_tendsto (p := 2) (by simp) hf.aestronglyMeasurable
    (fun n => ((g n).memLp 2 volume).aestronglyMeasurable) hf.eLpNorm_ne_top
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_ofReal_inv_succ
      (fun _ => bot_le) (fun n => by simpa [eLpNorm_sub_comm] using hg2 n))

lemma eLpNorm_fourier_sub_le_schwartz (f : Plane → ℂ) (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume) (g : 𝓢(Plane, ℂ)) :
    eLpNorm (𝓕 f - 𝓕 (g : Plane → ℂ)) 2 volume ≤
      eLpNorm (f - (g : Plane → ℂ)) 2 volume := by
  have hex : ∀ n : ℕ, ∃ h : 𝓢(Plane, ℂ),
      eLpNorm (f - (h : Plane → ℂ)) 1 volume ≤ ENNReal.ofReal ((n : ℝ) + 1)⁻¹ ∧
      eLpNorm (f - (h : Plane → ℂ)) 2 volume ≤ ENNReal.ofReal ((n : ℝ) + 1)⁻¹ :=
    fun n => exists_schwartz_approx f hf1 hf2 ((n : ℝ) + 1)⁻¹ (by positivity)
  choose h hh1 hh2 using hex
  have hpt : ∀ᵐ u : Plane,
      Tendsto (fun n : ℕ => (𝓕 (h n : Plane → ℂ) - 𝓕 (g : Plane → ℂ)) u)
        atTop (𝓝 ((𝓕 f - 𝓕 (g : Plane → ℂ)) u)) :=
    Eventually.of_forall fun u =>
      (tendsto_fourier_approx f hf1 h hh1 u).sub tendsto_const_nhds
  have hmeas : ∀ n, AEStronglyMeasurable (𝓕 (h n : Plane → ℂ) - 𝓕 (g : Plane → ℂ)) volume :=
    fun n => ((continuous_of_integrable (schwartz_integrable (h n))).sub
      (continuous_of_integrable (schwartz_integrable g))).aestronglyMeasurable
  have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) hmeas (𝓕 f - 𝓕 (g : Plane → ℂ)) hpt
  refine hlim.trans ?_
  have hcongr : (atTop.liminf fun n =>
      eLpNorm (𝓕 (h n : Plane → ℂ) - 𝓕 (g : Plane → ℂ)) 2 volume) =
      atTop.liminf fun n => eLpNorm ((h n : Plane → ℂ) - (g : Plane → ℂ)) 2 volume := by
    refine Filter.liminf_congr ?_
    filter_upwards with n
    have heq : 𝓕 (h n : Plane → ℂ) - 𝓕 (g : Plane → ℂ) =
        𝓕 ((h n : Plane → ℂ) - (g : Plane → ℂ)) :=
      (fourier_sub_of_integrable (schwartz_integrable (h n)) (schwartz_integrable g)).symm
    rw [heq, show (h n : Plane → ℂ) - (g : Plane → ℂ) = ⇑(h n - g) from rfl]
    exact schwartz_fourier_eLpNorm_eq (h n - g)
  rw [hcongr]
  have hto : Tendsto (fun n => eLpNorm ((h n : Plane → ℂ) - (g : Plane → ℂ)) 2 volume)
      atTop (𝓝 (eLpNorm (f - (g : Plane → ℂ)) 2 volume)) := by
    refine tendsto_eLpNorm_of_sub_tendsto (p := 2) (by simp)
      (hf2.aestronglyMeasurable.sub ((g.memLp 2 volume).aestronglyMeasurable))
      (fun n => ((h n).memLp 2 volume).aestronglyMeasurable.sub
        ((g.memLp 2 volume).aestronglyMeasurable))
      (hf2.sub (g.memLp 2 volume)).eLpNorm_ne_top ?_
    have : (fun n => eLpNorm
        (((h n : Plane → ℂ) - (g : Plane → ℂ)) - (f - (g : Plane → ℂ))) 2 volume) =
        fun n => eLpNorm ((h n : Plane → ℂ) - f) 2 volume := by
      ext n; congr 1; ext x; simp
    rw [this]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_ofReal_inv_succ
      (fun _ => bot_le) (fun n => by simpa [eLpNorm_sub_comm] using hh2 n)
  exact (hto.liminf_eq).le

lemma fourier_memLp_two (f : Plane → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume ∧
      eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  have hex : ∀ n : ℕ, ∃ g : 𝓢(Plane, ℂ),
      eLpNorm (f - (g : Plane → ℂ)) 1 volume ≤ ENNReal.ofReal ((n : ℝ) + 1)⁻¹ ∧
      eLpNorm (f - (g : Plane → ℂ)) 2 volume ≤ ENNReal.ofReal ((n : ℝ) + 1)⁻¹ :=
    fun n => exists_schwartz_approx f hf1 hf2 ((n : ℝ) + 1)⁻¹ (by positivity)
  choose g hg1 hg2 using hex
  have hpt : ∀ᵐ u : Plane, Tendsto (fun n : ℕ => 𝓕 (g n : Plane → ℂ) u) atTop (𝓝 (𝓕 f u)) :=
    Eventually.of_forall fun u => tendsto_fourier_approx f hf1 g hg1 u
  have hmeas : ∀ n, AEStronglyMeasurable (𝓕 (g n : Plane → ℂ)) volume :=
    fun n => (continuous_of_integrable (schwartz_integrable (g n))).aestronglyMeasurable
  have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) hmeas (𝓕 f) hpt
  have hto_g := tendsto_eLpNorm_approx hf2 hg2
  have hto_Fg : Tendsto (fun n => eLpNorm (𝓕 (g n : Plane → ℂ)) 2 volume) atTop
      (𝓝 (eLpNorm f 2 volume)) := by
    simpa [fun n => schwartz_fourier_eLpNorm_eq (g n)] using hto_g
  have hftop : eLpNorm (𝓕 f) 2 volume < ⊤ :=
    hlim.trans_lt (hto_Fg.liminf_eq.symm ▸ hf2.eLpNorm_lt_top)
  have hfF : MemLp (𝓕 f) 2 volume :=
    ⟨(continuous_of_integrable hf1).aestronglyMeasurable, hftop⟩
  have hle : eLpNorm (𝓕 f) 2 volume ≤ eLpNorm f 2 volume :=
    hlim.trans_eq hto_Fg.liminf_eq
  have hge : eLpNorm f 2 volume ≤ eLpNorm (𝓕 f) 2 volume := by
    have hdiff : Tendsto (fun n => eLpNorm (𝓕 (g n : Plane → ℂ) - 𝓕 f) 2 volume)
        atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_ofReal_inv_succ
        (fun _ => bot_le) (fun n => ?_)
      rw [eLpNorm_sub_comm]
      exact (eLpNorm_fourier_sub_le_schwartz f hf1 hf2 (g n)).trans (hg2 n)
    have := tendsto_eLpNorm_of_sub_tendsto (p := 2) (by simp)
      hfF.aestronglyMeasurable hmeas hfF.eLpNorm_ne_top hdiff
    -- this is Tendsto eLpNorm (𝓕 g_n) → eLpNorm (𝓕 f)
    -- but eLpNorm (𝓕 g_n) → eLpNorm f, so eLpNorm f = eLpNorm (𝓕 f)
    have h1 := this
    have h2 := hto_Fg
    exact le_of_eq (tendsto_nhds_unique h2 h1)
  exact ⟨hfF, le_antisymm hle hge⟩


lemma integrable_normSq_of_memLp_two {f : Plane → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun u : Plane => ((‖f u‖ ^ 2 : ℝ) : ℂ)) :=
  Integrable.ofReal (𝕜 := ℂ) ((memLp_two_iff_integrable_sq_norm hf.1).1 hf)

lemma fourierInv_sub_of_integrable {f g : Plane → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕⁻ (f - g) = 𝓕⁻ f - 𝓕⁻ g := by
  ext u
  calc 𝓕⁻ (f - g) u
      = 𝓕 (f - g) (-u) := Real.fourierInv_eq_fourier_neg _ _
    _ = (𝓕 f - 𝓕 g) (-u) := congrFun (fourier_sub_of_integrable hf hg) (-u)
    _ = 𝓕 f (-u) - 𝓕 g (-u) := rfl
    _ = 𝓕⁻ f u - 𝓕⁻ g u := by
        simp only [Real.fourierInv_eq_fourier_neg]

lemma fourierInv_diff_le {F G : Plane → ℂ} (hF : Integrable F) (hG : Integrable G) (x : Plane) :
    ‖𝓕⁻ F x - 𝓕⁻ G x‖ ≤ (eLpNorm (F - G) 1 volume).toReal := by
  have h := congrFun (fourierInv_sub_of_integrable hF hG) x
  rw [Pi.sub_apply] at h
  rw [← h]
  exact (norm_fourierInv_le (F - G) x).trans
    (le_of_eq (integral_norm_eq_eLpNorm_one (hF.sub hG)))

lemma eLpNorm_fourier_sub_eq (f g : Plane → ℂ)
    (hf1 : Integrable f) (hg1 : Integrable g)
    (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume) :
    eLpNorm (𝓕 f - 𝓕 g) 2 volume = eLpNorm (f - g) 2 volume := by
  have h := fourier_memLp_two (f - g) (hf1.sub hg1) (hf2.sub hg2)
  rw [← h.2, fourier_sub_of_integrable hf1 hg1]

lemma eLpNorm_normSq_sub {f g : Plane → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    eLpNorm (fun u : Plane => ((‖f u‖ ^ 2 : ℝ) : ℂ) - ((‖g u‖ ^ 2 : ℝ) : ℂ)) 1 volume ≤
      eLpNorm (f - g) 2 volume * (eLpNorm f 2 volume + eLpNorm g 2 volume) := by
  have hpt : ∀ u, ‖((‖f u‖ ^ 2 : ℝ) : ℂ) - ((‖g u‖ ^ 2 : ℝ) : ℂ)‖ ≤
      ‖(f - g) u‖ * (‖f u‖ + ‖g u‖) := by
    intro u
    have hco : ((‖f u‖ ^ 2 : ℝ) : ℂ) - ((‖g u‖ ^ 2 : ℝ) : ℂ) =
        ((‖f u‖ ^ 2 - ‖g u‖ ^ 2 : ℝ) : ℂ) := by
      simp [Complex.ofReal_sub]
    rw [hco, Complex.norm_real, Real.norm_eq_abs, sq_sub_sq, abs_mul,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le (f u) (g u))
      (add_nonneg (norm_nonneg (f u)) (norm_nonneg (g u)))
  let φ : Plane → ℝ := fun u => ‖(f - g) u‖
  let ψ : Plane → ℝ := fun u => ‖f u‖ + ‖g u‖
  have hφ : MemLp φ 2 volume := (hf.sub hg).norm
  have hψ : MemLp ψ 2 volume := hf.norm.add hg.norm
  have hφnn : ∀ u, 0 ≤ φ u := fun u => norm_nonneg _
  have hψnn : ∀ u, 0 ≤ ψ u := fun u => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hint : Integrable (fun u => φ u * ψ u) := by
    have hφsq : Integrable (fun u => φ u ^ 2) :=
      (memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).1 hφ
    have hψsq : Integrable (fun u => ψ u ^ 2) :=
      (memLp_two_iff_integrable_sq hψ.aestronglyMeasurable).1 hψ
    refine (hφsq.add hψsq).div_const 2 |>.mono'
      (hφ.aestronglyMeasurable.mul hψ.aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    have := two_mul_le_add_sq (φ u) (ψ u)
    have : |φ u * ψ u| ≤ (φ u ^ 2 + ψ u ^ 2) / 2 := by
      rw [abs_mul, abs_of_nonneg (hφnn u), abs_of_nonneg (hψnn u)]
      linarith
    simpa [Real.norm_eq_abs] using this
  have hCS : ∫ u, φ u * ψ u ≤
      (eLpNorm (f - g) 2 volume).toReal *
        (eLpNorm ψ 2 volume).toReal := by
    have heq : ∫ u, φ u * ψ u = inner ℝ (hφ.toLp φ) (hψ.toLp ψ) := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hφ, MemLp.coeFn_toLp hψ] with u hu hv
      rw [hu, hv, RCLike.inner_apply (𝕜 := ℝ)]
      exact (mul_comm _ _).symm
    rw [heq]
    have hinter_nn : 0 ≤ inner ℝ (hφ.toLp φ) (hψ.toLp ψ) := by
      rw [← heq]
      exact integral_nonneg fun u => mul_nonneg (hφnn u) (hψnn u)
    have hbound := norm_inner_le_norm (𝕜 := ℝ) (hφ.toLp φ) (hψ.toLp ψ)
    have hnφ : ‖hφ.toLp φ‖ = (eLpNorm (f - g) 2 volume).toReal := by
      rw [Lp.norm_toLp]
      simp only [φ, eLpNorm_norm]
    rw [Real.norm_eq_abs, abs_of_nonneg hinter_nn, hnφ, Lp.norm_toLp] at hbound
    exact hbound
  have hadd : eLpNorm ψ 2 volume ≤ eLpNorm f 2 volume + eLpNorm g 2 volume := by
    have hψ' : ψ = (fun x => ‖f x‖) + fun x => ‖g x‖ := by
      ext u; simp [ψ, Pi.add_apply]
    rw [hψ']
    have := eLpNorm_add_le (p := 2) (μ := volume)
      hf.aestronglyMeasurable.norm hg.aestronglyMeasurable.norm (by simp)
    simpa [eLpNorm_norm] using this
  have hmono : eLpNorm (fun u : Plane =>
      ((‖f u‖ ^ 2 : ℝ) : ℂ) - ((‖g u‖ ^ 2 : ℝ) : ℂ)) 1 volume ≤
      eLpNorm (fun u : Plane => φ u * ψ u) 1 volume := by
    have hn := eLpNorm_norm (f := fun u : Plane =>
      ((‖f u‖ ^ 2 : ℝ) : ℂ) - ((‖g u‖ ^ 2 : ℝ) : ℂ)) (p := 1) (μ := volume)
    rw [← hn]
    refine eLpNorm_mono fun u => ?_
    have hnn : 0 ≤ φ u * ψ u := mul_nonneg (hφnn u) (hψnn u)
    have hleft : ‖‖((‖f u‖ ^ 2 : ℝ) : ℂ) - ((‖g u‖ ^ 2 : ℝ) : ℂ)‖‖ =
        ‖((‖f u‖ ^ 2 : ℝ) : ℂ) - ((‖g u‖ ^ 2 : ℝ) : ℂ)‖ :=
      (Real.norm_eq_abs _).trans (abs_norm _)
    have hright : ‖φ u * ψ u‖ = φ u * ψ u := (Real.norm_eq_abs _).trans (abs_of_nonneg hnn)
    exact (hleft.le.trans (hpt u)).trans hright.ge
  have hone : eLpNorm (fun u : Plane => φ u * ψ u) 1 volume =
      ENNReal.ofReal (∫ u, φ u * ψ u) := by
    have hnnf : (fun u => φ u * ψ u) = fun u => ‖(φ u * ψ u : ℝ)‖ := by
      ext u
      exact ((Real.norm_eq_abs (φ u * ψ u)).trans (abs_of_nonneg (mul_nonneg (hφnn u) (hψnn u)))).symm
    rw [hnnf, eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm]
    · simp
    · simpa [hnnf] using hint.norm
  have hfinψ : eLpNorm ψ 2 volume ≠ ⊤ := hψ.eLpNorm_ne_top
  have hfinφ : eLpNorm (f - g) 2 volume ≠ ⊤ := (hf.sub hg).eLpNorm_ne_top
  refine hmono.trans ?_
  rw [hone]
  have hnnint : 0 ≤ ∫ u, φ u * ψ u :=
    integral_nonneg fun u => mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have := ENNReal.ofReal_le_ofReal hCS
  refine this.trans ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfinφ,
    ENNReal.ofReal_toReal hfinψ]
  exact mul_le_mul_of_nonneg_left hadd bot_le

lemma eLpNorm_two_triangle_toReal {f g : Plane → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    (eLpNorm g 2 volume).toReal ≤
      (eLpNorm f 2 volume).toReal + (eLpNorm (g - f) 2 volume).toReal := by
  have hle : eLpNorm g 2 volume ≤ eLpNorm f 2 volume + eLpNorm (g - f) 2 volume := by
    have heq : g = f + (g - f) := by ext; simp
    nth_rw 1 [heq]
    exact eLpNorm_add_le hf.1 (hg.1.sub hf.1) (by simp)
  have := ENNReal.toReal_mono (by
    rw [ENNReal.add_ne_top]; exact ⟨hf.eLpNorm_ne_top, (hg.sub hf).eLpNorm_ne_top⟩) hle
  rwa [ENNReal.toReal_add hf.eLpNorm_ne_top (hg.sub hf).eLpNorm_ne_top] at this

lemma prod_eLpNorm_approx_le (E : Plane → ℂ) (g : 𝓢(Plane, ℂ))
    (hE2 : MemLp E 2 volume) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hg2 : eLpNorm (E - (g : Plane → ℂ)) 2 volume ≤ ENNReal.ofReal δ) :
    (eLpNorm (E - (g : Plane → ℂ)) 2 volume).toReal *
      ((eLpNorm E 2 volume).toReal + (eLpNorm (g : Plane → ℂ) 2 volume).toReal) ≤
      δ * (2 * (eLpNorm E 2 volume).toReal + 1) := by
  set C := (eLpNorm E 2 volume).toReal
  have hg2r := eLpNorm_two_toReal_le hδ0 hg2
  have hgC : (eLpNorm (g : Plane → ℂ) 2 volume).toReal ≤ C + 1 :=
    (eLpNorm_two_triangle_toReal hE2 (g.memLp 2 volume)).trans
      (add_le_add le_rfl ((eLpNorm_two_toReal_le hδ0
        (by simpa [eLpNorm_sub_comm] using hg2)).trans hδ1))
  calc
    _ ≤ δ * (C + (eLpNorm (g : Plane → ℂ) 2 volume).toReal) :=
        mul_le_mul_of_nonneg_right hg2r (by positivity)
    _ ≤ δ * (C + (C + 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hgC) hδ0
    _ = δ * (2 * C + 1) := by ring

lemma wk_general (E : Plane → ℂ) (hE1 : Integrable E) (hE2 : MemLp E 2 volume)
    (x : Plane) :
    𝓕⁻ (fun u : Plane => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ)) x = autocorrelation E x := by
  have hF := fourier_memLp_two E hE1 hE2
  have hgoal : ∀ ε > 0,
      ‖𝓕⁻ (fun u : Plane => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ)) x - autocorrelation E x‖ ≤ ε := by
    intro ε hε
    set C : ℝ := (eLpNorm E 2 volume).toReal
    have hC : 0 ≤ C := ENNReal.toReal_nonneg
    have hden : 0 < 2 * (2 * C + 1) := by positivity
    let δ : ℝ := min 1 (ε / (2 * (2 * C + 1)))
    have hδ : 0 < δ := by positivity
    have hδ0 : 0 ≤ δ := hδ.le
    have hδ1 : δ ≤ 1 := min_le_left _ _
    obtain ⟨g, -, hg2⟩ := exists_schwartz_approx E hE1 hE2 δ hδ
    have hgI : Integrable (g : Plane → ℂ) := schwartz_integrable g
    have hgM : MemLp (g : Plane → ℂ) 2 volume := g.memLp 2 volume
    have hgF := fourier_memLp_two (g : Plane → ℂ) hgI hgM
    have hprod := prod_eLpNorm_approx_le E g hE2 hδ0 hδ1 hg2
    have hA : ‖autocorrelation E x - autocorrelation (g : Plane → ℂ) x‖ ≤
        δ * (2 * C + 1) := (autocorr_diff_norm hE2 hgM x).trans hprod
    have hPE : Integrable (fun u => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ)) :=
      integrable_normSq_of_memLp_two hF.1
    have hPG : Integrable (fun u => ((‖𝓕 (g : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ)) :=
      integrable_normSq_of_memLp_two hgF.1
    have hP : ‖𝓕⁻ (fun u => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ)) x -
        𝓕⁻ (fun u => ((‖𝓕 (g : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ)) x‖ ≤
          δ * (2 * C + 1) := by
      refine (fourierInv_diff_le hPE hPG x).trans ?_
      have hnm := eLpNorm_normSq_sub hF.1 hgF.1
      have hrew : eLpNorm
          (fun u => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ) - ((‖𝓕 (g : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ))
          1 volume ≤
          eLpNorm (E - (g : Plane → ℂ)) 2 volume *
            (eLpNorm E 2 volume + eLpNorm (g : Plane → ℂ) 2 volume) := by
        rw [← eLpNorm_fourier_sub_eq E (g : Plane → ℂ) hE1 hgI hE2 hgM, ← hF.2, ← hgF.2]
        exact hnm
      have hfin : eLpNorm
          (fun u => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ) - ((‖𝓕 (g : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ))
          1 volume ≠ ⊤ :=
        ne_top_of_le_ne_top
          (ENNReal.mul_ne_top (hE2.sub hgM).eLpNorm_ne_top
            (by rw [ENNReal.add_ne_top]; exact ⟨hE2.eLpNorm_ne_top, hgM.eLpNorm_ne_top⟩)) hrew
      have := ENNReal.toReal_mono
        (ENNReal.mul_ne_top (hE2.sub hgM).eLpNorm_ne_top
          (by rw [ENNReal.add_ne_top]; exact ⟨hE2.eLpNorm_ne_top, hgM.eLpNorm_ne_top⟩))
        hrew
      refine this.trans ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_add hE2.eLpNorm_ne_top hgM.eLpNorm_ne_top]
      exact hprod
    have hsum :
        ‖𝓕⁻ (fun u => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ)) x - autocorrelation E x‖ ≤
          2 * (δ * (2 * C + 1)) := by
      have hdecomp :
          𝓕⁻ (fun u => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ)) x - autocorrelation E x =
            (𝓕⁻ (fun u => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ)) x -
              𝓕⁻ (fun u => ((‖𝓕 (g : Plane → ℂ) u‖ ^ 2 : ℝ) : ℂ)) x) +
            (autocorrelation (g : Plane → ℂ) x - autocorrelation E x) := by
        rw [wk_schwartz g x]; abel
      rw [hdecomp]
      have hA' : ‖autocorrelation (g : Plane → ℂ) x - autocorrelation E x‖ ≤
          δ * (2 * C + 1) := by
        rw [norm_sub_rev]; exact hA
      have := (norm_add_le _ _).trans (add_le_add hP hA')
      have h2 : δ * (2 * C + 1) + δ * (2 * C + 1) = 2 * (δ * (2 * C + 1)) := by ring
      rwa [h2] at this
    have hδε : 2 * (δ * (2 * C + 1)) ≤ ε := by
      have hδle : δ ≤ ε / (2 * (2 * C + 1)) := min_le_right _ _
      have hmul : δ * (2 * C + 1) ≤ (ε / (2 * (2 * C + 1))) * (2 * C + 1) :=
        mul_le_mul_of_nonneg_right hδle (by positivity)
      have : 2 * (δ * (2 * C + 1)) ≤ 2 * ((ε / (2 * (2 * C + 1))) * (2 * C + 1)) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
      have hcancel : 2 * ((ε / (2 * (2 * C + 1))) * (2 * C + 1)) = ε := by
        field
      exact this.trans (le_of_eq hcancel)
    exact hsum.trans hδε
  have h0 :
      ‖𝓕⁻ (fun u : Plane => ((‖𝓕 E u‖ ^ 2 : ℝ) : ℂ)) x - autocorrelation E x‖ ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using hgoal ε hε
  exact eq_of_sub_eq_zero (norm_le_zero_iff.mp h0)

end WK

open WK Arxiv1808_03267 MeasureTheory

theorem solution (E : Plane → ℂ) (hE1 : Integrable E) (hE2 : MemLp E 2)
    (x : Plane) :
    𝓕⁻ (fun u : Plane => (powerSpectrum E u : ℂ)) x = autocorrelation E x := by
  unfold powerSpectrum
  exact wk_general E hE1 hE2 x
