-- Prove2me | solution 1 for AntonelliBFSDE.NonsingularExample.closed_form_V
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:35:23.991213+00:00
-- url     : https://prove2.me/submissions/8224753b-3d09-4006-a6b4-d66d79de259d

import Mathlib
import Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2

open MeasureTheory
open scoped NNReal ENNReal


namespace AntonelliBFSDE.NonsingularExample

open Set Filter Topology

lemma d33_fub_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (G : ℝ × Ω → ℝ) (hG : Measurable G)
    (hfin : ∫⁻ ω, ∫⁻ r in Ioc 0 T, ‖G (r, ω)‖ₑ ∂volume ∂P < ⊤) {s t : ℝ} (hs : 0 ≤ s)
    (ht : t ≤ T) :
    Integrable (fun ω => ∫ r in Ioc s t, G (r, ω)) P ∧
    ∫ ω, ∫ r in Ioc s t, G (r, ω) ∂volume ∂P = ∫ r in Ioc s t, ∫ ω, G (r, ω) ∂P ∧
    IntegrableOn (fun r => ∫ ω, G (r, ω) ∂P) (Ioc s t) := by
  have hint : Integrable G ((volume.restrict (Ioc s t)).prod P) := by
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod_symm' _ hG.enorm]
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfin
    exact lintegral_mono' (Measure.restrict_mono (Ioc_subset_Ioc hs ht) le_rfl) le_rfl
  refine ⟨hint.integral_prod_right, ?_, hint.integral_prod_left⟩
  exact (integral_integral_swap (f := fun r ω => G (r, ω)) hint).symm

lemma d33_procFub {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (hX : AntonelliBFSDE.SingularExample.MemL1Dt P T X)
    (A : Set Ω) (hA : MeasurableSet A) (w : ℝ → ℝ) (hw : Measurable w) (K : ℝ) (hK : 0 ≤ K)
    (hwb : ∀ r ∈ Ioc (0:ℝ) T, |w r| ≤ K) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ T) :
    Integrable (fun ω => ∫ r in Ioc s t, w r * X r.toNNReal ω) P ∧
    ∫ ω in A, ∫ r in Ioc s t, w r * X r.toNNReal ω ∂volume ∂P
      = ∫ r in Ioc s t, w r * ∫ ω in A, X r.toNNReal ω ∂P ∧
    IntegrableOn (fun r => ∫ ω in A, X r.toNNReal ω ∂P) (Ioc s t) := by
  have hsub : Ioc s t ⊆ Ioc (0:ℝ) T := Ioc_subset_Ioc hs ht
  let X' : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then X p.1.toNNReal p.2 else 0
  have hX'm : Measurable X' := hX.1.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hX'eq : ∀ r ∈ Ioc (0:ℝ) T, ∀ ω, X' (r, ω) = X r.toNNReal ω := by
    intro r hr ω
    have : r.toNNReal ≤ T := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    simp [X', this]
  have hfinX : ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖X' (r, ω)‖ₑ ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hX.2
    unfold AntonelliBFSDE.SingularExample.L1NormDt
    exact lintegral_congr fun ω =>
      setLIntegral_congr_fun measurableSet_Ioc (fun r hr => by rw [hX'eq r hr ω])
  have hfin : ∀ (c : ℝ) (G : ℝ × Ω → ℝ), 0 ≤ c →
      (∀ r ∈ Ioc (0:ℝ) T, ∀ ω, ‖G (r, ω)‖ ≤ c * ‖X' (r, ω)‖) →
      ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖G (r, ω)‖ₑ ∂volume ∂P < ⊤ := by
    intro c G hc hG
    calc ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖G (r, ω)‖ₑ ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ENNReal.ofReal c * ‖X' (r, ω)‖ₑ ∂volume ∂P := by
          refine lintegral_mono fun ω => setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hc]
          exact ENNReal.ofReal_le_ofReal (hG r hr ω)
      _ = ENNReal.ofReal c * ∫⁻ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖X' (r, ω)‖ₑ ∂volume ∂P := by
          simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinX
  let G1 : ℝ × Ω → ℝ := fun p => w p.1 * X' p
  have hG1m : Measurable G1 := (hw.comp measurable_fst).mul hX'm
  have hG1b : ∀ r ∈ Ioc (0:ℝ) T, ∀ ω, ‖G1 (r, ω)‖ ≤ K * ‖X' (r, ω)‖ := by
    intro r hr ω
    simp only [G1, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hwb r hr) (abs_nonneg _)
  let G2 : ℝ × Ω → ℝ := (Prod.snd ⁻¹' A).indicator G1
  have hG2m : Measurable G2 := hG1m.indicator (measurable_snd hA)
  have hG2eq : ∀ r ω, G2 (r, ω) = A.indicator (fun ω => G1 (r, ω)) ω := by
    intro r ω; by_cases h : ω ∈ A <;> simp [G2, h]
  have hG2b : ∀ r ∈ Ioc (0:ℝ) T, ∀ ω, ‖G2 (r, ω)‖ ≤ K * ‖X' (r, ω)‖ := by
    intro r hr ω
    rw [hG2eq]
    by_cases h : ω ∈ A
    · simp only [h, indicator_of_mem]; exact hG1b r hr ω
    · simp only [h, not_false_eq_true, indicator_of_notMem, norm_zero]; positivity
  let G3 : ℝ × Ω → ℝ := (Prod.snd ⁻¹' A).indicator X'
  have hG3m : Measurable G3 := hX'm.indicator (measurable_snd hA)
  have hG3eq : ∀ r ω, G3 (r, ω) = A.indicator (fun ω => X' (r, ω)) ω := by
    intro r ω; by_cases h : ω ∈ A <;> simp [G3, h]
  have hG3b : ∀ r ∈ Ioc (0:ℝ) T, ∀ ω, ‖G3 (r, ω)‖ ≤ 1 * ‖X' (r, ω)‖ := by
    intro r hr ω
    rw [hG3eq, one_mul]
    by_cases h : ω ∈ A
    · simp [h]
    · simp [h]
  obtain ⟨i1, -, -⟩ := d33_fub_core P T G1 hG1m (hfin K G1 hK hG1b) hs ht
  obtain ⟨-, e2, -⟩ := d33_fub_core P T G2 hG2m (hfin K G2 hK hG2b) hs ht
  obtain ⟨-, -, i3⟩ := d33_fub_core P T G3 hG3m (hfin 1 G3 zero_le_one hG3b) hs ht
  have hin1 : ∀ ω, ∫ r in Ioc s t, G1 (r, ω) = ∫ r in Ioc s t, w r * X r.toNNReal ω := by
    intro ω
    exact setIntegral_congr_fun measurableSet_Ioc (fun r hr => by
      simp only [G1]; rw [hX'eq r (hsub hr) ω])
  refine ⟨i1.congr (ae_of_all _ hin1), ?_, ?_⟩
  · rw [← integral_indicator hA]
    have h1 : ∀ ω, A.indicator (fun ω => ∫ r in Ioc s t, w r * X r.toNNReal ω) ω
        = ∫ r in Ioc s t, G2 (r, ω) := by
      intro ω
      by_cases h : ω ∈ A
      · rw [indicator_of_mem h, ← hin1]
        exact setIntegral_congr_fun measurableSet_Ioc (fun r _ => by
          rw [hG2eq, indicator_of_mem h])
      · rw [indicator_of_notMem h]
        symm
        refine (setIntegral_congr_fun measurableSet_Ioc (fun r _ => ?_)).trans (integral_zero _ _)
        show G2 (r, ω) = 0
        rw [hG2eq, indicator_of_notMem h]
    simp_rw [h1]
    rw [e2]
    refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
    simp only [hG2eq]
    rw [integral_indicator hA, ← integral_const_mul]
    refine setIntegral_congr_fun hA (fun ω _ => ?_)
    simp only [G1]; rw [hX'eq r (hsub hr) ω]
  · refine i3.congr_fun (fun r hr => ?_) measurableSet_Ioc
    simp only [hG3eq]
    rw [integral_indicator hA]
    refine setIntegral_congr_fun hA (fun ω _ => ?_)
    rw [hX'eq r (hsub hr) ω]


lemma d33_const {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : f b = f a := by
  obtain ⟨c, _, hc'⟩ := exists_hasDerivAt_eq_slope f (fun _ => (0:ℝ)) hab hc hd
  have hne : b - a ≠ 0 := by linarith
  have h := hc'.symm
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hne

lemma d33_ode {t0 T a d : ℝ} (h0 : 0 ≤ t0) (hT : t0 ≤ T) {φ ψ : ℝ → ℝ}
    (hφi : IntegrableOn φ (Ioc 0 T)) (hψi : IntegrableOn ψ (Ioc 0 T))
    (hφ : ∀ x ∈ Icc t0 T, φ x = a + ∫ r in Ioc 0 x, ψ r)
    (hψ : ∀ x ∈ Icc t0 T, ψ x = d + ∫ r in Ioc x T, φ r) :
    ψ t0 = φ T * Real.sin (T - t0) + d * Real.cos (T - t0) ∧
    φ T * Real.cos (T - t0) = φ t0 + d * Real.sin (T - t0) ∧
    (T - t0) * φ T - ∫ r in Ioc t0 T, φ r = ∫ r in Ioc t0 T, (r - t0) * ψ r := by
  have hψT : ψ T = d := by rw [hψ T ⟨hT, le_rfl⟩]; simp
  rcases eq_or_lt_of_le hT with heq | hlt
  · subst heq; simp [hψT]
  have hφii : ∀ x ∈ Icc 0 T, IntervalIntegrable φ volume 0 x := fun x hx =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).2
      (hφi.mono_set (Ioc_subset_Ioc le_rfl hx.2))
  have hψii : ∀ x ∈ Icc 0 T, IntervalIntegrable ψ volume 0 x := fun x hx =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).2
      (hψi.mono_set (Ioc_subset_Ioc le_rfl hx.2))
  have hφI : IntegrableOn φ (uIcc 0 T) := by
    rw [uIcc_of_le (h0.trans hT), integrableOn_Icc_iff_integrableOn_Ioc]; exact hφi
  have hψI : IntegrableOn ψ (uIcc 0 T) := by
    rw [uIcc_of_le (h0.trans hT), integrableOn_Icc_iff_integrableOn_Ioc]; exact hψi
  have hPφ : ContinuousOn (fun x => ∫ r in (0:ℝ)..x, φ r) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval hφI
    rwa [uIcc_of_le (h0.trans hT)] at this
  have hPψ : ContinuousOn (fun x => ∫ r in (0:ℝ)..x, ψ r) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval hψI
    rwa [uIcc_of_le (h0.trans hT)] at this
  have hφ' : ∀ x ∈ Icc t0 T, φ x = a + ∫ r in (0:ℝ)..x, ψ r := fun x hx => by
    rw [hφ x hx, intervalIntegral.integral_of_le (h0.trans hx.1)]
  have hψ' : ∀ x ∈ Icc t0 T,
      ψ x = d + ((∫ r in (0:ℝ)..T, φ r) - ∫ r in (0:ℝ)..x, φ r) := fun x hx => by
    rw [hψ x hx, intervalIntegral.integral_interval_sub_left (hφii T ⟨h0.trans hT, le_rfl⟩)
      (hφii x ⟨h0.trans hx.1, hx.2⟩), intervalIntegral.integral_of_le hx.2]
  have hsub : Icc t0 T ⊆ Icc 0 T := Icc_subset_Icc h0 le_rfl
  have hφc : ContinuousOn φ (Icc t0 T) :=
    (continuousOn_const.add (hPψ.mono hsub)).congr hφ'
  have hψc : ContinuousOn ψ (Icc t0 T) :=
    (continuousOn_const.add (continuousOn_const.sub (hPφ.mono hsub))).congr hψ'
  have hnhds : ∀ x ∈ Ioo t0 T, Icc t0 T ∈ 𝓝 x := fun x hx => Icc_mem_nhds hx.1 hx.2
  have hDφ : ∀ x ∈ Ioo t0 T, HasDerivAt φ (ψ x) x := by
    intro x hx
    have hxI : x ∈ Icc 0 T := ⟨h0.trans hx.1.le, hx.2.le⟩
    have h1 : HasDerivAt (fun y => ∫ r in (0:ℝ)..y, ψ r) (ψ x) x :=
      intervalIntegral.integral_hasDerivAt_right (hψii x hxI)
        ((hψc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
        (hψc.continuousAt (hnhds x hx))
    refine (h1.const_add a).congr_of_eventuallyEq ?_
    filter_upwards [hnhds x hx] with y hy
    exact hφ' y hy
  have hDψ : ∀ x ∈ Ioo t0 T, HasDerivAt ψ (-φ x) x := by
    intro x hx
    have hxI : x ∈ Icc 0 T := ⟨h0.trans hx.1.le, hx.2.le⟩
    have h1 : HasDerivAt (fun y => ∫ r in (0:ℝ)..y, φ r) (φ x) x :=
      intervalIntegral.integral_hasDerivAt_right (hφii x hxI)
        ((hφc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
        (hφc.continuousAt (hnhds x hx))
    refine ((h1.const_sub (∫ r in (0:ℝ)..T, φ r)).const_add d).congr_of_eventuallyEq ?_
    filter_upwards [hnhds x hx] with y hy
    exact hψ' y hy
  have hprim : ∀ f : ℝ → ℝ, ContinuousOn f (Icc t0 T) →
      ContinuousOn (fun y => ∫ r in t0..y, f r) (Icc t0 T) ∧
      ∀ x ∈ Ioo t0 T, HasDerivAt (fun y => ∫ r in t0..y, f r) (f x) x := by
    intro f hf
    constructor
    · have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
        (f := f) (a := t0) (b := T) (by
          rw [uIcc_of_le hT]; exact hf.integrableOn_compact isCompact_Icc)
      rwa [uIcc_of_le hT] at this
    · intro x hx
      exact intervalIntegral.integral_hasDerivAt_right
        ((hf.mono (uIcc_subset_Icc ⟨le_rfl, hT⟩ ⟨hx.1.le, hx.2.le⟩)).intervalIntegrable)
        ((hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
        (hf.continuousAt (hnhds x hx))
  -- first invariant
  have e1 := d33_const (f := fun y => φ y * Real.sin (y - t0) + ψ y * Real.cos (y - t0)) hlt
    ((hφc.mul (by fun_prop)).add (hψc.mul (by fun_prop))) (by
      intro x hx
      have h := ((hDφ x hx).mul ((hasDerivAt_id' x).sub_const t0).sin).add
        ((hDψ x hx).mul ((hasDerivAt_id' x).sub_const t0).cos)
      exact h.congr_deriv (by ring))
  have e2 := d33_const (f := fun y => φ y * Real.cos (y - t0) - ψ y * Real.sin (y - t0)) hlt
    ((hφc.mul (by fun_prop)).sub (hψc.mul (by fun_prop))) (by
      intro x hx
      have h := ((hDφ x hx).mul ((hasDerivAt_id' x).sub_const t0).cos).sub
        ((hDψ x hx).mul ((hasDerivAt_id' x).sub_const t0).sin)
      exact h.congr_deriv (by ring))
  have hχc : ContinuousOn (fun r => (r - t0) * ψ r) (Icc t0 T) := (by fun_prop : Continuous fun r : ℝ => r - t0).continuousOn.mul hψc
  obtain ⟨hc1, hd1⟩ := hprim φ hφc
  obtain ⟨hc2, hd2⟩ := hprim _ hχc
  have e3 := d33_const (f := fun y => (y - t0) * φ y - (∫ r in t0..y, φ r)
      - ∫ r in t0..y, (r - t0) * ψ r) hlt
    ((((by fun_prop : Continuous fun r : ℝ => r - t0).continuousOn.mul hφc).sub hc1).sub hc2)
    (by
      intro x hx
      have h := ((((hasDerivAt_id' x).sub_const t0).mul (hDφ x hx)).sub (hd1 x hx)).sub (hd2 x hx)
      exact h.congr_deriv (by ring))
  simp only [sub_self, Real.sin_zero, Real.cos_zero, mul_zero, mul_one, zero_add, zero_mul,
    sub_zero, intervalIntegral.integral_same, hψT] at e1 e2 e3
  refine ⟨by linarith, by linarith, ?_⟩
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT] at e3
  linarith

lemma d33_procFub1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (hX : AntonelliBFSDE.SingularExample.MemL1Dt P T X)
    (A : Set Ω) (hA : MeasurableSet A) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ T) :
    Integrable (fun ω => ∫ r in Ioc s t, X r.toNNReal ω) P ∧
    ∫ ω in A, ∫ r in Ioc s t, X r.toNNReal ω ∂volume ∂P
      = ∫ r in Ioc s t, ∫ ω in A, X r.toNNReal ω ∂P ∧
    IntegrableOn (fun r => ∫ ω in A, X r.toNNReal ω ∂P) (Ioc s t) := by
  have := d33_procFub P T X hX A hA (fun _ => 1) measurable_const 1 zero_le_one
    (fun r _ => by simp) hs ht
  simpa using this

lemma d33_sys {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ) (hJint : Integrable J₀ P)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v)
      (fun u _ => u) Y U V)
    (t0 : ℝ≥0) (ht0 : t0 ≤ T) (A : Set Ω) (hA : MeasurableSet[𝓕 t0] A) :
    IntegrableOn (fun r : ℝ => ∫ ω in A, U r.toNNReal ω ∂P) (Ioc 0 T) ∧
    IntegrableOn (fun r : ℝ => ∫ ω in A, V r.toNNReal ω ∂P) (Ioc 0 T) ∧
    (∀ x ∈ Icc (0:ℝ) T, (∫ ω in A, U x.toNNReal ω ∂P) =
      (∫ ω in A, J₀ ω ∂P) + ∫ r in Ioc 0 x, ∫ ω in A, V r.toNNReal ω ∂P) ∧
    (∀ x ∈ Icc (t0:ℝ) T, (∫ ω in A, V x.toNNReal ω ∂P) =
      (∫ ω in A, Y ω ∂P) + ∫ r in Ioc x T, ∫ ω in A, U r.toNNReal ω ∂P) ∧
    Integrable (UT T J₀ V) P ∧ Integrable Y P ∧
    ∫ ω in A, UT T J₀ V ω ∂P =
      (∫ ω in A, J₀ ω ∂P) + ∫ r in Ioc 0 (T:ℝ), ∫ ω in A, V r.toNNReal ω ∂P := by
  obtain ⟨hU, hV, hUad, hVad, hpath, hξ, W, hW, hUV, hVT⟩ := hsol
  have hAm : MeasurableSet A := 𝓕.le t0 A hA
  have hYint : Integrable Y P := by
    have h := hξ T le_rfl
    have e : AntonelliBFSDE.SingularExample.xiDt T (fun u _ => u) Y U V T = Y := by
      funext ω; unfold AntonelliBFSDE.SingularExample.xiDt; simp
    rwa [e] at h
  have hUTeq : UT T J₀ V = fun ω => J₀ ω + ∫ s in Ioc (0:ℝ) T, V s.toNNReal ω := rfl
  have hUTint : Integrable (UT T J₀ V) P := by
    rw [hUTeq]; exact hJint.add (d33_procFub1 P T V hV A hAm le_rfl le_rfl).1
  refine ⟨(d33_procFub1 P T U hU A hAm le_rfl le_rfl).2.2,
    (d33_procFub1 P T V hV A hAm le_rfl le_rfl).2.2, ?_, ?_, hUTint, hYint, ?_⟩
  · intro x hx
    have htx : ((x.toNNReal : ℝ≥0) : ℝ) = x := Real.coe_toNNReal x hx.1
    have htxT : x.toNNReal ≤ T := by rw [← NNReal.coe_le_coe, htx]; exact hx.2
    have h1 := (hUV x.toNNReal htxT).1
    simp only [htx] at h1
    obtain ⟨i1, e1, -⟩ := d33_procFub1 P T V hV A hAm le_rfl hx.2
    rw [integral_congr_ae (ae_restrict_of_ae h1), integral_add hJint.integrableOn i1.integrableOn,
      e1]
  · intro x hx
    have hx0 : (0:ℝ) ≤ x := le_trans t0.2 hx.1
    have htx : ((x.toNNReal : ℝ≥0) : ℝ) = x := Real.coe_toNNReal x hx0
    have htxT : x.toNNReal ≤ T := by rw [← NNReal.coe_le_coe, htx]; exact hx.2
    have ht0x : t0 ≤ x.toNNReal := by rw [← NNReal.coe_le_coe, htx]; exact hx.1
    have hAx : MeasurableSet[𝓕 x.toNNReal] A := 𝓕.mono ht0x A hA
    have h1 := (hUV x.toNNReal htxT).2
    have h2 := hW.2.2 x.toNNReal htxT
    rw [integral_congr_ae (ae_restrict_of_ae (h1.trans h2)),
      setIntegral_condExp (𝓕.le _) (hξ _ htxT) hAx]
    obtain ⟨i1, e1, -⟩ := d33_procFub1 P T U hU A hAm hx0 le_rfl
    simp only [AntonelliBFSDE.SingularExample.xiDt, htx]
    rw [integral_add i1.integrableOn hYint.integrableOn, e1, add_comm]
  · rw [hUTeq]
    obtain ⟨i1, e1, -⟩ := d33_procFub1 P T V hV A hAm le_rfl le_rfl
    rw [integral_add hJint.integrableOn i1.integrableOn, e1]

theorem mean_terminal_identity_core {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ) (hJint : Integrable J₀ P)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v)
      (fun u _ => u) Y U V) :
    Integrable (UT T J₀ V) P ∧ Integrable Y P ∧
    (∫ ω, UT T J₀ V ω ∂P) * Real.cos (T : ℝ) =
      (∫ ω, J₀ ω ∂P) + (∫ ω, Y ω ∂P) * Real.sin (T : ℝ) := by
  obtain ⟨iφ, iψ, hφ, hψ, hUT, hY, eUT⟩ :=
    d33_sys P 𝓕 T J₀ Y U V hJint hsol 0 bot_le univ MeasurableSet.univ
  refine ⟨hUT, hY, ?_⟩
  have h0 : (0:ℝ) ≤ ((0:ℝ≥0):ℝ) := le_rfl
  obtain ⟨-, e, -⟩ := d33_ode (a := ∫ ω in univ, J₀ ω ∂P) (d := ∫ ω in univ, Y ω ∂P)
    h0 (NNReal.coe_nonneg T) iφ iψ (fun x hx => hφ x hx) (fun x hx => hψ x hx)
  have hφT := hφ T ⟨NNReal.coe_nonneg T, le_rfl⟩
  have hφ0 := hφ 0 ⟨le_rfl, NNReal.coe_nonneg T⟩
  simp only [NNReal.coe_zero, sub_zero, Ioc_self, Measure.restrict_empty, integral_zero_measure,
    add_zero] at e hφ0
  rw [hφT, ← eUT] at e
  simp only [Measure.restrict_univ, Real.toNNReal_zero, NNReal.coe_zero] at e hφ0
  rw [hφ0] at e
  exact e

theorem example_2_core {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (hT : (T : ℝ) = Real.pi / 2)
    (hJint : Integrable J₀ P) (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω) (hYpos : ∀ᵐ ω ∂P, 0 < Y ω) :
    ¬ ∃ U V : ℝ≥0 → Ω → ℝ,
      AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v)
        (fun u _ => u) Y U V := by
  rintro ⟨U, V, hsol⟩
  obtain ⟨-, hY, e⟩ := mean_terminal_identity_core P 𝓕 T J₀ Y U V hJint hsol
  rw [hT, Real.cos_pi_div_two, Real.sin_pi_div_two] at e
  have hJ0 : 0 ≤ ∫ ω, J₀ ω ∂P := integral_nonneg_of_ae (hJpos.mono fun ω h => h.le)
  have hY0 : 0 ≤ ∫ ω, Y ω ∂P := integral_nonneg_of_ae (hYpos.mono fun ω h => h.le)
  have hJz : ∫ ω, J₀ ω ∂P = 0 := by linarith
  rw [integral_eq_zero_iff_of_nonneg_ae (hJpos.mono fun ω h => h.le) hJint] at hJz
  obtain ⟨ω, h1, h2⟩ := (hJz.and hJpos).exists
  rw [h1] at h2
  exact lt_irrefl _ h2

lemma d33_L1zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (D : ℝ≥0 → Ω → ℝ)
    (hDm : Measurable (Function.uncurry (fun t ω => if t ≤ T then D t ω else 0)))
    (hD : ∀ t ≤ T, D t =ᵐ[P] 0) :
    AntonelliBFSDE.SingularExample.L1NormDt P T D = 0 := by
  unfold AntonelliBFSDE.SingularExample.L1NormDt
  let D' : ℝ × Ω → ℝ := fun p => if p.1.toNNReal ≤ T then D p.1.toNNReal p.2 else 0
  have hD'm : Measurable D' := hDm.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hT' : ∀ r ∈ Ioc (0:ℝ) T, r.toNNReal ≤ T := fun r hr => by
    rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  have h1 : ∀ ω, ∫⁻ r in Ioc 0 (T:ℝ), ‖D r.toNNReal ω‖ₑ = ∫⁻ r in Ioc 0 (T:ℝ), ‖D' (r, ω)‖ₑ :=
    fun ω => setLIntegral_congr_fun measurableSet_Ioc (fun r hr => by simp [D', hT' r hr])
  simp_rw [h1]
  rw [lintegral_lintegral_swap (f := fun ω r => ‖D' (r, ω)‖ₑ)
    ((hD'm.comp measurable_swap).enorm.aemeasurable)]
  refine le_antisymm ?_ (by simp)
  calc ∫⁻ r in Ioc 0 (T:ℝ), ∫⁻ ω, ‖D' (r, ω)‖ₑ ∂P ≤ ∫⁻ r in Ioc 0 (T:ℝ), 0 := by
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => le_of_eq ?_
        rw [lintegral_congr_ae (g := fun _ => (0:ℝ≥0∞)) ((hD _ (hT' r hr)).mono fun ω h => by
          simp [D', hT' r hr, h])]
        simp
    _ = 0 := lintegral_zero

lemma d33_cond {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V M Yc : ℝ≥0 → Ω → ℝ) (hJint : Integrable J₀ P)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v)
      (fun u _ => u) Y U V)
    (hM : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => UT T J₀ V) M)
    (hYc : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => Y) Yc)
    (t : ℝ≥0) (ht : t ≤ T) :
    Integrable (V t) P ∧ Integrable (M t) P ∧ Integrable (Yc t) P ∧
    (∀ A, MeasurableSet[𝓕 t] A → ∫ ω in A, M t ω ∂P = ∫ ω in A, UT T J₀ V ω ∂P) ∧
    (∀ A, MeasurableSet[𝓕 t] A → ∫ ω in A, Yc t ω ∂P = ∫ ω in A, Y ω ∂P) ∧
    AEStronglyMeasurable[𝓕 t] (M t) P ∧ AEStronglyMeasurable[𝓕 t] (Yc t) P ∧
    V t =ᵐ[P] fun ω => M t ω * Real.sin ((T:ℝ) - t) + Yc t ω * Real.cos ((T:ℝ) - t) := by
  have hsol' := hsol
  obtain ⟨hU, hV, hUad, hVad, hpath, hξ, W, hW, hUV, hVT⟩ := hsol'
  have hVc : V t =ᵐ[P] (P[AntonelliBFSDE.SingularExample.xiDt T (fun u _ => u) Y U V t | 𝓕 t]) :=
    (hUV t ht).2.trans (hW.2.2 t ht)
  have hVint : Integrable (V t) P := integrable_condExp.congr hVc.symm
  have hMc : M t =ᵐ[P] P[UT T J₀ V | 𝓕 t] := hM.2.2 t ht
  have hYcc : Yc t =ᵐ[P] P[Y | 𝓕 t] := hYc.2.2 t ht
  have hMint : Integrable (M t) P := integrable_condExp.congr hMc.symm
  have hYcint : Integrable (Yc t) P := integrable_condExp.congr hYcc.symm
  obtain ⟨-, -, -, -, hUT, hY, -⟩ :=
    d33_sys P 𝓕 T J₀ Y U V hJint hsol 0 bot_le univ MeasurableSet.univ
  have hMA : ∀ A, MeasurableSet[𝓕 t] A → ∫ ω in A, M t ω ∂P = ∫ ω in A, UT T J₀ V ω ∂P :=
    fun A hA => by
      rw [setIntegral_congr_ae (𝓕.le t A hA) (hMc.mono fun ω h _ => h),
        setIntegral_condExp (𝓕.le t) hUT hA]
  have hYA : ∀ A, MeasurableSet[𝓕 t] A → ∫ ω in A, Yc t ω ∂P = ∫ ω in A, Y ω ∂P :=
    fun A hA => by
      rw [setIntegral_congr_ae (𝓕.le t A hA) (hYcc.mono fun ω h _ => h),
        setIntegral_condExp (𝓕.le t) hY hA]
  have hMm : AEStronglyMeasurable[𝓕 t] (M t) P :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hMc.symm
  have hYcm : AEStronglyMeasurable[𝓕 t] (Yc t) P :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hYcc.symm
  refine ⟨hVint, hMint, hYcint, hMA, hYA, hMm, hYcm, ?_⟩
  set s := Real.sin ((T:ℝ) - t)
  set c := Real.cos ((T:ℝ) - t)
  have hf : Integrable (s • UT T J₀ V + c • Y) P := (hUT.smul s).add (hY.smul c)
  have h1 : V t =ᵐ[P] P[s • UT T J₀ V + c • Y | 𝓕 t] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t) hf
      (fun _ _ _ => hVint.integrableOn) (fun A hA _ => ?_) (hVad t ht).aestronglyMeasurable
    have hAm : MeasurableSet A := 𝓕.le t A hA
    obtain ⟨iφ, iψ, hφ, hψ, -, -, eUT⟩ := d33_sys P 𝓕 T J₀ Y U V hJint hsol t ht A hA
    obtain ⟨e1, -, -⟩ := d33_ode (a := ∫ ω in A, J₀ ω ∂P) (d := ∫ ω in A, Y ω ∂P)
      (NNReal.coe_nonneg t) (by exact_mod_cast ht) iφ iψ
      (fun x hx => hφ x ⟨le_trans (NNReal.coe_nonneg t) hx.1, hx.2⟩) (fun x hx => hψ x hx)
    have hφT := hφ T ⟨NNReal.coe_nonneg T, le_rfl⟩
    simp only [Real.toNNReal_coe] at e1 hφT
    rw [hφT, ← eUT] at e1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1, integral_add (hUT.const_mul s).integrableOn (hY.const_mul c).integrableOn,
      integral_const_mul, integral_const_mul]
    ring
  have h2 : P[s • UT T J₀ V + c • Y | 𝓕 t] =ᵐ[P]
      s • P[UT T J₀ V | 𝓕 t] + c • P[Y | 𝓕 t] :=
    (condExp_add (hUT.smul s) (hY.smul c) _).trans
      ((condExp_smul s _ _).add (condExp_smul c _ _))
  filter_upwards [h1, h2, hMc, hYcc] with ω e1 e2 e3 e4
  rw [e1, e2]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e3, e4]
  ring

theorem closed_form_V_core {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V M Yc : ℝ≥0 → Ω → ℝ) (hJint : Integrable J₀ P)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v)
      (fun u _ => u) Y U V)
    (hM : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => UT T J₀ V) M)
    (hYc : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => Y) Yc) :
    AntonelliBFSDE.SingularExample.L1NormDt P T (fun t ω => V t ω -
      (M t ω * Real.sin ((T : ℝ) - (t : ℝ)) +
       Yc t ω * Real.cos ((T : ℝ) - (t : ℝ)))) = 0 := by
  apply d33_L1zero
  · have hV := hsol.2.1.1
    have e : (Function.uncurry fun t ω => if t ≤ T then V t ω -
        (M t ω * Real.sin ((T : ℝ) - (t : ℝ)) + Yc t ω * Real.cos ((T : ℝ) - (t : ℝ))) else 0)
        = fun p => (Function.uncurry (fun t ω => if t ≤ T then V t ω else 0)) p -
          ((Function.uncurry (fun t ω => if t ≤ T then M t ω else 0)) p *
            Real.sin ((T : ℝ) - (p.1 : ℝ)) +
           (Function.uncurry (fun t ω => if t ≤ T then Yc t ω else 0)) p *
            Real.cos ((T : ℝ) - (p.1 : ℝ))) := by
      funext p
      simp only [Function.uncurry]
      split_ifs <;> simp
    rw [e]
    refine hV.sub ((hM.1.mul ?_).add (hYc.1.mul ?_))
    · exact Real.continuous_sin.measurable.comp (measurable_const.sub measurable_fst.coe_nnreal_real)
    · exact Real.continuous_cos.measurable.comp (measurable_const.sub measurable_fst.coe_nnreal_real)
  · intro t ht
    obtain ⟨-, -, -, -, -, -, -, h⟩ := d33_cond P 𝓕 T J₀ Y U V M Yc hJint hsol hM hYc t ht
    filter_upwards [h] with ω hω
    simp [hω]

theorem equation_3_12_core {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V M Yc : ℝ≥0 → Ω → ℝ) (hJint : Integrable J₀ P)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v)
      (fun u _ => u) Y U V)
    (hM : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => UT T J₀ V) M)
    (hYc : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => Y) Yc) :
    (∀ t : ℝ≥0, t ≤ T → Integrable (weightedTail T V t) P) ∧
    ∃ W : ℝ≥0 → Ω → ℝ,
      AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (weightedTail T V) W ∧
      AntonelliBFSDE.SingularExample.L1NormDt P T (fun t ω => V t ω -
        (((T : ℝ) - (t : ℝ)) * M t ω - W t ω + Yc t ω)) = 0 := by
  have hV := hsol.2.1
  have hwb : ∀ t : ℝ≥0, t ≤ T → ∀ r ∈ Ioc (0:ℝ) T, |(fun r : ℝ => r - t) r| ≤ T := by
    intro t ht r hr
    have h1 : (t:ℝ) ≤ T := by exact_mod_cast ht
    have h2 : (0:ℝ) ≤ t := NNReal.coe_nonneg t
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  have hWT : ∀ t : ℝ≥0, t ≤ T → Integrable (weightedTail T V t) P := by
    intro t ht
    exact (d33_procFub P T V hV univ MeasurableSet.univ (fun r => r - t)
      (measurable_id.sub_const _) T (NNReal.coe_nonneg T) (hwb t ht) (s := t) (t := T) (NNReal.coe_nonneg t)
      le_rfl).1
  refine ⟨hWT, fun t ω => ((T:ℝ) - t) * M t ω + Yc t ω - V t ω, ⟨?_, hWT, ?_⟩, ?_⟩
  · have e : (Function.uncurry fun t ω => if t ≤ T then
        ((T:ℝ) - t) * M t ω + Yc t ω - V t ω else 0)
        = fun p => ((T:ℝ) - (p.1 : ℝ)) * (Function.uncurry (fun t ω => if t ≤ T then M t ω else 0)) p
          + (Function.uncurry (fun t ω => if t ≤ T then Yc t ω else 0)) p
          - (Function.uncurry (fun t ω => if t ≤ T then V t ω else 0)) p := by
      funext p
      simp only [Function.uncurry]
      split_ifs <;> simp
    rw [e]
    exact (((measurable_const.sub measurable_fst.coe_nnreal_real).mul hM.1).add hYc.1).sub hV.1
  · intro t ht
    obtain ⟨hVint, hMint, hYcint, hMA, hYA, hMm, hYcm, -⟩ :=
      d33_cond P 𝓕 T J₀ Y U V M Yc hJint hsol hM hYc t ht
    have hVm : AEStronglyMeasurable[𝓕 t] (V t) P := (hsol.2.2.2.1 t ht).aestronglyMeasurable
    have hgi : Integrable (fun ω => ((T:ℝ) - t) * M t ω + Yc t ω - V t ω) P :=
      ((hMint.const_mul _).add hYcint).sub hVint
    refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t) (hWT t ht)
      (fun _ _ _ => hgi.integrableOn) (fun A hA _ => ?_)
      (((hMm.const_mul ((T:ℝ) - t)).add hYcm).sub hVm)
    have hAm : MeasurableSet A := 𝓕.le t A hA
    obtain ⟨iφ, iψ, hφ, hψ, -, -, eUT⟩ := d33_sys P 𝓕 T J₀ Y U V hJint hsol t ht A hA
    obtain ⟨-, -, e3⟩ := d33_ode (a := ∫ ω in A, J₀ ω ∂P) (d := ∫ ω in A, Y ω ∂P)
      (NNReal.coe_nonneg t) (by exact_mod_cast ht) iφ iψ
      (fun x hx => hφ x ⟨le_trans (NNReal.coe_nonneg t) hx.1, hx.2⟩) (fun x hx => hψ x hx)
    have hφT := hφ T ⟨NNReal.coe_nonneg T, le_rfl⟩
    have hψt := hψ t ⟨le_rfl, by exact_mod_cast ht⟩
    simp only [Real.toNNReal_coe] at e3 hφT hψt
    rw [hφT, ← eUT] at e3
    have e4 := (d33_procFub P T V hV A hAm (fun r => r - t)
      (measurable_id.sub_const _) T (NNReal.coe_nonneg T) (hwb t ht) (s := t) (t := T) (NNReal.coe_nonneg t)
      le_rfl).2.1
    have hwt : ∀ ω, weightedTail T V t ω = ∫ r in Ioc (t:ℝ) T, (r - t) * V r.toNNReal ω :=
      fun ω => rfl
    simp_rw [hwt]
    have k1 : ∫ x in A, ((T:ℝ) - t) * M t x + Yc t x - V t x ∂P =
        ((T:ℝ) - t) * (∫ x in A, M t x ∂P) + (∫ x in A, Yc t x ∂P) - ∫ x in A, V t x ∂P := by
      rw [integral_sub (f := fun x => ((T:ℝ) - t) * M t x + Yc t x) (g := V t)
        ((hMint.const_mul _).add hYcint).integrableOn hVint.integrableOn,
        integral_add (f := fun x => ((T:ℝ) - t) * M t x) (g := Yc t)
        (hMint.const_mul _).integrableOn hYcint.integrableOn, integral_const_mul]
    rw [e4, ← e3, k1, hMA A hA, hYA A hA]
    linarith
  · have e : ∀ t ω, V t ω - (((T : ℝ) - (t : ℝ)) * M t ω -
        (((T:ℝ) - t) * M t ω + Yc t ω - V t ω) + Yc t ω) = 0 := fun t ω => by ring
    simp only [AntonelliBFSDE.SingularExample.L1NormDt, e]
    simp
end AntonelliBFSDE.NonsingularExample

open AntonelliBFSDE.NonsingularExample


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V M Yc : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P) (hT : 0 < T)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hYbounded : ∃ C : ℝ, ∀ᵐ ω ∂P, |Y ω| ≤ C)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v) (fun u _ => u) Y U V)
    (hM : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => UT T J₀ V) M)
    (hYc : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => Y) Yc) :
    AntonelliBFSDE.SingularExample.L1NormDt P T (fun t ω => V t ω -
      (M t ω * Real.sin ((T : ℝ) - (t : ℝ)) +
       Yc t ω * Real.cos ((T : ℝ) - (t : ℝ)))) = 0 := by
  exact closed_form_V_core P 𝓕 T J₀ Y U V M Yc hJint hsol hM hYc
