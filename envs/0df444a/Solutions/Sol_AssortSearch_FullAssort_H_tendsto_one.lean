-- Prove2me | solution 1 for AssortSearch.FullAssort.H_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:46:40.668036+00:00
-- url     : https://prove2.me/submissions/eb468042-0f25-45e2-a9ce-8d2c8f35a9c2

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model

open MeasureTheory Filter Topology Set
open AssortSearch.FullAssort

namespace FullAssortHT

lemma lam_pos (μ y : ℝ) : 0 < AssortSearch.Cannibal.lam μ y := Real.exp_pos _

lemma lam_eq (μ y : ℝ) : AssortSearch.Cannibal.lam μ y =
    Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(1 / μ) * y) := by
  unfold AssortSearch.Cannibal.lam
  rw [← Real.exp_add]; congr 1; ring

lemma lam_anti {μ : ℝ} (hμ : 0 < μ) {y y' : ℝ} (h : y ≤ y') :
    AssortSearch.Cannibal.lam μ y' ≤ AssortSearch.Cannibal.lam μ y := by
  unfold AssortSearch.Cannibal.lam
  apply Real.exp_le_exp.2
  have := div_le_div_of_nonneg_right h hμ.le
  linarith

lemma w_eq {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (y : ℝ) :
    w μ v S y = outsidePref v S / μ * AssortSearch.Cannibal.lam μ y *
      Real.exp (-(AssortSearch.Cannibal.lam μ y * outsidePref v S)) := rfl

lemma w_nonneg {n : ℕ} {μ : ℝ} (hμ : 0 < μ) (v : Fin n → ℝ) (S : Finset (Fin n))
    (hV : 0 ≤ outsidePref v S) (y : ℝ) : 0 ≤ w μ v S y := by
  rw [w_eq]
  have := lam_pos μ y
  positivity

lemma w_le {n : ℕ} {μ : ℝ} (hμ : 0 < μ) (v : Fin n → ℝ) (S : Finset (Fin n))
    (hV : 0 ≤ outsidePref v S) (y : ℝ) :
    w μ v S y ≤ outsidePref v S / μ * AssortSearch.Cannibal.lam μ y := by
  rw [w_eq]
  have := lam_pos μ y
  have h1 : Real.exp (-(AssortSearch.Cannibal.lam μ y * outsidePref v S)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ AssortSearch.Cannibal.lam μ y * outsidePref v S := by positivity
    linarith
  exact mul_le_of_le_one_right (by positivity) h1

/-- the constant in the exponential bound -/
noncomputable def C0 (μ V : ℝ) : ℝ := V / μ * Real.exp (-Real.eulerMascheroniConstant) * (2 * μ)

lemma f_bound {n : ℕ} {μ : ℝ} (hμ : 0 < μ) (v : Fin n → ℝ) (S : Finset (Fin n))
    (hV : 0 ≤ outsidePref v S) (u t : ℝ) (ht : u ≤ t) :
    0 ≤ (t - u) * w μ v S t ∧
      (t - u) * w μ v S t ≤ C0 μ (outsidePref v S) * Real.exp (-u / (2 * μ)) *
        Real.exp (-(1 / (2 * μ)) * t) := by
  have hw0 := w_nonneg hμ v S hV t
  refine ⟨mul_nonneg (by linarith) hw0, ?_⟩
  have h1 : (t - u) * w μ v S t ≤ (t - u) * (outsidePref v S / μ * AssortSearch.Cannibal.lam μ t) :=
    mul_le_mul_of_nonneg_left (w_le hμ v S hV t) (by linarith)
  have h2 : t - u ≤ 2 * μ * Real.exp ((t - u) / (2 * μ)) := by
    have := Real.add_one_le_exp ((t - u) / (2 * μ))
    have h3 : (t - u) = 2 * μ * ((t - u) / (2 * μ)) := by field_simp
    have h4 : (t - u) / (2 * μ) ≤ Real.exp ((t - u) / (2 * μ)) := by linarith
    calc t - u = 2 * μ * ((t - u) / (2 * μ)) := h3
      _ ≤ 2 * μ * Real.exp ((t - u) / (2 * μ)) := by
        apply mul_le_mul_of_nonneg_left h4; linarith
  have hexp : Real.exp ((t - u) / (2 * μ)) * Real.exp (-(1 / μ) * t) =
      Real.exp (-u / (2 * μ)) * Real.exp (-(1 / (2 * μ)) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
  have hK : 0 ≤ outsidePref v S / μ * Real.exp (-Real.eulerMascheroniConstant) := by positivity
  calc (t - u) * w μ v S t
      ≤ (t - u) * (outsidePref v S / μ * AssortSearch.Cannibal.lam μ t) := h1
    _ = (outsidePref v S / μ * Real.exp (-Real.eulerMascheroniConstant)) *
          ((t - u) * Real.exp (-(1 / μ) * t)) := by rw [lam_eq]; ring
    _ ≤ (outsidePref v S / μ * Real.exp (-Real.eulerMascheroniConstant)) *
          (2 * μ * Real.exp ((t - u) / (2 * μ)) * Real.exp (-(1 / μ) * t)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = C0 μ (outsidePref v S) * Real.exp (-u / (2 * μ)) *
          Real.exp (-(1 / (2 * μ)) * t) := by
        unfold C0
        rw [mul_assoc (2 * μ), hexp]; ring

lemma f_cont {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (u : ℝ) :
    Continuous (fun t => (t - u) * w μ v S t) := by
  unfold w outsideCdf AssortSearch.Cannibal.lam
  fun_prop

lemma g_int (μ : ℝ) (hμ : 0 < μ) (K a : ℝ) :
    IntegrableOn (fun t => K * Real.exp (-(1 / (2 * μ)) * t)) (Ioi a) :=
  (exp_neg_integrableOn_Ioi a (b := 1 / (2 * μ)) (by positivity)).const_mul K

lemma f_int {n : ℕ} {μ : ℝ} (hμ : 0 < μ) (v : Fin n → ℝ) (S : Finset (Fin n))
    (hV : 0 ≤ outsidePref v S) (u : ℝ) :
    IntegrableOn (fun t => (t - u) * w μ v S t) (Ioi u) := by
  refine Integrable.mono' (g_int μ hμ (C0 μ (outsidePref v S) * Real.exp (-u / (2 * μ))) u)
    (f_cont μ v S u).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have hb := f_bound hμ v S hV u t (le_of_lt ht)
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

lemma gain_upper {n : ℕ} {μ : ℝ} (hμ : 0 < μ) (v : Fin n → ℝ) (S : Finset (Fin n))
    (hV : 0 ≤ outsidePref v S) (u : ℝ) (hu : 0 ≤ u) :
    searchGain μ v S u ≤ C0 μ (outsidePref v S) * Real.exp (-u / (2 * μ)) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-(1 / (2 * μ)) * t) := by
  unfold searchGain
  have hK : 0 ≤ C0 μ (outsidePref v S) * Real.exp (-u / (2 * μ)) := by
    unfold C0; positivity
  calc (∫ t in Ioi u, (t - u) * w μ v S t)
      ≤ ∫ t in Ioi u, C0 μ (outsidePref v S) * Real.exp (-u / (2 * μ)) *
          Real.exp (-(1 / (2 * μ)) * t) :=
        setIntegral_mono_on (f_int hμ v S hV u) (g_int μ hμ _ u) measurableSet_Ioi
          (fun t ht => (f_bound hμ v S hV u t (le_of_lt ht)).2)
    _ = C0 μ (outsidePref v S) * Real.exp (-u / (2 * μ)) *
          ∫ t in Ioi u, Real.exp (-(1 / (2 * μ)) * t) := by
        rw [integral_const_mul]
    _ ≤ C0 μ (outsidePref v S) * Real.exp (-u / (2 * μ)) *
          ∫ t in Ioi (0 : ℝ), Real.exp (-(1 / (2 * μ)) * t) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply setIntegral_mono_set (exp_neg_integrableOn_Ioi 0 (by positivity))
        · exact (ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun t _ => (Real.exp_pos _).le)
        · exact (Ioi_subset_Ioi hu).eventuallyLE

lemma gain_small {n : ℕ} {μ : ℝ} (hμ : 0 < μ) (v : Fin n → ℝ) (S : Finset (Fin n))
    (hV : 0 ≤ outsidePref v S) (b : ℝ) (hb : 0 < b) :
    ∃ u, searchGain μ v S u ≤ b := by
  set I := ∫ t in Ioi (0 : ℝ), Real.exp (-(1 / (2 * μ)) * t)
  have hT : Tendsto (fun u : ℝ => C0 μ (outsidePref v S) * Real.exp (-u / (2 * μ)) * I)
      atTop (𝓝 (C0 μ (outsidePref v S) * 0 * I)) := by
    refine (Tendsto.const_mul _ ?_).mul_const I
    exact Real.tendsto_exp_atBot.comp
      (Tendsto.atBot_div_const (by positivity) tendsto_neg_atTop_atBot)
  simp only [mul_zero, zero_mul] at hT
  have h1 := hT.eventually (gt_mem_nhds hb)
  obtain ⟨u, hu1, hu2⟩ := (h1.and (eventually_ge_atTop (0 : ℝ))).exists
  exact ⟨u, (gain_upper hμ v S hV u hu2).trans hu1.le⟩

/-- the lower bound constant -/
noncomputable def δ0 (μ V M : ℝ) : ℝ :=
  V / μ * AssortSearch.Cannibal.lam μ (M + 2) *
    Real.exp (-(AssortSearch.Cannibal.lam μ (M + 1) * V))

lemma δ0_pos {μ V : ℝ} (hμ : 0 < μ) (hV : 0 < V) (M : ℝ) : 0 < δ0 μ V M := by
  unfold δ0
  have := lam_pos μ (M + 2)
  positivity

lemma gain_lower {n : ℕ} {μ : ℝ} (hμ : 0 < μ) (v : Fin n → ℝ) (S : Finset (Fin n))
    (hV : 0 ≤ outsidePref v S) (M u : ℝ) (hu : u ≤ M) :
    δ0 μ (outsidePref v S) M ≤ searchGain μ v S u := by
  unfold searchGain
  have hint := f_int hμ v S hV u
  have hsub : Ioc (M + 1) (M + 2) ⊆ Ioi u := fun t ht => by
    simp only [mem_Ioc, mem_Ioi] at ht ⊢; linarith [ht.1]
  calc δ0 μ (outsidePref v S) M
      = ∫ _ in Ioc (M + 1) (M + 2), δ0 μ (outsidePref v S) M := by
        rw [setIntegral_const]; simp; norm_num
    _ ≤ ∫ t in Ioc (M + 1) (M + 2), (t - u) * w μ v S t := by
        refine setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set hsub)
          measurableSet_Ioc (fun t ht => ?_)
        simp only [mem_Ioc] at ht
        have hl1 : AssortSearch.Cannibal.lam μ (M + 2) ≤ AssortSearch.Cannibal.lam μ t :=
          lam_anti hμ ht.2
        have hl2 : AssortSearch.Cannibal.lam μ t ≤ AssortSearch.Cannibal.lam μ (M + 1) :=
          lam_anti hμ ht.1.le
        have he : Real.exp (-(AssortSearch.Cannibal.lam μ (M + 1) * outsidePref v S)) ≤
            Real.exp (-(AssortSearch.Cannibal.lam μ t * outsidePref v S)) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_right hl2 hV
          linarith
        have hwt : δ0 μ (outsidePref v S) M ≤ w μ v S t := by
          rw [w_eq]; unfold δ0
          have := lam_pos μ (M + 2)
          have := lam_pos μ t
          apply mul_le_mul _ he (Real.exp_pos _).le (by positivity)
          exact mul_le_mul_of_nonneg_left hl1 (by positivity)
        have h0 : 0 ≤ δ0 μ (outsidePref v S) M := by
          unfold δ0; have := lam_pos μ (M + 2); positivity
        calc δ0 μ (outsidePref v S) M = 1 * δ0 μ (outsidePref v S) M := by ring
          _ ≤ (t - u) * w μ v S t := by
            apply mul_le_mul (by linarith) hwt h0 (by linarith)
    _ ≤ ∫ t in Ioi u, (t - u) * w μ v S t := by
        apply setIntegral_mono_set hint
        · exact (ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun t ht => (f_bound hμ v S hV u t (le_of_lt ht)).1)
        · exact hsub.eventuallyLE

lemma V_pos {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 < v i) (S : Finset (Fin n))
    (hS : S ≠ Finset.univ) : 0 < outsidePref v S := by
  unfold outsidePref
  obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
    by_contra h
    push Not at h
    exact hS (Finset.eq_univ_of_forall h)
  exact Finset.sum_pos (fun j _ => hv j) ⟨i, by simpa using hi⟩

theorem Ubar_tendsto {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    Tendsto (fun b => Ubar μ v S b) (𝓝[>] 0) atTop := by
  have hV := V_pos v hv S hS
  refine tendsto_atTop.2 fun M => ?_
  refine mem_of_superset (Ioo_mem_nhdsGT (δ0_pos hμ hV M)) (fun b hb => ?_)
  simp only [mem_Ioo] at hb
  show M ≤ Ubar μ v S b
  unfold Ubar
  obtain ⟨u0, hu0⟩ := gain_small hμ v S hV.le b hb.1
  apply le_csInf ⟨u0, hu0⟩
  intro u hu
  simp only [mem_ofPred_eq] at hu
  by_contra h
  push Not at h
  have := gain_lower hμ v S hV.le M u h.le
  linarith [hb.2]

theorem H_tendsto {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (v0 : ℝ) (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    Tendsto (fun b => AssortSearch.Cannibal.H μ (Ubar μ v S b) v v0 S) (𝓝[>] 0) (𝓝 1) := by
  have hlam : Tendsto (fun U => AssortSearch.Cannibal.lam μ U) atTop (𝓝 0) := by
    unfold AssortSearch.Cannibal.lam
    refine Real.tendsto_exp_atBot.comp ?_
    refine tendsto_neg_atTop_atBot.comp ?_
    exact tendsto_atTop_add_const_right _ _ (Tendsto.atTop_div_const hμ tendsto_id)
  have h2 : Tendsto (fun U => AssortSearch.Cannibal.H μ U v v0 S) atTop (𝓝 1) := by
    unfold AssortSearch.Cannibal.H
    have := ((Real.continuous_exp.tendsto _).comp ((hlam.mul_const (v0 + ∑ j ∈ S, v j)).neg))
    simpa [Function.comp_def] using this
  exact h2.comp (Ubar_tendsto μ hμ v hv S hS)

end FullAssortHT

open FullAssortHT in
theorem solution {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (v0 : ℝ) (hv0 : 0 < v0) (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    Tendsto (fun b => AssortSearch.Cannibal.H μ (Ubar μ v S b) v v0 S) (𝓝[>] 0) (𝓝 1) ∧
      ∀ i ∈ S, Tendsto (fun b => demandSO μ v v0 b S i) (𝓝[>] 0) (𝓝 0) := by
  have hH := H_tendsto μ hμ v hv v0 S hS
  refine ⟨hH, fun i _ => ?_⟩
  have heq : (fun b => demandSO μ v v0 b S i) = fun b =>
      RetailVariety.Structure.share v v0 S i *
        (1 - AssortSearch.Cannibal.H μ (Ubar μ v S b) v v0 S) := by
    funext b; simp [demandSO, hS]
  rw [heq]
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub hH
  simpa using this.const_mul (RetailVariety.Structure.share v v0 S i)
