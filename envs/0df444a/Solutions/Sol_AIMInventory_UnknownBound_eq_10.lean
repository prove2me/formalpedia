-- Prove2me | solution 1 for AIMInventory.UnknownBound.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:56:34.989884+00:00
-- url     : https://prove2.me/submissions/69b90d41-6078-4c83-b9f7-182c1c048a74

import Definitions.Def_AIMInventory_UnknownBound_AIM

open MeasureTheory


namespace AIMInventory.UnknownBound

open scoped NNReal

noncomputable def phi (h b y d : ℝ) : ℝ := h * max (y - d) 0 + b * max (d - y) 0

lemma phi_sub (h b y y' d : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    phi h b y d + (if d < y then h else -b) * (y' - y) ≤ phi h b y' d := by
  unfold phi
  split_ifs with hd
  · have h1 : max (y - d) 0 = y - d := max_eq_left (by linarith)
    have h2 : max (d - y) 0 = 0 := max_eq_right (by linarith)
    have h3 : y' - d ≤ max (y' - d) 0 := le_max_left _ _
    have h4 : 0 ≤ max (d - y') 0 := le_max_right _ _
    rw [h1, h2]; nlinarith [mul_le_mul_of_nonneg_left h3 hh, mul_nonneg hb h4]
  · have h1 : max (y - d) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (d - y) 0 = d - y := max_eq_left (by linarith)
    have h3 : d - y' ≤ max (d - y') 0 := le_max_left _ _
    have h4 : 0 ≤ max (y' - d) 0 := le_max_right _ _
    rw [h1, h2]; nlinarith [mul_le_mul_of_nonneg_left h3 hb, mul_nonneg hh h4]

lemma phi_lip (h b y y' d : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    |phi h b y d - phi h b y' d| ≤ max b h * |y - y'| := by
  have hM1 : h ≤ max b h := le_max_right _ _
  have hM2 : b ≤ max b h := le_max_left _ _
  have hM0 : 0 ≤ max b h := le_trans hb hM2
  have e1 := mul_le_mul_of_nonneg_left (le_abs_self (y - y')) hM0
  have e2 := mul_le_mul_of_nonneg_left (neg_abs_le (y - y')) hM0
  have f1 := mul_le_mul_of_nonneg_left (le_abs_self (y - y')) hb
  have f2 := mul_le_mul_of_nonneg_left (neg_abs_le (y - y')) hb
  have f3 := mul_le_mul_of_nonneg_left (le_abs_self (y - y')) hh
  have f4 := mul_le_mul_of_nonneg_left (neg_abs_le (y - y')) hh
  have g1 := mul_le_mul_of_nonneg_right hM2 (abs_nonneg (y - y'))
  have g2 := mul_le_mul_of_nonneg_right hM1 (abs_nonneg (y - y'))
  unfold phi
  rw [abs_le]
  rcases le_total y d with h1 | h1 <;> rcases le_total y' d with h2 | h2
  · rw [max_eq_right (by linarith : y - d ≤ 0), max_eq_left (by linarith : 0 ≤ d - y),
      max_eq_right (by linarith : y' - d ≤ 0), max_eq_left (by linarith : 0 ≤ d - y')]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hM2) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hM2) (sub_nonneg.2 h2)]
  · rw [max_eq_right (by linarith : y - d ≤ 0), max_eq_left (by linarith : 0 ≤ d - y),
      max_eq_left (by linarith : 0 ≤ y' - d), max_eq_right (by linarith : d - y' ≤ 0)]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hM2) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hM1) (sub_nonneg.2 h2)]
  · rw [max_eq_left (by linarith : 0 ≤ y - d), max_eq_right (by linarith : d - y ≤ 0),
      max_eq_right (by linarith : y' - d ≤ 0), max_eq_left (by linarith : 0 ≤ d - y')]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hM1) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hM2) (sub_nonneg.2 h2)]
  · rw [max_eq_left (by linarith : 0 ≤ y - d), max_eq_right (by linarith : d - y ≤ 0),
      max_eq_left (by linarith : 0 ≤ y' - d), max_eq_right (by linarith : d - y' ≤ 0)]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hM1) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hM1) (sub_nonneg.2 h2)]

open CappedBaseStock

lemma integrable_hold (P : DemandLaw) (y : ℝ) :
    Integrable (fun d : ℝ≥0 => max (y - (d : ℝ)) 0) P.law := by
  have hm : Integrable (fun d : ℝ≥0 => |y| + (d : ℝ)) P.law := (integrable_const _).add P.finiteMean
  refine Integrable.mono' hm (by fun_prop) (Filter.Eventually.of_forall fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [le_abs_self y, d.coe_nonneg]) (by positivity)

lemma integrable_short (P : DemandLaw) (y : ℝ) :
    Integrable (fun d : ℝ≥0 => max ((d : ℝ) - y) 0) P.law := by
  have hm : Integrable (fun d : ℝ≥0 => |y| + (d : ℝ)) P.law := (integrable_const _).add P.finiteMean
  refine Integrable.mono' hm (by fun_prop) (Filter.Eventually.of_forall fun d => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [neg_abs_le y, d.coe_nonneg]) (by positivity)

lemma integrable_phi (P : DemandLaw) (h b y : ℝ) :
    Integrable (fun d : ℝ≥0 => phi h b y d) P.law :=
  ((integrable_hold P y).const_mul h).add ((integrable_short P y).const_mul b)

lemma cost_eq (P : DemandLaw) (h b y : ℝ) :
    cost P h b y = ∫ d : ℝ≥0, phi h b (max y 0) d ∂P.law := by
  unfold cost LostSalesOrderUpTo.Asymptotic.backorderCost
    LostSalesOrderUpTo.Asymptotic.expectedHolding LostSalesOrderUpTo.Asymptotic.expectedShortfall
  rw [Real.coe_toNNReal', ← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrable_hold P _).const_mul h) ((integrable_short P _).const_mul b)]
  rfl

lemma cost_lip (P : DemandLaw) (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (y y' : ℝ) :
    |cost P h b y - cost P h b y'| ≤ max b h * |y - y'| := by
  rw [cost_eq, cost_eq, ← integral_sub (integrable_phi P h b _) (integrable_phi P h b _)]
  have hM0 : 0 ≤ max b h := le_trans hb (le_max_left _ _)
  calc _ ≤ ∫ d : ℝ≥0, |phi h b (max y 0) d - phi h b (max y' 0) d| ∂P.law := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := P.law)
            (fun d : ℝ≥0 => phi h b (max y 0) d - phi h b (max y' 0) d)
    _ ≤ ∫ d : ℝ≥0, max b h * |y - y'| ∂P.law := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun d => abs_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall fun d => ?_)
        refine (phi_lip h b _ _ _ hh hb).trans ?_
        exact mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs y y' 0 |>.trans_eq (by simp)) hM0
    _ = _ := by simp

lemma continuous_cost (P : DemandLaw) (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    Continuous (cost P h b) := by
  refine (LipschitzWith.of_dist_le' (K := max b h) ?_).continuous
  intro x y
  simpa [Real.dist_eq] using cost_lip P h b hh hb x y

lemma cost_le (P : DemandLaw) (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (y y' : ℝ) :
    cost P h b y - cost P h b y' ≤ max b h * |y - y'| :=
  (le_abs_self _).trans (cost_lip P h b hh hb y y')


lemma project_nonneg (a z : ℝ) : 0 ≤ project a z := le_max_right _ _

lemma project_le (a z : ℝ) (ha : 0 ≤ a) : project a z ≤ a := max_le (min_le_right _ _) ha

lemma project_sq (a z c : ℝ) (hc0 : 0 ≤ c) (hca : c ≤ a) :
    (project a z - c) ^ 2 ≤ (z - c) ^ 2 := by
  unfold project
  rcases le_total z a with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total z 0 with h2 | h2
    · rw [max_eq_right h2]; nlinarith
    · rw [max_eq_left h2]
  · rw [min_eq_right h1, max_eq_left (by linarith : 0 ≤ a)]; nlinarith

lemma radius_nonneg (δ : ℝ) (t : ℕ) : 0 ≤ radius δ t := Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma one_le_radius (δ : ℝ) (hδ : 0 ≤ δ) (t : ℕ) (ht : 1 ≤ t) : 1 ≤ radius δ t :=
  Real.one_le_rpow (by exact_mod_cast ht) (by positivity)

lemma radius_mono (δ : ℝ) (hδ : 0 ≤ δ) {t t' : ℕ} (h : t ≤ t') : radius δ t ≤ radius δ t' :=
  Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.2 h) (by positivity)

lemma run_bounds (δ b h y₁ : ℝ) (hδ : 0 ≤ δ) (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1)
    (d : CappedBaseStock.DemandPath) (k : ℕ) :
    0 ≤ modAimRun δ b h y₁ d k ∧ modAimRun δ b h y₁ d k ≤ radius δ (k + 1) := by
  induction k with
  | zero =>
    exact ⟨hy₁.1, hy₁.2.trans (one_le_radius δ hδ 1 le_rfl)⟩
  | succ k ih =>
    refine ⟨project_nonneg _ _, ?_⟩
    exact (project_le _ _ (radius_nonneg _ _)).trans (radius_mono δ hδ (Nat.le_succ _))

lemma target_bounds (δ b h y₁ : ℝ) (hδ : 0 ≤ δ) (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1)
    (d : CappedBaseStock.DemandPath) (t : ℕ) (ht : 1 ≤ t) :
    0 ≤ modAimTarget δ b h y₁ d t ∧ modAimTarget δ b h y₁ d t ≤ radius δ t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simpa [modAimTarget] using run_bounds δ b h y₁ hδ hy₁ d k

lemma target_succ (δ b h y₁ : ℝ) (d : CappedBaseStock.DemandPath) (t : ℕ) (ht : 1 ≤ t) :
    modAimTarget δ b h y₁ d (t + 1) =
      project (radius δ t) (modAimTarget δ b h y₁ d t -
        stepSize b h t * signal h b (modAimTarget δ b h y₁ d t) (d (t - 1))) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp [modAimTarget, modAimRun]

lemma measurable_run (δ b h y₁ : ℝ) (k : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => modAimRun δ b h y₁ d k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [modAimRun, project, signal]
    have hd : Measurable (fun d : CappedBaseStock.DemandPath => ((d k : ℝ≥0) : ℝ)) :=
      (measurable_pi_apply k).coe_nnreal_real
    have hs : Measurable (fun d : CappedBaseStock.DemandPath =>
        if ((d k : ℝ≥0) : ℝ) < modAimRun δ b h y₁ d k then h else -b) :=
      Measurable.ite (measurableSet_lt hd ih) measurable_const measurable_const
    exact ((ih.sub (hs.const_mul _)).min measurable_const).max measurable_const

lemma measurable_target (δ b h y₁ : ℝ) (t : ℕ) :
    Measurable (fun d : CappedBaseStock.DemandPath => modAimTarget δ b h y₁ d t) :=
  measurable_run δ b h y₁ (t - 1)

lemma run_congr (δ b h y₁ : ℝ) (d d' : CappedBaseStock.DemandPath) (k : ℕ)
    (hdd : ∀ i < k, d i = d' i) : modAimRun δ b h y₁ d k = modAimRun δ b h y₁ d' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have := ih (fun i hi => hdd i (by omega))
    simp only [modAimRun, this, hdd k (by omega)]


open ProbabilityTheory

lemma indep_coord (P : DemandLaw) (n : ℕ) (Y : DemandPath → ℝ) (hY : Measurable Y)
    (hdep : ∀ d d' : DemandPath, (∀ i < n, d i = d' i) → Y d = Y d') :
    IndepFun Y (fun d => d n) (demandPathLaw P) := by
  have hi : iIndepFun (fun (i : ℕ) (d : DemandPath) => d i) (demandPathLaw P) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => P.law) (X := fun _ x => x) (fun _ => measurable_id)
  have := hi.indepFun_finset (Finset.range n) {n} (by simp) (fun i => measurable_pi_apply i)
  let ext : (↥(Finset.range n) → ℝ≥0) → DemandPath :=
    fun u i => if hi : i < n then u ⟨i, Finset.mem_range.2 hi⟩ else 0
  have hext : Measurable ext := by
    refine measurable_pi_lambda _ (fun i => ?_)
    by_cases hi : i < n
    · simp only [ext, hi, dif_pos]; exact measurable_pi_apply _
    · simp only [ext, hi, dif_neg, not_false_eq_true]; exact measurable_const
  have h1 := this.comp (hY.comp hext) (measurable_pi_apply (⟨n, by simp⟩ : ↥({n} : Finset ℕ)))
  have e1 : (Y ∘ ext) ∘ (fun (a : DemandPath) (i : ↥(Finset.range n)) => a i) = Y := by
    funext d
    exact hdep _ _ (fun i hi => by simp [ext, hi])
  have e2 : (fun u : ↥({n} : Finset ℕ) → ℝ≥0 => u ⟨n, by simp⟩) ∘
      (fun (a : DemandPath) (i : ↥({n} : Finset ℕ)) => a i) = fun d => d n := by
    funext d; rfl
  rw [e1, e2] at h1
  exact h1

lemma phi_clamp_bound (h b c d B : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (hc0 : 0 ≤ c) (hcB : c ≤ B)
    (hd : 0 ≤ d) : |phi h b c d| ≤ h * B + b * d := by
  unfold phi
  have h1 : max (c - d) 0 ≤ B := max_le (by linarith) (by linarith)
  have h2 : max (d - c) 0 ≤ d := max_le (by linarith) hd
  have h3 : 0 ≤ max (c - d) 0 := le_max_right _ _
  have h4 : 0 ≤ max (d - c) 0 := le_max_right _ _
  rw [abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hh, mul_le_mul_of_nonneg_left h2 hb]

lemma integral_phi_indep (P : DemandLaw) (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (n : ℕ)
    (Y : DemandPath → ℝ) (hY : Measurable Y) (B : ℝ) (hB0 : 0 ≤ B)
    (hY0 : ∀ d, 0 ≤ Y d) (hYB : ∀ d, Y d ≤ B)
    (hdep : ∀ d d' : DemandPath, (∀ i < n, d i = d' i) → Y d = Y d') :
    Integrable (fun d : DemandPath => phi h b (Y d) (d n)) (demandPathLaw P) ∧
    ∫ d : DemandPath, phi h b (Y d) (d n) ∂demandPathLaw P =
      ∫ d : DemandPath, cost P h b (Y d) ∂demandPathLaw P := by
  set μ := demandPathLaw P with hμ
  have hind := indep_coord P n Y hY hdep
  have hD : Measurable (fun d : DemandPath => d n) := measurable_pi_apply n
  have hmapD : μ.map (fun d : DemandPath => d n) = P.law := by
    simpa [hμ, demandPathLaw] using Measure.infinitePi_map_eval (fun _ : ℕ => P.law) n
  have hmap : μ.map (fun d => (Y d, d n)) = (μ.map Y).prod P.law := by
    rw [← hmapD]
    exact (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hD.aemeasurable).1 hind
  set ν := μ.map Y with hν
  let clamp : ℝ → ℝ := fun y => max (min y B) 0
  have hclamp : Continuous clamp := by unfold clamp; fun_prop
  have hclampY : ∀ d, clamp (Y d) = Y d := by
    intro d
    simp only [clamp, min_eq_left (hYB d), max_eq_left (hY0 d)]
  let ψ : ℝ × ℝ≥0 → ℝ := fun p => phi h b (clamp p.1) p.2
  have hψ : Continuous ψ := by
    unfold ψ phi; have := hclamp; fun_prop
  have hψint : Integrable ψ (ν.prod P.law) := by
    have hg : Integrable (fun d : ℝ≥0 => h * B + b * (d : ℝ)) P.law :=
      (integrable_const _).add (P.finiteMean.const_mul b)
    have hν' : IsFiniteMeasure ν := by rw [hν]; infer_instance
    refine Integrable.mono' (hg.comp_snd ν) hψ.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact phi_clamp_bound h b _ _ B hh hb (le_max_right _ _)
      (max_le (min_le_right _ _) hB0) p.2.coe_nonneg
  have hpair : Measurable (fun d : DemandPath => (Y d, d n)) := hY.prodMk hD
  have hcomp : (fun d : DemandPath => phi h b (Y d) (d n)) = fun d => ψ (Y d, d n) := by
    funext d; simp only [ψ, hclampY]
  constructor
  · rw [hcomp]
    have := (integrable_map_measure hψ.aestronglyMeasurable hpair.aemeasurable).1
      (by rw [hmap]; exact hψint)
    exact this
  · rw [hcomp]
    have e1 : ∫ d, ψ (Y d, d n) ∂μ = ∫ p, ψ p ∂(ν.prod P.law) := by
      rw [← hmap, integral_map hpair.aemeasurable hψ.aestronglyMeasurable]
    rw [e1, integral_prod _ hψint]
    have e2 : ∀ y : ℝ, ∫ d : ℝ≥0, ψ (y, d) ∂P.law = cost P h b (clamp y) := by
      intro y
      rw [cost_eq]
      simp only [ψ]
      rw [max_eq_left (le_max_right _ _)]
    simp_rw [e2]
    have hcc : Continuous (fun y => cost P h b (clamp y)) := (continuous_cost P h b hh hb).comp hclamp
    rw [hν, integral_map hY.aemeasurable hcc.aestronglyMeasurable]
    simp only [hclampY]


lemma integrable_of_bdd {μ : Measure DemandPath} [IsFiniteMeasure μ] {f : DemandPath → ℝ}
    (hf : Measurable f) (C : ℝ) (hC : ∀ d, |f d| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun d => by
    rw [Real.norm_eq_abs]; exact hC d)

lemma measurable_signal (h b : ℝ) (Y : DemandPath → ℝ) (hY : Measurable Y) (n : ℕ) :
    Measurable (fun d : DemandPath => signal h b (Y d) (d n)) := by
  unfold signal
  have hd : Measurable (fun d : DemandPath => ((d n : ℝ≥0) : ℝ)) :=
    (measurable_pi_apply n).coe_nnreal_real
  exact Measurable.ite (measurableSet_lt hd hY) measurable_const measurable_const

lemma signal_abs_le (h b y : ℝ) (d : ℝ≥0) (hh : 0 ≤ h) (hb : 0 ≤ b) :
    |signal h b y d| ≤ max b h := by
  unfold signal
  split_ifs
  · rw [abs_of_nonneg hh]; exact le_max_right _ _
  · rw [abs_neg, abs_of_nonneg hb]; exact le_max_left _ _

lemma integral_phi_const (P : DemandLaw) (h b c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    Integrable (fun d : DemandPath => phi h b c (d n)) (demandPathLaw P) ∧
    ∫ d : DemandPath, phi h b c (d n) ∂demandPathLaw P = cost P h b c := by
  have hD : Measurable (fun d : DemandPath => d n) := measurable_pi_apply n
  have hmapD : (demandPathLaw P).map (fun d : DemandPath => d n) = P.law := by
    simpa [demandPathLaw] using Measure.infinitePi_map_eval (fun _ : ℕ => P.law) n
  have hcont : Continuous (fun x : ℝ≥0 => phi h b c x) := by unfold phi; fun_prop
  constructor
  · have := (integrable_map_measure (μ := demandPathLaw P) (f := fun d : DemandPath => d n)
      (g := fun x : ℝ≥0 => phi h b c x) hcont.aestronglyMeasurable hD.aemeasurable).1
      (by rw [hmapD]; exact integrable_phi P h b c)
    exact this
  · have := integral_map (μ := demandPathLaw P) hD.aemeasurable
      (φ := fun d : DemandPath => d n) (f := fun x : ℝ≥0 => phi h b c x) hcont.aestronglyMeasurable
    rw [hmapD] at this
    rw [cost_eq, max_eq_left hc]
    exact this.symm


lemma stepSize_pos (b h : ℝ) (hb : 0 < b) (hh : 0 < h) (t : ℕ) (ht : 1 ≤ t) :
    0 < stepSize b h t := by
  unfold stepSize
  have : (0 : ℝ) < t := by exact_mod_cast ht
  have : 0 < max b h := lt_max_of_lt_left hb
  positivity

lemma eq15_core (P : DemandLaw) (δ b h y₁ : ℝ) (t : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (ht : 1 ≤ t)
    (hcomp : newsvendor P h b ≤ radius δ t) :
    (∫ d : CappedBaseStock.DemandPath,
        (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b (newsvendor P h b))
          ∂CappedBaseStock.demandPathLaw P) ≤
      (∫ d : CappedBaseStock.DemandPath,
          (modAimTarget δ b h y₁ d t - newsvendor P h b) ^ 2
            ∂CappedBaseStock.demandPathLaw P) / (2 * stepSize b h t) -
      (∫ d : CappedBaseStock.DemandPath,
          (modAimTarget δ b h y₁ d (t + 1) - newsvendor P h b) ^ 2
            ∂CappedBaseStock.demandPathLaw P) / (2 * stepSize b h t) +
      stepSize b h t / 2 *
        (∫ d : CappedBaseStock.DemandPath,
          (signal h b (modAimTarget δ b h y₁ d t) (d (t - 1))) ^ 2
            ∂CappedBaseStock.demandPathLaw P) := by
  have hδ0 : 0 ≤ δ := hδ.1.le
  have hh0 : 0 ≤ h := hh.le
  have hb0 : 0 ≤ b := hb.le
  set μ := demandPathLaw P with hμ
  set c := newsvendor P h b with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact NNReal.coe_nonneg _
  set M := max b h with hM
  set η := stepSize b h t with hη
  have hηpos : 0 < η := stepSize_pos b h hb hh t ht
  set Y : DemandPath → ℝ := fun d => modAimTarget δ b h y₁ d t with hY
  set Y' : DemandPath → ℝ := fun d => modAimTarget δ b h y₁ d (t + 1) with hY'
  set sg : DemandPath → ℝ := fun d => signal h b (Y d) (d (t - 1)) with hsg
  have hYm : Measurable Y := measurable_target δ b h y₁ t
  have hY'm : Measurable Y' := measurable_target δ b h y₁ (t + 1)
  have hsgm : Measurable sg := measurable_signal h b Y hYm (t - 1)
  have hYb : ∀ d, 0 ≤ Y d ∧ Y d ≤ radius δ t := fun d => target_bounds δ b h y₁ hδ0 hy₁ d t ht
  have hY'b : ∀ d, 0 ≤ Y' d ∧ Y' d ≤ radius δ (t + 1) :=
    fun d => target_bounds δ b h y₁ hδ0 hy₁ d (t + 1) (by omega)
  have hsgb : ∀ d, |sg d| ≤ M := fun d => signal_abs_le h b _ _ hh0 hb0
  have hdep : ∀ d d' : DemandPath, (∀ i < t - 1, d i = d' i) → Y d = Y d' := by
    intro d d' hdd
    exact run_congr δ b h y₁ d d' (t - 1) hdd
  obtain ⟨hI1, hI2⟩ := integral_phi_indep P h b hh0 hb0 (t - 1) Y hYm (radius δ t)
    (radius_nonneg _ _) (fun d => (hYb d).1) (fun d => (hYb d).2) hdep
  obtain ⟨hJ1, hJ2⟩ := integral_phi_const P h b c hc0 (t - 1)
  -- integrability of the building blocks
  have hcostY : Continuous (cost P h b) := continuous_cost P h b hh0 hb0
  have hcostYm : Measurable (fun d => cost P h b (Y d)) := hcostY.measurable.comp hYm
  have hcostYb : ∀ d, |cost P h b (Y d)| ≤ |cost P h b c| + M * radius δ t := by
    intro d
    have := cost_lip P h b hh0 hb0 (Y d) c
    have h2 : |Y d - c| ≤ radius δ t := by
      rw [abs_le]; constructor <;> linarith [(hYb d).1, (hYb d).2]
    have h3 : 0 ≤ M := le_trans hb0 (le_max_left _ _)
    calc |cost P h b (Y d)| = |(cost P h b (Y d) - cost P h b c) + cost P h b c| := by ring_nf
      _ ≤ |cost P h b (Y d) - cost P h b c| + |cost P h b c| := abs_add_le _ _
      _ ≤ M * |Y d - c| + |cost P h b c| := by gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hcostYi : Integrable (fun d => cost P h b (Y d)) μ := integrable_of_bdd hcostYm _ hcostYb
  have hlin : Integrable (fun d => sg d * (c - Y d)) μ := by
    refine integrable_of_bdd (hsgm.mul (measurable_const.sub hYm)) (M * radius δ t) (fun d => ?_)
    rw [abs_mul]
    have h2 : |c - Y d| ≤ radius δ t := by
      rw [abs_le]; constructor <;> linarith [(hYb d).1, (hYb d).2]
    exact mul_le_mul (hsgb d) h2 (abs_nonneg _) (le_trans hb0 (le_max_left _ _))
  -- Step 1 : subgradient inequality
  have step1 : ∫ d, sg d * (c - Y d) ∂μ ≤ cost P h b c - ∫ d, cost P h b (Y d) ∂μ := by
    have hpt : ∀ d, sg d * (c - Y d) ≤ phi h b c (d (t - 1)) - phi h b (Y d) (d (t - 1)) := by
      intro d
      have := phi_sub h b (Y d) c (d (t - 1)) hh0 hb0
      simp only [hsg, signal]
      linarith
    calc ∫ d, sg d * (c - Y d) ∂μ
        ≤ ∫ d, (phi h b c (d (t - 1)) - phi h b (Y d) (d (t - 1))) ∂μ :=
          integral_mono hlin (hJ1.sub hI1) hpt
      _ = _ := by rw [integral_sub hJ1 hI1, hJ2, hI2]
  -- Step 2 : pointwise projection inequality
  have hpt2 : ∀ d, sg d * (Y d - c) ≤
      (Y d - c) ^ 2 / (2 * η) - (Y' d - c) ^ 2 / (2 * η) + η / 2 * sg d ^ 2 := by
    intro d
    have h1 := project_sq (radius δ t) (Y d - η * sg d) c hc0 hcomp
    have h2 : Y' d = project (radius δ t) (Y d - η * sg d) := target_succ δ b h y₁ d t ht
    rw [h2]
    have h3 : (project (radius δ t) (Y d - η * sg d) - c) ^ 2 ≤ (Y d - c) ^ 2 - 2 * η * (sg d * (Y d - c)) + η ^ 2 * sg d ^ 2 := by
      nlinarith [h1]
    have h4 : 2 * η * (sg d * (Y d - c)) ≤ (Y d - c) ^ 2 - (project (radius δ t) (Y d - η * sg d) - c) ^ 2 + η ^ 2 * sg d ^ 2 := by linarith
    have h5 : sg d * (Y d - c) ≤ ((Y d - c) ^ 2 - (project (radius δ t) (Y d - η * sg d) - c) ^ 2 + η ^ 2 * sg d ^ 2) / (2 * η) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    refine h5.trans (le_of_eq ?_)
    field_simp
  have iA : Integrable (fun d => (Y d - c) ^ 2) μ := by
    refine integrable_of_bdd ((hYm.sub measurable_const).pow_const 2) ((radius δ t) ^ 2) (fun d => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    have : |Y d - c| ≤ radius δ t := by
      rw [abs_le]; constructor <;> linarith [(hYb d).1, (hYb d).2]
    nlinarith [abs_nonneg (Y d - c), sq_abs (Y d - c)]
  have iA' : Integrable (fun d => (Y' d - c) ^ 2) μ := by
    have hr : radius δ t ≤ radius δ (t + 1) := radius_mono δ hδ0 (Nat.le_succ _)
    refine integrable_of_bdd ((hY'm.sub measurable_const).pow_const 2) ((radius δ (t + 1)) ^ 2) (fun d => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    have : |Y' d - c| ≤ radius δ (t + 1) := by
      rw [abs_le]; constructor <;> linarith [(hY'b d).1, (hY'b d).2]
    nlinarith [abs_nonneg (Y' d - c), sq_abs (Y' d - c)]
  have iS : Integrable (fun d => sg d ^ 2) μ := by
    refine integrable_of_bdd (hsgm.pow_const 2) (M ^ 2) (fun d => ?_)
    rw [abs_of_nonneg (sq_nonneg _)]
    have := hsgb d
    nlinarith [abs_nonneg (sg d), sq_abs (sg d)]
  have hsm : Integrable (fun d => sg d * (Y d - c)) μ := by
    refine (hlin.neg).congr (Filter.Eventually.of_forall fun d => ?_)
    simp only [Pi.neg_apply]; ring
  have step2 : ∫ d, sg d * (Y d - c) ∂μ ≤
      (∫ d, (Y d - c) ^ 2 ∂μ) / (2 * η) - (∫ d, (Y' d - c) ^ 2 ∂μ) / (2 * η) +
        η / 2 * ∫ d, sg d ^ 2 ∂μ := by
    have hi : Integrable (fun d => (Y d - c) ^ 2 / (2 * η) - (Y' d - c) ^ 2 / (2 * η) + η / 2 * sg d ^ 2) μ :=
      ((iA.div_const _).sub (iA'.div_const _)).add (iS.const_mul _)
    calc ∫ d, sg d * (Y d - c) ∂μ
        ≤ ∫ d, ((Y d - c) ^ 2 / (2 * η) - (Y' d - c) ^ 2 / (2 * η) + η / 2 * sg d ^ 2) ∂μ :=
          integral_mono hsm hi hpt2
      _ = _ := by
        rw [integral_add (f := fun d => (Y d - c) ^ 2 / (2 * η) - (Y' d - c) ^ 2 / (2 * η))
            (g := fun d => η / 2 * sg d ^ 2) ((iA.div_const _).sub (iA'.div_const _)) (iS.const_mul _),
          integral_sub (f := fun d => (Y d - c) ^ 2 / (2 * η)) (g := fun d => (Y' d - c) ^ 2 / (2 * η))
            (iA.div_const _) (iA'.div_const _), integral_div, integral_div,
          integral_const_mul]
  -- conclude
  have hL : ∫ d, (cost P h b (Y d) - cost P h b c) ∂μ = ∫ d, cost P h b (Y d) ∂μ - cost P h b c := by
    rw [integral_sub hcostYi (integrable_const _)]; simp
  have hR : ∫ d, sg d * (Y d - c) ∂μ = - ∫ d, sg d * (c - Y d) ∂μ := by
    rw [← integral_neg]; congr 1; funext d; ring
  show ∫ d, (cost P h b (Y d) - cost P h b c) ∂μ ≤ _
  rw [hL]
  linarith [step1, step2, hR]


lemma integral_le_const' {μ : Measure DemandPath} [IsProbabilityMeasure μ] (f : DemandPath → ℝ) {C : ℝ}
    (hf : ∀ d, f d ≤ C) (hC : 0 ≤ C) : ∫ d, f d ∂μ ≤ C := by
  by_cases hi : Integrable f μ
  · calc ∫ d, f d ∂μ ≤ ∫ _d, C ∂μ := integral_mono hi (integrable_const _) hf
      _ = C := by simp
  · rw [integral_undef hi]; exact hC

lemma early_card (δ c : ℝ) (hc : 0 ≤ c) (T : ℕ) :
    ((earlyRounds δ c T).card : ℝ) ≤ Real.rpow c (2 / δ) := by
  have hx : 0 ≤ Real.rpow c (2 / δ) := Real.rpow_nonneg hc _
  have hsub : earlyRounds δ c T ⊆ Finset.Ico 1 ⌈Real.rpow c (2 / δ)⌉₊ := by
    intro t ht
    simp only [earlyRounds, Finset.mem_filter, Finset.mem_Icc] at ht
    simp only [Finset.mem_Ico]
    exact ⟨ht.1.1, Nat.lt_ceil.2 ht.2⟩
  refine (Nat.cast_le.2 ((Finset.card_le_card hsub).trans (by rw [Nat.card_Ico]))).trans ?_
  rcases Nat.eq_zero_or_pos ⌈Real.rpow c (2 / δ)⌉₊ with h0 | h0
  · rw [h0]; simpa using hx
  · rw [Nat.cast_sub h0]
    have := Nat.ceil_lt_add_one hx
    simp only [Nat.cast_one]
    linarith

lemma eq10_core (P : DemandLaw) (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    (∫ d : CappedBaseStock.DemandPath,
        (∑ t ∈ earlyRounds δ (newsvendor P h b) T,
          (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b (newsvendor P h b)))
          ∂CappedBaseStock.demandPathLaw P) ≤
      max b h * Real.rpow (newsvendor P h b) (1 + 2 / δ) := by
  have hδ0 : 0 < δ := hδ.1
  set c := newsvendor P h b with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact NNReal.coe_nonneg _
  set M := max b h with hM
  have hM0 : 0 ≤ M := le_trans hb.le (le_max_left _ _)
  have hpt : ∀ d : DemandPath, ∑ t ∈ earlyRounds δ c T,
      (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b c) ≤ M * Real.rpow c (1 + 2 / δ) := by
    intro d
    have hterm : ∀ t ∈ earlyRounds δ c T,
        cost P h b (modAimTarget δ b h y₁ d t) - cost P h b c ≤ M * c := by
      intro t ht
      simp only [earlyRounds, Finset.mem_filter, Finset.mem_Icc] at ht
      obtain ⟨⟨ht1, htT⟩, htx⟩ := ht
      obtain ⟨hY0, hYr⟩ := target_bounds δ b h y₁ hδ0.le hy₁ d t ht1
      have hcpos : 0 < c := by
        by_contra hn
        have h0 : c = 0 := le_antisymm (not_lt.1 hn) hc0
        simp only [Real.rpow_eq_pow] at htx
        rw [h0, Real.zero_rpow (by positivity)] at htx
        exact absurd htx (not_lt.2 (Nat.cast_nonneg _))
      have hrc : radius δ t < c := by
        unfold radius
        calc Real.rpow (t : ℝ) (δ / 2) < Real.rpow (Real.rpow c (2 / δ)) (δ / 2) :=
              Real.rpow_lt_rpow (Nat.cast_nonneg _) htx (by positivity)
          _ = c := by
              simp only [Real.rpow_eq_pow]
              rw [← Real.rpow_mul hc0]
              have : 2 / δ * (δ / 2) = 1 := by field_simp
              rw [this, Real.rpow_one]
      have h1 := cost_le P h b hh.le hb.le (modAimTarget δ b h y₁ d t) c
      have h2 : |modAimTarget δ b h y₁ d t - c| ≤ c := by
        rw [abs_le]; constructor <;> linarith
      nlinarith [mul_le_mul_of_nonneg_left h2 hM0]
    calc _ ≤ ∑ t ∈ earlyRounds δ c T, M * c := Finset.sum_le_sum hterm
      _ = ((earlyRounds δ c T).card : ℝ) * (M * c) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.rpow c (2 / δ) * (M * c) :=
          mul_le_mul_of_nonneg_right (early_card δ c hc0 T) (mul_nonneg hM0 hc0)
      _ = M * Real.rpow c (1 + 2 / δ) := by
          rcases hc0.eq_or_lt with h0 | h0
          · rw [← h0]
            simp [Real.zero_rpow (show (1 + 2 / δ) ≠ 0 by positivity)]
          · simp only [Real.rpow_eq_pow]
            rw [Real.rpow_add h0, Real.rpow_one]; ring
  exact integral_le_const' _ hpt (mul_nonneg hM0 (Real.rpow_nonneg hc0 _))

end AIMInventory.UnknownBound

open AIMInventory.UnknownBound


theorem solution (P : CappedBaseStock.DemandLaw) (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    (∫ d : CappedBaseStock.DemandPath,
        (∑ t ∈ earlyRounds δ (newsvendor P h b) T,
          (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b (newsvendor P h b)))
          ∂CappedBaseStock.demandPathLaw P) ≤
      max b h * Real.rpow (newsvendor P h b) (1 + 2 / δ) := by
  exact eq10_core P δ b h y₁ T hδ hb hh hy₁ hT
