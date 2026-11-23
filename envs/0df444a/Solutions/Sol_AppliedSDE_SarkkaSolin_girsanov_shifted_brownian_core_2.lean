-- Prove2me | solution 2 for AppliedSDE.SarkkaSolin.girsanov_shifted_brownian_core
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T01:46:19.855488+00:00
-- url     : https://prove2.me/submissions/c29df571-a667-4a43-a53d-99356d5f2880

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionApi
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology

lemma gauss_exp_lintegral (v : ℝ≥0) (x : ℝ) :
    ∫⁻ d, ENNReal.ofReal (Real.exp (x * d - x ^ 2 * v / 2)) ∂(gaussianReal 0 v) = 1 := by
  have hint : Integrable (fun d : ℝ => Real.exp (x * d - x ^ 2 * v / 2)) (gaussianReal 0 v) := by
    have := (integrable_exp_mul_gaussianReal (μ := 0) (v := v) x).div_const (Real.exp (x ^ 2 * v / 2))
    refine this.congr (Eventually.of_forall fun d => ?_)
    simp [Real.exp_sub]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun d => (Real.exp_pos _).le)]
  have h1 : ∫ d, Real.exp (x * d - x ^ 2 * v / 2) ∂(gaussianReal 0 v)
      = mgf id (gaussianReal 0 v) x / Real.exp (x ^ 2 * v / 2) := by
    rw [mgf, ← integral_div]
    congr 1; funext d; simp [Real.exp_sub]
  rw [h1, mgf_id_gaussianReal]
  simp only [zero_mul, zero_add]
  rw [show (v : ℝ) * x ^ 2 / 2 = x ^ 2 * v / 2 by ring, div_self (Real.exp_pos _).ne']
  simp

lemma gauss_cexp_integral (v : ℝ≥0) (x c : ℝ) :
    ∫ d, Complex.exp ((x + c * Complex.I) * d - x ^ 2 * v / 2 - Complex.I * c * x * v
      + c ^ 2 * v / 2) ∂(gaussianReal 0 v) = 1 := by
  have h1 : ∀ d : ℝ, Complex.exp ((x + c * Complex.I) * d - x ^ 2 * v / 2 - Complex.I * c * x * v
      + c ^ 2 * v / 2) = Complex.exp ((x + c * Complex.I) * d) *
        Complex.exp (- x ^ 2 * v / 2 - Complex.I * c * x * v + c ^ 2 * v / 2) := by
    intro d; rw [← Complex.exp_add]; congr 1; ring
  simp_rw [h1]
  rw [integral_mul_const]
  have h2 : ∫ d : ℝ, Complex.exp ((x + c * Complex.I) * d) ∂(gaussianReal 0 v)
      = complexMGF id (gaussianReal 0 v) (x + c * Complex.I) := rfl
  rw [h2, complexMGF_id_gaussianReal, ← Complex.exp_add]
  rw [← Complex.exp_zero]; congr 1
  push_cast; ring_nf; rw [Complex.I_sq]; ring

section Step
variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ m)
  (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)

include hW in
lemma indep_pair {E : Type*} [MeasurableSpace E] {q r : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (f : Ω → E) (hf : Measurable[ℱ q] f) (v : ℝ≥0) (hv : v = ⟨r - q, by linarith⟩) :
    P.map (fun ω => (f ω, W.W r ω - W.W q ω)) =
      (P.map f).prod (gaussianReal 0 v) := by
  have hD : Measurable (fun ω => W.W r ω - W.W q ω) := (W.measurable_eval r).sub (W.measurable_eval q)
  have hind : IndepFun f (fun ω => W.W r ω - W.W q ω) P :=
    indep_of_indep_of_le_left (hW.indep hq hqr) hf.comap_le
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hf.mono (ℱ.le q) le_rfl).aemeasurable
    hD.aemeasurable).1 hind, W.increment_gaussian hq hqr, hv]

include hW in
lemma step_lintegral {q r : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (V : Ω → ℝ≥0∞) (hV : Measurable[ℱ q] V) (ξ : Ω → ℝ) (hξ : Measurable[ℱ q] ξ) :
    ∫⁻ ω, V ω * ENNReal.ofReal (Real.exp (ξ ω * (W.W r ω - W.W q ω) - ξ ω ^ 2 * (r - q) / 2)) ∂P
      = ∫⁻ ω, V ω ∂P := by
  have hle := ℱ.le q
  have hf' : Measurable[ℱ q] (fun ω => (V ω, ξ ω)) := hV.prodMk hξ
  have hf : Measurable (fun ω => (V ω, ξ ω)) := hf'.mono hle le_rfl
  have hD : Measurable (fun ω => W.W r ω - W.W q ω) := (W.measurable_eval r).sub (W.measurable_eval q)
  set v : ℝ≥0 := ⟨r - q, by linarith⟩ with hv
  let F : (ℝ≥0∞ × ℝ) × ℝ → ℝ≥0∞ := fun p =>
    p.1.1 * ENNReal.ofReal (Real.exp (p.1.2 * p.2 - p.1.2 ^ 2 * (v : ℝ) / 2))
  have hF : Measurable F := by
    refine (measurable_fst.comp measurable_fst).mul ?_
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop))
  have e1 : ∫⁻ ω, V ω * ENNReal.ofReal (Real.exp (ξ ω * (W.W r ω - W.W q ω) - ξ ω ^ 2 * (r - q) / 2)) ∂P
      = ∫⁻ p, F p ∂(P.map (fun ω => ((V ω, ξ ω), W.W r ω - W.W q ω))) := by
    rw [lintegral_map hF (hf.prodMk hD)]; rfl
  rw [e1, indep_pair W ℱ hW hq hqr _ hf' v hv, lintegral_prod _ hF.aemeasurable]
  have inner : ∀ a : ℝ≥0∞ × ℝ, ∫⁻ d, F (a, d) ∂(gaussianReal 0 v) = a.1 := by
    intro a
    simp only [F]
    have hm : Measurable fun d : ℝ => ENNReal.ofReal (Real.exp (a.2 * d - a.2 ^ 2 * (v:ℝ) / 2)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop))
    rw [lintegral_const_mul _ hm, gauss_exp_lintegral, mul_one]
  simp_rw [inner]
  rw [lintegral_map measurable_fst hf]

include hW in
lemma step_integral {q r : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (V : Ω → ℂ) (hV : StronglyMeasurable[ℱ q] V) (hVi : Integrable V P)
    (ξ : Ω → ℝ) (hξ : Measurable[ℱ q] ξ) (c : ℝ) :
    ∫ ω, V ω * Complex.exp ((ξ ω + c * Complex.I) * (W.W r ω - W.W q ω) - ξ ω ^ 2 * (r - q) / 2
      - Complex.I * c * ξ ω * (r - q) + c ^ 2 * (r - q) / 2) ∂P = ∫ ω, V ω ∂P := by
  have hle := ℱ.le q
  have hVm' : Measurable[ℱ q] V := hV.measurable
  have hf' : Measurable[ℱ q] (fun ω => (V ω, ξ ω)) := hVm'.prodMk hξ
  have hf : Measurable (fun ω => (V ω, ξ ω)) := hf'.mono hle le_rfl
  have hD : Measurable (fun ω => W.W r ω - W.W q ω) := (W.measurable_eval r).sub (W.measurable_eval q)
  set v : ℝ≥0 := ⟨r - q, by linarith⟩ with hv
  have hvr' : (v : ℝ) = r - q := by rw [hv]; rfl
  have hvr : ((v : ℝ) : ℂ) = (r : ℂ) - q := by rw [hvr']; push_cast; ring
  let F : (ℂ × ℝ) × ℝ → ℂ := fun p =>
    p.1.1 * Complex.exp ((p.1.2 + c * Complex.I) * p.2 - p.1.2 ^ 2 * (v : ℝ) / 2
      - Complex.I * c * p.1.2 * (v : ℝ) + c ^ 2 * (v : ℝ) / 2)
  have hF : Measurable F := by
    refine (measurable_fst.comp measurable_fst).mul ?_
    exact Complex.measurable_exp.comp (by fun_prop)
  have hpm : Measurable (fun ω => ((V ω, ξ ω), W.W r ω - W.W q ω)) := hf.prodMk hD
  have e1 : ∫ ω, V ω * Complex.exp ((ξ ω + c * Complex.I) * (W.W r ω - W.W q ω) - ξ ω ^ 2 * (r - q) / 2
      - Complex.I * c * ξ ω * (r - q) + c ^ 2 * (r - q) / 2) ∂P
      = ∫ p, F p ∂(P.map (fun ω => ((V ω, ξ ω), W.W r ω - W.W q ω))) := by
    rw [integral_map hpm.aemeasurable hF.aestronglyMeasurable]
    congr 1; funext ω; simp only [F, hvr]; push_cast; ring_nf
  -- integrability of F on the product
  have hnorm : ∀ p : (ℂ × ℝ) × ℝ, ‖F p‖ = (‖p.1.1‖ * Real.exp (c ^ 2 * (r - q) / 2)) *
      Real.exp (p.1.2 * p.2 - p.1.2 ^ 2 * (r - q) / 2) := by
    intro p
    simp only [F, norm_mul, Complex.norm_exp, hvr']
    rw [mul_assoc (‖p.1.1‖), ← Real.exp_add]
    congr 2
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, sq]
    ring
  have hFint : Integrable F (P.map (fun ω => ((V ω, ξ ω), W.W r ω - W.W q ω))) := by
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm, lintegral_map (hF.norm.ennreal_ofReal) hpm]
    simp_rw [hnorm]
    have hVm2 : Measurable[ℱ q] (fun ω => ENNReal.ofReal (‖V ω‖ * Real.exp (c ^ 2 * (r - q) / 2))) :=
      ENNReal.measurable_ofReal.comp ((measurable_norm.comp hVm').mul_const _)
    have := step_lintegral W ℱ hW hq hqr _ hVm2 ξ hξ
    have e2 : ∀ ω, ENNReal.ofReal (‖V ω‖ * Real.exp (c ^ 2 * (r - q) / 2) *
        Real.exp (ξ ω * (W.W r ω - W.W q ω) - ξ ω ^ 2 * (r - q) / 2))
        = ENNReal.ofReal (‖V ω‖ * Real.exp (c ^ 2 * (r - q) / 2)) *
          ENNReal.ofReal (Real.exp (ξ ω * (W.W r ω - W.W q ω) - ξ ω ^ 2 * (r - q) / 2)) := by
      intro ω; rw [ENNReal.ofReal_mul (by positivity)]
    simp_rw [e2, this]
    exact (hVi.norm.mul_const _).lintegral_lt_top
  rw [e1]
  rw [indep_pair W ℱ hW hq hqr _ hf' v hv] at hFint ⊢
  rw [integral_prod _ hFint]
  have inner : ∀ a : ℂ × ℝ, ∫ d, F (a, d) ∂(gaussianReal 0 v) = a.1 := by
    intro a
    simp only [F]
    rw [integral_const_mul, gauss_cexp_integral, mul_one]
  simp_rw [inner]
  rw [integral_map hf.aemeasurable (by fun_prop)]

end Step

lemma bp_induction (B : Finset ℝ) (p : ℝ → Prop) (h0 : p 0)
    (hstep : ∀ q r, 0 ≤ q → q < r → (∀ b ∈ B, ¬ (q < b ∧ b < r)) → p q → p r) :
    ∀ r, 0 ≤ r → p r := by
  have hempty : ∀ r, 0 ≤ r → B.filter (fun b => 0 < b ∧ b < r) = ∅ → p r := by
    intro r hr he
    rcases hr.eq_or_lt with h | h
    · rw [← h]; exact h0
    · refine hstep 0 r le_rfl h ?_ h0
      intro b hb hb'
      have : b ∈ B.filter (fun b => 0 < b ∧ b < r) := Finset.mem_filter.2 ⟨hb, hb'⟩
      rw [he] at this; simp at this
  suffices H : ∀ n : ℕ, ∀ r, 0 ≤ r → (B.filter (fun b => 0 < b ∧ b < r)).card ≤ n → p r by
    intro r hr; exact H _ r hr le_rfl
  intro n
  induction n with
  | zero =>
    intro r hr hc
    exact hempty r hr (Finset.card_eq_zero.1 (Nat.le_zero.1 hc))
  | succ n ih =>
    intro r hr hc
    by_cases hne : (B.filter (fun b => 0 < b ∧ b < r)).Nonempty
    · set q := (B.filter (fun b => 0 < b ∧ b < r)).max' hne with hqdef
      have hqm := Finset.mem_filter.1 (Finset.max'_mem _ hne)
      rw [← hqdef] at hqm
      refine hstep q r hqm.2.1.le hqm.2.2 ?_ (ih q hqm.2.1.le ?_)
      · intro b hb hb'
        have : b ≤ q := Finset.le_max' _ b (Finset.mem_filter.2 ⟨hb, lt_trans hqm.2.1 hb'.1, hb'.2⟩)
        linarith [hb'.1]
      · have hss : B.filter (fun b => 0 < b ∧ b < q) ⊂ B.filter (fun b => 0 < b ∧ b < r) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨q, Finset.mem_filter.2 ⟨hqm.1, hqm.2⟩, fun h => ?_⟩
            exact lt_irrefl q (Finset.mem_filter.1 h).2.2
          · intro b hb
            have := Finset.mem_filter.1 hb
            exact Finset.mem_filter.2 ⟨this.1, this.2.1, lt_trans this.2.2 hqm.2.2⟩
        have := Finset.card_lt_card hss
        omega
    · exact hempty r hr (Finset.not_nonempty_iff_eq_empty.1 hne)

/-! Step functions. -/

noncomputable def stepEval {Ω : Type*} {N : ℕ} (p : Fin (N + 1) → ℝ) (ξ : Fin N → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  ∑ i : Fin N, if p i.castSucc < t ∧ t ≤ p i.succ then ξ i ω else 0

def stepInt {Ω : Type*} (w : ℝ → Ω → ℝ) {N : ℕ} (p : Fin (N + 1) → ℝ) (ξ : Fin N → Ω → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin N, ξ i ω * (w (min (p i.succ) t) ω - w (min (p i.castSucc) t) ω)

lemma stepEval_blank {Ω : Type*} {N : ℕ} (p : Fin (N + 1) → ℝ) (ξ : Fin N → Ω → ℝ) {q r : ℝ}
    (hb : ∀ j, ¬ (q < p j ∧ p j < r)) (ω : Ω) {s : ℝ} (hqs : q < s) (hsr : s ≤ r) :
    stepEval p ξ ω s = stepEval p ξ ω r := by
  unfold stepEval
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hb i.castSucc
  have h2 := hb i.succ
  have : (p i.castSucc < s ∧ s ≤ p i.succ) ↔ (p i.castSucc < r ∧ r ≤ p i.succ) := by
    constructor
    · rintro ⟨a, b⟩
      have : p i.castSucc ≤ q := by
        by_contra hc; exact h1 ⟨lt_of_not_ge hc, lt_of_lt_of_le a hsr⟩
      refine ⟨by linarith, ?_⟩
      by_contra hc; exact h2 ⟨by linarith, lt_of_not_ge hc⟩
    · rintro ⟨a, b⟩
      have : p i.castSucc ≤ q := by
        by_contra hc; exact h1 ⟨lt_of_not_ge hc, a⟩
      exact ⟨by linarith, by linarith⟩
  simp only [this]

lemma stepInt_blank {Ω : Type*} (w : ℝ → Ω → ℝ) {N : ℕ} (p : Fin (N + 1) → ℝ)
    (hp : ∀ i : Fin N, p i.castSucc ≤ p i.succ) (ξ : Fin N → Ω → ℝ) {q r : ℝ} (hqr : q < r)
    (hb : ∀ j, ¬ (q < p j ∧ p j < r)) (ω : Ω) :
    stepInt w p ξ r ω - stepInt w p ξ q ω = stepEval p ξ ω r * (w r ω - w q ω) := by
  unfold stepInt stepEval
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hb i.castSucc
  have h2 := hb i.succ
  have hpi := hp i
  by_cases ha : p i.castSucc < r
  · have hq1 : p i.castSucc ≤ q := by
      by_contra hc; exact h1 ⟨lt_of_not_ge hc, ha⟩
    by_cases hc : r ≤ p i.succ
    · rw [if_pos ⟨ha, hc⟩, min_eq_right hc, min_eq_right (by linarith : q ≤ p i.succ),
        min_eq_left ha.le, min_eq_left hq1]
      ring
    · have hq2 : p i.succ ≤ q := by
        by_contra hc'; exact h2 ⟨lt_of_not_ge hc', lt_of_not_ge hc⟩
      rw [if_neg (fun h => hc h.2), min_eq_left (by linarith : p i.succ ≤ r), min_eq_left hq2,
        min_eq_left ha.le, min_eq_left hq1]
      ring
  · push Not at ha
    rw [if_neg (fun h => not_lt.2 ha h.1), min_eq_right (by linarith : r ≤ p i.succ),
      min_eq_right (by linarith : q ≤ p i.succ), min_eq_right ha, min_eq_right (by linarith : q ≤ p i.castSucc)]
    ring

lemma stepEval_meas {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ m) {N : ℕ}
    (p : Fin (N + 1) → ℝ) (ξ : Fin N → Ω → ℝ) (hξ : ∀ i, Measurable[ℱ (p i.castSucc)] (ξ i))
    {q r : ℝ} (hb : ∀ j, ¬ (q < p j ∧ p j < r)) :
    Measurable[ℱ q] (fun ω => stepEval p ξ ω r) := by
  unfold stepEval
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases h : p i.castSucc < r ∧ r ≤ p i.succ
  · simp only [if_pos h]
    have : p i.castSucc ≤ q := by
      by_contra hc; exact hb i.castSucc ⟨lt_of_not_ge hc, h.1⟩
    exact (hξ i).mono (ℱ.mono this) le_rfl
  · simp only [if_neg h]; exact measurable_const

lemma stepEval_measurable_t {Ω : Type*} {N : ℕ} (p : Fin (N + 1) → ℝ) (ξ : Fin N → Ω → ℝ) (ω : Ω) :
    Measurable (stepEval p ξ ω) := by
  unfold stepEval
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id |>.inter
    (measurableSet_le measurable_id measurable_const)) measurable_const measurable_const

lemma stepEval_bdd {Ω : Type*} {N : ℕ} (p : Fin (N + 1) → ℝ) (ξ : Fin N → Ω → ℝ) (ω : Ω) :
    ∃ C, ∀ t, |stepEval p ξ ω t| ≤ C := by
  refine ⟨∑ i : Fin N, |ξ i ω|, fun t => ?_⟩
  unfold stepEval
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  split_ifs <;> simp


noncomputable def Mc (j a k b c : ℝ) : ℂ :=
  Complex.exp ((j : ℂ) - (a : ℂ) / 2 + Complex.I * ((k : ℂ) - (b : ℂ)) + (c : ℂ) / 2)

lemma Mc_step (j a k b c x y D δ : ℝ) :
    Mc (j + x * D) (a + δ * x ^ 2) (k + y * D) (b + δ * (y * x)) (c + δ * y ^ 2)
      = Mc j a k b c * Complex.exp ((x + y * Complex.I) * D - x ^ 2 * δ / 2
          - Complex.I * y * x * δ + y ^ 2 * δ / 2) := by
  unfold Mc; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma Mc_norm (j a k b c : ℝ) : ‖Mc j a k b c‖ = Real.exp (j - a / 2) * Real.exp (c / 2) := by
  unfold Mc
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re]

lemma Mc_zero : Mc 0 0 0 0 0 = 1 := by simp [Mc]

lemma bdd_ii (f : ℝ → ℝ) (hm : Measurable f) (C : ℝ) (hC : ∀ t, |f t| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun hm.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs]
  exact (hC t).trans (le_abs_self C)

lemma int_blank (f : ℝ → ℝ) (hf : ∀ a b, IntervalIntegrable f volume a b) {q r : ℝ} (hqr : q ≤ r)
    (hc : ∀ s, q < s → s ≤ r → f s = f r) :
    ∫ s in (0:ℝ)..r, f s = (∫ s in (0:ℝ)..q, f s) + (r - q) * f r := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf 0 q) (hf q r)]
  congr 1
  rw [intervalIntegral.integral_of_le hqr, setIntegral_congr_fun measurableSet_Ioc
    (fun s hs => hc s hs.1 hs.2), setIntegral_const]
  simp [Real.volume_Ioc, hqr]

section Abstract
variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ m)
  (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)

include hW in
lemma abstract_identity (g : Ω → ℝ → ℝ) (J K : ℝ → Ω → ℝ) (u : ℝ → ℝ) (B : Finset ℝ)
    (hJ0 : ∀ ω, J 0 ω = 0) (hK0 : ∀ ω, K 0 ω = 0)
    (hgm : ∀ ω, Measurable (g ω)) (hgb : ∀ ω, ∃ C, ∀ t, |g ω t| ≤ C)
    (hum : Measurable u) (hub : ∃ C, ∀ t, |u t| ≤ C)
    (hblank : ∀ q r, 0 ≤ q → q < r → (∀ b ∈ B, ¬ (q < b ∧ b < r)) →
      (∀ ω, J r ω - J q ω = g ω r * (W.W r ω - W.W q ω)) ∧
      (∀ ω, K r ω - K q ω = u r * (W.W r ω - W.W q ω)) ∧
      (∀ ω s, q < s → s ≤ r → g ω s = g ω r) ∧ (∀ s, q < s → s ≤ r → u s = u r) ∧
      Measurable[ℱ q] (fun ω => g ω r)) :
    ∀ r, 0 ≤ r →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (J r ω - (∫ s in (0:ℝ)..r, g ω s ^ 2) / 2)) ∂P = 1) ∧
      (∫ ω, Mc (J r ω) (∫ s in (0:ℝ)..r, g ω s ^ 2) (K r ω) (∫ s in (0:ℝ)..r, u s * g ω s)
        (∫ s in (0:ℝ)..r, u s ^ 2) ∂P = 1) := by
  obtain ⟨Cu, hCu⟩ := hub
  have hii_g2 : ∀ ω a b, IntervalIntegrable (fun s => g ω s ^ 2) volume a b := by
    intro ω a b
    obtain ⟨C, hC⟩ := hgb ω
    exact bdd_ii _ ((hgm ω).pow_const 2) (C ^ 2) (fun t => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC t) 2) a b
  have hii_ug : ∀ ω a b, IntervalIntegrable (fun s => u s * g ω s) volume a b := by
    intro ω a b
    obtain ⟨C, hC⟩ := hgb ω
    exact bdd_ii _ (hum.mul (hgm ω)) (Cu * C) (fun t => by
      show |u t * g ω t| ≤ _; rw [abs_mul]; exact mul_le_mul (hCu t) (hC t) (abs_nonneg _) ((abs_nonneg _).trans (hCu t))) a b
  have hii_u2 : ∀ a b, IntervalIntegrable (fun s => u s ^ 2) volume a b := by
    intro a b
    exact bdd_ii _ (hum.pow_const 2) (Cu ^ 2) (fun t => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCu t) 2) a b
  let p : ℝ → Prop := fun r =>
    Measurable[ℱ r] (J r) ∧ Measurable[ℱ r] (K r) ∧
    Measurable[ℱ r] (fun ω => ∫ s in (0:ℝ)..r, g ω s ^ 2) ∧
    Measurable[ℱ r] (fun ω => ∫ s in (0:ℝ)..r, u s * g ω s) ∧
    (∫⁻ ω, ENNReal.ofReal (Real.exp (J r ω - (∫ s in (0:ℝ)..r, g ω s ^ 2) / 2)) ∂P = 1) ∧
    (∫ ω, Mc (J r ω) (∫ s in (0:ℝ)..r, g ω s ^ 2) (K r ω) (∫ s in (0:ℝ)..r, u s * g ω s)
        (∫ s in (0:ℝ)..r, u s ^ 2) ∂P = 1)
  have key : ∀ r, 0 ≤ r → p r := by
    refine bp_induction B p ?_ ?_
    · have hJ : J 0 = fun _ => 0 := funext hJ0
      have hK : K 0 = fun _ => 0 := funext hK0
      refine ⟨by rw [hJ]; exact measurable_const, by rw [hK]; exact measurable_const, ?_, ?_, ?_, ?_⟩
      · simp only [intervalIntegral.integral_same]; exact measurable_const
      · simp only [intervalIntegral.integral_same]; exact measurable_const
      · simp [hJ0]
      · simp [hJ0, hK0, Mc_zero]
    · intro q r hq hqr hb hp
      obtain ⟨hJm, hKm, ham, hbm, hR, hC⟩ := hp
      obtain ⟨hJs, hKs, hgc, huc, hξm⟩ := hblank q r hq hqr hb
      have hmono : ℱ q ≤ ℱ r := ℱ.mono hqr.le
      have hWr : Measurable[ℱ r] (W.W r) := hW.measurable r
      have hWq : Measurable[ℱ r] (W.W q) := (hW.measurable q).mono hmono le_rfl
      have hJe : ∀ ω, J r ω = J q ω + g ω r * (W.W r ω - W.W q ω) := fun ω => by
        linarith [hJs ω]
      have hKe : ∀ ω, K r ω = K q ω + u r * (W.W r ω - W.W q ω) := fun ω => by
        linarith [hKs ω]
      have hae : ∀ ω, ∫ s in (0:ℝ)..r, g ω s ^ 2 = (∫ s in (0:ℝ)..q, g ω s ^ 2) + (r - q) * g ω r ^ 2 :=
        fun ω => int_blank (fun s => g ω s ^ 2) (hii_g2 ω) hqr.le (fun s h1 h2 => by rw [hgc ω s h1 h2])
      have hbe : ∀ ω, ∫ s in (0:ℝ)..r, u s * g ω s = (∫ s in (0:ℝ)..q, u s * g ω s)
          + (r - q) * (u r * g ω r) :=
        fun ω => int_blank (fun s => u s * g ω s) (hii_ug ω) hqr.le
          (fun s h1 h2 => by rw [hgc ω s h1 h2, huc s h1 h2])
      have hce : ∫ s in (0:ℝ)..r, u s ^ 2 = (∫ s in (0:ℝ)..q, u s ^ 2) + (r - q) * u r ^ 2 :=
        int_blank (fun s => u s ^ 2) hii_u2 hqr.le (fun s h1 h2 => by rw [huc s h1 h2])
      have hξr : Measurable[ℱ r] (fun ω => g ω r) := hξm.mono hmono le_rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show J r = fun ω => J q ω + g ω r * (W.W r ω - W.W q ω) from funext hJe]
        exact (hJm.mono hmono le_rfl).add (hξr.mul (hWr.sub hWq))
      · rw [show K r = fun ω => K q ω + u r * (W.W r ω - W.W q ω) from funext hKe]
        exact (hKm.mono hmono le_rfl).add ((hWr.sub hWq).const_mul _)
      · simp_rw [hae]
        exact (ham.mono hmono le_rfl).add ((hξr.pow_const 2).const_mul _)
      · simp_rw [hbe]
        exact (hbm.mono hmono le_rfl).add ((hξr.const_mul _).const_mul _)
      · have e : ∀ ω, ENNReal.ofReal (Real.exp (J r ω - (∫ s in (0:ℝ)..r, g ω s ^ 2) / 2))
            = ENNReal.ofReal (Real.exp (J q ω - (∫ s in (0:ℝ)..q, g ω s ^ 2) / 2)) *
              ENNReal.ofReal (Real.exp (g ω r * (W.W r ω - W.W q ω) - g ω r ^ 2 * (r - q) / 2)) := by
          intro ω
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hJe, hae]
          congr 2; ring
        simp_rw [e]
        have hVm : Measurable[ℱ q] (fun ω => ENNReal.ofReal (Real.exp (J q ω - (∫ s in (0:ℝ)..q, g ω s ^ 2) / 2))) :=
          ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hJm.sub (ham.div_const 2)))
        rw [step_lintegral W ℱ hW hq hqr _ hVm _ hξm, hR]
      · have e : ∀ ω, Mc (J r ω) (∫ s in (0:ℝ)..r, g ω s ^ 2) (K r ω) (∫ s in (0:ℝ)..r, u s * g ω s)
              (∫ s in (0:ℝ)..r, u s ^ 2)
            = Mc (J q ω) (∫ s in (0:ℝ)..q, g ω s ^ 2) (K q ω) (∫ s in (0:ℝ)..q, u s * g ω s)
              (∫ s in (0:ℝ)..q, u s ^ 2) *
              Complex.exp ((g ω r + u r * Complex.I) * (W.W r ω - W.W q ω) - g ω r ^ 2 * (r - q) / 2
                - Complex.I * u r * g ω r * (r - q) + u r ^ 2 * (r - q) / 2) := by
          intro ω
          rw [hJe, hae, hKe, hbe, hce, Mc_step]
          push_cast; ring_nf
        simp_rw [e]
        have hMm : Measurable[ℱ q] (fun ω => Mc (J q ω) (∫ s in (0:ℝ)..q, g ω s ^ 2) (K q ω)
            (∫ s in (0:ℝ)..q, u s * g ω s) (∫ s in (0:ℝ)..q, u s ^ 2)) := by
          unfold Mc
          refine Complex.measurable_exp.comp ?_
          refine ((((Complex.measurable_ofReal.comp hJm).sub
            ((Complex.measurable_ofReal.comp ham).div_const _)).add
            (((Complex.measurable_ofReal.comp hKm).sub (Complex.measurable_ofReal.comp hbm)).const_mul _)).add
            measurable_const)
        have hMi : Integrable (fun ω => Mc (J q ω) (∫ s in (0:ℝ)..q, g ω s ^ 2) (K q ω)
            (∫ s in (0:ℝ)..q, u s * g ω s) (∫ s in (0:ℝ)..q, u s ^ 2)) P := by
          refine ⟨(hMm.mono (ℱ.le q) le_rfl).aestronglyMeasurable, ?_⟩
          rw [hasFiniteIntegral_iff_norm]
          simp_rw [Mc_norm]
          have e2 : ∀ ω, ENNReal.ofReal (Real.exp (J q ω - (∫ s in (0:ℝ)..q, g ω s ^ 2) / 2) *
              Real.exp ((∫ s in (0:ℝ)..q, u s ^ 2) / 2)) =
              ENNReal.ofReal (Real.exp ((∫ s in (0:ℝ)..q, u s ^ 2) / 2)) *
              ENNReal.ofReal (Real.exp (J q ω - (∫ s in (0:ℝ)..q, g ω s ^ 2) / 2)) := by
            intro ω; rw [mul_comm, ENNReal.ofReal_mul (Real.exp_pos _).le]
          simp_rw [e2]
          have hVm : Measurable (fun ω => ENNReal.ofReal (Real.exp (J q ω - (∫ s in (0:ℝ)..q, g ω s ^ 2) / 2))) :=
            ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hJm.sub (ham.div_const 2)).mono (ℱ.le q) le_rfl))
          rw [lintegral_const_mul _ hVm, hR]
          simp
        rw [step_integral W ℱ hW hq hqr _ hMm.stronglyMeasurable hMi _ hξm (u r), hC]
  intro r hr
  exact ⟨(key r hr).2.2.2.2.1, (key r hr).2.2.2.2.2⟩

end Abstract

lemma step_mul_integral {N : ℕ} (p : Fin (N + 1) → ℝ) (hp : ∀ i : Fin N, p i.castSucc ≤ p i.succ)
    (h0 : ∀ j, 0 ≤ p j) (R : ℝ) (hR : ∀ j, p j ≤ R) (c : Fin N → ℝ) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 R) :
    ∫ t in (0:ℝ)..R, (∑ i : Fin N, if p i.castSucc < t ∧ t ≤ p i.succ then c i else 0) * f t
      = ∑ i : Fin N, c i * ∫ t in (p i.castSucc)..(p i.succ), f t := by
  have hR0 : 0 ≤ R := (h0 0).trans (hR 0)
  have hfo : IntegrableOn f (Set.Ioc 0 R) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hR0).1 hf
  have hterm : ∀ i : Fin N, (fun t => (if p i.castSucc < t ∧ t ≤ p i.succ then c i else 0) * f t)
      = (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun t => c i * f t) := by
    intro i; funext t
    by_cases h : p i.castSucc < t ∧ t ≤ p i.succ
    · rw [if_pos h, Set.indicator_of_mem (show t ∈ Set.Ioc _ _ from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show t ∉ Set.Ioc _ _ from h), zero_mul]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hterm i, intervalIntegral.integral_of_le hR0, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.2 (Set.Ioc_subset_Ioc (h0 _) (hR _)), intervalIntegral.integral_of_le (hp i),
      integral_const_mul]
  · intro i _
    rw [hterm i, intervalIntegrable_iff_integrableOn_Ioc_of_le hR0]
    exact (hfo.const_mul (c i)).indicator measurableSet_Ioc

lemma step_eval_on {m : ℕ} (s : Fin (m + 1) → ℝ) (hs : Monotone s) (a : Fin m → ℝ) (i : Fin m) {t : ℝ}
    (ht : s i.castSucc < t ∧ t ≤ s i.succ) :
    (∑ j : Fin m, if s j.castSucc < t ∧ t ≤ s j.succ then a j else 0) = a i := by
  rw [Finset.sum_eq_single i]
  · rw [if_pos ht]
  · intro j _ hji
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have : s j.succ ≤ s i.castSucc := hs (by rw [Fin.le_def]; simp; omega)
      linarith [ht.1]
    · have : s i.succ ≤ s j.castSucc := hs (by rw [Fin.le_def]; simp; omega)
      linarith [ht.2]
  · simp

lemma step_sq_integral {m : ℕ} (s : Fin (m + 1) → ℝ) (hs : Monotone s) (h0 : ∀ j, 0 ≤ s j)
    (a : Fin m → ℝ) (R : ℝ) (hR : ∀ j, s j ≤ R) :
    ∫ t in (0:ℝ)..R, (∑ j : Fin m, if s j.castSucc < t ∧ t ≤ s j.succ then a j else 0) ^ 2
      = ∑ j : Fin m, a j ^ 2 * (s j.succ - s j.castSucc) := by
  set u : ℝ → ℝ := fun t => ∑ j : Fin m, if s j.castSucc < t ∧ t ≤ s j.succ then a j else 0 with hu
  have hum : Measurable u := stepEval_measurable_t (Ω := Unit) s (fun j _ => a j) ()
  obtain ⟨C, hC⟩ := stepEval_bdd (Ω := Unit) s (fun j _ => a j) ()
  have hmono : ∀ i : Fin m, s i.castSucc ≤ s i.succ := fun i => hs (Fin.castSucc_le_succ i)
  have e : ∀ t, u t ^ 2 = u t * u t := fun t => sq _
  simp_rw [show (fun t => (∑ j : Fin m, if s j.castSucc < t ∧ t ≤ s j.succ then a j else 0) ^ 2)
    = fun t => u t * u t from funext e]
  rw [step_mul_integral s hmono h0 R hR a u (bdd_ii u hum C hC 0 R)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_of_le (hmono i), setIntegral_congr_fun measurableSet_Ioc
    (fun t ht => step_eval_on s hs a i ht), setIntegral_const]
  simp [Real.volume_Ioc, hmono i, sq]
  ring

open LevyStochCalc.Brownian.Ito in
lemma concrete_identity {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ m)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {T' : ℝ} (G : SimplePredictable Ω T')
    (hGa : ∀ i : Fin G.N, StronglyMeasurable[ℱ (G.partition i.castSucc)] (G.ξ i))
    {M : ℕ} (s : Fin (M + 1) → ℝ) (hs : Monotone s) (hs0 : ∀ j, 0 ≤ s j) (a : Fin M → ℝ)
    (R : ℝ) (hsR : ∀ j, s j ≤ R) (hR : 0 ≤ R) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (simpleIntegral W G R ω
        - (∫ t in (0:ℝ)..R, G.eval t ω ^ 2) / 2)) ∂P = 1) ∧
    (∫ ω, Mc (simpleIntegral W G R ω) (∫ t in (0:ℝ)..R, G.eval t ω ^ 2)
        (∑ j : Fin M, a j * (W.W (s j.succ) ω - W.W (s j.castSucc) ω))
        (∑ j : Fin M, a j * ∫ t in (s j.castSucc)..(s j.succ), G.eval t ω)
        (∑ j : Fin M, a j ^ 2 * (s j.succ - s j.castSucc)) ∂P = 1) := by
  set u : ℝ → ℝ := fun t => ∑ j : Fin M, if s j.castSucc < t ∧ t ≤ s j.succ then a j else 0 with hu
  have hum : Measurable u := stepEval_measurable_t (Ω := Unit) s (fun j _ => a j) ()
  have hub : ∃ C, ∀ t, |u t| ≤ C := stepEval_bdd (Ω := Unit) s (fun j _ => a j) ()
  have hGmono : ∀ i : Fin G.N, G.partition i.castSucc ≤ G.partition i.succ :=
    fun i => G.partition_strictMono.monotone (Fin.castSucc_le_succ i)
  have hsmono : ∀ i : Fin M, s i.castSucc ≤ s i.succ := fun i => hs (Fin.castSucc_le_succ i)
  set B : Finset ℝ := Finset.univ.image G.partition ∪ Finset.univ.image s with hB
  have hA := abstract_identity W ℱ hW (fun ω t => G.eval t ω) (fun r ω => simpleIntegral W G r ω)
    (fun r ω => stepInt W.W s (fun j _ => a j) r ω) u B
    (fun ω => simpleIntegral_eq_zero_of_nonpos W G le_rfl ω)
    (fun ω => by simp [stepInt, min_eq_right (hs0 _)])
    (fun ω => stepEval_measurable_t G.partition G.ξ ω) (fun ω => stepEval_bdd G.partition G.ξ ω)
    hum hub (by
      intro q r hq hqr hb
      have hbG : ∀ j, ¬ (q < G.partition j ∧ G.partition j < r) := fun j =>
        hb _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
      have hbs : ∀ j, ¬ (q < s j ∧ s j < r) := fun j =>
        hb _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
      exact ⟨fun ω => stepInt_blank W.W G.partition hGmono G.ξ hqr hbG ω,
        fun ω => stepInt_blank W.W s hsmono (fun j _ => a j) hqr hbs ω,
        fun ω s' h1 h2 => stepEval_blank G.partition G.ξ hbG ω h1 h2,
        fun s' h1 h2 => stepEval_blank (Ω := Unit) s (fun j _ => a j) hbs () h1 h2,
        stepEval_meas ℱ G.partition G.ξ (fun i => (hGa i).measurable) hbG⟩) R hR
  obtain ⟨h1, h2⟩ := hA
  refine ⟨h1, ?_⟩
  rw [← h2]
  congr 1; funext ω
  have eK : stepInt W.W s (fun j _ => a j) R ω
      = ∑ j : Fin M, a j * (W.W (s j.succ) ω - W.W (s j.castSucc) ω) := by
    simp only [stepInt, min_eq_left (hsR _)]
  have hgii : IntervalIntegrable (fun t => G.eval t ω) volume 0 R := by
    obtain ⟨C, hC⟩ := stepEval_bdd G.partition G.ξ ω
    exact bdd_ii _ (stepEval_measurable_t G.partition G.ξ ω) C hC 0 R
  have eB : ∫ t in (0:ℝ)..R, u t * G.eval t ω
      = ∑ j : Fin M, a j * ∫ t in (s j.castSucc)..(s j.succ), G.eval t ω :=
    step_mul_integral s hsmono hs0 R hsR a _ hgii
  have eC : ∫ t in (0:ℝ)..R, u t ^ 2 = ∑ j : Fin M, a j ^ 2 * (s j.succ - s j.castSucc) :=
    step_sq_integral s hs hs0 a R hsR
  rw [eK, eB, eC]

/-! Limit lemmas. -/

lemma ae_subseq_of_lintegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : ℕ → Ω → ℝ≥0∞) (hH : ∀ n, AEMeasurable (H n) P)
    (h : Tendsto (fun n => ∫⁻ ω, H n ω ∂P) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P, Tendsto (fun k => H (ns k) ω) atTop (𝓝 0) := by
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop, ∫⁻ ω, H n ω ∂P ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    exact (ENNReal.tendsto_nhds_zero.1 h) _ (ENNReal.pow_pos (by norm_num : (0:ℝ≥0∞) < 2⁻¹) k)
  obtain ⟨ns, hmono, hns⟩ := extraction_forall_of_eventually hev
  refine ⟨ns, hmono, ?_⟩
  have hsum : ∫⁻ ω, ∑' k, H (ns k) ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum (fun k => hH _)]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hns)
    rw [ENNReal.tsum_geometric]
    simp
  have hae := ae_lt_top' (AEMeasurable.tsum (fun k => hH (ns k))) hsum
  filter_upwards [hae] with ω hω
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne

lemma memLp2_of_lint {α : Type*} [MeasurableSpace α] {μ : Measure α} (k : α → ℝ) (hk : Measurable k)
    (h : ∫⁻ t, (‖k t‖₊ : ℝ≥0∞) ^ 2 ∂μ < ⊤) : MemLp k 2 μ := by
  refine ⟨hk.aestronglyMeasurable, ?_⟩
  rw [← ENNReal.rpow_lt_top_iff_of_pos (show (0:ℝ) < 2 by norm_num),
    LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq]
  exact h

lemma nnsq_eq (x : ℝ) : (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (by positivity)]
  congr 1; simp [sq_abs]

lemma integral_sq_eq_lint {α : Type*} [MeasurableSpace α] {μ : Measure α} (k : α → ℝ)
    (hk : AEStronglyMeasurable k μ) :
    ∫ t, k t ^ 2 ∂μ = (∫⁻ t, (‖k t‖₊ : ℝ≥0∞) ^ 2 ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => sq_nonneg _)
    (hk.pow 2)]
  simp_rw [nnsq_eq]

lemma cs_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α} (d : ℕ → α → ℝ) (k : α → ℝ)
    (hd : ∀ n, MemLp (d n) 2 μ) (hk : MemLp k 2 μ)
    (h : Tendsto (fun n => ∫ t, d n t ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, d n t * k t ∂μ) atTop (𝓝 0) := by
  have hb : ∀ n, |∫ t, d n t * k t ∂μ| ≤ (∫ t, d n t ^ 2 ∂μ) ^ (1 / (2:ℝ)) *
      (∫ t, k t ^ 2 ∂μ) ^ (1 / (2:ℝ)) := by
    intro n
    have hpq : (2:ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
    have h1 := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (f := fun t => |d n t|) (g := fun t => |k t|)
      (Eventually.of_forall fun t => abs_nonneg _) (Eventually.of_forall fun t => abs_nonneg _)
      (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact (hd n).abs)
      (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact hk.abs)
    simp only [Real.rpow_two, sq_abs] at h1
    refine le_trans ?_ h1
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    congr 1; funext t; rw [abs_mul]
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun n => abs_nonneg _) hb ?_
  have : Tendsto (fun n => (∫ t, d n t ^ 2 ∂μ) ^ (1 / (2:ℝ))) atTop (𝓝 0) := by
    have := ((Real.continuous_rpow_const (show (0:ℝ) ≤ 1 / 2 by norm_num)).tendsto 0).comp h
    rw [Real.zero_rpow (by norm_num)] at this
    exact this
  simpa using this.mul_const ((∫ t, k t ^ 2 ∂μ) ^ (1 / (2:ℝ)))

lemma det_l2 (h : ℝ → ℝ) (f : ℕ → ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R) (hhm : Measurable h)
    (hfm : ∀ n, Measurable (f n))
    (hh : ∫⁻ t in Set.Icc (0:ℝ) R, (‖h t‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hf : ∀ n, ∫⁻ t in Set.Icc (0:ℝ) R, (‖f n t‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hc : Tendsto (fun n => ∫⁻ t in Set.Icc (0:ℝ) R, (‖h t - f n t‖₊ : ℝ≥0∞) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t in (0:ℝ)..R, f n t ^ 2) atTop (𝓝 (∫ t in (0:ℝ)..R, h t ^ 2)) ∧
    ∀ a b, 0 ≤ a → a ≤ b → b ≤ R →
      Tendsto (fun n => ∫ t in a..b, f n t) atTop (𝓝 (∫ t in a..b, h t)) := by
  set ν := volume.restrict (Set.Icc (0:ℝ) R) with hν
  have hhL : MemLp h 2 ν := memLp2_of_lint h hhm hh
  have hfL : ∀ n, MemLp (f n) 2 ν := fun n => memLp2_of_lint (f n) (hfm n) (hf n)
  set d : ℕ → ℝ → ℝ := fun n t => f n t - h t with hd
  have hdL : ∀ n, MemLp (d n) 2 ν := fun n => (hfL n).sub hhL
  have hd2 : Tendsto (fun n => ∫ t, d n t ^ 2 ∂ν) atTop (𝓝 0) := by
    have e : ∀ n, ∫ t, d n t ^ 2 ∂ν = (∫⁻ t in Set.Icc (0:ℝ) R, (‖h t - f n t‖₊ : ℝ≥0∞) ^ 2).toReal := by
      intro n
      rw [integral_sq_eq_lint _ (hdL n).1]
      congr 2; funext t; rw [← nnnorm_neg, neg_sub]
    simp_rw [e]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc
    simp only [ENNReal.toReal_zero] at this
    exact this
  have hii : ∀ k : ℝ → ℝ, Integrable k ν → ∫ t in (0:ℝ)..R, k t = ∫ t, k t ∂ν := by
    intro k _
    rw [intervalIntegral.integral_of_le hR, integral_Icc_eq_integral_Ioc]
  refine ⟨?_, ?_⟩
  · have e : ∀ n, ∫ t in (0:ℝ)..R, f n t ^ 2 = ∫ t, d n t ^ 2 ∂ν + 2 * ∫ t, d n t * h t ∂ν
        + ∫ t, h t ^ 2 ∂ν := by
      intro n
      have i1 : Integrable (fun t => d n t ^ 2) ν := (hdL n).integrable_sq
      have i2 : Integrable (fun t => 2 * (d n t * h t)) ν := ((hdL n).integrable_mul hhL).const_mul 2
      have i3 : Integrable (fun t => h t ^ 2) ν := hhL.integrable_sq
      have i12 : Integrable (fun t => d n t ^ 2 + 2 * (d n t * h t)) ν := i1.add i2
      rw [hii _ (hfL n).integrable_sq, ← integral_const_mul, ← integral_add i1 i2, ← integral_add i12 i3]
      congr 1; funext t; simp only [hd]; ring
    simp_rw [e]
    rw [hii _ hhL.integrable_sq]
    have h1 := cs_tendsto d h hdL hhL hd2
    have := (hd2.add (h1.const_mul 2)).add_const (∫ t, h t ^ 2 ∂ν)
    simpa using this
  · intro a b ha hab hb
    set k : ℝ → ℝ := (Set.Ioc a b).indicator (fun _ => (1:ℝ)) with hk
    have hkm : Measurable k := measurable_const.indicator measurableSet_Ioc
    have hkL : MemLp k 2 ν := by
      refine MemLp.of_bound hkm.aestronglyMeasurable 1 (Eventually.of_forall fun t => ?_)
      simp only [hk]
      by_cases ht : t ∈ Set.Ioc a b
      · simp [Set.indicator_of_mem ht]
      · simp [Set.indicator_of_notMem ht]
    have hint : ∀ g : ℝ → ℝ, MemLp g 2 ν → ∫ t in a..b, g t = ∫ t, k t * g t ∂ν := by
      intro g hg
      have e1 : (fun t => k t * g t) = (Set.Ioc a b).indicator g := by
        funext t
        by_cases ht : t ∈ Set.Ioc a b
        · simp [hk, Set.indicator_of_mem ht]
        · simp [hk, Set.indicator_of_notMem ht]
      rw [e1, hν, setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.2 (show Set.Ioc a b ⊆ Set.Icc 0 R from
          fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩),
        intervalIntegral.integral_of_le hab]
    have e : ∀ n, ∫ t in a..b, f n t = ∫ t, d n t * k t ∂ν + ∫ t, k t * h t ∂ν := by
      intro n
      have i1 : Integrable (fun t => d n t * k t) ν := (hdL n).integrable_mul hkL
      have i2 : Integrable (fun t => k t * h t) ν := hkL.integrable_mul hhL
      rw [hint _ (hfL n), ← integral_add i1 i2]
      congr 1; funext t; simp only [hd]; ring
    simp_rw [e]
    rw [hint _ hhL]
    simpa using (cs_tendsto d k hdL hkL hd2).add_const (∫ t, k t * h t ∂ν)

lemma norm_cexp_I (x : ℝ) : ‖Complex.exp (Complex.I * x)‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

lemma scheffe_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Zn : ℕ → Ω → ℝ) (Z : Ω → ℝ) (Φn : ℕ → Ω → ℝ) (Φ : Ω → ℝ)
    (hZn0 : ∀ n ω, 0 ≤ Zn n ω) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZni : ∀ n, Integrable (Zn n) P) (hZi : Integrable Z P)
    (hint : ∀ n, ∫ ω, Zn n ω ∂P = ∫ ω, Z ω ∂P)
    (hΦnm : ∀ n, AEStronglyMeasurable (Φn n) P) (hΦm : AEStronglyMeasurable Φ P)
    (hcZ : ∀ᵐ ω ∂P, Tendsto (fun n => Zn n ω) atTop (𝓝 (Z ω)))
    (hcΦ : ∀ᵐ ω ∂P, Tendsto (fun n => Φn n ω) atTop (𝓝 (Φ ω))) :
    Tendsto (fun n => ∫ ω, (Zn n ω : ℂ) * Complex.exp (Complex.I * Φn n ω) ∂P) atTop
      (𝓝 (∫ ω, (Z ω : ℂ) * Complex.exp (Complex.I * Φ ω) ∂P)) := by
  -- L¹ convergence (Scheffé)
  have hL1 : Tendsto (fun n => ∫ ω, |Zn n ω - Z ω| ∂P) atTop (𝓝 0) := by
    have e : ∀ n, ∫ ω, |Zn n ω - Z ω| ∂P = 2 * ∫ ω, max (Z ω - Zn n ω) 0 ∂P := by
      intro n
      have h1 : ∀ ω, |Zn n ω - Z ω| = (Zn n ω - Z ω) + 2 * max (Z ω - Zn n ω) 0 := by
        intro ω
        rcases le_total (Zn n ω) (Z ω) with h | h
        · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
        · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]; ring
      have hm : Integrable (fun ω => max (Z ω - Zn n ω) 0) P := (hZi.sub (hZni n)).sup (integrable_zero _ _ _)
      simp_rw [h1]
      have i1 : Integrable (fun ω => Zn n ω - Z ω) P := (hZni n).sub hZi
      have i2 : Integrable (fun ω => 2 * max (Z ω - Zn n ω) 0) P := hm.const_mul 2
      rw [integral_add i1 i2, integral_sub (hZni n) hZi, hint n, integral_const_mul]
      ring
    simp_rw [e]
    have : Tendsto (fun n => ∫ ω, max (Z ω - Zn n ω) 0 ∂P) atTop (𝓝 (∫ ω, (0:ℝ) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence Z (fun n => ?_) hZi (fun n => ?_) ?_
      · exact ((hZi.sub (hZni n)).sup (integrable_zero _ _ _)).aestronglyMeasurable
      · refine Eventually.of_forall fun ω => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [hZn0 n ω]) (hZ0 ω)
      · filter_upwards [hcZ] with ω hω
        have := ((tendsto_const_nhds (x := Z ω)).sub hω).max (tendsto_const_nhds (x := (0:ℝ)))
        simpa using this
    simpa using this.const_mul 2
  -- convergence with Z fixed
  have hZe : Tendsto (fun n => ∫ ω, (Z ω : ℂ) * Complex.exp (Complex.I * Φn n ω) ∂P) atTop
      (𝓝 (∫ ω, (Z ω : ℂ) * Complex.exp (Complex.I * Φ ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence Z (fun n => ?_) hZi (fun n => ?_) ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hZi.1).mul
        (Complex.continuous_exp.comp_aestronglyMeasurable
          (continuous_const.mul Complex.continuous_ofReal |>.comp_aestronglyMeasurable (hΦnm n)))
    · refine Eventually.of_forall fun ω => ?_
      rw [norm_mul, norm_cexp_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)]
    · filter_upwards [hcΦ] with ω hω
      refine tendsto_const_nhds.mul ?_
      exact (Complex.continuous_exp.tendsto _).comp
        ((tendsto_const_nhds.mul (Complex.continuous_ofReal.tendsto _ |>.comp hω)))
  have hdiff : Tendsto (fun n => ∫ ω, (Zn n ω : ℂ) * Complex.exp (Complex.I * Φn n ω) ∂P
      - ∫ ω, (Z ω : ℂ) * Complex.exp (Complex.I * Φn n ω) ∂P) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hL1
    have hi1 : ∀ g : Ω → ℝ, Integrable g P → Integrable (fun ω => (g ω : ℂ) *
        Complex.exp (Complex.I * Φn n ω)) P := by
      intro g hg
      refine Integrable.mono (Integrable.ofReal (𝕜 := ℂ) hg) ?_ (Eventually.of_forall fun ω => ?_)
      · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.1).mul
          (Complex.continuous_exp.comp_aestronglyMeasurable
            (continuous_const.mul Complex.continuous_ofReal |>.comp_aestronglyMeasurable (hΦnm n)))
      · rw [norm_mul, norm_cexp_I, mul_one]; exact le_rfl
    rw [← integral_sub (hi1 _ (hZni n)) (hi1 _ hZi)]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun ω => ?_)))
    simp only
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, norm_cexp_I, mul_one,
      Real.norm_eq_abs]
  have := hdiff.add hZe
  simpa using this


open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito in
theorem em_ito_increment
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (h_sq : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq t ω
        - stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq s ω) ^ 2 ∂P
      = (∫⁻ ω, ∫⁻ u in Set.Ioc s t, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
  set I := stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq with hI
  have hmt := stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq t
  have hms := stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq s
  have hmart := martingale_stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq
  have hsm : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ s) (I s) :=
    stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas h_sq s
  have hprod : Integrable (I s * I t) P :=
    (hms.integrable_sq.add hmt.integrable_sq).mono' (hms.1.mul hmt.1)
      (Filter.Eventually.of_forall (fun ω => by
        simp only [Pi.mul_apply, Pi.add_apply, Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|I s ω| - |I t ω|), sq_abs (I s ω), sq_abs (I t ω),
          abs_nonneg (I s ω), abs_nonneg (I t ω)]))
  have hcross : ∫ ω, I s ω * I t ω ∂P = ∫ ω, I s ω ^ 2 ∂P := by
    have h1 := condExp_mul_of_stronglyMeasurable_left hsm hprod (hmt.integrable one_le_two)
    have h2 := hmart.condExp_ae_eq hst
    calc ∫ ω, I s ω * I t ω ∂P = ∫ ω, (I s * I t) ω ∂P := rfl
      _ = ∫ ω, (P[I s * I t | ℱ s]) ω ∂P := (integral_condExp (ℱ.le s)).symm
      _ = ∫ ω, I s ω ^ 2 ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [h1, h2] with ω h1 h2
        rw [h1, Pi.mul_apply, h2, sq]
  have hsqI : ∀ r, 0 ≤ r → ∫ ω, I r ω ^ 2 ∂P
      = (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    intro r hr
    have hmr := stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq r
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
      hmr.integrable_sq.aestronglyMeasurable]
    simp_rw [← nnsq_eq]
    rw [stochasticIntegralBrownian_lintegral_sq W ℱ hℱ H h_meas h_progMeas h_sq hr]
  have hexp : (fun ω => (I t ω - I s ω) ^ 2)
      = fun ω => (I t ω ^ 2 + I s ω ^ 2) - 2 * (I s ω * I t ω) := funext (fun ω => by ring)
  have hi1 : Integrable (fun ω => I t ω ^ 2 + I s ω ^ 2) P := hmt.integrable_sq.add hms.integrable_sq
  have hi2 : Integrable (fun ω => 2 * (I s ω * I t ω)) P := hprod.const_mul 2
  rw [hexp, integral_sub hi1 hi2,
    integral_add hmt.integrable_sq hms.integrable_sq, integral_const_mul, hcross,
    hsqI t (hs.trans hst), hsqI s hs, horizon_lintegral_add H h_meas hs hst]
  have hA : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := by
    rw [← stochasticIntegralBrownian_lintegral_sq W ℱ hℱ H h_meas h_progMeas h_sq hs]
    simp_rw [nnsq_eq]
    exact hms.integrable_sq.lintegral_lt_top.ne
  have hB : ∫⁻ ω, ∫⁻ u in Set.Ioc s t, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := by
    have h := horizon_lintegral_add (P := P) H h_meas hs hst
    rw [← stochasticIntegralBrownian_lintegral_sq W ℱ hℱ H h_meas h_progMeas h_sq (hs.trans hst)]
      at h
    have hfin : ∫⁻ ω, (‖I t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := by
      simp_rw [nnsq_eq]; exact hmt.integrable_sq.lintegral_lt_top.ne
    rw [h] at hfin
    exact (ENNReal.add_ne_top.mp hfin).2
  rw [ENNReal.toReal_add hA hB]
  ring

lemma Mc_split (j a k b c : ℝ) : Mc j a k b c =
    ((Real.exp (j - a / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * ((k - b : ℝ) : ℂ)) *
      Complex.exp ((c : ℂ) / 2) := by
  unfold Mc
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma stepEval_joint {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (p : Fin (N + 1) → ℝ)
    (ξ : Fin N → Ω → ℝ) (hξ : ∀ i, Measurable (ξ i)) :
    Measurable (fun q : Ω × ℝ => stepEval p ξ q.1 q.2) := by
  unfold stepEval
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite ?_ ((hξ i).comp measurable_fst) measurable_const
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_const)

lemma meas_iint {Ω : Type*} [MeasurableSpace Ω] (F : Ω → ℝ → ℝ) (hF : Measurable (Function.uncurry F))
    {a b : ℝ} (hab : a ≤ b) : Measurable (fun ω => ∫ t in a..b, F ω t) := by
  have : (fun ω => ∫ t in a..b, F ω t) = fun ω => ∫ t, Function.uncurry F (ω, t) ∂(volume.restrict (Set.Ioc a b)) := by
    funext ω; rw [intervalIntegral.integral_of_le hab]; rfl
  rw [this]
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc a b))).measurable

lemma tendsto_of_nnsq (x : ℕ → ℝ) (y : ℝ)
    (h : Tendsto (fun k => (‖x k - y‖₊ : ℝ≥0∞) ^ 2) atTop (𝓝 0)) : Tendsto x atTop (𝓝 y) := by
  simp_rw [nnsq_eq] at h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_zero] at h2
  have h3 := ((Real.continuous_sqrt.tendsto 0).comp h2)
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h3
  have h4 : Tendsto (fun k => x k - y) atTop (𝓝 0) := (tendsto_zero_iff_abs_tendsto_zero _).2 h3
  simpa using h4.add_const y

lemma bdd_lint_lt_top (f : ℝ → ℝ) (C : ℝ) (hC : ∀ t, |f t| ≤ C) (R : ℝ) :
    ∫⁻ t in Set.Icc (0:ℝ) R, (‖f t‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono (g := fun _ => ENNReal.ofReal (C ^ 2)) fun t => ?_) ?_
  · rw [nnsq_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hC t
    nlinarith [abs_nonneg (f t), sq_abs (f t)]
  · simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito in
lemma key_P {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T : ℝ) (hT : 0 < T)
    (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ θ)
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0)
    (Z : Ω → ℝ)
    (hZ : ∀ ω : Ω,
      Z ω = Real.exp (
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW θ hθmeas hθprog hθq T ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..T, θ ω s ^ 2))
    (hZmean : ∫ ω, Z ω ∂P = 1)
    {M : ℕ} (s : Fin (M + 1) → ℝ) (hs : Monotone s) (hs0 : ∀ j, 0 ≤ s j) (a : Fin M → ℝ) :
    ∫ ω, (Z ω : ℂ) * Complex.exp (Complex.I * ((∑ j : Fin M, a j *
      ((W.W (s j.succ) ω - ∫ t in (0:ℝ)..(s j.succ), θ ω t) -
       (W.W (s j.castSucc) ω - ∫ t in (0:ℝ)..(s j.castSucc), θ ω t)) : ℝ) : ℂ)) ∂P
      = Complex.exp (-((∑ j : Fin M, a j ^ 2 * (s j.succ - s j.castSucc) : ℝ) : ℂ) / 2) := by
  set R := max T (s (Fin.last M)) with hRdef
  have hTR : T ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := hT.le.trans hTR
  have hRpos : 0 < R := lt_of_lt_of_le hT hTR
  have hsR : ∀ j, s j ≤ R := fun j => (hs (Fin.le_last j)).trans (le_max_right _ _)
  set G := fun n => masterApprox ℱ θ hθmeas hθprog hθq n with hG
  set I := stochasticIntegralBrownian W ℱ hW θ hθmeas hθprog hθq with hI
  set cS : ℝ := ∑ j : Fin M, a j ^ 2 * (s j.succ - s j.castSucc) with hcS
  set Zn : ℕ → Ω → ℝ := fun n ω => Real.exp (simpleIntegral W (G n) R ω
    - (∫ t in (0:ℝ)..R, (G n).eval t ω ^ 2) / 2) with hZn
  set Φn : ℕ → Ω → ℝ := fun n ω => (∑ j : Fin M, a j * (W.W (s j.succ) ω - W.W (s j.castSucc) ω))
    - ∑ j : Fin M, a j * ∫ t in (s j.castSucc)..(s j.succ), (G n).eval t ω with hΦn
  set Φ : Ω → ℝ := fun ω => ∑ j : Fin M, a j * ((W.W (s j.succ) ω - ∫ t in (0:ℝ)..(s j.succ), θ ω t)
    - (W.W (s j.castSucc) ω - ∫ t in (0:ℝ)..(s j.castSucc), θ ω t)) with hΦ
  have hCI := fun n => concrete_identity W ℱ hW (G n) (masterApprox_adapt ℱ θ hθmeas hθprog hθq n)
    s hs hs0 a R hsR hR0
  have hGj : ∀ n, Measurable (fun q : Ω × ℝ => (G n).eval q.2 q.1) :=
    fun n => stepEval_joint _ _ (G n).ξ_measurable
  have hJm : ∀ n, Measurable (fun ω => simpleIntegral W (G n) R ω) := by
    intro n; unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((G n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hAm : ∀ n, Measurable (fun ω => ∫ t in (0:ℝ)..R, (G n).eval t ω ^ 2) := fun n =>
    meas_iint (fun ω t => (G n).eval t ω ^ 2) ((hGj n).pow_const 2) hR0
  have hZnm : ∀ n, Measurable (Zn n) := fun n =>
    Real.measurable_exp.comp ((hJm n).sub ((hAm n).div_const 2))
  have hZn0 : ∀ n ω, 0 ≤ Zn n ω := fun n ω => (Real.exp_pos _).le
  have hZnl : ∀ n, ∫⁻ ω, ENNReal.ofReal (Zn n ω) ∂P = 1 := fun n => (hCI n).1
  have hZni : ∀ n, Integrable (Zn n) P := by
    intro n
    refine ⟨(hZnm n).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hZn0 n)), hZnl n]
    exact ENNReal.one_lt_top
  have hZnint : ∀ n, ∫ ω, Zn n ω ∂P = ∫ ω, Z ω ∂P := by
    intro n
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (hZn0 n))
      (hZnm n).aestronglyMeasurable, hZnl n, hZmean]; simp
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by rw [hZ ω]; exact (Real.exp_pos _).le
  have hZi : Integrable Z P := by
    by_contra h; rw [integral_undef h] at hZmean; exact zero_ne_one hZmean
  have hΦnm : ∀ n, Measurable (Φn n) := by
    intro n
    exact (Finset.measurable_sum _ fun j _ =>
      ((W.measurable_eval _).sub (W.measurable_eval _)).const_mul _).sub
      (Finset.measurable_sum _ fun j _ => (meas_iint (fun ω t => (G n).eval t ω) (hGj n)
        (hs (Fin.castSucc_le_succ j))).const_mul _)
  have hΦm : Measurable Φ := by
    refine Finset.measurable_sum _ fun j _ => ?_
    exact (((W.measurable_eval _).sub (meas_iint θ hθmeas (hs0 _))).sub
      ((W.measurable_eval _).sub (meas_iint θ hθmeas (hs0 _)))).const_mul _
  have hEq : ∀ n, ∫ ω, (Zn n ω : ℂ) * Complex.exp (Complex.I * (Φn n ω : ℂ)) ∂P
      = Complex.exp (-(cS : ℂ) / 2) := by
    intro n
    have h2 := (hCI n).2
    simp_rw [Mc_split] at h2
    rw [integral_mul_const] at h2
    have h3 : (∫ ω, (Zn n ω : ℂ) * Complex.exp (Complex.I * (Φn n ω : ℂ)) ∂P)
        * Complex.exp ((cS : ℂ) / 2) = 1 := h2
    rw [eq_inv_of_mul_eq_one_left h3, ← Complex.exp_neg]
    congr 1; ring
  -- I_R = I_T a.e.
  have hIRT : I R =ᵐ[P] I T := by
    have hinc := em_ito_increment W ℱ hW θ hθmeas hθprog hθq hT.le hTR
    have hzero : ∫⁻ ω, ∫⁻ u in Set.Ioc T R, (‖θ ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
      have : ∀ ω, ∫⁻ u in Set.Ioc T R, (‖θ ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume = 0 := fun ω => by
        rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0)
          (fun u hu => by simp [hθzero ω u hu.1.le])]
        simp
      simp [this]
    rw [hzero, ENNReal.toReal_zero] at hinc
    have hm1 := stochasticIntegralBrownian_memLp W ℱ hW θ hθmeas hθprog hθq R
    have hm2 := stochasticIntegralBrownian_memLp W ℱ hW θ hθmeas hθprog hθq T
    have hint : Integrable (fun ω => (I R ω - I T ω) ^ 2) P := (hm1.sub hm2).integrable_sq
    have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).1 hinc
    filter_upwards [this] with ω hω
    have h0 : (I R ω - I T ω) ^ 2 = 0 := hω
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
  -- subsequence
  have hIRm : AEMeasurable (I R) P :=
    (stochasticIntegralBrownian_memLp W ℱ hW θ hθmeas hθprog hθq R).1.aemeasurable
  set H : ℕ → Ω → ℝ≥0∞ := fun n ω => (‖simpleIntegral W (G n) R ω - I R ω‖₊ : ℝ≥0∞) ^ 2
    + ∫⁻ t in Set.Icc (0:ℝ) R, (‖θ ω t - (G n).eval t ω‖₊ : ℝ≥0∞) ^ 2 with hH
  have hH1m : ∀ n, AEMeasurable (fun ω => (‖simpleIntegral W (G n) R ω - I R ω‖₊ : ℝ≥0∞) ^ 2) P :=
    fun n => (((hJm n).aemeasurable.sub hIRm).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hH2m : ∀ n, Measurable (fun ω => ∫⁻ t in Set.Icc (0:ℝ) R,
      (‖θ ω t - (G n).eval t ω‖₊ : ℝ≥0∞) ^ 2) := fun n =>
    Measurable.lintegral_prod_right' (f := fun q : Ω × ℝ => (‖θ q.1 q.2 - (G n).eval q.2 q.1‖₊ : ℝ≥0∞) ^ 2)
      (ν := volume.restrict (Set.Icc (0:ℝ) R)) ((hθmeas.sub (hGj n)).nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hHm : ∀ n, AEMeasurable (H n) P := fun n => (hH1m n).add (hH2m n).aemeasurable
  have hHt : Tendsto (fun n => ∫⁻ ω, H n ω ∂P) atTop (𝓝 0) := by
    have e : ∀ n, ∫⁻ ω, H n ω ∂P = ∫⁻ ω, (‖simpleIntegral W (G n) R ω - I R ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ∫⁻ ω, ∫⁻ t in Set.Icc (0:ℝ) R, (‖θ ω t - (G n).eval t ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
      fun n => lintegral_add_left' (hH1m n) _
    simp_rw [e]
    have hL2 := masterApprox_tendsto_L2 W ℱ hW θ hθmeas hθprog hθq hR0
    have h1 := ((ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto 0).comp hL2
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
    simp only [Function.comp_def, eLpNorm_two_rpow_eq_lintegral_sq] at h1
    have h2 := masterApprox_eval_tendsto ℱ θ hθmeas hθprog hθq (P := P) (t := R)
    simpa using h1.add h2
  obtain ⟨ns, -, hns⟩ := ae_subseq_of_lintegral H hHm hHt
  have hθL : ∀ᵐ ω ∂P, ∫⁻ t in Set.Icc (0:ℝ) R, (‖θ ω t‖₊ : ℝ≥0∞) ^ 2 < ⊤ :=
    ae_lt_top (Measurable.lintegral_prod_right' (f := fun q : Ω × ℝ => (‖θ q.1 q.2‖₊ : ℝ≥0∞) ^ 2)
      (ν := volume.restrict (Set.Icc (0:ℝ) R)) (hθmeas.nnnorm.coe_nnreal_ennreal.pow_const 2))
      (hθq R hRpos).ne
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun k => Zn (ns k) ω) atTop (𝓝 (Z ω)) ∧
      Tendsto (fun k => Φn (ns k) ω) atTop (𝓝 (Φ ω)) := by
    filter_upwards [hns, hIRT, hθL] with ω h1 h2 h3
    have t1 : Tendsto (fun k => (‖simpleIntegral W (G (ns k)) R ω - I R ω‖₊ : ℝ≥0∞) ^ 2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun k => zero_le)
        (fun k => le_self_add)
    have t2 : Tendsto (fun k => ∫⁻ t in Set.Icc (0:ℝ) R,
        (‖θ ω t - (G (ns k)).eval t ω‖₊ : ℝ≥0∞) ^ 2) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun k => zero_le)
        (fun k => le_add_self)
    have hJc := tendsto_of_nnsq _ _ t1
    rw [h2] at hJc
    have hθm : Measurable (θ ω) := hθmeas.comp measurable_prodMk_left
    have hd := det_l2 (θ ω) (fun k t => (G (ns k)).eval t ω) R hR0 hθm
      (fun k => stepEval_measurable_t _ _ ω) h3 (fun k => by
        obtain ⟨C, hC⟩ := stepEval_bdd (G (ns k)).partition (G (ns k)).ξ ω
        exact bdd_lint_lt_top _ C hC R) t2
    have hθLp : MemLp (θ ω) 2 (volume.restrict (Set.Icc (0:ℝ) R)) := memLp2_of_lint _ hθm h3
    have hθI : IntegrableOn (θ ω) (Set.Icc 0 R) := hθLp.integrable one_le_two
    have hθ2I : IntegrableOn (fun t => θ ω t ^ 2) (Set.Icc 0 R) := hθLp.integrable_sq
    have hθii : ∀ x y, 0 ≤ x → x ≤ y → y ≤ R → IntervalIntegrable (θ ω) volume x y := by
      intro x y hx hxy hy
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
      exact hθI.mono_set (Set.Icc_subset_Icc hx hy)
    have hθint : ∫ t in (0:ℝ)..R, θ ω t ^ 2 = ∫ t in (0:ℝ)..T, θ ω t ^ 2 := by
      have i1 : IntervalIntegrable (fun t => θ ω t ^ 2) volume 0 T := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
        exact hθ2I.mono_set (Set.Icc_subset_Icc le_rfl hTR)
      have i2 : IntervalIntegrable (fun t => θ ω t ^ 2) volume T R := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTR]
        exact hθ2I.mono_set (Set.Icc_subset_Icc hT.le le_rfl)
      rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, intervalIntegral.integral_of_le hTR,
        setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0:ℝ))
          (fun u hu => by simp [hθzero ω u hu.1.le])]
      simp
    refine ⟨?_, ?_⟩
    · have hZe : Z ω = Real.exp (I T ω - (∫ t in (0:ℝ)..R, θ ω t ^ 2) / 2) := by
        rw [hZ ω, hθint]; ring_nf
      rw [hZe]
      exact (Real.continuous_exp.tendsto _).comp (hJc.sub (hd.1.div_const 2))
    · have hΦe : Φ ω = (∑ j : Fin M, a j * (W.W (s j.succ) ω - W.W (s j.castSucc) ω))
          - ∑ j : Fin M, a j * ∫ t in (s j.castSucc)..(s j.succ), θ ω t := by
        simp only [hΦ]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← intervalIntegral.integral_interval_sub_left (hθii 0 _ le_rfl (hs0 _) (hsR _))
          (hθii 0 _ le_rfl (hs0 _) (hsR _))]
        ring
      rw [hΦe]
      exact tendsto_const_nhds.sub (tendsto_finset_sum _ fun j _ =>
        (hd.2 _ _ (hs0 _) (hs (Fin.castSucc_le_succ j)) (hsR _)).const_mul _)
  have hlim := scheffe_limit (fun k => Zn (ns k)) Z (fun k => Φn (ns k)) Φ (fun k => hZn0 (ns k))
    hZ0 (fun k => hZni (ns k)) hZi (fun k => hZnint (ns k)) (fun k => (hΦnm (ns k)).aestronglyMeasurable)
    hΦm.aestronglyMeasurable (hconv.mono fun ω h => h.1) (hconv.mono fun ω h => h.2)
  simp only [hEq] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm


open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito in
lemma charfun_Q
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T : ℝ) (hT : 0 < T)
    (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ θ)
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0)
    (Z : Ω → ℝ)
    (hZ : ∀ ω : Ω,
      Z ω = Real.exp (
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW θ hθmeas hθprog hθq T ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..T, θ ω s ^ 2))
    (hZmean : ∫ ω, Z ω ∂P = 1) {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) (a : Fin n → ℝ) :
    ∫ ω, Complex.exp (((∑ i : Fin n, a i * ((W.W (t i.succ : ℝ) ω - ∫ s in (0:ℝ)..(t i.succ : ℝ), θ ω s)
      - (W.W (t i.castSucc : ℝ) ω - ∫ s in (0:ℝ)..(t i.castSucc : ℝ), θ ω s)) : ℝ) : ℂ) * Complex.I)
      ∂(P.withDensity (fun ω => ENNReal.ofReal (Z ω)))
      = ∏ i : Fin n, Complex.exp (-((a i ^ 2 * ((t i.succ : ℝ) - (t i.castSucc : ℝ)) : ℝ) : ℂ) / 2) := by
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => by rw [hZ ω]; exact (Real.exp_pos _).le
  have hZm : Measurable Z := by
    have e : Z = fun ω => Real.exp (stochasticIntegralBrownian W ℱ hW θ hθmeas hθprog hθq T ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..T, θ ω s ^ 2) := funext hZ
    rw [e]
    exact Real.measurable_exp.comp
      (((stochasticIntegralBrownian_stronglyAdapted W ℱ hW θ hθmeas hθprog hθq T).measurable.mono
        (ℱ.le T) le_rfl).sub
        ((meas_iint (fun ω s => θ ω s ^ 2) (hθmeas.pow_const 2) hT.le).const_mul _))
  have hk := key_P P W ℱ hW T hT θ hθmeas hθprog hθq hθzero Z hZ hZmean (fun j => (t j : ℝ))
    (fun i j h => NNReal.coe_le_coe.2 (ht h)) (fun j => (t j).2) a
  have hQ : P.withDensity (fun ω => ENNReal.ofReal (Z ω))
      = P.withDensity (fun ω => ((Z ω).toNNReal : ℝ≥0∞)) := rfl
  rw [hQ, integral_withDensity_eq_integral_smul (f := fun ω => (Z ω).toNNReal) (measurable_real_toNNReal.comp hZm)]
  have e2 : ∀ ω, (Z ω).toNNReal • Complex.exp (((∑ i : Fin n, a i * ((W.W (t i.succ : ℝ) ω
      - ∫ s in (0:ℝ)..(t i.succ : ℝ), θ ω s) - (W.W (t i.castSucc : ℝ) ω
      - ∫ s in (0:ℝ)..(t i.castSucc : ℝ), θ ω s)) : ℝ) : ℂ) * Complex.I)
      = (Z ω : ℂ) * Complex.exp (Complex.I * ((∑ i : Fin n, a i * ((W.W (t i.succ : ℝ) ω
      - ∫ s in (0:ℝ)..(t i.succ : ℝ), θ ω s) - (W.W (t i.castSucc : ℝ) ω
      - ∫ s in (0:ℝ)..(t i.castSucc : ℝ), θ ω s)) : ℝ) : ℂ)) := by
    intro ω
    rw [NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal _ (hZ0 ω), mul_comm _ Complex.I]
  simp_rw [e2]
  rw [hk, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_div]

/-- Step C (proved): a.s. continuity of `t ↦ ∫_0^t θ` on `[0,∞)`. -/
lemma drift_integral_continuous {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, θ ω s) (Set.Ici 0) := by
  have hae : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
    ae_lt_top (Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ => (‖θ p.1 p.2‖₊ : ℝ≥0∞) ^ 2)
      (ν := volume.restrict (Set.Icc (0:ℝ) T)) (hθmeas.nnnorm.coe_nnreal_ennreal.pow_const 2)) (hθq T hT).ne
  filter_upwards [hae] with ω hω
  have hm : Measurable (θ ω) := hθmeas.comp measurable_prodMk_left
  have hint : IntegrableOn (θ ω) (Set.Icc 0 T) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    have : ∫⁻ s in Set.Icc (0:ℝ) T, (‖θ ω s‖₊ : ℝ≥0∞) ∂volume ≤
        ∫⁻ s in Set.Icc (0:ℝ) T, (1 + (‖θ ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume := by
      refine lintegral_mono fun s => ?_
      rcases le_total (‖θ ω s‖₊ : ℝ≥0∞) 1 with h | h
      · exact h.trans (le_add_right le_rfl)
      · exact (le_self_pow₀ h two_ne_zero).trans (le_add_left le_rfl)
    refine lt_of_le_of_lt this ?_
    rw [lintegral_add_left measurable_const]
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.add_lt_top.2 ⟨by simp, hω⟩
  have hgint : Integrable ((Set.Icc (0:ℝ) T).indicator (θ ω)) := by
    exact (integrable_indicator_iff measurableSet_Icc).2 hint
  have hcont := intervalIntegral.continuous_primitive (fun a b => hgint.intervalIntegrable (a := a) (b := b)) 0
  refine hcont.continuousOn.congr fun t ht => ?_
  have ht0 : (0:ℝ) ≤ t := ht
  show _ = ∫ x in (0:ℝ)..t, (Set.Icc (0:ℝ) T).indicator (θ ω) x
  rw [intervalIntegral.integral_of_le ht0, intervalIntegral.integral_of_le ht0]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  by_cases h : s ≤ T
  · have hs' : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1.le, h⟩
    simp [Set.indicator_of_mem hs']
  · rw [Set.indicator_of_notMem (fun hh => h hh.2), hθzero ω s (not_le.1 h).le]

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T : ℝ) (hT : 0 < T)
    (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ θ)
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0)
    (Z : Ω → ℝ)
    (hZ : ∀ ω : Ω,
      Z ω = Real.exp (
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW θ hθmeas hθprog hθq T ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..T, θ ω s ^ 2))
    (hZmean : ∫ ω, Z ω ∂P = 1) :
    let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    let shifted : ℝ≥0 → Ω → ℝ := fun t ω =>
      W.W (t : ℝ) ω - ∫ s in (0 : ℝ)..(t : ℝ), θ ω s
    IsBrownianReal shifted Q := by
  intro Q shifted
  have hZpos : ∀ ω, 0 < Z ω := fun ω => by rw [hZ ω]; exact Real.exp_pos _
  have hZint : Integrable Z P := by
    by_contra h
    rw [integral_undef h] at hZmean; exact zero_ne_one hZmean
  haveI hQ : IsProbabilityMeasure Q := by
    refine ⟨?_⟩
    simp only [Q, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hZint (Eventually.of_forall fun ω => (hZpos ω).le),
      hZmean]; simp
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hXm : ∀ t, Measurable (shifted t) := fun t =>
    (W.measurable_eval _).sub (meas_iint θ hθmeas t.2)
  have h0 : ∀ᵐ ω ∂Q, shifted 0 ω = 0 := by
    filter_upwards [hQP.ae_le W.initial_zero] with ω a
    simp [shifted, a]
  have hmarg : ∀ {n : ℕ} (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ (i : Fin n) (v : ℝ),
      ∫ ω, Complex.exp (((v * (shifted (t i.succ) ω - shifted (t i.castSucc) ω) : ℝ) : ℂ) * Complex.I) ∂Q
        = Complex.exp (-((v ^ 2 * ((t i.succ : ℝ) - (t i.castSucc : ℝ)) : ℝ) : ℂ) / 2) := by
    intro n t ht i v
    have := charfun_Q P W ℱ hW T hT θ hθmeas hθprog hθq hθzero Z hZ hZmean t ht
      (fun j => if j = i then v else 0)
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [show (∫ ω, Complex.exp (((v * (shifted (t i.succ) ω - shifted (t i.castSucc) ω) : ℝ) : ℂ)
      * Complex.I) ∂Q) = _ from this]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  have hlaw : ∀ t, HasLaw (shifted t) (gaussianReal 0 t) Q := by
    intro t
    refine ⟨(hXm t).aemeasurable, ?_⟩
    apply Measure.ext_of_charFun
    funext u
    rw [charFun_apply_real, charFun_gaussianReal, integral_map (hXm t).aemeasurable (by fun_prop)]
    have hmono : Monotone ![(0 : ℝ≥0), t] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have := hmarg ![(0 : ℝ≥0), t] hmono 0 u
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.succ_zero_eq_one, Fin.castSucc_zero] at this
    have e : ∫ ω, Complex.exp (((u * shifted t ω : ℝ) : ℂ) * Complex.I) ∂Q
        = ∫ ω, Complex.exp (((u * (shifted t ω - shifted 0 ω) : ℝ) : ℂ) * Complex.I) ∂Q :=
      integral_congr_ae (h0.mono fun ω h => by simp only [h, sub_zero])
    have e1 : (fun ω => Complex.exp (↑u * ↑(shifted t ω) * Complex.I))
        = fun ω => Complex.exp (((u * shifted t ω : ℝ) : ℂ) * Complex.I) := by
      funext ω; push_cast; ring_nf
    rw [e1, e, this]
    congr 1; push_cast; ring
  have hincr : HasIndepIncrements shifted Q := by
    intro n t ht
    rw [iIndepFun_iff_charFun_pi (X := fun (i : Fin n) ω => shifted (t i.succ) ω - shifted (t i.castSucc) ω)
      (fun i => ((hXm _).sub (hXm _)).aemeasurable)]
    intro v
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    simp only [PiLp.inner_apply, charFun_apply_real, RCLike.inner_apply, conj_trivial]
    have hl := charfun_Q P W ℱ hW T hT θ hθmeas hθprog hθq hθzero Z hZ hZmean t ht (fun i => v.ofLp i)
    have hr : ∀ i : Fin n, ∫ x, Complex.exp (↑(v.ofLp i) * ↑x * Complex.I)
        ∂(Q.map (fun ω => shifted (t i.succ) ω - shifted (t i.castSucc) ω))
        = Complex.exp (-((v.ofLp i ^ 2 * ((t i.succ : ℝ) - (t i.castSucc : ℝ)) : ℝ) : ℂ) / 2) := by
      intro i
      have hYm : Measurable (fun ω => shifted (t i.succ) ω - shifted (t i.castSucc) ω) :=
        (hXm _).sub (hXm _)
      rw [integral_map hYm.aemeasurable (by fun_prop)]
      rw [← hmarg t ht i (v.ofLp i)]
      congr 1; funext ω; push_cast; ring_nf
    rw [Finset.prod_congr rfl fun i _ => hr i]
    exact hl
  exact { toIsPreBrownianReal := HasIndepIncrements.isPreBrownianReal_of_hasLaw hlaw hincr,
          cont := by
            have h1 := hQP.ae_le W.continuous_paths
            have h2 := hQP.ae_le (drift_integral_continuous P T θ hθmeas hθq hθzero hT)
            filter_upwards [h1, h2] with ω a b
            exact (a.comp continuous_subtype_val).sub
              (b.comp_continuous continuous_subtype_val (fun x => x.2)) }
