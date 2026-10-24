-- Prove2me | solution 1 for AssortSearch.Cannibal.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T21:29:42.461314+00:00
-- url     : https://prove2.me/submissions/c93afa79-dbee-49b7-9360-d8ab2e1e9309

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open AssortSearch.Cannibal in
/-- Left-tail bound for the zero-mean Gumbel distribution function. -/
lemma asc2_left_tail (μ t : ℝ) :
    gumbelCdf μ (-t) ≤ Real.exp Real.eulerMascheroniConstant * Real.exp (-(1 / μ) * t) := by
  unfold gumbelCdf
  have h := Real.add_one_le_exp (-((-t) / μ + Real.eulerMascheroniConstant))
  have h1 : Real.exp (-Real.exp (-((-t) / μ + Real.eulerMascheroniConstant)))
      ≤ Real.exp ((-t) / μ + Real.eulerMascheroniConstant) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp ((-t) / μ + Real.eulerMascheroniConstant)
      = Real.exp Real.eulerMascheroniConstant * Real.exp (-(1 / μ) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  linarith

open AssortSearch.Cannibal in
/-- Right-tail bound for the zero-mean Gumbel distribution function. -/
lemma asc2_right_tail (μ t : ℝ) :
    1 - gumbelCdf μ t ≤ Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(1 / μ) * t) := by
  unfold gumbelCdf
  have h := Real.add_one_le_exp (-Real.exp (-(t / μ + Real.eulerMascheroniConstant)))
  have h2 : Real.exp (-(t / μ + Real.eulerMascheroniConstant))
      = Real.exp (-Real.eulerMascheroniConstant) * Real.exp (-(1 / μ) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  linarith

open AssortSearch.Cannibal in
lemma asc2_cdf_le_one (μ t : ℝ) : gumbelCdf μ t ≤ 1 := by
  unfold gumbelCdf
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos _).le)

open AssortSearch.Cannibal in
lemma asc2_tail_meas (μ : ℝ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) (t : ℝ) :
    G {x | t < |x|} ≤ ENNReal.ofReal
      ((Real.exp Real.eulerMascheroniConstant + Real.exp (-Real.eulerMascheroniConstant))
        * Real.exp (-(1 / μ) * t)) := by
  have hsub : {x : ℝ | t < |x|} ⊆ Set.Iic (-t) ∪ (Set.Iic t)ᶜ := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rcases lt_abs.mp hx with h | h
    · right; simp only [Set.mem_compl_iff, Set.mem_Iic, not_le]; exact h
    · left; simp only [Set.mem_Iic]; linarith
  have hA : G (Set.Iic (-t)) = ENNReal.ofReal (gumbelCdf μ (-t)) := by
    rw [← ofReal_cdf, hG]
  have hB : G (Set.Iic t)ᶜ = ENNReal.ofReal (1 - gumbelCdf μ t) := by
    rw [prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, hG,
      ENNReal.ofReal_sub 1 (show (0:ℝ) ≤ gumbelCdf μ t from (Real.exp_pos _).le), ENNReal.ofReal_one]
  have h0 : 0 ≤ gumbelCdf μ (-t) := (Real.exp_pos _).le
  have h1 : 0 ≤ 1 - gumbelCdf μ t := by linarith [asc2_cdf_le_one μ t]
  calc G {x | t < |x|} ≤ G (Set.Iic (-t) ∪ (Set.Iic t)ᶜ) := measure_mono hsub
    _ ≤ G (Set.Iic (-t)) + G (Set.Iic t)ᶜ := measure_union_le _ _
    _ = ENNReal.ofReal (gumbelCdf μ (-t) + (1 - gumbelCdf μ t)) := by
        rw [hA, hB, ENNReal.ofReal_add h0 h1]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have := asc2_left_tail μ t
        have := asc2_right_tail μ t
        nlinarith

open AssortSearch.Cannibal in
lemma asc2_integrable (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) : Integrable (fun x : ℝ => x) G := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [Real.enorm_eq_ofReal_abs]
  have hl := lintegral_eq_lintegral_meas_lt G (f := fun x : ℝ => |x|)
    (ae_of_all _ (fun x => abs_nonneg x)) continuous_abs.measurable.aemeasurable
  rw [hl]
  have hint : IntegrableOn (fun t : ℝ =>
      (Real.exp Real.eulerMascheroniConstant + Real.exp (-Real.eulerMascheroniConstant))
        * Real.exp (-(1 / μ) * t)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by positivity : (0 : ℝ) < 1 / μ)).const_mul _
  calc (∫⁻ t in Set.Ioi 0, G {x | t < |x|})
      ≤ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal
          ((Real.exp Real.eulerMascheroniConstant + Real.exp (-Real.eulerMascheroniConstant))
            * Real.exp (-(1 / μ) * t)) :=
        lintegral_mono (fun t => asc2_tail_meas μ G hG t)
    _ < ⊤ := hint.lintegral_lt_top

open AssortSearch.Cannibal in
lemma asc2_sw_iff (G : Measure ℝ) [IsProbabilityMeasure G] (hid : Integrable (fun x : ℝ => x) G)
    (ur b y : ℝ) : SearchWorthwhile G ur b y ↔ ur - y + ∫ x, x ∂G ≥ b := by
  unfold SearchWorthwhile
  have hg : Integrable (fun x : ℝ => ur + x - y) G :=
    ((integrable_const ur).add hid).sub (integrable_const y)
  have hneg : (∫ x in Set.Iic (y - ur), (y - ur - x) ∂G)
      = - ∫ x in Set.Iic (y - ur), (ur + x - y) ∂G := by
    rw [← integral_neg]; congr 1; ext x; ring
  have hsum : (∫ x in Set.Ioi (y - ur), (ur + x - y) ∂G)
      - (∫ x in Set.Iic (y - ur), (y - ur - x) ∂G) = ur - y + ∫ x, x ∂G := by
    rw [hneg, sub_neg_eq_add, add_comm, ← Set.compl_Iic,
      integral_add_compl measurableSet_Iic hg]
    have hi1 : Integrable (fun x : ℝ => ur + x) G := (integrable_const ur).add hid
    rw [integral_sub hi1 (integrable_const y),
      integral_add (integrable_const ur) hid, integral_const, integral_const]
    simp
    ring
  rw [hsum]

open AssortSearch.Cannibal in
lemma asc2_Ioc_pos (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) (a : ℝ) : 0 < G (Set.Ioc a (a + 1)) := by
  rw [← measure_cdf G, StieltjesFunction.measure_Ioc, hG, hG]
  apply ENNReal.ofReal_pos.mpr
  apply sub_pos.mpr
  unfold gumbelCdf
  apply Real.exp_lt_exp.mpr
  apply neg_lt_neg
  apply Real.exp_lt_exp.mpr
  have : a / μ < (a + 1) / μ := (div_lt_div_iff_of_pos_right hμ).mpr (by linarith)
  linarith

open MeasureTheory ProbabilityTheory AssortSearch.Cannibal in
theorem solution {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) (ur b : ℝ) (w : Fin n → ℝ) (u0 : ℝ) (S Splus : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) (hS : S ⊂ Splus) :
    searchProb G ur b w u0 S i > searchProb G ur b w u0 Splus i := by
  classical
  have hid := asc2_integrable μ hμ G hG
  obtain ⟨k, hkSp, hkS⟩ := Finset.exists_of_ssubset hS
  have hki : k ≠ i := fun h => hkS (h ▸ hi)
  have hSsub : S ⊆ Splus := hS.subset
  set L : ℝ := ur + (∫ x, x ∂G) - b with hL
  let lo : Option (Fin n) → ℝ := fun o =>
    if o = some i then L else if o = some k then L + 2 else L - 2
  let I : Option (Fin n) → Set ℝ := fun o =>
    Set.Ioc (lo o - netUtility w u0 o) (lo o - netUtility w u0 o + 1)
  let B : Set (Option (Fin n) → ℝ) := Set.pi Set.univ I
  have hBmeas : MeasurableSet B := MeasurableSet.univ_pi (fun o => measurableSet_Ioc)
  have hPB : 0 < Measure.pi (fun _ : Option (Fin n) => G) B := by
    simp only [B]
    rw [Measure.pi_pi]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro o _
    exact (asc2_Ioc_pos μ hμ G hG _).ne'
  have hU : ∀ ζ ∈ B, ∀ o, lo o < utility w u0 ζ o ∧ utility w u0 ζ o ≤ lo o + 1 := by
    intro ζ hζ o
    have h := hζ o (Set.mem_univ _)
    simp only [I, Set.mem_Ioc] at h
    simp only [utility]
    constructor <;> linarith [h.1, h.2]
  have hloi : lo (some i) = L := by simp [lo]
  have hlok : lo (some k) = L + 2 := by simp [lo, hki]
  have hlonone : lo none = L - 2 := by simp [lo]
  have hloj : ∀ j ∈ S, j ≠ i → lo (some j) = L - 2 := by
    intro j hj hji
    have hjk : j ≠ k := fun h => hkS (h ▸ hj)
    simp [lo, hji, hjk]
  unfold searchProb
  refine (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr ?_
  refine lt_of_lt_of_le (ENNReal.lt_add_right (measure_ne_top _ _) hPB.ne') ?_
  refine (measure_union ?_ hBmeas).symm.le.trans (measure_mono ?_)
  · rw [Set.disjoint_left]
    intro ζ hA hζB
    simp only [Set.mem_ofPred_eq] at hA
    have h1 := hA.1 k hkSp hki
    have hk := hU ζ hζB (some k)
    have hi' := hU ζ hζB (some i)
    rw [hlok] at hk
    rw [hloi] at hi'
    linarith [hk.1, hi'.2]
  · apply Set.union_subset
    · intro ζ hA
      simp only [Set.mem_ofPred_eq] at hA ⊢
      exact ⟨fun j hj hji => hA.1 j (hSsub hj) hji, hA.2.1, hA.2.2⟩
    · intro ζ hζB
      simp only [Set.mem_ofPred_eq]
      have hi' := hU ζ hζB (some i)
      rw [hloi] at hi'
      refine ⟨?_, ?_, ?_⟩
      · intro j hj hji
        have hj' := hU ζ hζB (some j)
        rw [hloj j hj hji] at hj'
        linarith [hj'.2, hi'.1]
      · have h0 := hU ζ hζB none
        rw [hlonone] at h0
        linarith [h0.2, hi'.1]
      · rw [asc2_sw_iff G hid]
        intro hsw
        linarith [hi'.1]
