-- Prove2me | solution 1 for AssortSearch.MNLQC.Supplement.overlap_search_iff
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:52.36141+00:00
-- url     : https://prove2.me/submissions/dfb93982-b8a5-43ac-a705-964fcb7de65a

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

open AssortSearch
open AssortSearch.MNLQC
open AssortSearch.MNLQC.Supplement

/-- Proof of Theorem 3 (p. 11): for an assortment `S ⊊ N` and a search cost `b > 0`, the consumer
whose best utility in the assortment is `y = U_max` searches by rule (5), `Φ_S(y) ≥ b`, exactly when
`y ≤ Ū(S)`; and the search gain strictly exceeds `b` exactly when `y < Ū(S)`. -/
theorem solution {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (S : Finset (Fin n)) (hS : S ≠ Finset.univ) (b : ℝ) (hb : 0 < b) (y : ℝ) :
    (b ≤ AssortSearch.FullAssort.searchGain μ v S y ↔ y ≤ AssortSearch.FullAssort.Ubar μ v S b) ∧
      (b < AssortSearch.FullAssort.searchGain μ v S y ↔
        y < AssortSearch.FullAssort.Ubar μ v S b) := by
          classical
          obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = AssortSearch.FullAssort.outsidePref v S := ⟨_, rfl⟩
          have hV : 0 < V := by
            rw [hVdef]
            obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
              by_contra h
              push Not at h
              exact hS (Finset.eq_univ_of_forall h)
            exact Finset.sum_pos (fun j _ => hv j) ⟨i, by simpa using hi⟩
          obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = Real.eulerMascheroniConstant := ⟨_, rfl⟩
          obtain ⟨W, hWdef⟩ : ∃ W : ℝ → ℝ, W = AssortSearch.FullAssort.w μ v S := ⟨_, rfl⟩
          have hwdef : ∀ t, W t = V / μ * Real.exp (-(t/μ + γ)) *
              Real.exp (-(Real.exp (-(t/μ+γ)) * V)) := by
            intro t; rw [hWdef, hVdef, hγ]; rfl
          have hwfun : W = fun t => V / μ * Real.exp (-(t/μ + γ)) *
              Real.exp (-(Real.exp (-(t/μ+γ)) * V)) := funext hwdef
          have hwcont : Continuous W := by rw [hwfun]; fun_prop
          have hwpos : ∀ t, 0 < W t := by intro t; rw [hwdef]; positivity
          have hwle : ∀ t, W t ≤ V/μ * Real.exp (-(t/μ+γ)) := by
            intro t; rw [hwdef]
            have h1 : Real.exp (-(Real.exp (-(t/μ+γ)) * V)) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              have := Real.exp_pos (-(t/μ+γ)); nlinarith
            have h2 : 0 ≤ V/μ * Real.exp (-(t/μ+γ)) := by positivity
            calc _ ≤ V/μ * Real.exp (-(t/μ+γ)) * 1 := mul_le_mul_of_nonneg_left h1 h2
              _ = _ := mul_one _
          have hwint : ∀ a, IntegrableOn W (Set.Ioi a) := by
            intro a
            have hb' : IntegrableOn (fun t => V/μ * Real.exp (-γ) * Real.exp (-(1/μ) * t)) (Set.Ioi a) :=
              (exp_neg_integrableOn_Ioi a (by positivity : (0:ℝ) < 1/μ)).const_mul _
            refine hb'.mono' hwcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_))
            rw [Real.norm_eq_abs, abs_of_pos (hwpos t)]
            calc W t ≤ V/μ * Real.exp (-(t/μ+γ)) := hwle t
              _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
          have hgint : ∀ c, Integrable (fun t => max (t - c) 0 * W t) := by
            intro c
            have hcont : Continuous (fun t => max (t - c) 0 * W t) := by fun_prop
            rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := c), integrableOn_union]
            constructor
            · refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Iic
              simp only [Set.mem_Iic] at ht
              simp [max_eq_right (by linarith : t - c ≤ 0)]
            · have hb' : IntegrableOn (fun t => 2 * V * Real.exp (-(c/(2*μ)) - γ) *
                  Real.exp (-(1/(2*μ)) * t)) (Set.Ioi c) :=
                (exp_neg_integrableOn_Ioi c (by positivity)).const_mul _
              refine hb'.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
              have hm : max (t - c) 0 ≤ 2*μ * Real.exp ((t-c)/(2*μ)) := by
                apply max_le
                · have h1 := Real.add_one_le_exp ((t-c)/(2*μ))
                  have h2 : t - c = 2*μ*((t-c)/(2*μ)) := by field_simp
                  nlinarith
                · positivity
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (hwpos t).le)]
              calc max (t-c) 0 * W t ≤ 2*μ*Real.exp ((t-c)/(2*μ)) * (V/μ * Real.exp (-(t/μ+γ))) :=
                    mul_le_mul hm (hwle t) (hwpos t).le (by positivity)
                _ = 2*V*(Real.exp ((t-c)/(2*μ)) * Real.exp (-(t/μ+γ))) := by field_simp
                _ = _ := by
                  have hx : (t - c) / (2 * μ) + -(t / μ + γ) = (-(c/(2*μ)) - γ) + (-(1/(2*μ)) * t) := by
                    field_simp; ring
                  rw [← Real.exp_add, hx, Real.exp_add]; ring
          obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ → ℝ, φ = AssortSearch.FullAssort.searchGain μ v S := ⟨_, rfl⟩
          have hφ : ∀ y, φ y = ∫ t, max (t - y) 0 * W t := by
            intro y
            rw [hφdef, hWdef]
            unfold AssortSearch.FullAssort.searchGain
            rw [← integral_indicator measurableSet_Ioi]
            congr 1; funext t
            by_cases ht : t ∈ Set.Ioi y
            · rw [Set.indicator_of_mem ht, max_eq_left (by simp at ht; linarith)]
            · rw [Set.indicator_of_notMem ht, max_eq_right (by simp at ht; linarith), zero_mul]
          have hφnn : ∀ y, 0 ≤ φ y := by
            intro y; rw [hφ]
            exact integral_nonneg fun t => mul_nonneg (le_max_right _ _) (hwpos t).le
          have hdiff : ∀ y y', y ≤ y' → (y' - y) * ∫ t in Set.Ioi y', W t ≤ φ y - φ y' := by
            intro y y' hyy
            rw [hφ, hφ, ← integral_sub (hgint y) (hgint y'), ← integral_const_mul,
              ← integral_indicator measurableSet_Ioi]
            apply integral_mono (IntegrableOn.integrable_indicator
              (f := fun t => (y' - y) * W t) ((hwint y').const_mul (y' - y)) measurableSet_Ioi)
              ((hgint y).sub (hgint y'))
            intro t
            by_cases ht : t ∈ Set.Ioi y'
            · rw [Set.indicator_of_mem ht]
              simp only [Set.mem_Ioi] at ht
              simp only [Pi.sub_apply]
              rw [max_eq_left (by linarith), max_eq_left (by linarith)]
              apply le_of_eq; ring
            · rw [Set.indicator_of_notMem ht]
              simp only [Set.mem_Ioi, not_lt] at ht
              simp only [Pi.sub_apply]
              rw [max_eq_right (by linarith : t - y' ≤ 0)]
              simp only [zero_mul, sub_zero]
              exact mul_nonneg (le_max_right _ _) (hwpos t).le
          have hwIpos : ∀ a, 0 < ∫ t in Set.Ioi a, W t := by
            intro a
            rw [setIntegral_pos_iff_support_of_nonneg_ae
              (Filter.Eventually.of_forall fun t => (hwpos t).le) (hwint a)]
            have : Function.support W = Set.univ := Set.eq_univ_of_forall fun t => (hwpos t).ne'
            rw [this, Set.univ_inter]; simp
          have hanti : StrictAnti φ := by
            intro y y' hyy
            have h1 := hdiff y y' hyy.le
            have h2 := hwIpos y'
            have h3 : 0 < (y' - y) * ∫ t in Set.Ioi y', W t := mul_pos (by linarith) h2
            linarith
          have hcontφ : Continuous φ := by
            have : φ = fun y => ∫ t, max (t - y) 0 * W t := funext hφ
            rw [this, continuous_iff_continuousAt]
            intro y0
            apply continuousAt_of_dominated (bound := fun t => max (t - (y0 - 1)) 0 * W t)
            · exact Filter.Eventually.of_forall fun y => (hgint y).aestronglyMeasurable
            · filter_upwards [Ioi_mem_nhds (by linarith : y0 - 1 < y0)] with y hy
              refine Filter.Eventually.of_forall fun t => ?_
              simp only [Set.mem_Ioi] at hy
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (hwpos t).le)]
              exact mul_le_mul_of_nonneg_right (max_le_max (by linarith) le_rfl) (hwpos t).le
            · exact hgint _
            · refine Filter.Eventually.of_forall fun t => ?_
              fun_prop
          have hlim : Filter.Tendsto φ Filter.atTop (nhds 0) := by
            have : Filter.Tendsto (fun y => ∫ t, max (t - y) 0 * W t) Filter.atTop
                (nhds (∫ t : ℝ, (0:ℝ))) := by
              apply tendsto_integral_filter_of_dominated_convergence (fun t => max (t - 0) 0 * W t)
              · exact Filter.Eventually.of_forall fun y => (hgint y).aestronglyMeasurable
              · filter_upwards [Filter.eventually_ge_atTop 0] with y hy
                refine Filter.Eventually.of_forall fun t => ?_
                rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (hwpos t).le)]
                exact mul_le_mul_of_nonneg_right (max_le_max (by linarith) le_rfl) (hwpos t).le
              · exact hgint 0
              · refine Filter.Eventually.of_forall fun t => ?_
                apply tendsto_const_nhds.congr'
                filter_upwards [Filter.eventually_gt_atTop t] with y hy
                rw [max_eq_right (by linarith)]; simp
            have hφfun : φ = fun y => ∫ t, max (t - y) 0 * W t := funext hφ
            rw [hφfun]; simpa using this
          -- a point with φ > b
          obtain ⟨y0, hy0⟩ : ∃ y0, b < φ y0 := by
            set c0 := ∫ t in Set.Ioi (0:ℝ), W t with hc0
            have hc0pos : 0 < c0 := hwIpos 0
            refine ⟨-(b / c0) - 1, ?_⟩
            have h1 := hdiff (-(b / c0) - 1) 0 (by
              have : 0 ≤ b / c0 := by positivity
              linarith)
            have h2 := hφnn 0
            have h3 : (0 - (-(b / c0) - 1)) * c0 = b + c0 := by field_simp; ring
            rw [h3] at h1
            linarith
          -- a point with φ ≤ b
          obtain ⟨y1, hy1⟩ : ∃ y1, φ y1 ≤ b := by
            have := (hlim.eventually (gt_mem_nhds hb)).exists
            obtain ⟨y1, h⟩ := this
            exact ⟨y1, h.le⟩
          set A := {u : ℝ | φ u ≤ b} with hA
          have hUbar : AssortSearch.FullAssort.Ubar μ v S b = sInf A := by
            rw [hA, hφdef]; rfl
          have hAclosed : IsClosed A := isClosed_le hcontφ continuous_const
          have hAne : A.Nonempty := ⟨y1, hy1⟩
          have hAbdd : BddBelow A := by
            refine ⟨y0, fun u hu => ?_⟩
            by_contra h
            push Not at h
            have := hanti h
            simp only [hA, Set.mem_ofPred_eq] at hu
            linarith
          set c := sInf A with hc
          have hcA : c ∈ A := hAclosed.csInf_mem hAne hAbdd
          have hy0c : y0 ≤ c := le_csInf hAne (fun u hu => by
            by_contra h
            push Not at h
            have := hanti h
            simp only [hA, Set.mem_ofPred_eq] at hu
            linarith)
          have hφc : φ c = b := by
            have hcb : φ c ≤ b := hcA
            obtain ⟨d, hd, hdb⟩ := intermediate_value_Icc' hy0c hcontφ.continuousOn
              (show b ∈ Set.Icc (φ c) (φ y0) from ⟨hcb, hy0.le⟩)
            have hdA : d ∈ A := by simp only [hA, Set.mem_ofPred_eq]; rw [hdb]
            have : c ≤ d := csInf_le hAbdd hdA
            have : d = c := le_antisymm hd.2 this
            rw [← this, hdb]
          rw [← hφdef, hUbar, ← hφc]
          exact ⟨hanti.le_iff_ge, hanti.lt_iff_gt⟩
