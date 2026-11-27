-- Prove2me | solution 1 for AssortSearch.MNLQC.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:36.39148+00:00
-- url     : https://prove2.me/submissions/6cda3555-37fe-441a-8f5a-c2cf1b9e0e8a

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

/-- **Theorem 3** (p. 11), overlapping assortment model. Let the shocks be i.i.d. zero-mean Gumbel
of scale `μ > 0`, let `v_j = exp(a_j/μ)`, `v_0 = exp(u_0/μ)`, `S ⊊ N` and `b > 0`. Then (4),
`∫_u^∞ (ȳ − u) w(ȳ, S) dȳ = b`, has exactly one solution `u = Ū(S)`, and for every `i ∈ S` the
probability that the consumer buys `i` is `q_i^so(S) = q_i^m(S) (1 − H(Ū(S), S))`. -/
theorem solution {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : AssortSearch.Cannibal.IsZeroMeanGumbel μ G) (a : Fin n → ℝ) (u0 b : ℝ) (hb : 0 < b)
    (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    (AssortSearch.FullAssort.searchGain μ (AssortSearch.Cannibal.pref μ a) S
          (AssortSearch.FullAssort.Ubar μ (AssortSearch.Cannibal.pref μ a) S b) = b ∧
        ∀ u : ℝ, AssortSearch.FullAssort.searchGain μ (AssortSearch.Cannibal.pref μ a) S u = b →
          u = AssortSearch.FullAssort.Ubar μ (AssortSearch.Cannibal.pref μ a) S b) ∧
      ∀ i ∈ S, overlapProb G μ a u0 b S i =
        share (AssortSearch.Cannibal.pref μ a) (AssortSearch.Cannibal.pref0 μ u0) S i *
          (1 - AssortSearch.Cannibal.H μ
            (AssortSearch.FullAssort.Ubar μ (AssortSearch.Cannibal.pref μ a) S b)
            (AssortSearch.Cannibal.pref μ a) (AssortSearch.Cannibal.pref0 μ u0) S) := by
              classical
              open AssortSearch.Cannibal AssortSearch.FullAssort Filter Set in
              have hv : ∀ j, 0 < pref μ a j := fun j => Real.exp_pos _
              have hLpos : ∀ y, 0 < lam μ y := fun y => Real.exp_pos _
              have hLd : ∀ y, HasDerivAt (fun y => lam μ y) (-(lam μ y) / μ) y := by
                intro y
                have h1 : HasDerivAt (fun y : ℝ => -(y / μ + Real.eulerMascheroniConstant)) (-(1 / μ)) y :=
                  (((hasDerivAt_id y).div_const μ).add_const Real.eulerMascheroniConstant).neg
                have := h1.exp
                convert this using 1
                · rfl
                show -(Real.exp (-(y / μ + Real.eulerMascheroniConstant))) / μ = _
                ring
              have hLc : Continuous (fun y => lam μ y) :=
                continuous_iff_continuousAt.2 (fun y => (hLd y).continuousAt)
              have hEd : ∀ k y, HasDerivAt (fun y => Real.exp (-(lam μ y * k)))
                  (k / μ * lam μ y * Real.exp (-(lam μ y * k))) y := by
                intro k y
                have h1 : HasDerivAt (fun y : ℝ => -(lam μ y * k)) (-(-(lam μ y) / μ * k)) y :=
                  ((hLd y).mul_const k).neg
                have := h1.exp
                convert this using 1; ring
              have hLtop : Tendsto (fun y => lam μ y) atTop (nhds 0) := by
                have : Tendsto (fun y : ℝ => -(y / μ + Real.eulerMascheroniConstant)) atTop atBot := by
                  apply tendsto_neg_atTop_atBot.comp
                  exact tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_div_const hμ)
                exact Real.tendsto_exp_atBot.comp this
              have hLbot : Tendsto (fun y => lam μ y) atBot atTop := by
                have : Tendsto (fun y : ℝ => -(y / μ + Real.eulerMascheroniConstant)) atBot atTop := by
                  apply tendsto_neg_atBot_atTop.comp
                  exact tendsto_atBot_add_const_right _ _ (tendsto_id.atBot_div_const hμ)
                exact Real.tendsto_exp_atTop.comp this
              have hEtop : ∀ k, Tendsto (fun y => Real.exp (-(lam μ y * k))) atTop (nhds 1) := by
                intro k
                have := ((hLtop.mul_const k).neg).rexp
                simpa using this
              have hEbot : ∀ k, 0 < k → Tendsto (fun y => Real.exp (-(lam μ y * k))) atBot (nhds 0) := by
                intro k hk
                exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hLbot.atTop_mul_const hk))
              have hIntIoi : ∀ k, 0 < k → ∀ t, IntegrableOn
                  (fun y => k / μ * lam μ y * Real.exp (-(lam μ y * k))) (Ioi t) := by
                intro k hk t
                exact integrableOn_Ioi_deriv_of_nonneg (hEd k t).continuousAt.continuousWithinAt
                  (fun y _ => hEd k y) (fun y _ => by have := hLpos y; positivity) (hEtop k)
              have hIoi : ∀ k, 0 < k → ∀ t, ∫ y in Ioi t, k / μ * lam μ y * Real.exp (-(lam μ y * k))
                  = 1 - Real.exp (-(lam μ t * k)) := by
                intro k hk t
                exact integral_Ioi_of_hasDerivAt_of_tendsto (hEd k t).continuousAt.continuousWithinAt
                  (fun y _ => hEd k y) (hIntIoi k hk t) (hEtop k)
              have hSc : Sᶜ.Nonempty := by
                by_contra h
                rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
                exact hS h
              have hV : 0 < outsidePref (pref μ a) S := Finset.sum_pos (fun j _ => hv j) hSc
              set V := outsidePref (pref μ a) S with hVdef
              set wf : ℝ → ℝ := fun y => V / μ * lam μ y * Real.exp (-(lam μ y * V)) with hwf
              have hΦ : ∀ u, searchGain μ (pref μ a) S u = ∫ y in Ioi u, (y - u) * wf y := fun u => rfl
              have hwnn : ∀ y, 0 ≤ wf y := fun y => by have := hLpos y; simp only [hwf]; positivity
              have hwint : ∀ t, IntegrableOn wf (Ioi t) := hIntIoi V hV
              have hI : ∀ t, ∫ y in Ioi t, wf y = 1 - Real.exp (-(lam μ t * V)) := hIoi V hV
              have hywint : ∀ t, IntegrableOn (fun y => y * wf y) (Ioi t) := by
                intro t
                have hcont : Continuous (fun y => y * wf y) := by
                  simp only [hwf]; fun_prop
                refine integrable_of_isBigO_exp_neg (b := 1 / (2 * μ)) (by positivity) hcont.continuousOn ?_
                refine Asymptotics.IsBigO.of_bound (2 * V * Real.exp (-Real.eulerMascheroniConstant)) ?_
                filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
                set q := Real.exp (-(1 / (2 * μ)) * y) with hqdef
                have hq : 0 < q := Real.exp_pos _
                have hL : lam μ y = q * q * Real.exp (-Real.eulerMascheroniConstant) := by
                  rw [hqdef, ← Real.exp_add, ← Real.exp_add]
                  show Real.exp (-(y / μ + Real.eulerMascheroniConstant)) = _
                  congr 1; field_simp; ring
                have hyq : y * q ≤ 2 * μ := by
                  have h1 := Real.add_one_le_exp (y / (2 * μ))
                  have h2 : Real.exp (y / (2 * μ)) * q = 1 := by
                    rw [hqdef, ← Real.exp_add]
                    rw [show y / (2 * μ) + -(1 / (2 * μ)) * y = 0 by ring]
                    exact Real.exp_zero
                  have h3 : y = 2 * μ * (y / (2 * μ)) := by field_simp
                  have h4 : y / (2 * μ) * q ≤ (Real.exp (y / (2 * μ)) - 1) * q :=
                    mul_le_mul_of_nonneg_right (by linarith) hq.le
                  have h5 : y * q = 2 * μ * (y / (2 * μ) * q) := by rw [h3]; field_simp
                  rw [h5]
                  nlinarith
                have hE : Real.exp (-(lam μ y * V)) ≤ 1 := by
                  have := hLpos y
                  calc Real.exp (-(lam μ y * V)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
                    _ = 1 := Real.exp_zero
                rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hy (hwnn y)), abs_of_pos hq]
                simp only [hwf]
                set E := Real.exp (-(lam μ y * V)) with hEdef
                rw [hL]
                have he := Real.exp_pos (-Real.eulerMascheroniConstant)
                have hE0 : 0 < E := Real.exp_pos _
                calc y * (V / μ * (q * q * Real.exp (-Real.eulerMascheroniConstant)) * E)
                    ≤ y * (V / μ * (q * q * Real.exp (-Real.eulerMascheroniConstant))) := by
                      apply mul_le_mul_of_nonneg_left _ hy
                      have : 0 ≤ V / μ * (q * q * Real.exp (-Real.eulerMascheroniConstant)) := by positivity
                      nlinarith
                  _ = (y * q) * (V / μ * q * Real.exp (-Real.eulerMascheroniConstant)) := by ring
                  _ ≤ (2 * μ) * (V / μ * q * Real.exp (-Real.eulerMascheroniConstant)) :=
                      mul_le_mul_of_nonneg_right hyq (by positivity)
                  _ = 2 * V * Real.exp (-Real.eulerMascheroniConstant) * q := by field_simp
              have hint2 : ∀ u t, IntegrableOn (fun y => (y - u) * wf y) (Ioi t) := by
                intro u t
                have := (hywint t).sub ((hwint t).const_mul u)
                refine this.congr_fun (fun y _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
              have hEV1 : ∀ t, Real.exp (-(lam μ t * V)) < 1 := fun t => by
                have := hLpos t
                calc Real.exp (-(lam μ t * V)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
                  _ = 1 := Real.exp_zero
              have hsplitw : ∀ u u', u < u' → ∫ y in Ioi u, wf y = (∫ y in Ioc u u', wf y) + ∫ y in Ioi u', wf y := by
                intro u u' h
                rw [← Set.Ioc_union_Ioi_eq_Ioi h.le]
                exact setIntegral_union (Set.Ioc_disjoint_Ioi_same) measurableSet_Ioi
                  ((hwint u).mono_set Set.Ioc_subset_Ioi_self) (hwint u')
              have hsplit : ∀ u u', u < u' → searchGain μ (pref μ a) S u =
                  (∫ y in Ioc u u', (y - u) * wf y) + searchGain μ (pref μ a) S u' + (u' - u) * ∫ y in Ioi u', wf y := by
                intro u u' h
                rw [hΦ, hΦ, ← Set.Ioc_union_Ioi_eq_Ioi h.le]
                rw [setIntegral_union (Set.Ioc_disjoint_Ioi_same) measurableSet_Ioi
                  ((hint2 u u).mono_set Set.Ioc_subset_Ioi_self) (hint2 u u')]
                have : ∫ y in Ioi u', (y - u) * wf y = ∫ y in Ioi u', ((y - u') * wf y + (u' - u) * wf y) := by
                  congr 1; ext y; ring
                rw [this, integral_add (hint2 u' u') ((hwint u').const_mul _), integral_const_mul]
                ring
              have hIocnn : ∀ u u', 0 ≤ ∫ y in Ioc u u', (y - u) * wf y := by
                intro u u'
                exact setIntegral_nonneg measurableSet_Ioc (fun y hy => mul_nonneg (by linarith [hy.1]) (hwnn y))
              have hIocle : ∀ u u', u < u' → ∫ y in Ioc u u', (y - u) * wf y ≤ (u' - u) * ∫ y in Ioc u u', wf y := by
                intro u u' h
                rw [← integral_const_mul]
                exact setIntegral_mono_on ((hint2 u u).mono_set Set.Ioc_subset_Ioi_self)
                  (((hwint u).mono_set Set.Ioc_subset_Ioi_self).const_mul _) measurableSet_Ioc
                  (fun y hy => mul_le_mul_of_nonneg_right (by linarith [hy.2]) (hwnn y))
              have hanti : ∀ u u', u < u' → searchGain μ (pref μ a) S u' < searchGain μ (pref μ a) S u := by
                intro u u' h
                rw [hsplit u u' h, hI u']
                have := hIocnn u u'
                have := hEV1 u'
                have : 0 < (u' - u) * (1 - Real.exp (-(lam μ u' * V))) := mul_pos (by linarith) (by linarith)
                linarith
              have hlip : ∀ u u', u < u' → searchGain μ (pref μ a) S u ≤ searchGain μ (pref μ a) S u' + (u' - u) := by
                intro u u' h
                have e1 := hsplit u u' h
                have e2 := hsplitw u u' h
                have e3 := hIocle u u' h
                have e4 := hI u
                have : (u' - u) * ((∫ y in Ioc u u', wf y) + ∫ y in Ioi u', wf y) ≤ (u' - u) := by
                  rw [← e2, e4]
                  have := Real.exp_pos (-(lam μ u * V))
                  nlinarith
                nlinarith
              have hΦnn : ∀ u, 0 ≤ searchGain μ (pref μ a) S u := fun u =>
                setIntegral_nonneg measurableSet_Ioi (fun y hy => mul_nonneg (by linarith [show u < y from hy]) (hwnn y))
              -- a point where Φ > b
              obtain ⟨ulo, hulo⟩ : ∃ u, b < searchGain μ (pref μ a) S u := by
                set I0 := 1 - Real.exp (-(lam μ 0 * V))
                have hI0 : 0 < I0 := by have := hEV1 0; simp only [I0]; linarith
                refine ⟨-(b / I0) - 1, ?_⟩
                have h := hsplit (-(b / I0) - 1) 0 (by have : 0 < b / I0 := div_pos hb hI0; linarith)
                rw [hI 0] at h
                have := hIocnn (-(b / I0) - 1) 0
                have := hΦnn 0
                have : (0 - (-(b / I0) - 1)) * I0 = b + I0 := by field_simp; ring
                linarith
              -- a point where Φ < b
              obtain ⟨uhi, huhi⟩ : ∃ u, searchGain μ (pref μ a) S u < b := by
                have hT := tendsto_setIntegral_of_antitone (μ := volume) (f := fun y => y * wf y)
                  (s := fun m : ℕ => Ioi (m : ℝ)) (fun m => measurableSet_Ioi)
                  (fun m m' h => Set.Ioi_subset_Ioi (by exact_mod_cast h)) ⟨0, hywint _⟩
                have hempty : (⋂ m : ℕ, Ioi (m : ℝ)) = ∅ := by
                  ext y; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_forall, not_lt]
                  exact ⟨⌈y⌉₊, Nat.le_ceil y⟩
                rw [hempty, Measure.restrict_empty, integral_zero_measure] at hT
                obtain ⟨m, hm⟩ := (hT.eventually (gt_mem_nhds hb)).exists
                refine ⟨m, lt_of_le_of_lt ?_ hm⟩
                rw [hΦ]
                exact setIntegral_mono_on (hint2 _ _) (hywint _) measurableSet_Ioi
                  (fun y hy => mul_le_mul_of_nonneg_right (by have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith) (hwnn y))
              set c := Ubar μ (pref μ a) S b with hc
              have hTne : ({u | searchGain μ (pref μ a) S u ≤ b} : Set ℝ).Nonempty := ⟨uhi, le_of_lt huhi⟩
              have hTbdd : BddBelow ({u | searchGain μ (pref μ a) S u ≤ b} : Set ℝ) := by
                refine ⟨ulo, fun u hu => ?_⟩
                by_contra h
                push_neg at h
                have := hanti u ulo h
                simp only [Set.mem_setOf_eq] at hu
                linarith
              have hcle : searchGain μ (pref μ a) S c ≤ b := by
                apply le_of_forall_pos_lt_add
                intro ε hε
                obtain ⟨u, hu, hlt⟩ := exists_lt_of_csInf_lt hTne (show c < c + ε by linarith)
                have hcu : c ≤ u := csInf_le hTbdd hu
                simp only [Set.mem_setOf_eq] at hu
                rcases hcu.lt_or_eq with h | h
                · have := hlip c u h; linarith
                · rw [h]; linarith
              have hcge : b ≤ searchGain μ (pref μ a) S c := by
                by_contra h
                push_neg at h
                set δ := b - searchGain μ (pref μ a) S c
                have hδ : 0 < δ := by simp only [δ]; linarith
                have := hlip (c - δ) c (by linarith)
                have hmem : c - δ ∈ ({u | searchGain μ (pref μ a) S u ≤ b} : Set ℝ) := by
                  simp only [Set.mem_setOf_eq]; simp only [δ] at this ⊢; linarith
                have := csInf_le hTbdd hmem
                have : c ≤ c - δ := this
                linarith
              have hceq : searchGain μ (pref μ a) S c = b := le_antisymm hcle hcge
              have hiff : ∀ x, searchGain μ (pref μ a) S x < b ↔ c < x := by
                intro x
                constructor
                · intro hx
                  by_contra h; push_neg at h
                  rcases h.lt_or_eq with h | h
                  · have := hanti x c h; linarith
                  · rw [h] at hx; linarith
                · intro hx; have := hanti c x hx; linarith
              refine ⟨⟨hceq, fun u hu => ?_⟩, ?_⟩
              · rcases lt_trichotomy u c with h | h | h
                · have := hanti u c h; linarith
                · exact h
                · have := hanti c u h; linarith
              intro i hi
              have hvi := hv i
              have hW : 0 < (∑ j ∈ S, pref μ a j) + pref0 μ u0 :=
                add_pos (Finset.sum_pos (fun j _ => hv j) ⟨i, hi⟩) (Real.exp_pos _)
              set W := (∑ j ∈ S, pref μ a j) + pref0 μ u0 with hWdef
              have hWge : pref μ a i ≤ ∑ j ∈ S, pref μ a j :=
                Finset.single_le_sum (fun j _ => (hv j).le) hi
              set R := (W - pref μ a i) / pref μ a i with hR
              have hR1 : R + 1 = W / pref μ a i := by simp only [hR]; field_simp; ring
              have hR1pos : 0 < R + 1 := by rw [hR1]; positivity
              have hpdfI : ∀ x, IntegrableOn (fun y => 1 / μ * lam μ y * Real.exp (-(lam μ y * 1))) (Iic x) := by
                intro x
                refine integrableOn_Iic_of_intervalIntegral_norm_bounded (l := atTop) (a := fun m : ℕ => x - m) 1 x ?_ ?_ ?_
                · intro m
                  exact intervalIntegral.integrableOn_deriv_of_nonneg (fun y _ => (hEd 1 y).continuousAt.continuousWithinAt)
                    (fun y _ => hEd 1 y) (fun y _ => by have := hLpos y; positivity)
                · simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left atTop x
                    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
                · filter_upwards with m
                  have hm : x - (m : ℝ) ≤ x := by have := Nat.cast_nonneg (α := ℝ) m; linarith
                  rw [intervalIntegral.integral_congr (g := fun y => 1 / μ * lam μ y * Real.exp (-(lam μ y * 1)))
                    (fun y _ => Real.norm_of_nonneg (by have := hLpos y; positivity))]
                  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hEd 1 y)
                    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hm).2
                      (intervalIntegral.integrableOn_deriv_of_nonneg (fun y _ => (hEd 1 y).continuousAt.continuousWithinAt)
                      (fun y _ => hEd 1 y) (fun y _ => by have := hLpos y; positivity)))]
                  have := Real.exp_pos (-(lam μ (x - m) * 1))
                  have := Real.exp_pos (-(lam μ x * 1))
                  have : Real.exp (-(lam μ x * 1)) ≤ 1 := by
                    have := hLpos x
                    calc Real.exp (-(lam μ x * 1)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
                      _ = 1 := Real.exp_zero
                  linarith
              have hpdfm : Measurable (fun y => ENNReal.ofReal (1 / μ * lam μ y * Real.exp (-(lam μ y * 1)))) := by
                apply ENNReal.measurable_ofReal.comp
                exact (Continuous.measurable (by
                  have := hLc
                  exact (continuous_const.mul this).mul (Real.continuous_exp.comp ((this.mul continuous_const).neg))))
              have hGd : G = volume.withDensity (fun y => ENNReal.ofReal (1 / μ * lam μ y * Real.exp (-(lam μ y * 1)))) := by
                refine Measure.ext_of_Iic G _ (fun x => ?_)
                rw [← ProbabilityTheory.ofReal_cdf, hG x, withDensity_apply _ measurableSet_Iic,
                  ← ofReal_integral_eq_lintegral_ofReal (hpdfI x)
                    (Filter.Eventually.of_forall (fun y => by have := hLpos y; positivity)),
                  integral_Iic_of_hasDerivAt_of_tendsto (hEd 1 x).continuousAt.continuousWithinAt
                    (fun y _ => hEd 1 y) (hpdfI x) (hEbot 1 one_pos)]
                simp only [gumbelCdf, mul_one, sub_zero]
                rfl
              have hAC : G ≪ volume := by rw [hGd]; exact withDensity_absolutelyContinuous _ _
              have hGIio : ∀ t, G (Iio t) = ENNReal.ofReal (Real.exp (-(lam μ t * 1))) := by
                intro t
                rw [measure_congr (hAC.ae_eq Iio_ae_eq_Iic), ← ProbabilityTheory.ofReal_cdf, hG t]
                simp only [gumbelCdf, mul_one]
                rfl
              have hshift : ∀ z x y, lam μ (z + x - y) = lam μ z * (Real.exp (y / μ) / Real.exp (x / μ)) := by
                intro z x y
                simp only [lam]
                rw [← Real.exp_sub, ← Real.exp_add]; congr 1; ring
              have hB : ∫⁻ z in Ioi (c - a i), ENNReal.ofReal (Real.exp (-(lam μ z * R))) ∂G =
                  ENNReal.ofReal ((1 - Real.exp (-(lam μ (c - a i) * (R + 1)))) / (R + 1)) := by
                have hgm : Measurable (fun z => ENNReal.ofReal (Real.exp (-(lam μ z * R)))) := by
                  apply ENNReal.measurable_ofReal.comp
                  exact (Real.continuous_exp.comp ((hLc.mul continuous_const).neg)).measurable
                rw [hGd, restrict_withDensity measurableSet_Ioi, lintegral_withDensity_eq_lintegral_mul _ hpdfm hgm]
                have hfun : ∀ z, ((fun y => ENNReal.ofReal (1 / μ * lam μ y * Real.exp (-(lam μ y * 1)))) *
                    (fun z => ENNReal.ofReal (Real.exp (-(lam μ z * R))))) z =
                    ENNReal.ofReal (1 / (R + 1) * ((R + 1) / μ * lam μ z * Real.exp (-(lam μ z * (R + 1))))) := by
                  intro z
                  simp only [Pi.mul_apply]
                  rw [← ENNReal.ofReal_mul (by have := hLpos z; positivity)]
                  congr 1
                  rw [show -(lam μ z * (R + 1)) = -(lam μ z * 1) + -(lam μ z * R) by ring, Real.exp_add]
                  field_simp
                simp_rw [hfun]
                rw [← ofReal_integral_eq_lintegral_ofReal ((hIntIoi (R + 1) hR1pos _).const_mul _)
                    (Filter.Eventually.of_forall (fun y => by have := hLpos y; positivity)),
                  integral_const_mul, hIoi (R + 1) hR1pos]
                congr 1; ring
              have hA : overlapProb G μ a u0 b S i =
                  (∫⁻ z in Ioi (c - a i), ENNReal.ofReal (Real.exp (-(lam μ z * R))) ∂G).toReal := by
                obtain ⟨p, hp⟩ : ∃ p : Option (Fin n) → Prop, p = fun j => j = some i := ⟨_, rfl⟩
                have hpi : ∀ j, p j ↔ j = some i := fun j => by rw [hp]
                let i0 : {j // p j} := ⟨some i, (hpi _).2 rfl⟩
                let s : ℝ → Option (Fin n) → Set ℝ := fun z j =>
                  Option.elim j (Iio (z + a i - u0)) (fun k => if k ∈ S then Iio (z + a i - a k) else univ)
                let r : Option (Fin n) → ℝ := fun j =>
                  Option.elim j (pref0 μ u0 / pref μ a i) (fun k => if k ∈ S then pref μ a k / pref μ a i else 0)
                let B : Set ((({j // p j}) → ℝ) × ({j // ¬ p j} → ℝ)) :=
                  {x | c - a i < x.1 i0 ∧ ∀ j : {j // ¬ p j}, x.2 j ∈ s (x.1 i0) j.1}
                have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Option (Fin n) => G) p
                have hAB : {ζ : Option (Fin n) → ℝ | (∀ j ∈ S, j ≠ i →
                      utility a u0 ζ (some j) < utility a u0 ζ (some i)) ∧
                    utility a u0 ζ none < utility a u0 ζ (some i) ∧
                    searchGain μ (pref μ a) S (utility a u0 ζ (some i)) < b} =
                    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Option (Fin n) => ℝ) p ⁻¹' B := by
                  ext ζ
                  show _ ↔ (c - a i < ζ (some i) ∧ ∀ j : {j // ¬ p j}, ζ j.1 ∈ s (ζ (some i)) j.1)
                  simp only [Set.mem_setOf_eq, utility, netUtility, hiff]
                  constructor
                  · rintro ⟨h1, h2, h3⟩
                    refine ⟨by linarith, fun j => ?_⟩
                    rcases j with ⟨_ | k, hk⟩
                    · simp only [s, Option.elim, Set.mem_Iio]; linarith
                    · by_cases hkS : k ∈ S
                      · have hki : k ≠ i := fun h => hk ((hpi _).2 (by rw [h]))
                        have := h1 k hkS hki
                        simp only [s, Option.elim, hkS, if_true, Set.mem_Iio]; linarith
                      · simp only [s, Option.elim, hkS, if_false, Set.mem_univ]
                  · rintro ⟨h3, h⟩
                    refine ⟨fun k hkS hki => ?_, ?_, by linarith⟩
                    · have := h ⟨some k, fun h' => hki (Option.some_injective _ ((hpi _).1 h'))⟩
                      simp only [s, Option.elim, hkS, if_true, Set.mem_Iio] at this; linarith
                    · have := h ⟨none, fun h' => Option.some_ne_none i ((hpi _).1 h').symm⟩
                      simp only [s, Option.elim, Set.mem_Iio] at this; linarith
                have hBm : MeasurableSet B := by
                  have hB' : B = {x | c - a i < x.1 i0} ∩ ⋂ j : {j // ¬ p j}, {x | x.2 j ∈ s (x.1 i0) j.1} := by
                    ext x; simp only [B, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
                  rw [hB']
                  have hm1 : Measurable (fun x : (({j // p j}) → ℝ) × ({j // ¬ p j} → ℝ) => x.1 i0) :=
                    (measurable_pi_apply i0).comp measurable_fst
                  refine (measurableSet_lt measurable_const hm1).inter (MeasurableSet.iInter fun j => ?_)
                  have hm2 : Measurable (fun x : (({j // p j}) → ℝ) × ({j // ¬ p j} → ℝ) => x.2 j) :=
                    (measurable_pi_apply j).comp measurable_snd
                  rcases j with ⟨_ | k, hk⟩
                  · simp only [s, Option.elim, Set.mem_Iio]
                    exact measurableSet_lt hm2 ((hm1.add_const _).sub_const _)
                  · by_cases hkS : k ∈ S
                    · simp only [s, Option.elim, hkS, if_true, Set.mem_Iio]
                      exact measurableSet_lt hm2 ((hm1.add_const _).sub_const _)
                    · simp only [s, Option.elim, hkS, if_false, Set.mem_univ, Set.setOf_true]
                      exact MeasurableSet.univ
                have hGs : ∀ z j, G (s z j) = ENNReal.ofReal (Real.exp (-(lam μ z * r j))) := by
                  intro z j
                  rcases j with _ | k
                  · simp only [s, r, Option.elim]
                    rw [hGIio, hshift, mul_one]; rfl
                  · by_cases hkS : k ∈ S
                    · simp only [s, r, Option.elim, hkS, if_true]
                      rw [hGIio, hshift, mul_one]; rfl
                    · simp only [s, r, Option.elim, hkS, if_false, measure_univ, mul_zero, neg_zero,
                        Real.exp_zero, ENNReal.ofReal_one]
                have hsumr : ∑ j : {j // ¬ p j}, r j.1 = R := by
                  have h1 := Fintype.sum_subtype_add_sum_subtype p r
                  rw [Fintype.sum_eq_single i0 (fun j hj => absurd (Subtype.ext ((hpi _).1 j.2)) hj), Fintype.sum_option] at h1
                  have hri : r i0.1 = 1 := by
                    show r (some i) = 1
                    simp only [r, Option.elim, hi, if_true]; exact div_self hvi.ne'
                  rw [hri] at h1
                  have h2 : ∑ k : Fin n, r (some k) = (∑ k ∈ S, pref μ a k) / pref μ a i := by
                    simp only [r, Option.elim]
                    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
                  rw [h2] at h1
                  have h3 : r none = pref0 μ u0 / pref μ a i := rfl
                  rw [h3] at h1
                  rw [hR]
                  have : W = (∑ k ∈ S, pref μ a k) + pref0 μ u0 := hWdef
                  rw [this]
                  have hx : ∑ j : {j // ¬ p j}, r j.1 = pref0 μ u0 / pref μ a i + (∑ k ∈ S, pref μ a k) / pref μ a i - 1 := by
                    linarith
                  rw [hx]; field_simp; ring
                have hslice : ∀ x1 : {j // p j} → ℝ, Measure.pi (fun _ : {j // ¬ p j} => G) (Prod.mk x1 ⁻¹' B) =
                    (Ioi (c - a i)).indicator (fun z => ENNReal.ofReal (Real.exp (-(lam μ z * R)))) (x1 i0) := by
                  intro x1
                  by_cases hx : c - a i < x1 i0
                  · have : Prod.mk x1 ⁻¹' B = Set.univ.pi (fun j : {j // ¬ p j} => s (x1 i0) j.1) := by
                      ext x2; simp [B, hx]
                    rw [this, Measure.pi_pi, Set.indicator_of_mem (show x1 i0 ∈ Ioi (c - a i) from hx)]
                    simp_rw [hGs]
                    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
                    congr 2
                    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hsumr]
                  · have : Prod.mk x1 ⁻¹' B = ∅ := by
                      ext x2; simp [B, hx]
                    rw [this, measure_empty, Set.indicator_of_notMem (show x1 i0 ∉ Ioi (c - a i) from hx)]
                show (Measure.pi (fun _ : Option (Fin n) => G) _).toReal = _
                rw [hAB, hmp.measure_preimage_equiv, Measure.prod_apply hBm]
                simp_rw [hslice]
                congr 1
                rw [← lintegral_indicator measurableSet_Ioi]
                have hgm : Measurable (fun z => ENNReal.ofReal (Real.exp (-(lam μ z * R)))) := by
                  apply ENNReal.measurable_ofReal.comp
                  exact (Real.continuous_exp.comp ((hLc.mul continuous_const).neg)).measurable
                exact (measurePreserving_eval (fun _ : {j // p j} => G) i0).lintegral_comp
                  (hgm.indicator measurableSet_Ioi)
              have hlamc : lam μ (c - a i) = lam μ c * pref μ a i := by
                show Real.exp _ = Real.exp _ * Real.exp _
                rw [← Real.exp_add]; congr 1; ring
              rw [hA, hB, ENNReal.toReal_ofReal]
              · rw [hR1, hlamc]
                simp only [share, H, pref0] at *
                rw [show lam μ c * pref μ a i * (W / pref μ a i) = lam μ c * (pref0 μ u0 + ∑ j ∈ S, pref μ a j) by
                  simp only [hWdef, pref0]; field_simp; ring]
                simp only [hWdef, pref0]
                field_simp
              · apply div_nonneg _ hR1pos.le
                have := Real.exp_pos (-(lam μ (c - a i) * (R + 1)))
                have := hLpos (c - a i)
                have : Real.exp (-(lam μ (c - a i) * (R + 1))) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
                rw [Real.exp_zero] at this; linarith
