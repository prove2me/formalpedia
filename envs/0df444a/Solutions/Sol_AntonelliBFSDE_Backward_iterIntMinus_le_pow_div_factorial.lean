-- Prove2me | solution 1 for AntonelliBFSDE.Backward.iterIntMinus_le_pow_div_factorial
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:31:31.085125+00:00
-- url     : https://prove2.me/submissions/6b6e9639-7ffa-4f7a-812c-38aaff9fc99e

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal


namespace AntonelliBFSDE.Backward

lemma d36_level (ν : Measure ℝ) [IsFiniteMeasure ν] (x : ℝ) (hx : 0 < x) :
    ν {s | x < (ν (Set.Iio s)).toReal} ≤ ENNReal.ofReal ((ν Set.univ).toReal - x) := by
  set F : ℝ → ℝ := fun s => (ν (Set.Iio s)).toReal with hF
  have hFmono : Monotone F := fun u v h =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iio_subset_Iio h))
  set S := {s | x < F s} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hFmono.measurable
  by_cases hS : S = ∅
  · rw [hS]; simp
  obtain ⟨s0, hs0⟩ := Set.nonempty_iff_ne_empty.mpr hS
  have hupper : ∀ u v, u ∈ S → u ≤ v → v ∈ S := fun u v hu huv =>
    lt_of_lt_of_le hu (hFmono huv)
  have hcompl : x ≤ (ν Sᶜ).toReal := by
    by_cases hSc : Sᶜ = ∅
    · exfalso
      have hall : ∀ s, x < F s := by
        intro s
        by_contra h
        have : s ∈ Sᶜ := h
        rw [hSc] at this; exact this
      have ht := tendsto_measure_iInter_atTop (μ := ν) (s := fun k : ℕ => Set.Iio (-(k:ℝ)))
        (fun i => measurableSet_Iio.nullMeasurableSet)
        (fun i j hij => Set.Iio_subset_Iio (by simp; exact_mod_cast hij))
        ⟨0, measure_ne_top _ _⟩
      have hempty : (⋂ k : ℕ, Set.Iio (-(k:ℝ))) = ∅ := by
        ext y
        simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_forall,
          not_lt]
        obtain ⟨k, hk⟩ := exists_nat_ge (-y)
        exact ⟨k, by linarith⟩
      rw [hempty, measure_empty] at ht
      have hlt : ∀ᶠ k in atTop, (ν ∘ fun k : ℕ => Set.Iio (-(k:ℝ))) k < ENNReal.ofReal x :=
        ht.eventually (gt_mem_nhds (by simpa using hx))
      obtain ⟨k, hk⟩ := hlt.exists
      have h1 := hall (-(k:ℝ))
      simp only [Function.comp_apply] at hk
      have : (ν (Set.Iio (-(k:ℝ)))).toReal < x := by
        rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]
        exact hk
      exact absurd h1 (not_lt.mpr this.le)
    have hne : Sᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr hSc
    have hbdd : BddAbove Sᶜ := ⟨s0, fun u hu => by
      by_contra h
      exact hu (hupper s0 u hs0 (le_of_lt (not_le.mp h)))⟩
    set c := sSup Sᶜ
    have hIio : Set.Iio c ⊆ Sᶜ := by
      intro u hu
      obtain ⟨u', hu', huu'⟩ := exists_lt_of_lt_csSup hne hu
      intro huS
      exact hu' (hupper u u' huS huu'.le)
    by_cases hc : c ∈ S
    · exact le_trans (le_of_lt hc)
        (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hIio))
    · have hIic : Set.Iic c ⊆ Sᶜ := by
        intro u hu
        rcases eq_or_lt_of_le (Set.mem_Iic.mp hu) with h | h
        · rw [h]; exact hc
        · exact hIio h
      have ht := tendsto_measure_iInter_atTop (μ := ν)
        (s := fun k : ℕ => Set.Iio (c + 1 / ((k:ℝ) + 1)))
        (fun i => measurableSet_Iio.nullMeasurableSet)
        (fun i j hij => Set.Iio_subset_Iio (by
          have : (i:ℝ) + 1 ≤ (j:ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
          have := one_div_le_one_div_of_le (by positivity) this
          linarith))
        ⟨0, measure_ne_top _ _⟩
      have hinter : (⋂ k : ℕ, Set.Iio (c + 1 / ((k:ℝ) + 1))) = Set.Iic c := by
        ext y
        simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_Iic]
        constructor
        · intro h
          by_contra hy
          rw [not_le] at hy
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
          have := h k
          linarith
        · intro hy k
          have : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
          linarith
      rw [hinter] at ht
      have ht' := (ENNReal.tendsto_toReal (measure_ne_top ν (Set.Iic c))).comp ht
      have hmem : ∀ k : ℕ, x ≤ ((ENNReal.toReal ∘ (ν ∘ fun k : ℕ =>
          Set.Iio (c + 1 / ((k:ℝ) + 1))))) k := by
        intro k
        have hgt : c < c + 1 / ((k:ℝ) + 1) := by
          have : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
          linarith
        have hin : c + 1 / ((k:ℝ) + 1) ∈ S := by
          by_contra h
          have := le_csSup hbdd h
          linarith
        exact le_of_lt hin
      have hle : x ≤ (ν (Set.Iic c)).toReal := ge_of_tendsto' ht' hmem
      exact le_trans hle (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hIic))
  have hsum := measure_add_measure_compl (μ := ν) hSm
  have hreal : (ν S).toReal + (ν Sᶜ).toReal = (ν Set.univ).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum]
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν S)]
  exact ENNReal.ofReal_le_ofReal (by linarith)


lemma d36_poly_integral (M : ℝ) (hM : 0 ≤ M) (m : ℕ) :
    ∫ x in Set.Ioc (0:ℝ) M, ((m:ℝ) + 1) * x ^ m * (M - x) = M ^ (m + 2) / ((m:ℝ) + 2) := by
  rw [← intervalIntegral.integral_of_le hM]
  have : (fun x : ℝ => ((m:ℝ) + 1) * x ^ m * (M - x)) =
      fun x => (((m:ℝ) + 1) * M) * x ^ m - ((m:ℝ) + 1) * x ^ (m + 1) := by
    funext x; ring
  rw [this, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  · push_cast
    field_simp
    ring
  · exact (by fun_prop : Continuous fun x : ℝ => (((m:ℝ) + 1) * M) * x ^ m).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x : ℝ => ((m:ℝ) + 1) * x ^ (m + 1)).intervalIntegrable _ _

lemma d36_key (ν : Measure ℝ) [IsFiniteMeasure ν] (n : ℕ) :
    ∫ s, (ν (Set.Iio s)).toReal ^ n ∂ν ≤ (ν Set.univ).toReal ^ (n + 1) / ((n:ℝ) + 1) := by
  set F : ℝ → ℝ := fun s => (ν (Set.Iio s)).toReal with hF
  have hFmono : Monotone F := fun u v h =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iio_subset_Iio h))
  set M := (ν Set.univ).toReal with hMdef
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  rcases n with _ | m
  · simp [M, Measure.real]
  have hFnn : ∀ s, 0 ≤ F s := fun s => ENNReal.toReal_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun s => pow_nonneg (hFnn s) _)
    ((hFmono.measurable.pow_const _).aestronglyMeasurable)]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul ν (f := F)
    (g := fun t => ((m:ℝ) + 1) * t ^ m) (Eventually.of_forall hFnn)
    hFmono.measurable.aemeasurable
    (fun t _ => (by fun_prop : Continuous fun t : ℝ => ((m:ℝ) + 1) * t ^ m).intervalIntegrable _ _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) => by positivity)
  have hint : ∀ s, ∫ t in (0:ℝ)..F s, ((m:ℝ) + 1) * t ^ m = F s ^ (m + 1) := by
    intro s
    rw [intervalIntegral.integral_const_mul, integral_pow]
    field_simp
    simp
  simp_rw [hint] at hlc
  rw [hlc]
  calc ∫⁻ t in Set.Ioi 0, ν {a | t < F a} * ENNReal.ofReal (((m:ℝ) + 1) * t ^ m)
      ≤ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (((m:ℝ) + 1) * t ^ m * (M - t)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t (ht : 0 < t)
        have h0 : (0:ℝ) ≤ ((m:ℝ) + 1) * t ^ m := by positivity
        rw [ENNReal.ofReal_mul h0, mul_comm (ν _)]
        exact mul_le_mul_of_nonneg_left (d36_level ν t ht) zero_le
    _ ≤ ∫⁻ t, (Set.Ioc 0 M).indicator
          (fun t => ENNReal.ofReal (((m:ℝ) + 1) * t ^ m * (M - t))) t := by
        refine le_trans (setLIntegral_mono' measurableSet_Ioi ?_) (setLIntegral_le_lintegral _ _)
        intro t (ht : 0 < t)
        by_cases htM : t ≤ M
        · rw [Set.indicator_of_mem (show t ∈ Set.Ioc 0 M from ⟨ht, htM⟩)]
        · rw [Set.indicator_of_notMem (fun h => htM h.2)]
          apply le_of_eq
          apply ENNReal.ofReal_of_nonpos
          have : 0 ≤ ((m:ℝ) + 1) * t ^ m := by positivity
          nlinarith [not_le.mp htM]
    _ = ∫⁻ t in Set.Ioc 0 M, ENNReal.ofReal (((m:ℝ) + 1) * t ^ m * (M - t)) :=
        lintegral_indicator measurableSet_Ioc _
    _ = ENNReal.ofReal (∫ t in Set.Ioc 0 M, ((m:ℝ) + 1) * t ^ m * (M - t)) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact (by fun_prop : Continuous fun t : ℝ => ((m:ℝ) + 1) * t ^ m * (M - t)).integrableOn_Icc.mono_set
            Set.Ioc_subset_Icc_self
        · refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
          have h1 : 0 ≤ ((m:ℝ) + 1) * t ^ m := by have := ht.1.le; positivity
          exact mul_nonneg h1 (sub_nonneg.mpr ht.2)
    _ = ENNReal.ofReal (M ^ (m + 1 + 1) / (((m + 1 : ℕ) : ℝ) + 1)) := by
        rw [d36_poly_integral M hM m]
        push_cast
        ring_nf


lemma d36_measure_Ioc (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0) (r : ℝ≥0) :
    stieltjesMeasureOf a (Set.Ioc 0 r) = ENNReal.ofReal (a r) := by
  have hrc : ∀ x : ℝ, ContinuousWithinAt (a ∘ Real.toNNReal) (Set.Ici x) x := fun x =>
    (ha_rc x.toNNReal).comp continuous_real_toNNReal.continuousWithinAt
      (fun y hy => Real.toNNReal_le_toNNReal hy)
  unfold stieltjesMeasureOf
  rw [dif_pos ha_mono, StieltjesFunction.measure_Ioc, Monotone.stieltjesFunction_eq,
    Monotone.stieltjesFunction_eq, (hrc _).rightLim_eq, (hrc _).rightLim_eq]
  simp [ha_zero]

lemma d36_ind (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0) (n : ℕ) :
    (∀ r, 0 ≤ iterIntMinus a n r) ∧ Monotone (iterIntMinus a n) ∧
      ∀ r, iterIntMinus a n r ≤ a r ^ n / (n.factorial : ℝ) := by
  have ha_nn : ∀ r, 0 ≤ a r := fun r => ha_zero ▸ ha_mono (bot_le (a := r))
  induction n with
  | zero =>
    refine ⟨fun r => by simp [iterIntMinus], fun x y _ => by simp [iterIntMinus],
      fun r => by simp [iterIntMinus]⟩
  | succ n ih =>
    obtain ⟨hnn, hmono, hbd⟩ := ih
    set μ := stieltjesMeasureOf a with hμ
    set f := iterIntMinus a n with hf
    have hstep : ∀ r, iterIntMinus a (n+1) r =
        ∫ s in Set.Ioc (0:ℝ) r, Function.leftLim f s.toNNReal ∂μ := fun r => rfl
    set L : ℝ → ℝ := fun s => Function.leftLim f s.toNNReal with hL
    have hLmono : Monotone L := fun x y h => hmono.leftLim (Real.toNNReal_le_toNNReal h)
    have hLnn : ∀ s, 0 < s → 0 ≤ L s := fun s hs =>
      le_trans (hnn 0) (hmono.le_leftLim (Real.toNNReal_pos.mpr hs))
    have hLle : ∀ (r : ℝ≥0) (s : ℝ), s ≤ r → L s ≤ f r := fun r s hs =>
      hmono.leftLim_le (Real.toNNReal_le_iff_le_coe.mpr hs)
    have hfin : ∀ r : ℝ≥0, μ (Set.Ioc 0 r) < ⊤ := by
      intro r; rw [hμ, d36_measure_Ioc a ha_mono ha_rc ha_zero]; exact ENNReal.ofReal_lt_top
    have hLint : ∀ r : ℝ≥0, IntegrableOn L (Set.Ioc 0 r) μ := fun r =>
      IntegrableOn.of_bound (hfin r) hLmono.measurable.aestronglyMeasurable (f r)
        (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hLnn s hs.1)]; exact hLle r s hs.2)
    refine ⟨?_, ?_, ?_⟩
    · intro r; rw [hstep]; exact setIntegral_nonneg measurableSet_Ioc fun s hs => hLnn s hs.1
    · intro r r' hrr
      rw [hstep, hstep]
      exact setIntegral_mono_set (hLint r')
        (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => hLnn s hs.1)
        (Set.Ioc_subset_Ioc_right (by exact_mod_cast hrr)).eventuallyLE
    · intro r
      rw [hstep]
      set ν := μ.restrict (Set.Ioc 0 r) with hν
      haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (hfin r).ne
      have hνuniv : (ν Set.univ).toReal = a r := by
        rw [hν, Measure.restrict_apply_univ, hμ, d36_measure_Ioc a ha_mono ha_rc ha_zero,
          ENNReal.toReal_ofReal (ha_nn r)]
      have hpt : ∀ s ∈ Set.Ioc (0:ℝ) r,
          L s ≤ (ν (Set.Iio s)).toReal ^ n / (n.factorial : ℝ) := by
        intro s hs
        have hs' : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs.1
        haveI : (𝓝[<] s.toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs'⟩
        show Function.leftLim f s.toNNReal ≤ _
        rw [hmono.leftLim_eq_sSup]
        apply csSup_le (Set.Nonempty.image _ ⟨0, hs'⟩)
        rintro _ ⟨r', hr', rfl⟩
        refine le_trans (hbd r') (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (ha_nn r') ?_ n) (by positivity))
        rw [← ENNReal.toReal_ofReal (ha_nn r'), ← d36_measure_Ioc a ha_mono ha_rc ha_zero]
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        rw [hν, Measure.restrict_apply measurableSet_Iio]
        apply measure_mono
        have hr's : (r':ℝ) < s := by
          have := (Real.lt_toNNReal_iff_coe_lt).mp hr'
          exact this
        intro y hy
        exact ⟨lt_of_le_of_lt hy.2 hr's, hy.1, le_trans hy.2 (le_trans hr's.le hs.2)⟩
      have hGint : IntegrableOn (fun s => (ν (Set.Iio s)).toReal ^ n / (n.factorial : ℝ))
          (Set.Ioc 0 r) μ := by
        have hFmono : Monotone fun s => (ν (Set.Iio s)).toReal := fun u v h =>
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iio_subset_Iio h))
        refine Integrable.of_bound
          ((hFmono.measurable.pow_const n).div_const _).aestronglyMeasurable
          ((ν Set.univ).toReal ^ n / (n.factorial : ℝ)) (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ ENNReal.toReal_nonneg
          (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))) n)
          (by positivity)
      calc ∫ s in Set.Ioc (0:ℝ) r, L s ∂μ
          ≤ ∫ s in Set.Ioc (0:ℝ) r, (ν (Set.Iio s)).toReal ^ n / (n.factorial : ℝ) ∂μ :=
            setIntegral_mono_on (hLint r) hGint measurableSet_Ioc hpt
        _ = (∫ s, (ν (Set.Iio s)).toReal ^ n ∂ν) / (n.factorial : ℝ) := integral_div _ _
        _ ≤ a r ^ (n + 1) / ((n:ℝ) + 1) / (n.factorial : ℝ) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            have := d36_key ν n
            rwa [hνuniv] at this
        _ = a r ^ (n + 1) / ((n + 1).factorial : ℝ) := by
            rw [Nat.factorial_succ]; push_cast; field_simp

theorem d36_core (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0)
    (n : ℕ) (t : ℝ≥0) :
    iterIntMinus a n t ≤ a t ^ n / (n.factorial : ℝ) :=
  (d36_ind a ha_mono ha_rc ha_zero n).2.2 t

end AntonelliBFSDE.Backward

open AntonelliBFSDE.Backward


theorem solution (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0)
    (n : ℕ) (t : ℝ≥0) :
    iterIntMinus a n t ≤ a t ^ n / (n.factorial : ℝ) := by
  exact d36_core a ha_mono ha_rc ha_zero n t
