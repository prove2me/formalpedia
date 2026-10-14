-- Prove2me | solution 1 for AntonelliBFSDE.Backward.iterated_integral_relation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:37:41.001426+00:00
-- url     : https://prove2.me/submissions/b6fc044d-f918-46ea-96d5-ec5ca068aca3

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


lemma d36_intOn_mono (μ : Measure ℝ) (t : ℝ) (hfin : μ (Set.Ioc 0 t) < ⊤) (φ : ℝ → ℝ)
    (hφ : Monotone φ) : IntegrableOn φ (Set.Ioc 0 t) μ :=
  IntegrableOn.of_bound hfin hφ.measurable.aestronglyMeasurable (|φ 0| + |φ t|)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => by
      rw [Real.norm_eq_abs]
      have h1 := hφ hx.1.le
      have h2 := hφ hx.2
      exact abs_le.mpr ⟨by linarith [neg_abs_le (φ 0), abs_nonneg (φ t)],
        by linarith [le_abs_self (φ t), abs_nonneg (φ 0)]⟩)

lemma d36_prod_rule (μ : Measure ℝ) (t : ℝ) (hfin : μ (Set.Ioc 0 t) < ⊤) (φ ψ : ℝ → ℝ)
    (hφ : IntegrableOn φ (Set.Ioc 0 t) μ) (hψ : IntegrableOn ψ (Set.Ioc 0 t) μ) :
    (∫ r in Set.Ioc 0 t, φ r ∂μ) * (∫ s in Set.Ioc 0 t, ψ s ∂μ) =
      ∫ s in Set.Ioc 0 t, (∫ r in Set.Ioo 0 s, φ r ∂μ) * ψ s ∂μ +
        ∫ r in Set.Ioc 0 t, φ r * (∫ s in Set.Ioc 0 r, ψ s ∂μ) ∂μ := by
  set ν := μ.restrict (Set.Ioc 0 t) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin.ne
  have hprod := integral_prod_mul (μ := ν) (ν := ν) φ ψ
  have hint : Integrable (fun z : ℝ × ℝ => φ z.1 * ψ z.2) (ν.prod ν) :=
    Integrable.mul_prod hφ hψ
  set D := {z : ℝ × ℝ | z.1 < z.2} with hDdef
  have hD : MeasurableSet D := measurableSet_lt measurable_fst measurable_snd
  rw [← hprod, ← integral_add_compl hD hint]
  congr 1
  · rw [← integral_indicator hD, integral_prod_symm _ (hint.indicator hD)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have : (fun r => D.indicator (fun z : ℝ × ℝ => φ z.1 * ψ z.2) (r, s)) =
        fun r => (Set.Iio s).indicator φ r * ψ s := by
      funext r
      by_cases h : r < s
      · simp [D, h]
      · simp [D, h]
    simp only [this]
    rw [integral_mul_const, integral_indicator measurableSet_Iio, hν,
      Measure.restrict_restrict measurableSet_Iio]
    have hset : Set.Iio s ∩ Set.Ioc 0 t = Set.Ioo 0 s := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2.le hs.2⟩
    rw [hset]
  · rw [← integral_indicator hD.compl, integral_prod _ (hint.indicator hD.compl)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    have : (fun s => Dᶜ.indicator (fun z : ℝ × ℝ => φ z.1 * ψ z.2) (r, s)) =
        fun s => φ r * (Set.Iic r).indicator ψ s := by
      funext s
      by_cases h : r < s
      · have : ¬ s ≤ r := not_le.mpr h
        simp [D, h, this]
      · have : s ≤ r := not_lt.mp h
        simp [D, h, this]
    simp only [this]
    rw [integral_const_mul, integral_indicator measurableSet_Iic, hν,
      Measure.restrict_restrict measurableSet_Iic]
    have hset : Set.Iic r ∩ Set.Ioc 0 t = Set.Ioc 0 r := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 hr.2⟩
    rw [hset]


lemma d36_leftLim_int (μ : Measure ℝ) (L : ℝ → ℝ) (u : ℝ≥0 → ℝ)
    (hu : ∀ x : ℝ≥0, u x = ∫ r in Set.Ioc 0 (x:ℝ), L r ∂μ)
    (hLnn : ∀ r, 0 ≤ L r) (hint : ∀ x : ℝ≥0, IntegrableOn L (Set.Ioc 0 (x:ℝ)) μ)
    (s : ℝ) (hs : 0 < s) : Function.leftLim u s.toNNReal = ∫ r in Set.Ioo 0 s, L r ∂μ := by
  have hmono : Monotone u := fun x y h => by
    rw [hu, hu]
    exact setIntegral_mono_set (hint y) (Eventually.of_forall fun r => hLnn r)
      (Set.Ioc_subset_Ioc_right (by exact_mod_cast h)).eventuallyLE
  have hs' : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs
  haveI : (𝓝[<] s.toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs'⟩
  have hIoo : IntegrableOn L (Set.Ioo 0 s) μ := (hint s.toNNReal).mono_set (by
    rw [Real.coe_toNNReal _ hs.le]; exact Set.Ioo_subset_Ioc_self)
  have hle : ∀ x : ℝ≥0, x < s.toNNReal → u x ≤ ∫ r in Set.Ioo 0 s, L r ∂μ := by
    intro x hx
    rw [hu]
    have hxs : (x:ℝ) < s := Real.lt_toNNReal_iff_coe_lt.mp hx
    exact setIntegral_mono_set hIoo (Eventually.of_forall fun r => hLnn r)
      (Set.Ioc_subset_Ioo_right hxs).eventuallyLE
  rw [hmono.leftLim_eq_sSup]
  apply le_antisymm
  · exact csSup_le (Set.Nonempty.image _ ⟨0, hs'⟩) (by rintro _ ⟨x, hx, rfl⟩; exact hle x hx)
  · set y : ℕ → ℝ := fun k => s - s / ((k:ℝ) + 2) with hydef
    have hy_lt : ∀ k, y k < s := fun k => by
      have : 0 < s / ((k:ℝ) + 2) := by positivity
      simp only [hydef]; linarith
    have hy_pos : ∀ k, 0 < y k := fun k => by
      have : s / ((k:ℝ) + 2) ≤ s / 2 := div_le_div_of_nonneg_left hs.le (by norm_num)
        (by have := k.cast_nonneg (α := ℝ); linarith)
      simp only [hydef]; linarith
    have hymono : Monotone y := fun i j h => by
      have : s / ((j:ℝ) + 2) ≤ s / ((i:ℝ) + 2) := div_le_div_of_nonneg_left hs.le
        (by positivity) (by have : (i:ℝ) ≤ j := by exact_mod_cast h
                            linarith)
      simp only [hydef]; linarith
    have hunion : (⋃ k, Set.Ioc 0 (y k)) = Set.Ioo 0 s := by
      ext r
      simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · rintro ⟨k, h1, h2⟩; exact ⟨h1, lt_of_le_of_lt h2 (hy_lt k)⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨k, hk⟩ := exists_nat_gt (s / (s - r))
        refine ⟨k, h1, ?_⟩
        have hsr : 0 < s - r := sub_pos.mpr h2
        have : s / ((k:ℝ) + 2) ≤ s - r := by
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hsr] at hk
          nlinarith
        simp only [hydef]; linarith
    have ht := tendsto_setIntegral_of_monotone (μ := μ) (f := L)
      (s := fun k => Set.Ioc 0 (y k)) (fun k => measurableSet_Ioc)
      (fun i j h => Set.Ioc_subset_Ioc_right (hymono h)) (by rw [hunion]; exact hIoo)
    rw [hunion] at ht
    have hbdd : BddAbove (u '' Set.Iio s.toNNReal) :=
      ⟨_, by rintro _ ⟨x, hx, rfl⟩; exact hle x hx⟩
    apply le_of_tendsto' ht
    intro k
    apply le_csSup hbdd
    refine ⟨(y k).toNNReal, (Real.toNNReal_lt_toNNReal_iff hs).mpr (hy_lt k), ?_⟩
    rw [hu, Real.coe_toNNReal _ (hy_pos k).le]

lemma d36_ind_g (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0) (i : ℕ) :
    (∀ r, 0 ≤ iterInt a i r) ∧ Monotone (iterInt a i) := by
  have hfin : ∀ x : ℝ≥0, stieltjesMeasureOf a (Set.Ioc 0 (x:ℝ)) < ⊤ := by
    intro x; rw [d36_measure_Ioc a ha_mono ha_rc ha_zero]; exact ENNReal.ofReal_lt_top
  induction i with
  | zero => exact ⟨fun r => by simp [iterInt], fun x y _ => by simp [iterInt]⟩
  | succ i ih =>
    obtain ⟨hnn, hmono⟩ := ih
    have hGmono : Monotone fun s : ℝ => iterInt a i s.toNNReal :=
      fun x y h => hmono (Real.toNNReal_le_toNNReal h)
    have hstep : ∀ r : ℝ≥0, iterInt a (i+1) r =
        ∫ s in Set.Ioc (0:ℝ) r, iterInt a i s.toNNReal ∂stieltjesMeasureOf a := fun r => rfl
    refine ⟨fun r => ?_, fun r r' hrr => ?_⟩
    · rw [hstep]; exact setIntegral_nonneg measurableSet_Ioc fun s _ => hnn _
    · rw [hstep, hstep]
      exact setIntegral_mono_set (d36_intOn_mono _ _ (hfin r') _ hGmono)
        (Eventually.of_forall fun s => hnn _)
        (Set.Ioc_subset_Ioc_right (by exact_mod_cast hrr)).eventuallyLE

theorem d36_rel_core (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ≥0) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * iterIntMinus a (n - i) t * iterInt a i t = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set μ := stieltjesMeasureOf a with hμ
  have hfin : ∀ x : ℝ≥0, μ (Set.Ioc 0 (x:ℝ)) < ⊤ := by
    intro x; rw [hμ, d36_measure_Ioc a ha_mono ha_rc ha_zero]; exact ENNReal.ofReal_lt_top
  set f := iterIntMinus a with hf
  set g := iterInt a with hg
  have hfp := fun j => d36_ind a ha_mono ha_rc ha_zero j
  have hgp := fun i => d36_ind_g a ha_mono ha_rc ha_zero i
  set Fm : ℕ → ℝ → ℝ := fun j r => Function.leftLim (f j) r.toNNReal with hFm
  set G : ℕ → ℝ → ℝ := fun i r => g i r.toNNReal with hG
  have hFm_mono : ∀ j, Monotone (Fm j) := fun j x y h =>
    (hfp j).2.1.leftLim (Real.toNNReal_le_toNNReal h)
  have hFm_nn : ∀ j r, 0 ≤ Fm j r := by
    intro j r
    simp only [hFm]
    rcases eq_zero_or_pos (r.toNNReal) with h | h
    · rw [h, leftLim_eq_of_isBot (fun b => by positivity)]; exact (hfp j).1 0
    · exact le_trans ((hfp j).1 0) ((hfp j).2.1.le_leftLim h)
  have hG_mono : ∀ i, Monotone (G i) := fun i x y h =>
    (hgp i).2 (Real.toNNReal_le_toNNReal h)
  have hG_nn : ∀ i r, 0 ≤ G i r := fun i r => (hgp i).1 _
  have hf_succ : ∀ j (x : ℝ≥0), f (j+1) x = ∫ r in Set.Ioc 0 (x:ℝ), Fm j r ∂μ :=
    fun _ _ => rfl
  have hg_succ : ∀ i (x : ℝ≥0), g (i+1) x = ∫ r in Set.Ioc 0 (x:ℝ), G i r ∂μ :=
    fun _ _ => rfl
  have hFm0 : ∀ r, Fm 0 r = 1 := by
    intro r
    show Function.leftLim (fun _ => (1:ℝ)) r.toNNReal = 1
    exact continuousWithinAt_const.leftLim_eq
  have hG0 : ∀ r, G 0 r = 1 := fun r => rfl
  have hf0 : ∀ x, f 0 x = 1 := fun x => rfl
  have hg0 : ∀ x, g 0 x = 1 := fun x => rfl
  have hFm_succ : ∀ j, ∀ s ∈ Set.Ioc (0:ℝ) t, Fm (j+1) s = ∫ r in Set.Ioo 0 s, Fm j r ∂μ := by
    intro j s hs
    exact d36_leftLim_int μ (Fm j) (f (j+1)) (hf_succ j) (hFm_nn j)
      (fun x => d36_intOn_mono μ x (hfin x) _ (hFm_mono j)) s hs.1
  have hint : ∀ j i, IntegrableOn (fun r => Fm j r * G i r) (Set.Ioc 0 (t:ℝ)) μ := fun j i =>
    d36_intOn_mono μ t (hfin t) _
      (Monotone.mul (hFm_mono j) (hG_mono i) (hFm_nn j) (hG_nn i))
  have hprod : ∀ j i, f (j+1) t * g (i+1) t =
      ∫ s in Set.Ioc (0:ℝ) t, (Fm (j+1) s * G i s + Fm j s * G (i+1) s) ∂μ := by
    intro j i
    rw [hf_succ, hg_succ, d36_prod_rule μ t (hfin t) (Fm j) (G i)
      (d36_intOn_mono μ t (hfin t) _ (hFm_mono j)) (d36_intOn_mono μ t (hfin t) _ (hG_mono i)),
      integral_add (hint (j+1) i) (hint j (i+1))]
    congr 1
    · apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp only
      rw [← hFm_succ j s hs]
    · apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      have h2 : ∫ x in Set.Ioc 0 s, G i x ∂μ = G (i+1) s := by
        show _ = ∫ r in Set.Ioc 0 ((s.toNNReal : ℝ)), G i r ∂μ
        rw [Real.coe_toNNReal _ hs.1.le]
      simp only
      rw [h2]
  set Y : ℕ → ℝ → ℝ := fun k s =>
    if 1 ≤ k ∧ k ≤ m + 1 then (-1 : ℝ) ^ (k - 1) * (Fm (m - (k - 1)) s * G (k - 1) s) else 0
    with hY
  have hY_int : ∀ k, IntegrableOn (Y k) (Set.Ioc 0 (t:ℝ)) μ := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ m + 1
    · have : Y k = fun s => (-1 : ℝ) ^ (k - 1) * (Fm (m - (k - 1)) s * G (k - 1) s) := by
        funext s; simp only [hY, if_pos hk]
      rw [this]; exact (hint _ _).const_mul _
    · have : Y k = fun s => 0 := by funext s; simp only [hY, if_neg hk]
      rw [this]; exact integrableOn_zero
  have hterm : ∀ i ∈ Finset.range (m + 1 + 1),
      (-1 : ℝ) ^ i * f (m + 1 - i) t * g i t =
        ∫ s in Set.Ioc (0:ℝ) t, (Y (i+1) s - Y i s) ∂μ := by
    intro i hi
    have hi' : i ≤ m + 1 := by simp at hi; omega
    rcases i with _ | k
    · have : ∀ s, Y 1 s - Y 0 s = Fm m s := by
        intro s; simp [hY, hG0]
      simp only [this, pow_zero, one_mul, Nat.sub_zero, hg0, mul_one]
      exact hf_succ m t
    · rcases lt_or_eq_of_le (Nat.le_of_succ_le_succ hi') with hk | hk
      · obtain ⟨j, hj⟩ : ∃ j, m - k = j + 1 := ⟨m - k - 1, by omega⟩
        have hm : m + 1 - (k + 1) = j + 1 := by omega
        have : ∀ s, Y (k + 1 + 1) s - Y (k + 1) s =
            (-1 : ℝ) ^ (k + 1) * (Fm (j+1) s * G k s + Fm j s * G (k+1) s) := by
          intro s
          have h1 : 1 ≤ k + 1 + 1 ∧ k + 1 + 1 ≤ m + 1 := ⟨by omega, by omega⟩
          have h2 : 1 ≤ k + 1 ∧ k + 1 ≤ m + 1 := ⟨by omega, by omega⟩
          simp only [hY, if_pos h1, if_pos h2]
          have e1 : k + 1 + 1 - 1 = k + 1 := by omega
          have e2 : k + 1 - 1 = k := by omega
          have e3 : m - (k + 1) = j := by omega
          rw [e1, e2, e3, hj, pow_succ]
          ring
        simp only [this]
        rw [integral_const_mul, ← hprod j k, hm, mul_assoc]
      · subst hk
        have : ∀ s, Y (k + 1 + 1) s - Y (k + 1) s = (-1 : ℝ) ^ (k + 1) * G k s := by
          intro s
          have h1 : ¬ (1 ≤ k + 1 + 1 ∧ k + 1 + 1 ≤ k + 1) := by omega
          have h2 : 1 ≤ k + 1 ∧ k + 1 ≤ k + 1 := ⟨by omega, le_rfl⟩
          simp only [hY, if_pos h2, if_neg h1]
          have e2 : k + 1 - 1 = k := by omega
          rw [e2, Nat.sub_self, hFm0, pow_succ]
          ring
        simp only [this]
        rw [integral_const_mul, Nat.sub_self, hf0, mul_one, hg_succ]
  rw [Finset.sum_congr rfl hterm, ← integral_finsetSum (Finset.range (m+1+1))
    (f := fun i s => Y (i+1) s - Y i s) (fun i _ => (hY_int (i+1)).sub (hY_int i))]
  have : ∀ s, ∑ i ∈ Finset.range (m + 1 + 1), (Y (i+1) s - Y i s) = 0 := by
    intro s
    rw [Finset.sum_range_sub (fun i => Y i s)]
    have h1 : ¬ (1 ≤ m + 1 + 1 ∧ m + 1 + 1 ≤ m + 1) := by omega
    have h0 : ¬ (1 ≤ 0 ∧ 0 ≤ m + 1) := by omega
    simp only [hY, if_neg h1, if_neg h0, sub_zero]
  simp only [this, integral_zero]

end AntonelliBFSDE.Backward

open AntonelliBFSDE.Backward


theorem solution (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ≥0) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * iterIntMinus a (n - i) t * iterInt a i t = 0 := by
  exact d36_rel_core a ha_mono ha_rc ha_zero n hn t
