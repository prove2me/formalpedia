-- Prove2me | solution 1 for AffineStorage.Ruin.eq_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:28:35.196249+00:00
-- url     : https://prove2.me/submissions/04a96801-c66b-4964-bab6-c08a8d423f2e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
import Theorems.Thm_AffineStorage_Ruin_eq_2
import Theorems.Thm_AffineStorage_Ruin_lemma_1
open MeasureTheory ProbabilityTheory Filter Topology
open AffineStorage.Ruin

/-- Pathwise: on the good event of `eq_2`, the penalty at a finite ruin time is in `[0,1]`. -/
lemma affRuin_payoff_le_one (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (x : ℝ) (hx : 0 < x) (ω : Ω)
    (hX0 : B.X P x 0 ω = x)
    (hrc : ∀ t, ContinuousWithinAt (fun s => B.X P x s ω) (Set.Ici t) t)
    (hll : ∀ t, Tendsto (fun s => B.X P x s ω) (𝓝[<] t) (𝓝 (B.Xminus P x t ω)))
    (hτ : B.tau P x ω < ⊤) : B.payoff P x ω ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, hα, hβ, hγ, -⟩ := hS
  set f : ℝ → ℝ := fun s => B.X P x s ω with hf
  set t := (B.tau P x ω).toReal with ht_def
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hτt : B.tau P x ω = ENNReal.ofReal t := (ENNReal.ofReal_toReal hτ.ne).symm
  have ha : ∀ s, 0 < s → f s ≤ 0 → t ≤ s := by
    intro s hs hfs
    refine ENNReal.toReal_le_of_le_ofReal hs.le ?_
    unfold Basis.tau
    exact iInf₂_le s ⟨hs, hfs⟩
  have hb : f t ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ s in 𝓝[≥] t, 0 < f s := (hrc t).eventually (lt_mem_nhds hcon)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have hu' : t < u := hu
    have hle : ENNReal.ofReal u ≤ B.tau P x ω := by
      unfold Basis.tau
      refine le_iInf₂ fun s hs => ENNReal.ofReal_le_ofReal ?_
      have hts := ha s hs.1 hs.2
      by_contra hsu
      push Not at hsu
      have := hsub ⟨hts, hsu⟩
      simp only [Set.mem_setOf_eq] at this
      exact absurd hs.2 (not_le.mpr this)
    rw [hτt] at hle
    have := (ENNReal.ofReal_le_ofReal_iff ht0).mp hle
    linarith
  have htpos : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hb; simp only [hf] at hb; rw [hX0] at hb; linarith
  have hd : 0 ≤ B.Xminus P x t ω := by
    refine ge_of_tendsto (hll t) ?_
    filter_upwards [Ioo_mem_nhdsLT htpos] with s hs
    by_contra hcon
    push Not at hcon
    have := ha s hs.1 hcon.le
    linarith [hs.2]
  unfold Basis.payoff
  rw [Real.exp_le_one_iff]
  have h1 : 0 ≤ P.α * t := mul_nonneg hα ht0
  have h2 : P.β * B.X P x t ω ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ hb
  have h3 : 0 ≤ P.γ * B.Xminus P x t ω := mul_nonneg hγ hd
  rw [← ht_def]
  linarith

lemma affRuin_rho_abs_le_one (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (x : ℝ) (hx : 0 < x) : |rho B P x| ≤ 1 := by
  have hν : 0 < P.ν := hS.2.2.2.2.2.1
  have := isProbabilityMeasure_expMeasure hν
  have : IsProbabilityMeasure B.P := hB.1
  obtain ⟨-, hgood⟩ := eq_2 P hS B hB x
  have hinner : ∀ s : ℝ, ‖∫ ω, Set.indicator {ω | B.tau P x ω < ENNReal.ofReal s}
      (B.payoff P x) ω ∂B.P‖ ≤ 1 := by
    intro s
    have := norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) (μ := B.P)
      (f := Set.indicator {ω | B.tau P x ω < ENNReal.ofReal s} (B.payoff P x)) ?_
    · simpa using this
    filter_upwards [hgood] with ω hω
    obtain ⟨h0, hrc, hll, -, -⟩ := hω
    by_cases hm : ω ∈ {ω | B.tau P x ω < ENNReal.ofReal s}
    · rw [Set.indicator_of_mem hm, Real.norm_eq_abs,
        abs_of_nonneg (by unfold Basis.payoff; exact (Real.exp_pos _).le)]
      exact affRuin_payoff_le_one P hS B x hx ω h0 hrc hll
        (lt_of_lt_of_le hm le_top)
    · rw [Set.indicator_of_notMem hm]; simp
  have := norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) (μ := expMeasure P.ν)
    (ae_of_all _ hinner)
  simpa [rho] using this

lemma affRuin_phi_abs_le_one (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) : |phi B P ϑ| ≤ 1 := by
  have hint : IntegrableOn (fun x => ϑ * Real.exp (-(ϑ * x))) (Set.Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 hϑ).const_mul ϑ
    simp only [neg_mul] at this; exact this
  have hval : ∫ x in Set.Ioi (0 : ℝ), ϑ * Real.exp (-(ϑ * x)) = 1 := by
    rw [integral_const_mul]
    have := integral_exp_mul_Ioi (a := -ϑ) (by linarith) 0
    simp only [mul_zero, Real.exp_zero, neg_mul] at this
    rw [this]; field_simp
  have := norm_integral_le_of_norm_le hint (μ := volume.restrict (Set.Ioi 0))
    (f := fun x => ϑ * Real.exp (-(ϑ * x)) * rho B P x) ?_
  · rw [hval] at this; simpa [phi] using this
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  have hr := affRuin_rho_abs_le_one P hS B hB x hx
  have hp : 0 < ϑ * Real.exp (-(ϑ * x)) := mul_pos hϑ (Real.exp_pos _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
  nlinarith [abs_nonneg (rho B P x)]

lemma affRuinP_d_integrable (P : Params) (hS : P.Standing) :
    IntegrableOn P.d (Set.Ioi 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := hS
  by_contra h
  rw [integral_undef h] at h1
  norm_num at h1

lemma affRuinP_expw (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x => a * Real.exp (-(a * x))) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), a * Real.exp (-(a * x)) = 1 := by
  have hint : IntegrableOn (fun x => a * Real.exp (-(a * x))) (Set.Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 ha).const_mul a
    simp only [neg_mul] at this; exact this
  refine ⟨hint, ?_⟩
  rw [integral_const_mul]
  have := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at this
  rw [this]; field_simp

lemma affRuinP_translate (f : ℝ → ℝ) (a : ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), f (a + y) = ∫ z in Set.Ioi a, f z := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_left_eq_self a (f := (Set.Ioi a).indicator f)]
  congr 1
  funext y
  by_cases hy : 0 < y
  · rw [Set.indicator_of_mem (show y ∈ Set.Ioi (0:ℝ) from hy),
      Set.indicator_of_mem (show a + y ∈ Set.Ioi a by simp [hy])]
  · rw [Set.indicator_of_notMem (show y ∉ Set.Ioi (0:ℝ) from hy),
      Set.indicator_of_notMem (show a + y ∉ Set.Ioi a by simpa using hy)]
lemma affRuinP_T3eq (P : Params) (ρ : ℝ → ℝ) (x : ℝ) :
    (∫ y in Set.Ioi 0, P.μ * Real.exp (-(P.μ * y)) * ρ (x + y)) = Real.exp (P.μ * x) *
      ∫ z in Set.Ioi x, P.μ * Real.exp (-(P.μ * z)) * ρ z := by
  have := affRuinP_translate (fun z => P.μ * Real.exp (-(P.μ * (z - x))) * ρ z) x
  simp only [add_sub_cancel_left] at this
  rw [this, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun z _ => ?_
  rw [show -(P.μ * (z - x)) = P.μ * x + -(P.μ * z) by ring, Real.exp_add]; ring


lemma affRuinC_tilde_measurable (ρ : ℝ → ℝ) (hρc : ContinuousOn ρ (Set.Ioi 0)) :
    Measurable ((Set.Ioi (0:ℝ)).indicator ρ) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hρc.measurable_piecewise continuousOn_const measurableSet_Ioi

lemma affRuin5_expint (k y : ℝ) (hk : k ≠ 0) :
    ∫ x in (0:ℝ)..y, Real.exp (k * x) = (Real.exp (k * y) - 1) / k := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) y, HasDerivAt (fun x => Real.exp (k * x) / k)
      (Real.exp (k * x)) x := by
    intro x _
    have := ((hasDerivAt_id' x).const_mul k).exp.div_const k
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x => Real.exp (k * x)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  ring

theorem solution (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑμ : ϑ ≠ P.μ) :
    P.lamPlus * (∫ x in Set.Ioi 0,
        (∫ y in Set.Ioi 0, P.μ * Real.exp (-(P.μ * y)) * rho B P (x + y))
          * (ϑ * Real.exp (-(ϑ * x))))
      = P.lamPlus * (P.μ / (P.μ - ϑ)) * phi B P ϑ
        - P.lamPlus * (ϑ / (P.μ - ϑ)) * phi B P P.μ := by
  have hμ : 0 < P.μ := hS.2.2.2.2.1
  have hρb : ∀ x, 0 < x → |rho B P x| ≤ 1 := fun x hx => affRuin_rho_abs_le_one P hS B hB x hx
  have hρc : ContinuousOn (rho B P) (Set.Ioi 0) :=
    fun x hx => (lemma_1 P hS B hB x hx).1.continuousAt.continuousWithinAt
  have hρm : AEStronglyMeasurable (rho B P) (volume.restrict (Set.Ioi 0)) :=
    hρc.aestronglyMeasurable measurableSet_Ioi
  set ρ := rho B P with hρ_def
  set ρt := (Set.Ioi (0:ℝ)).indicator ρ with hρt
  have hρtm : Measurable ρt := affRuinC_tilde_measurable _ hρc
  have hk : P.μ - ϑ ≠ 0 := sub_ne_zero.mpr (Ne.symm hϑμ)
  set m := volume.restrict (Set.Ioi (0:ℝ))
  set c := min ϑ P.μ / 2 with hc
  have hc0 : 0 < c := by positivity
  have hcϑ : 2 * c ≤ ϑ := by simp only [hc]; linarith [min_le_left ϑ P.μ]
  have hcμ : 2 * c ≤ P.μ := by simp only [hc]; linarith [min_le_right ϑ P.μ]
  set f : ℝ → ℝ → ℝ := fun x z => (Set.Ioi x).indicator
    (fun z => ϑ * Real.exp ((P.μ - ϑ) * x) * (P.μ * Real.exp (-(P.μ * z)) * ρt z)) z with hf
  have hint : Integrable (Function.uncurry f) (m.prod m) := by
    have he : Integrable (fun x => Real.exp (-c * x)) m := exp_neg_integrableOn_Ioi 0 hc0
    have hbound : Integrable (fun p : ℝ × ℝ => (ϑ * P.μ * Real.exp (-c * p.1)) *
        Real.exp (-c * p.2)) (m.prod m) := (he.const_mul _).mul_prod he
    have hmeas : Measurable (Function.uncurry f) := by
      have heq : Function.uncurry f = {p : ℝ × ℝ | p.1 < p.2}.indicator
          (fun p => ϑ * Real.exp ((P.μ - ϑ) * p.1) * (P.μ * Real.exp (-(P.μ * p.2)) * ρt p.2)) := by
        funext p
        simp only [Function.uncurry, hf, Set.indicator, Set.mem_Ioi, Set.mem_setOf_eq]
      rw [heq]
      refine Measurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)
      exact (by fun_prop : Measurable fun p : ℝ × ℝ => ϑ * Real.exp ((P.μ - ϑ) * p.1)).mul
        ((by fun_prop : Measurable fun p : ℝ × ℝ => P.μ * Real.exp (-(P.μ * p.2))).mul
          (hρtm.comp measurable_snd))
    refine Integrable.mono' hbound hmeas.aestronglyMeasurable ?_
    simp only [m]
    rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    refine Filter.Eventually.of_forall fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : (0:ℝ) < p.1 := hp1
    have hp2' : (0:ℝ) < p.2 := hp2
    simp only [Function.uncurry, hf]
    have hpos : 0 ≤ ϑ * P.μ * Real.exp (-c * p.1) * Real.exp (-c * p.2) := by positivity
    by_cases hlt : p.1 < p.2
    · rw [Set.indicator_of_mem (show p.2 ∈ Set.Ioi p.1 from hlt)]
      have hρ1 : |ρt p.2| ≤ 1 := by
        rw [hρt, Set.indicator_of_mem (show p.2 ∈ Set.Ioi (0:ℝ) from hp2')]
        exact hρb _ hp2'
      have hexp : Real.exp ((P.μ - ϑ) * p.1) * Real.exp (-(P.μ * p.2))
          ≤ Real.exp (-c * p.1) * Real.exp (-c * p.2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ϑ - 2 * c) hp1'.le,
          mul_nonneg (by linarith : (0:ℝ) ≤ P.μ - c) (by linarith : (0:ℝ) ≤ p.2 - p.1)]
      rw [Real.norm_eq_abs]
      have e1 := Real.exp_pos ((P.μ - ϑ) * p.1)
      have e2 := Real.exp_pos (-(P.μ * p.2))
      calc |ϑ * Real.exp ((P.μ - ϑ) * p.1) * (P.μ * Real.exp (-(P.μ * p.2)) * ρt p.2)|
          = ϑ * P.μ * (Real.exp ((P.μ - ϑ) * p.1) * Real.exp (-(P.μ * p.2))) * |ρt p.2| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hϑ, abs_of_pos hμ,
              abs_of_pos e1, abs_of_pos e2]; ring
        _ ≤ ϑ * P.μ * (Real.exp (-c * p.1) * Real.exp (-c * p.2)) * 1 := by
            gcongr
        _ = _ := by ring
    · rw [Set.indicator_of_notMem (show p.2 ∉ Set.Ioi p.1 from hlt)]
      simp only [norm_zero]
      exact hpos
  have hswap := integral_integral_swap hint
  have hL : ∀ x, 0 < x → ∫ z, f x z ∂m =
      (∫ y in Set.Ioi 0, P.μ * Real.exp (-(P.μ * y)) * ρ (x + y)) * (ϑ * Real.exp (-(ϑ * x))) := by
    intro x hx
    simp only [m, hf]
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hx.le), affRuinP_T3eq P ρ x,
      integral_const_mul]
    have hin : ∫ z in Set.Ioi x, P.μ * Real.exp (-(P.μ * z)) * ρt z
        = ∫ z in Set.Ioi x, P.μ * Real.exp (-(P.μ * z)) * ρ z := by
      refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
      have : (0:ℝ) < z := lt_trans hx hz
      simp only [hρt, Set.indicator_of_mem (show z ∈ Set.Ioi (0:ℝ) from this)]
    rw [hin]
    have he : Real.exp ((P.μ - ϑ) * x) = Real.exp (P.μ * x) * Real.exp (-(ϑ * x)) := by
      rw [← Real.exp_add]; ring_nf
    rw [he]; ring
  have hR : ∀ z, 0 < z → ∫ x, f x z ∂m =
      P.μ / (P.μ - ϑ) * (ϑ * Real.exp (-(ϑ * z)) * ρ z)
        - ϑ / (P.μ - ϑ) * (P.μ * Real.exp (-(P.μ * z)) * ρ z) := by
    intro z hz
    have : ∀ x, f x z = (Set.Iio z).indicator
        (fun x => ϑ * Real.exp ((P.μ - ϑ) * x) * (P.μ * Real.exp (-(P.μ * z)) * ρt z)) x := by
      intro x
      simp only [hf, Set.indicator, Set.mem_Ioi, Set.mem_Iio]
    simp only [m, this]
    rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio, integral_mul_const,
      integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hz.le,
      affRuin5_expint _ _ hk]
    simp only [hρt, Set.indicator_of_mem (show z ∈ Set.Ioi (0:ℝ) from hz)]
    have he : Real.exp ((P.μ - ϑ) * z) * Real.exp (-(P.μ * z)) = Real.exp (-(ϑ * z)) := by
      rw [← Real.exp_add]; ring_nf
    rw [← he]
    field_simp
  -- integrability of the two weighted transforms
  have hwi : ∀ a, 0 < a → IntegrableOn (fun z => a * Real.exp (-(a * z)) * ρ z) (Set.Ioi 0) := by
    intro a ha
    obtain ⟨hai, -⟩ := affRuinP_expw a ha
    refine Integrable.mono' hai (hai.aestronglyMeasurable.mul hρm) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun z hz => ?_)
    have hp : 0 < a * Real.exp (-(a * z)) := mul_pos ha (Real.exp_pos _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
    exact mul_le_of_le_one_right hp.le (hρb z hz)
  have i1 := (hwi ϑ hϑ).const_mul (P.μ / (P.μ - ϑ))
  have i2 := (hwi P.μ hμ).const_mul (ϑ / (P.μ - ϑ))
  calc P.lamPlus * (∫ x in Set.Ioi 0,
        (∫ y in Set.Ioi 0, P.μ * Real.exp (-(P.μ * y)) * ρ (x + y)) * (ϑ * Real.exp (-(ϑ * x))))
      = P.lamPlus * ∫ x, ∫ z, f x z ∂m ∂m := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Ioi fun x hx => (hL x hx).symm
    _ = P.lamPlus * ∫ z, ∫ x, f x z ∂m ∂m := by rw [hswap]
    _ = P.lamPlus * ∫ z in Set.Ioi 0, (P.μ / (P.μ - ϑ) * (ϑ * Real.exp (-(ϑ * z)) * ρ z)
        - ϑ / (P.μ - ϑ) * (P.μ * Real.exp (-(P.μ * z)) * ρ z)) := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Ioi fun z hz => hR z hz
    _ = _ := by
        rw [integral_sub i1 i2, integral_const_mul, integral_const_mul]
        simp only [phi, hρ_def]
        ring
