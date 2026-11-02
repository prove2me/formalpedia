-- Prove2me | solution 1 for AffineStorage.Ruin.convolution_transform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:26:57.389086+00:00
-- url     : https://prove2.me/submissions/1e2c20d1-e662-44ff-86be-b81fe6c1760e
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

lemma affRuinC_tilde_measurable (ρ : ℝ → ℝ) (hρc : ContinuousOn ρ (Set.Ioi 0)) :
    Measurable ((Set.Ioi (0:ℝ)).indicator ρ) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hρc.measurable_piecewise continuousOn_const measurableSet_Ioi

theorem solution (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    P.lamMinus * (∫ x in Set.Ioi 0,
        (∫ y in Set.Ioc 0 x, P.d y * rho B P (x - y)) * (ϑ * Real.exp (-(ϑ * x))))
      = P.lamMinus * (∫ y in Set.Ioi 0, Real.exp (-(ϑ * y)) *
          (∫ x in Set.Ioi y, rho B P (x - y) * (ϑ * Real.exp (-(ϑ * (x - y))))) * P.d y) ∧
    P.lamMinus * (∫ y in Set.Ioi 0, Real.exp (-(ϑ * y)) *
          (∫ x in Set.Ioi y, rho B P (x - y) * (ϑ * Real.exp (-(ϑ * (x - y))))) * P.d y)
      = P.lamMinus * P.lst ϑ * phi B P ϑ := by
  have hdi := affRuinP_d_integrable P hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hdm, hd0, -, -⟩ := id hS
  have hρb : ∀ x, 0 < x → |rho B P x| ≤ 1 := fun x hx => affRuin_rho_abs_le_one P hS B hB x hx
  have hρc : ContinuousOn (rho B P) (Set.Ioi 0) :=
    fun x hx => (lemma_1 P hS B hB x hx).1.continuousAt.continuousWithinAt
  -- inner translation: `∫_{(y,∞)} ρ(x-y) ϑ e^{-ϑ(x-y)} dx = φ(ϑ)`
  have htr : ∀ y, ∫ x in Set.Ioi y, rho B P (x - y) * (ϑ * Real.exp (-(ϑ * (x - y))))
      = phi B P ϑ := by
    intro y
    have := affRuinP_translate (fun x => rho B P (x - y) * (ϑ * Real.exp (-(ϑ * (x - y))))) y
    simp only [add_sub_cancel_left] at this
    rw [← this, phi]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  refine ⟨?_, ?_⟩
  · congr 1
    set ρt := (Set.Ioi (0:ℝ)).indicator (rho B P) with hρt
    have hρtm : Measurable ρt := affRuinC_tilde_measurable _ hρc
    set w : ℝ → ℝ := fun x => ϑ * Real.exp (-(ϑ * x)) with hw
    obtain ⟨hwi, -⟩ := affRuinP_expw ϑ hϑ
    set f : ℝ → ℝ → ℝ := fun x y =>
      (Set.Iio x).indicator (fun y => P.d y * ρt (x - y) * w x) y with hf
    set m := volume.restrict (Set.Ioi (0:ℝ))
    have hint : Integrable (Function.uncurry f) (m.prod m) := by
      have hbound : Integrable (fun p : ℝ × ℝ => w p.1 * P.d p.2) (m.prod m) :=
        hwi.mul_prod hdi
      have hmeas : Measurable (Function.uncurry f) := by
        have heq : Function.uncurry f = {p : ℝ × ℝ | p.2 < p.1}.indicator
            (fun p => P.d p.2 * ρt (p.1 - p.2) * w p.1) := by
          funext p
          simp only [Function.uncurry, hf, Set.indicator, Set.mem_Iio, Set.mem_setOf_eq]
        rw [heq]
        refine Measurable.indicator ?_ (measurableSet_lt measurable_snd measurable_fst)
        exact ((hdm.comp measurable_snd).mul (hρtm.comp (measurable_fst.sub measurable_snd))).mul
          (by simp only [hw]; fun_prop)
      refine Integrable.mono' hbound hmeas.aestronglyMeasurable ?_
      simp only [m]
      rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
      refine Filter.Eventually.of_forall fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : (0:ℝ) < p.1 := hp1
      simp only [Function.uncurry, hf]
      have hwp : 0 < w p.1 := mul_pos hϑ (Real.exp_pos _)
      by_cases hlt : p.2 < p.1
      · rw [Set.indicator_of_mem (show p.2 ∈ Set.Iio p.1 from hlt)]
        have hpos : 0 < p.1 - p.2 := by linarith
        have hρ1 : |ρt (p.1 - p.2)| ≤ 1 := by
          rw [hρt, Set.indicator_of_mem (show p.1 - p.2 ∈ Set.Ioi (0:ℝ) from hpos)]
          exact hρb _ hpos
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hd0 _), abs_of_pos hwp]
        calc P.d p.2 * |ρt (p.1 - p.2)| * w p.1 ≤ P.d p.2 * 1 * w p.1 := by
              gcongr
              exact hd0 _
          _ = w p.1 * P.d p.2 := by ring
      · rw [Set.indicator_of_notMem (show p.2 ∉ Set.Iio p.1 from hlt)]
        simp only [norm_zero]
        exact mul_nonneg hwp.le (hd0 _)
    have hswap := integral_integral_swap hint
    have hL : ∀ x, 0 < x → ∫ y, f x y ∂m =
        (∫ y in Set.Ioc 0 x, P.d y * rho B P (x - y)) * w x := by
      intro x hx
      simp only [m, hf]
      rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio, integral_Ioc_eq_integral_Ioo,
        ← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
      have hpos : 0 < x - y := by linarith [hy.2]
      simp only [hρt, Set.indicator_of_mem (show x - y ∈ Set.Ioi (0:ℝ) from hpos)]
    have hR : ∀ y, 0 < y → ∫ x, f x y ∂m = Real.exp (-(ϑ * y)) *
        (∫ x in Set.Ioi y, rho B P (x - y) * (ϑ * Real.exp (-(ϑ * (x - y))))) * P.d y := by
      intro y hy
      have : ∀ x, f x y = (Set.Ioi y).indicator (fun x => P.d y * ρt (x - y) * w x) x := by
        intro x
        simp only [hf, Set.indicator, Set.mem_Ioi, Set.mem_Iio]
      simp only [m, this]
      rw [setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hy.le), mul_comm, ← mul_assoc,
        ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx' : y < x := hx
      have hpos : 0 < x - y := by linarith
      simp only [hρt, Set.indicator_of_mem (show x - y ∈ Set.Ioi (0:ℝ) from hpos), hw]
      have he : Real.exp (-(ϑ * y)) * Real.exp (-(ϑ * (x - y))) = Real.exp (-(ϑ * x)) := by
        rw [← Real.exp_add]; ring_nf
      linear_combination (P.d y * rho B P (x - y) * ϑ) * he.symm
    calc (∫ x in Set.Ioi 0, (∫ y in Set.Ioc 0 x, P.d y * rho B P (x - y)) *
          (ϑ * Real.exp (-(ϑ * x))))
        = ∫ x, ∫ y, f x y ∂m ∂m :=
          setIntegral_congr_fun measurableSet_Ioi fun x hx => (hL x hx).symm
      _ = ∫ y, ∫ x, f x y ∂m ∂m := hswap
      _ = _ := setIntegral_congr_fun measurableSet_Ioi fun y hy => hR y hy
  · simp_rw [htr]
    rw [Params.lst, mul_assoc, ← integral_mul_const]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    ring
