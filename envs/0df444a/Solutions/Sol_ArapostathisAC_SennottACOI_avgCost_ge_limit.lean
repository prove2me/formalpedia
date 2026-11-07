-- Prove2me | solution 1 for ArapostathisAC.SennottACOI.avgCost_ge_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:29:25.069223+00:00
-- url     : https://prove2.me/submissions/a80a115e-bc00-4604-afdf-243311f27bb2

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions
import Theorems.Thm_SennottDP_Tauberian_abelian_inequalities

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ArapostathisAC.SennottACOI

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : ArapostathisAC.VanishingDiscount.CMP A) (h14 : Assumption5_14 M)
    (β : ℕ → ℝ) (hβ : ∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1))
    (ρ : ℝ) (i : ℕ)
    (hρ : Tendsto (fun n => (1 - β n) * (ArapostathisAC.VanishingDiscount.discValue M (β n) i).toReal) atTop (𝓝 ρ))
    (π : ArapostathisAC.VanishingDiscount.Policy M) :
    ENNReal.ofReal ρ ≤ ArapostathisAC.VanishingDiscount.avgCost M π i := by
  set μ := ArapostathisAC.VanishingDiscount.pathMeasure M π i with hμ
  have hmeas : ∀ t, Measurable (fun ω : ℕ → ℕ × A => ENNReal.ofReal (M.c (ω t).1 (ω t).2)) :=
    fun t => ENNReal.measurable_ofReal.comp (M.c_meas.comp (measurable_pi_apply t))
  set u : ℕ → ℝ≥0∞ := fun t => ∫⁻ ω, ENNReal.ofReal (M.c (ω t).1 (ω t).2) ∂μ with hu
  -- the average cost is the limsup of the Cesàro means of `u`
  have hcost : ∀ N, ArapostathisAC.VanishingDiscount.costN M π N i =
      SennottDP.Tauberian.w u N := by
    intro N
    simp only [ArapostathisAC.VanishingDiscount.costN, SennottDP.Tauberian.w, hu, ← hμ]
    exact lintegral_finset_sum _ (fun t _ => hmeas t)
  have havg : ArapostathisAC.VanishingDiscount.avgCost M π i =
      limsup (SennottDP.Tauberian.cesaroMean u) atTop := by
    unfold ArapostathisAC.VanishingDiscount.avgCost
    congr 1; funext N
    rw [hcost, SennottDP.Tauberian.cesaroMean, div_eq_mul_inv, mul_comm]
  rw [havg]
  -- the discounted cost is the power series of `u`
  have hdisc : ∀ b : ℝ, 0 ≤ b → ArapostathisAC.VanishingDiscount.discCost M π b i =
      SennottDP.Tauberian.U u b.toNNReal := by
    intro b hb
    simp only [ArapostathisAC.VanishingDiscount.discCost, SennottDP.Tauberian.U, hu, ← hμ]
    have hm2 : ∀ t, AEMeasurable
        (fun ω : ℕ → ℕ × A => ENNReal.ofReal (b ^ t * M.c (ω t).1 (ω t).2)) μ := fun t =>
      (measurable_const.mul (M.c_meas.comp (measurable_pi_apply t))).ennreal_ofReal.aemeasurable
    rw [lintegral_tsum hm2]
    congr 1; ext t
    have : ∀ ω : ℕ → ℕ × A, ENNReal.ofReal (b ^ t * M.c (ω t).1 (ω t).2) =
        ((b.toNNReal : ℝ≥0∞) ^ t) * ENNReal.ofReal (M.c (ω t).1 (ω t).2) := by
      intro ω
      rw [ENNReal.ofReal_mul (pow_nonneg hb t), ENNReal.ofReal_pow hb]
      rfl
    simp_rw [this]
    exact lintegral_const_mul _ (hmeas t)
  by_cases hu0 : u 0 = ⊤
  · -- infinite first-stage cost: every Cesàro mean with `N ≥ 1` is `∞`
    have hev : ∀ᶠ N in atTop, SennottDP.Tauberian.cesaroMean u N = ⊤ := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hw : SennottDP.Tauberian.w u N = ⊤ := by
        apply eq_top_iff.2
        rw [← hu0]
        exact Finset.single_le_sum (f := u) (fun _ _ => bot_le)
          (Finset.mem_range.2 (by omega))
      simp only [SennottDP.Tauberian.cesaroMean, hw]
      exact ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top N)
    rw [limsup_congr hev]
    simp
  · have hT := (SennottDP.Tauberian.abelian_inequalities u hu0).2.2
    refine le_trans ?_ hT
    -- the discount factors as a sequence in `ℝ≥0` tending to `1` from the left
    set α : ℕ → ℝ≥0 := fun n => (β n).toNNReal with hα
    have hαt : Tendsto α atTop (𝓝[<] (1 : ℝ≥0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun n => ?_)⟩
      · have := (continuous_real_toNNReal.tendsto 1).comp hβ1
        rw [Real.toNNReal_one] at this
        exact this
      · simp only [hα, Set.mem_Iio]
        exact Real.toNNReal_lt_one.2 (hβ n).2
    refine le_trans ?_ (hαt.limsup_comp_le_limsup (u := SennottDP.Tauberian.abelMean u))
    -- lower bound along the sequence
    have hle : ∀ n, ENNReal.ofReal ((1 - β n) *
        (ArapostathisAC.VanishingDiscount.discValue M (β n) i).toReal) ≤
        (SennottDP.Tauberian.abelMean u ∘ α) n := by
      intro n
      have hb0 : 0 ≤ β n := (hβ n).1.le
      simp only [Function.comp, SennottDP.Tauberian.abelMean, hα]
      rw [← hdisc (β n) hb0, ENNReal.ofReal_mul (by linarith [(hβ n).2]),
        ENNReal.ofReal_toReal (h14 (β n) (hβ n) i), ENNReal.ofReal_sub _ hb0, ENNReal.ofReal_one]
      exact mul_le_mul_right (iInf_le _ π) _
    have hlim : Tendsto (fun n => ENNReal.ofReal ((1 - β n) *
        (ArapostathisAC.VanishingDiscount.discValue M (β n) i).toReal)) atTop
        (𝓝 (ENNReal.ofReal ρ)) := (ENNReal.continuous_ofReal.tendsto _).comp hρ
    rw [← hlim.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall hle)
