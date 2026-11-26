-- Prove2me | solution 1 for Arxivcond_mat_0004049.mean_spectral_moment_divergent
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T14:11:25.977533+00:00
-- url     : https://prove2.me/submissions/7243fedb-fa98-4e00-869c-605dfcc92413

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology ProbabilityTheory Set

namespace Arxivcond_mat_0004049

/-! ### The Laguerre weight: measurability and finiteness of the normalization -/

private lemma laguerreWeight_measurable (N : ℕ) (γ : ℝ) : Measurable (laguerreWeight N γ) := by
  unfold laguerreWeight
  refine Measurable.ennreal_ofReal (Measurable.mul ?_ ?_)
  · refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    by_cases h : i < j
    · simp only [h, if_true]; fun_prop
    · simp only [h, if_false]; exact measurable_const
  · exact Finset.measurable_prod _ fun k _ =>
      Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply k)) (by fun_prop)
        measurable_const

/-- One-coordinate majorant of the Laguerre weight: `(1+x)^{2N} e^{-γ(N+1)x}` on `x > 0`. -/
private noncomputable def lagBound (N : ℕ) (γ x : ℝ) : ℝ :=
  if 0 < x then (1 + x) ^ (2 * N) * Real.exp (-γ * ((N : ℝ) + 1) * x) else 0

private lemma lagBound_nonneg (N : ℕ) (γ x : ℝ) : 0 ≤ lagBound N γ x := by
  unfold lagBound; split_ifs with h
  · exact mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
  · exact le_rfl

private lemma lagBound_integrable (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    Integrable (lagBound N γ) := by
  have hb : 0 < γ * ((N : ℝ) + 1) := by positivity
  have hfun : lagBound N γ = (Ioi (0 : ℝ)).indicator
      (fun x => ∑ k ∈ Finset.range (2 * N + 1),
        ((2 * N).choose k : ℝ) * (x ^ (k : ℝ) * Real.exp (-(γ * ((N : ℝ) + 1)) * x ^ (1 : ℝ)))) := by
    funext x
    unfold lagBound
    by_cases hx : 0 < x
    · rw [if_pos hx, indicator_of_mem (show x ∈ Ioi 0 from hx), add_comm (1 : ℝ) x, add_pow,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.rpow_natCast, Real.rpow_one, one_pow, mul_one]
      ring_nf
    · rw [if_neg hx, indicator_of_notMem (show x ∉ Ioi 0 from hx)]
  rw [hfun, integrable_indicator_iff measurableSet_Ioi]
  refine integrable_finsetSum _ fun k _ => Integrable.const_mul ?_ _
  exact integrableOn_rpow_mul_exp_neg_mul_rpow
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith) one_pos hb

private lemma laguerreWeight_le_prod (N : ℕ) (γ : ℝ) (μ : Fin N → ℝ) :
    laguerreWeight N γ μ ≤ ENNReal.ofReal (∏ k, lagBound N γ (μ k)) := by
  unfold laguerreWeight
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hpos : ∀ k, 0 < μ k
  · have hE : (∏ k, if 0 < μ k then Real.exp (-γ * ((N : ℝ) + 1) * μ k) else 0) =
        ∏ k, Real.exp (-γ * ((N : ℝ) + 1) * μ k) :=
      Finset.prod_congr rfl fun k _ => if_pos (hpos k)
    have hB : (∏ k, lagBound N γ (μ k)) =
        (∏ k, (1 + μ k) ^ (2 * N)) * ∏ k, Real.exp (-γ * ((N : ℝ) + 1) * μ k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => if_pos (hpos k)
    rw [hE, hB]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun k _ => (Real.exp_pos _).le)
    have hV : (∏ i, ∏ j, if i < j then |μ i - μ j| else 1) ≤
        ∏ i : Fin N, ∏ j : Fin N, ((1 + μ i) * (1 + μ j)) := by
      refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) fun i _ => ?_
      · split_ifs <;> positivity
      refine Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
      · split_ifs <;> positivity
      have hi := hpos i; have hj := hpos j
      split_ifs
      · rw [abs_le]; constructor <;> nlinarith
      · nlinarith
    refine hV.trans (le_of_eq ?_)
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow]
    ring
  · push Not at hpos
    obtain ⟨k, hk⟩ := hpos
    have : (∏ k, if 0 < μ k then Real.exp (-γ * ((N : ℝ) + 1) * μ k) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (not_lt.2 hk))
    rw [this, mul_zero]
    exact Finset.prod_nonneg fun k _ => lagBound_nonneg N γ (μ k)

/-- The normalization `∫ laguerreWeight` of eq. (7) is finite. -/
private lemma laguerre_norm_ne_top (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∫⁻ μ, laguerreWeight N γ μ ≠ ⊤ := by
  refine (lt_of_le_of_lt (lintegral_mono fun μ => laguerreWeight_le_prod N γ μ) ?_).ne
  have := Integrable.fintype_prod (μ := fun _ : Fin N => (volume : Measure ℝ))
    (fun _ => lagBound_integrable N γ hγ)
  rw [← volume_pi] at this
  exact this.lintegral_lt_top

/-! ### The divergent one-dimensional integral -/

private lemma lintegral_inv_Ioc_eq_top :
    ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal x⁻¹ = ⊤ := by
  by_contra h
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun x : ℝ => x⁻¹ :=
    (ae_restrict_mem measurableSet_Ioc).mono fun x hx => inv_nonneg.2 hx.1.le
  have hfin : HasFiniteIntegral (fun x : ℝ => x⁻¹) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 h)
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc 0 1) :=
    ⟨measurable_inv.aestronglyMeasurable, hfin⟩
  have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hint
  rw [intervalIntegrable_inv_iff] at this
  simp at this

/-! ### Lower bound on a box: the heavy tail at small rates -/

/-- For nonnegative weights `a` with `a i₀ > 0`, `⟨∑ a_i/μ_i⟩ = ∞` under the Laguerre ensemble. -/
private lemma laguerre_lintegral_inv_eq_top (n : ℕ) (γ : ℝ) (hγ : 0 < γ) (i₀ : Fin (n + 1))
    (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i) (hi₀ : 0 < a i₀) :
    ∫⁻ μ, ENNReal.ofReal (∑ i, a i * (μ i)⁻¹) ∂(laguerreEnsemble (n + 1) γ) = ⊤ := by
  set c := γ * (((n + 1 : ℕ) : ℝ) + 1) with hc
  have hc0 : 0 < c := by positivity
  set e0 := Real.exp (-c * (2 * ((n + 1 : ℕ) : ℝ) + 3)) with he0
  set w := ENNReal.ofReal (e0 ^ (n + 1)) with hw
  have hw0 : w ≠ 0 := by rw [hw]; exact ENNReal.ofReal_pos.2 (by positivity) |>.ne'
  -- the box for the other coordinates
  set I : Fin n → Set ℝ := fun j =>
    Ioo (2 * ((i₀.succAbove j : ℕ) : ℝ) + 2) (2 * ((i₀.succAbove j : ℕ) : ℝ) + 3) with hI
  set g : ℝ → ENNReal := (Ioc (0 : ℝ) 1).indicator fun x => ENNReal.ofReal (a i₀ * x⁻¹) with hg
  set h : (Fin n → ℝ) → ENNReal := (Set.pi univ I).indicator fun _ => w with hh
  -- rewrite the Laguerre integral as an integral against Lebesgue measure
  unfold laguerreEnsemble
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (laguerreWeight_measurable (n + 1) γ) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), smul_eq_mul]
  suffices H : ∫⁻ μ, (laguerreWeight (n + 1) γ * fun μ : Fin (n + 1) → ℝ => ENNReal.ofReal (∑ i, a i * (μ i)⁻¹)) μ = ⊤ by
    rw [H]; exact ENNReal.mul_top (ENNReal.inv_ne_zero.2 (laguerre_norm_ne_top (n + 1) γ hγ))
  -- pointwise lower bound by a split function `g (μ i₀) * h (rest)`
  set E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i₀ with hE
  have hpt : ∀ μ : Fin (n + 1) → ℝ, g (E μ).1 * h (E μ).2 ≤
      (laguerreWeight (n + 1) γ * fun μ : Fin (n + 1) → ℝ => ENNReal.ofReal (∑ i, a i * (μ i)⁻¹)) μ := by
    intro μ
    have hEμ : E μ = (μ i₀, fun j => μ (i₀.succAbove j)) := rfl
    rw [hEμ]
    by_cases hR : μ i₀ ∈ Ioc 0 1 ∧ ∀ j, μ (i₀.succAbove j) ∈ I j
    · obtain ⟨h0, hrest⟩ := hR
      rw [hg, hh, indicator_of_mem h0, indicator_of_mem (show (fun j => μ (i₀.succAbove j)) ∈
        Set.pi univ I from fun j _ => hrest j), mul_comm, Pi.mul_apply]
      -- every coordinate lies in its interval
      have hk : ∀ k, k ≠ i₀ → 2 * ((k : ℕ) : ℝ) + 2 < μ k ∧ μ k < 2 * ((k : ℕ) : ℝ) + 3 := by
        intro k hk
        obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
        exact hrest j
      have hposμ : ∀ k, 0 < μ k := by
        intro k
        by_cases hki : k = i₀
        · subst hki; exact h0.1
        · have h1 := (hk k hki).1
          have : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
      have hupper : ∀ k, μ k ≤ 2 * ((n + 1 : ℕ) : ℝ) + 3 := by
        intro k
        have hkN : ((k : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast k.isLt.le
        by_cases hki : k = i₀
        · subst hki; linarith [h0.2]
        · linarith [(hk k hki).2]
      refine mul_le_mul' ?_ ?_
      · -- the weight is at least `e0^N` on the box
        unfold laguerreWeight
        rw [hw]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ∀ i j : Fin (n + 1), 1 ≤ (if i < j then |μ i - μ j| else (1 : ℝ)) := by
          intro i j
          split_ifs with hij
          · have hij' : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
            have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
            have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
            by_cases hii : i = i₀
            · have hj : j ≠ i₀ := fun h => (ne_of_lt hij) (hii.trans h.symm)
              have := (hk j hj).1
              rw [hii, abs_sub_comm, le_abs]; left; linarith [h0.2]
            · by_cases hjj : j = i₀
              · have := (hk i hii).1
                rw [hjj, le_abs]; left; linarith [h0.2]
              · have := (hk i hii).2
                have := (hk j hjj).1
                rw [abs_sub_comm, le_abs]; left; linarith
          · exact le_rfl
        have hV : 1 ≤ ∏ i, ∏ j, if i < j then |μ i - μ j| else 1 :=
          calc (1 : ℝ) = ∏ _i : Fin (n + 1), ∏ _j : Fin (n + 1), (1 : ℝ) := by simp
            _ ≤ _ := Finset.prod_le_prod
                (fun _ _ => Finset.prod_nonneg fun _ _ => zero_le_one)
                fun i _ => Finset.prod_le_prod (fun _ _ => zero_le_one) fun j _ => h1 i j
        have hEx : e0 ^ (n + 1) ≤
            ∏ k, if 0 < μ k then Real.exp (-γ * (((n + 1 : ℕ) : ℝ) + 1) * μ k) else 0 :=
          calc e0 ^ (n + 1) = ∏ _k : Fin (n + 1), e0 := by simp
            _ ≤ _ := by
              refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun k _ => ?_
              rw [if_pos (hposμ k), he0, Real.exp_le_exp, hc]
              have := hupper k
              have hc' : 0 ≤ γ * (((n + 1 : ℕ) : ℝ) + 1) := hc0.le
              nlinarith
        calc e0 ^ (n + 1) = 1 * e0 ^ (n + 1) := (one_mul _).symm
          _ ≤ _ := mul_le_mul hV hEx (by positivity) (by linarith)
      · refine ENNReal.ofReal_le_ofReal ?_
        exact Finset.single_le_sum (f := fun i => a i * (μ i)⁻¹)
          (fun i _ => mul_nonneg (ha i) (inv_nonneg.2 (hposμ i).le)) (Finset.mem_univ i₀)
    · have : g (μ i₀) * h (fun j => μ (i₀.succAbove j)) = 0 := by
        rw [not_and_or] at hR
        rcases hR with hR | hR
        · rw [hg, indicator_of_notMem hR, zero_mul]
        · push Not at hR
          obtain ⟨j, hj⟩ := hR
          rw [hh, indicator_of_notMem (fun hmem => hj (Set.mem_univ_pi.1 hmem j)), mul_zero]
      rw [this]; exact zero_le
  refine eq_top_iff.2 (le_trans ?_ (lintegral_mono hpt))
  -- compute the split integral with Tonelli
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) i₀
  rw [← volume_pi] at hmp
  rw [hmp.lintegral_comp_emb E.measurableEmbedding (fun z => g z.1 * h z.2)]
  rw [lintegral_prod_mul ?_ ?_]
  · have hg_top : ∫⁻ x, g x = ⊤ := by
      rw [hg, lintegral_indicator measurableSet_Ioc]
      simp_rw [ENNReal.ofReal_mul (ha i₀)]
      rw [lintegral_const_mul _ (by fun_prop), lintegral_inv_Ioc_eq_top]
      exact ENNReal.mul_top (ENNReal.ofReal_pos.2 hi₀).ne'
    have hh_ne : ∫⁻ y, h y ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)) ≠ 0 := by
      rw [hh, lintegral_indicator_const (MeasurableSet.univ_pi fun _ => measurableSet_Ioo),
        Measure.pi_pi]
      refine mul_ne_zero hw0 (Finset.prod_ne_zero_iff.2 fun j _ => ?_)
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
    rw [hg_top, ENNReal.top_mul hh_ne]
  · exact (Measurable.indicator (by fun_prop) measurableSet_Ioc).aemeasurable
  · exact (measurable_const.indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)).aemeasurable

/-! ### The Gaussian vector has no atom at `0` -/

private lemma gaussVec_measurable_map (N : ℕ) :
    Measurable (fun (x : Fin N → ℝ × ℝ) (i : Fin N) => Complex.measurableEquivRealProd.symm (x i)) :=
  measurable_pi_lambda _ fun i => Complex.measurableEquivRealProd.symm.measurable.comp
    (measurable_pi_apply i)

private lemma gaussVec_isProb (N : ℕ) : IsProbabilityMeasure (gaussVec N) :=
  Measure.isProbabilityMeasure_map (gaussVec_measurable_map N).aemeasurable

private lemma gaussVec_compl_zero (N : ℕ) (hN : 1 ≤ N) : gaussVec N ({0}ᶜ) = 1 := by
  have := gaussVec_isProb N
  rw [prob_compl_eq_one_sub (measurableSet_singleton 0)]
  suffices h0 : gaussVec N {0} = 0 by rw [h0, tsub_zero]
  rw [gaussVec, Measure.map_apply (gaussVec_measurable_map N) (measurableSet_singleton 0)]
  refine measure_mono_null (t := Set.pi univ fun _ => {((0 : ℝ), (0 : ℝ))}) ?_ ?_
  · intro x hx i _
    have := congrFun hx i
    simp only [Pi.zero_apply] at this
    have h2 := congrArg Complex.measurableEquivRealProd this
    simpa using h2
  · rw [Measure.pi_pi]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, by omega⟩) ?_
    have hv : ((N : NNReal)⁻¹ / 2) ≠ 0 :=
      div_ne_zero (inv_ne_zero (by exact_mod_cast (show N ≠ 0 by omega))) two_ne_zero
    rw [← Set.singleton_prod_singleton, Measure.prod_prod,
      gaussianReal_absolutelyContinuous 0 hv Real.volume_singleton, zero_mul]

/-! ### Assembly -/

private instance laguerreEnsemble_sFinite (N : ℕ) (γ : ℝ) : SFinite (laguerreEnsemble N γ) := by
  unfold laguerreEnsemble; infer_instance

private lemma specMoment_one_eq {N : ℕ} (ω : Sample N) :
    specMoment 1 ω =
      ∑ i, Complex.normSq (ω.1 i) / (∑ j, Complex.normSq (ω.1 j)) * (ω.2.2 i)⁻¹ := by
  unfold specMoment uVec tau
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_one, map_div₀, Complex.normSq_ofReal,
    Real.mul_self_sqrt (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)]

private theorem mean_spectral_moment_divergent_aux (N : ℕ) (hN : 1 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    ∫⁻ ω, ENNReal.ofReal (specMoment 1 ω) ∂(localizedModel N γ) = ⊤ := by
  have := gaussVec_isProb N
  simp_rw [specMoment_one_eq]
  have hF : Measurable fun ω : Sample N => ENNReal.ofReal
      (∑ i, Complex.normSq (ω.1 i) / (∑ j, Complex.normSq (ω.1 j)) * (ω.2.2 i)⁻¹) := by
    have := Complex.continuous_normSq.measurable
    fun_prop
  unfold localizedModel
  rw [lintegral_prod _ hF.aemeasurable]
  refine eq_top_iff.2 ?_
  calc (⊤ : ENNReal) = ⊤ * gaussVec N ({0}ᶜ) := by rw [gaussVec_compl_zero N hN, mul_one]
    _ = ∫⁻ g, ({0}ᶜ : Set (Fin N → ℂ)).indicator (fun _ => ⊤) g ∂(gaussVec N) :=
        (lintegral_indicator_const (measurableSet_singleton 0).compl _).symm
    _ ≤ _ := lintegral_mono fun g => ?_
  by_cases hg : g = 0
  · rw [indicator_of_notMem (by simpa using hg)]; exact zero_le
  rw [indicator_of_mem (by simpa using hg)]
  refine le_trans ?_ (lintegral_prod _ (hF.comp measurable_prodMk_left).aemeasurable).symm.le
  obtain ⟨i₀, hi₀⟩ : ∃ i, g i ≠ 0 := by
    by_contra h; push Not at h; exact hg (funext h)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hS : 0 < ∑ j, Complex.normSq (g j) :=
    lt_of_lt_of_le (Complex.normSq_pos.2 hi₀)
      (Finset.single_le_sum (f := fun j => Complex.normSq (g j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i₀))
  have hinner : ∀ v : Fin (n + 1) → ℂ, ∫⁻ μ, ENNReal.ofReal
      (∑ i, Complex.normSq (g i) / (∑ j, Complex.normSq (g j)) * (μ i)⁻¹)
        ∂(laguerreEnsemble (n + 1) γ) = ⊤ := fun _ =>
    laguerre_lintegral_inv_eq_top n γ hγ i₀ _
      (fun i => div_nonneg (Complex.normSq_nonneg _) hS.le)
      (div_pos (Complex.normSq_pos.2 hi₀) hS)
  calc (⊤ : ENNReal) = ∫⁻ _v, ⊤ ∂(gaussVec (n + 1)) := by simp
    _ ≤ _ := lintegral_mono fun v => (hinner v).ge

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (N : ℕ) (hN : 1 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    ∫⁻ ω, ENNReal.ofReal (specMoment 1 ω) ∂(localizedModel N γ) = ⊤ :=
  mean_spectral_moment_divergent_aux N hN γ hγ
