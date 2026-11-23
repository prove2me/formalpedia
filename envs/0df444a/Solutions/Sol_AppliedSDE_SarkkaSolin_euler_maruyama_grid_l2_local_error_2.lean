-- Prove2me | solution 2 for AppliedSDE.SarkkaSolin.euler_maruyama_grid_l2_local_error
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T00:42:14.207284+00:00
-- url     : https://prove2.me/submissions/6ea48ff0-2ca2-44ed-9e5a-0e3461915f0f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionApi
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

open LevyStochCalc.Brownian.Ito in
/-- Isometry between the Itô integral of `H` and the integral of an adapted simple `G`. -/
theorem em_ito_sub_simple_isometry
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (h_sq : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T' : ℝ} (G : SimplePredictable Ω T')
    (hGa : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T') :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq t ω
        - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H ω s - G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have ht_nn : (0 : ℝ) ≤ t := le_of_lt ht
  set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) t) with hν
  set m := fun n => masterApprox ℱ H h_meas h_progMeas h_sq n with hm
  have hImeas : ∀ n, Measurable (fun ω => simpleIntegral W (m n) t ω) := by
    intro n
    unfold simpleIntegral
    exact Finset.measurable_sum _ (fun i _ =>
      ((m n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _)))
  have hGmeas : Measurable (fun ω => simpleIntegral W G t ω) := by
    unfold simpleIntegral
    exact Finset.measurable_sum _ (fun i _ =>
      (G.ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _)))
  have hbridge : ∀ f : Ω × ℝ → ℝ, Measurable f →
      ∫⁻ p, (‖f p‖₊ : ℝ≥0∞) ^ 2 ∂(P.prod ν)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro f hf
    rw [MeasureTheory.lintegral_prod _
      (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
  -- cross isometry for each `n`
  have hcross : ∀ n, ∫⁻ ω, (‖simpleIntegral W (m n) t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(m n).eval s ω - G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro n
    set K : ℝ := max ((n : ℝ) + 1) T' + 1 with hK
    have hKn : (m n).partition (Fin.last (m n).N) < K := by
      have h1 : (m n).partition (Fin.last (m n).N) ≤ (n : ℝ) + 1 := (m n).partition_le_T
      have := le_max_left ((n : ℝ) + 1) T'
      linarith
    have hKm : G.partition (Fin.last G.N) < K := by
      have h1 : G.partition (Fin.last G.N) ≤ T' := G.partition_le_T
      have := le_max_right ((n : ℝ) + 1) T'
      linarith
    have h_eq : ((m n).appendInterval hKn).partition (Fin.last ((m n).appendInterval hKn).N)
        = (G.appendInterval hKm).partition (Fin.last (G.appendInterval hKm).N) :=
      ((m n).appendInterval_partition_last hKn).trans (G.appendInterval_partition_last hKm).symm
    have ha_n := (m n).appendInterval_adapt ℱ hKn
      (masterApprox_adapt ℱ H h_meas h_progMeas h_sq n)
    have ha_m := G.appendInterval_adapt ℱ hKm hGa
    have hiso := simpleIntegral_intermediate_diff_isometry W ℱ hℱ ((m n).appendInterval hKn)
      (G.appendInterval hKm) h_eq ha_n ha_m ht_nn
    have hL : ∫⁻ ω, (‖simpleIntegral W (m n) t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖simpleIntegral W ((m n).appendInterval hKn) t ω
            - simpleIntegral W (G.appendInterval hKm) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      refine lintegral_congr (fun ω => ?_)
      rw [(m n).appendInterval_simpleIntegral W hKn t ω, G.appendInterval_simpleIntegral W hKm t ω]
    have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(m n).eval s ω - G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖((m n).appendInterval hKn).eval s ω - (G.appendInterval hKm).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
      refine lintegral_congr (fun ω => ?_)
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
      rw [(m n).appendInterval_eval hKn s ω, G.appendInterval_eval hKm s ω]
    rw [hL, hR]; exact hiso
  have hImemLp := stochasticIntegralBrownian_memLp W ℱ hℱ H h_meas h_progMeas h_sq t
  have hGmemLp : MemLp (fun ω => simpleIntegral W G t ω) 2 P :=
    simpleIntegral_memLp_intermediate_brownian W ℱ hℱ (lt_of_lt_of_le ht htT) G hGa ht_nn htT
  -- LHS limit
  have hLHS : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W (m n) t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds (∫⁻ ω,
        (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq t ω
          - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)) := by
    refine tendsto_lintegral_nnnorm_sq_of_eLpNorm
      (fun n => ((hImeas n).sub hGmeas).aestronglyMeasurable)
      (hImemLp.aestronglyMeasurable.sub hGmemLp.aestronglyMeasurable)
      ((hImemLp.sub hGmemLp).2.ne) ?_
    refine (masterApprox_tendsto_L2 W ℱ hℱ H h_meas h_progMeas h_sq ht_nn).congr (fun n => ?_)
    exact MeasureTheory.eLpNorm_congr_ae
      (Filter.Eventually.of_forall (fun ω => by simp only [Pi.sub_apply]; ring))
  -- RHS limit
  have hevalL2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun p : Ω × ℝ => (m n).eval p.2 p.1 - H p.1 p.2) 2 (P.prod ν))
        Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun p : Ω × ℝ => (m n).eval p.2 p.1 - H p.1 p.2) 2 (P.prod ν)
        ^ (2 : ℝ)) Filter.atTop (nhds 0) := by
      have he := masterApprox_eval_tendsto (t := t) ℱ H h_meas h_progMeas h_sq
      refine he.congr (fun n => ?_)
      rw [eLpNorm_sq_eq_lintegral_nnnorm_sq,
        hbridge (fun p : Ω × ℝ => (m n).eval p.2 p.1 - H p.1 p.2)
          (((m n).eval_jointly_measurable).sub h_meas)]
      refine lintegral_congr (fun ω => ?_)
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
      rw [show (‖H ω s - (m n).eval s ω‖₊ : ℝ≥0∞)
          = ‖(m n).eval s ω - H ω s‖₊ from by
        rw [← nnnorm_neg]; congr 1; ring_nf]
    have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr (fun n => ?_)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  have hGsq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(fun ω s => G.eval s ω) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T _ => eval_lintegral_sq_finite G T
  have hGm2 : Measurable (Function.uncurry (fun ω s => G.eval s ω)) := G.eval_jointly_measurable
  have hHdfin : MeasureTheory.eLpNorm (fun p : Ω × ℝ => H p.1 p.2 - G.eval p.2 p.1) 2 (P.prod ν)
      ≠ ⊤ :=
    ((compensatorH_memLp_prod H h_meas h_sq ht).sub
      (compensatorH_memLp_prod (fun ω s => G.eval s ω) hGm2 hGsq ht)).2.ne
  have hRHS' := tendsto_lintegral_nnnorm_sq_of_eLpNorm
    (μ := P.prod ν)
    (gₙ := fun n p => (m n).eval p.2 p.1 - G.eval p.2 p.1)
    (g := fun p => H p.1 p.2 - G.eval p.2 p.1)
    (fun n => (((m n).eval_jointly_measurable).sub
      G.eval_jointly_measurable).aestronglyMeasurable)
    (h_meas.aestronglyMeasurable.sub G.eval_jointly_measurable.aestronglyMeasurable) hHdfin
    (by
      refine hevalL2.congr (fun n => ?_)
      exact MeasureTheory.eLpNorm_congr_ae
        (Filter.Eventually.of_forall (fun p => by simp only [Pi.sub_apply]; ring)))
  rw [hbridge (fun p : Ω × ℝ => H p.1 p.2 - G.eval p.2 p.1)
    (h_meas.sub G.eval_jointly_measurable)] at hRHS'
  have hRHS : Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖(m n).eval s ω - G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s - G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
    refine hRHS'.congr' (Filter.Eventually.of_forall (fun n => ?_))
    exact (hbridge _ (((m n).eval_jointly_measurable).sub G.eval_jointly_measurable))
  exact tendsto_nhds_unique (hLHS.congr' (Filter.Eventually.of_forall (fun n => hcross n))) hRHS

theorem em_nnsq (x : ℝ) : (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), show ‖x‖ ^ 2 = x ^ 2 from by
      rw [Real.norm_eq_abs, sq_abs]]

open LevyStochCalc.Brownian.Ito in
/-- Itô integral minus a step sum with (unbounded) square-integrable adapted coefficients. -/
theorem em_ito_sub_step_le
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (h_sq : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {N : ℕ} (p : Fin (N + 1) → ℝ) (hp0 : p 0 = 0) (hpm : StrictMono p)
    (ht : 0 < p (Fin.last N))
    (Y : Fin N → Ω → ℝ)
    (hYa : ∀ i : Fin N, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ (p i.castSucc)) (Y i))
    (hY2 : ∀ i : Fin N, MemLp (Y i) 2 P) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq (p (Fin.last N)) ω
        - ∑ i : Fin N, Y i ω * (W.W (p i.succ) ω - W.W (p i.castSucc) ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) (p (Fin.last N)),
          (‖H ω s - ∑ i : Fin N,
            (if p i.castSucc < s ∧ s ≤ p i.succ then Y i ω else 0)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set t := p (Fin.last N) with ht_def
  set cl : ℕ → ℝ → ℝ := fun M y => max (-(M : ℝ)) (min (M : ℝ) y) with hcl
  have hcl_cont : ∀ M, Continuous (cl M) := fun M =>
    continuous_const.max (continuous_const.min continuous_id)
  have hcl_abs : ∀ M y, |cl M y| ≤ |y| := by
    intro M y
    have hM : (0 : ℝ) ≤ M := M.cast_nonneg
    have hy := abs_nonneg y
    refine abs_le.mpr ⟨le_trans (le_min (by linarith) (neg_abs_le y)) (le_max_right _ _),
      max_le (by linarith) (le_trans (min_le_right _ _) (le_abs_self y))⟩
  have hcl_bdd : ∀ (M : ℕ) y, |cl M y| ≤ M := by
    intro M y
    have hM : (0 : ℝ) ≤ M := M.cast_nonneg
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hcl_lim : ∀ y, Tendsto (fun M : ℕ => cl M y) atTop (𝓝 y) := by
    intro y
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|y|⌉₊] with M hM
    have h1 : |y| ≤ M := (Nat.le_ceil _).trans (by exact_mod_cast hM)
    show y = max (-(M : ℝ)) (min (M : ℝ) y)
    rw [min_eq_right (le_trans (le_abs_self y) h1), max_eq_right (by linarith [neg_abs_le y])]
  have hYm : ∀ i, Measurable (Y i) := fun i => ((hYa i).mono (ℱ.le _)).measurable
  let G : ℕ → SimplePredictable Ω t := fun M =>
    { N := N, partition := p, partition_zero := hp0, partition_le_T := le_rfl,
      partition_strictMono := hpm, ξ := fun i ω => cl M (Y i ω),
      ξ_bounded := fun i => ⟨M, fun ω => hcl_bdd M _⟩,
      ξ_measurable := fun i => (hcl_cont M).measurable.comp (hYm i) }
  have hGa : ∀ M, ∀ i : Fin (G M).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((G M).partition i.castSucc)) ((G M).ξ i) :=
    fun M i => (hcl_cont M).comp_stronglyMeasurable (hYa i)
  have hSI : ∀ M ω, simpleIntegral W (G M) t ω
      = ∑ i : Fin N, cl M (Y i ω) * (W.W (p i.succ) ω - W.W (p i.castSucc) ω) :=
    fun M ω => simpleIntegral_eq_sum W (G M) ω
  have hev : ∀ M s ω, (G M).eval s ω
      = ∑ i : Fin N, (if p i.castSucc < s ∧ s ≤ p i.succ then cl M (Y i ω) else 0) :=
    fun _ _ _ => rfl
  have hA : ∀ M, ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq t ω
        - ∑ i : Fin N, cl M (Y i ω) * (W.W (p i.succ) ω - W.W (p i.castSucc) ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H ω s - ∑ i : Fin N,
            (if p i.castSucc < s ∧ s ≤ p i.succ then cl M (Y i ω) else 0)‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
    intro M
    have h := em_ito_sub_simple_isometry W ℱ hℱ H h_meas h_progMeas h_sq (G M) (hGa M) ht le_rfl
    simp only [hSI, hev] at h
    exact h
  set sqf : ℝ → ℝ≥0∞ := fun x => (‖x‖₊ : ℝ≥0∞) ^ 2 with hsqf
  have hsqf_cont : Continuous sqf :=
    (ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)
  set I := stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq t with hI
  have hImeas : Measurable I :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H h_meas h_progMeas h_sq t).mono
      (ℱ.le t)).measurable
  set SM : ℕ → Ω → ℝ := fun M ω =>
    ∑ i : Fin N, cl M (Y i ω) * (W.W (p i.succ) ω - W.W (p i.castSucc) ω) with hSM
  set S : Ω → ℝ := fun ω =>
    ∑ i : Fin N, Y i ω * (W.W (p i.succ) ω - W.W (p i.castSucc) ω) with hS
  have hSMmeas : ∀ M, Measurable (SM M) := fun M =>
    Finset.measurable_sum _ (fun i _ => ((hcl_cont M).measurable.comp (hYm i)).mul
      ((W.measurable_eval _).sub (W.measurable_eval _)))
  have hLlim : ∀ ω, Tendsto (fun M => sqf (I ω - SM M ω)) atTop (𝓝 (sqf (I ω - S ω))) :=
    fun ω => (hsqf_cont.tendsto _).comp (tendsto_const_nhds.sub
      (tendsto_finsetSum _ (fun i _ => (hcl_lim _).mul_const _)))
  -- the right-hand sides converge (dominated convergence on the product measure)
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) t) with hν
  have hbridge : ∀ f : Ω × ℝ → ℝ, Measurable f →
      ∫⁻ q, sqf (f q) ∂(P.prod ν)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, sqf (f (ω, s)) ∂volume ∂P := by
    intro f hf
    rw [MeasureTheory.lintegral_prod _
      (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
  set K : ℕ → Ω × ℝ → ℝ := fun M q => H q.1 q.2 - ∑ i : Fin N,
    (if p i.castSucc < q.2 ∧ q.2 ≤ p i.succ then cl M (Y i q.1) else 0) with hK
  set K0 : Ω × ℝ → ℝ := fun q => H q.1 q.2 - ∑ i : Fin N,
    (if p i.castSucc < q.2 ∧ q.2 ≤ p i.succ then Y i q.1 else 0) with hK0
  have hset : ∀ i : Fin N, MeasurableSet {q : Ω × ℝ | p i.castSucc < q.2 ∧ q.2 ≤ p i.succ} :=
    fun i => (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hKmeas : ∀ M, Measurable (K M) := fun M => h_meas.sub
    (Finset.measurable_sum _ (fun i _ => Measurable.ite (hset i)
      (((hcl_cont M).measurable.comp (hYm i)).comp measurable_fst) measurable_const))
  have hK0meas : Measurable K0 := h_meas.sub
    (Finset.measurable_sum _ (fun i _ => Measurable.ite (hset i)
      ((hYm i).comp measurable_fst) measurable_const))
  set fS : Ω → ℝ := fun ω => ∑ i : Fin N, ‖Y i ω‖ with hfS
  have hfS2 : MemLp fS 2 P := memLp_finsetSum Finset.univ (fun i _ => (hY2 i).norm)
  have hfSm : Measurable fS := Finset.measurable_sum _ (fun i _ => (hYm i).norm)
  have hfSsq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(fun (ω : Ω) (_ : ℝ) => fS ω) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T _
    simp only [setLIntegral_const]
    rw [lintegral_mul_const' _ _ (by simp [Real.volume_Icc])]
    refine ENNReal.mul_lt_top ?_ (by simp [Real.volume_Icc])
    simp only [em_nnsq]
    exact hfS2.integrable_sq.lintegral_lt_top
  have hHL := compensatorH_memLp_prod H h_meas h_sq ht
  have hfL := compensatorH_memLp_prod (fun (ω : Ω) (_ : ℝ) => fS ω)
    (hfSm.comp measurable_fst) hfSsq ht
  set bnd : Ω × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (2 * (H q.1 q.2) ^ 2 + 2 * (fS q.1) ^ 2)
    with hbnd
  have hbnd_fin : ∫⁻ q, bnd q ∂(P.prod ν) ≠ ⊤ :=
    ((hHL.integrable_sq.const_mul 2).add (hfL.integrable_sq.const_mul 2)).lintegral_lt_top.ne
  have hbound : ∀ M, (fun q => sqf (K M q)) ≤ᵐ[P.prod ν] bnd := by
    intro M
    refine Filter.Eventually.of_forall (fun q => ?_)
    simp only [hsqf, em_nnsq, hbnd, hK]
    refine ENNReal.ofReal_le_ofReal ?_
    set a := H q.1 q.2
    set c := ∑ i : Fin N, (if p i.castSucc < q.2 ∧ q.2 ≤ p i.succ then cl M (Y i q.1) else 0)
    have hc : |c| ≤ fS q.1 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
      split_ifs
      · rw [Real.norm_eq_abs]; exact hcl_abs M _
      · simp
    have h1 : c ^ 2 ≤ (fS q.1) ^ 2 := by
      rw [← sq_abs c]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
    nlinarith [sq_nonneg (a + c)]
  have hlim : ∀ᵐ q ∂(P.prod ν), Tendsto (fun M => sqf (K M q)) atTop (𝓝 (sqf (K0 q))) := by
    refine Filter.Eventually.of_forall (fun q => ?_)
    refine (hsqf_cont.tendsto _).comp (tendsto_const_nhds.sub
      (tendsto_finsetSum _ (fun i _ => ?_)))
    by_cases hq : p i.castSucc < q.2 ∧ q.2 ≤ p i.succ
    · simp only [hq, and_self, if_true]; exact hcl_lim _
    · simp only [hq, if_false]; exact tendsto_const_nhds
  have hD := tendsto_lintegral_of_dominated_convergence bnd
    (fun M => ((hKmeas M).nnnorm.coe_nnreal_ennreal).pow_const 2) hbound hbnd_fin hlim
  have hR : Tendsto (fun M => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, sqf (K M (ω, s)) ∂volume ∂P)
      atTop (𝓝 (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, sqf (K0 (ω, s)) ∂volume ∂P)) := by
    rw [← hbridge K0 hK0meas]
    exact hD.congr (fun M => hbridge (K M) (hKmeas M))
  calc ∫⁻ ω, sqf (I ω - S ω) ∂P
      = ∫⁻ ω, liminf (fun M => sqf (I ω - SM M ω)) atTop ∂P :=
        lintegral_congr (fun ω => (hLlim ω).liminf_eq.symm)
    _ ≤ liminf (fun M => ∫⁻ ω, sqf (I ω - SM M ω) ∂P) atTop :=
        lintegral_liminf_le (fun M => ((hImeas.sub (hSMmeas M)).nnnorm.coe_nnreal_ennreal).pow_const 2)
    _ = liminf (fun M => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, sqf (K M (ω, s)) ∂volume ∂P) atTop := by
        congr 1; funext M; exact hA M
    _ = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, sqf (K0 (ω, s)) ∂volume ∂P := hR.liminf_eq

/-- Lipschitz functions on `ℝ` are continuous. -/
theorem em_lip_continuous (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) : Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) (fun x y => ?_)).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL]; exact hf x y

/-- The Euler–Maruyama iterates are adapted. -/
theorem em_sq_add_le (u v : ℝ) : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
  nlinarith [sq_nonneg (u - v)]

/-- Cauchy–Schwarz on an interval: `(∫ f)^2 ≤ (b - a) ∫ f^2`. -/
theorem em_interval_cs (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun u => f u ^ 2) volume a b) :
    (∫ u in a..b, f u) ^ 2 ≤ (b - a) * ∫ u in a..b, f u ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  have hd : 0 < b - a := by linarith
  set A := ∫ u in a..b, f u with hA
  set B := ∫ u in a..b, f u ^ 2 with hB
  set m := A / (b - a) with hm
  have h0 : 0 ≤ ∫ u in a..b, (f u - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
  have hexp : ∫ u in a..b, (f u - m) ^ 2 = B - 2 * m * A + (b - a) * m ^ 2 := by
    have e : (fun u => (f u - m) ^ 2) = fun u => (f u ^ 2 - (2 * m) * f u) + m ^ 2 := by
      funext u; ring
    rw [e, intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hf.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [hexp] at h0
  have hmA : A = m * (b - a) := by rw [hm]; field_simp
  rw [hmA] at h0 ⊢
  nlinarith [mul_nonneg hd.le h0]

open LevyStochCalc.Brownian.Ito in
/-- Increment isometry for the Itô integral. -/
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
    simp_rw [← em_nnsq]
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
    simp_rw [em_nnsq]
    exact hms.integrable_sq.lintegral_lt_top.ne
  have hB : ∫⁻ ω, ∫⁻ u in Set.Ioc s t, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := by
    have h := horizon_lintegral_add (P := P) H h_meas hs hst
    rw [← stochasticIntegralBrownian_lintegral_sq W ℱ hℱ H h_meas h_progMeas h_sq (hs.trans hst)]
      at h
    have hfin : ∫⁻ ω, (‖I t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := by
      simp_rw [em_nnsq]; exact hmt.integrable_sq.lintegral_lt_top.ne
    rw [h] at hfin
    exact (ENNReal.add_ne_top.mp hfin).2
  rw [ENNReal.toReal_add hA hB]
  ring

noncomputable def emPic (b : ℝ → ℝ) (x₀ : ℝ) (m : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun t => x₀ + m t
  | j + 1 => fun t => x₀ + (∫ r in (0 : ℝ)..t, b (emPic b x₀ m j r)) + m t

theorem em_pic_cont (b : ℝ → ℝ) (hb : Continuous b) (x₀ : ℝ) (m : ℝ → ℝ) (hm : Continuous m) :
    ∀ j, Continuous (emPic b x₀ m j) := by
  intro j
  induction j with
  | zero => exact continuous_const.add hm
  | succ j ih =>
    exact (continuous_const.add (intervalIntegral.continuous_primitive
      (fun a c => (hb.comp ih).intervalIntegrable a c) 0)).add hm

theorem em_iter_bound (u : ℕ → ℝ → ℝ) (hu : ∀ j, Continuous (u j)) (C L T : ℝ) (hL : 0 ≤ L)
    (h0 : ∀ t ∈ Set.Icc (0 : ℝ) T, |u 0 t| ≤ C)
    (hs : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, |u (j + 1) t| ≤ L * ∫ r in (0 : ℝ)..t, |u j r|) :
    ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, |u j t| ≤ C * (L * t) ^ j / (Nat.factorial j : ℝ) := by
  intro j
  induction j with
  | zero => intro t ht; simpa using h0 t ht
  | succ j ih =>
    intro t ht
    have hmono : ∫ r in (0 : ℝ)..t, |u j r| ≤ ∫ r in (0 : ℝ)..t, C * (L * r) ^ j / (Nat.factorial j : ℝ) := by
      refine intervalIntegral.integral_mono_on ht.1 ((hu j).abs.intervalIntegrable _ _)
        (by apply Continuous.intervalIntegrable; fun_prop) (fun r hr => ih r ⟨hr.1, hr.2.trans ht.2⟩)
    have hcalc : ∫ r in (0 : ℝ)..t, C * (L * r) ^ j / (Nat.factorial j : ℝ) =
        C * L ^ j / (Nat.factorial j : ℝ) * (t ^ (j + 1) / (j + 1)) := by
      have : (fun r : ℝ => C * (L * r) ^ j / (Nat.factorial j : ℝ)) = fun r => C * L ^ j / (Nat.factorial j : ℝ) * r ^ j := by
        funext r; rw [mul_pow]; ring
      rw [this, intervalIntegral.integral_const_mul, integral_pow]
      simp
    calc |u (j + 1) t| ≤ L * ∫ r in (0 : ℝ)..t, |u j r| := hs j t ht
      _ ≤ L * (C * L ^ j / (Nat.factorial j : ℝ) * (t ^ (j + 1) / (j + 1))) := by
          rw [← hcalc]; exact mul_le_mul_of_nonneg_left hmono hL
      _ = C * (L * t) ^ (j + 1) / (Nat.factorial (j + 1) : ℝ) := by
          rw [Nat.factorial_succ]; push_cast
          have : (Nat.factorial j : ℝ) ≠ 0 := by positivity
          field_simp
          ring

theorem em_pic_conv (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (x₀ T : ℝ) (m x : ℝ → ℝ) (hm : Continuous m) (hx : Continuous x)
    (hsol : ∀ t ∈ Set.Icc (0 : ℝ) T, x t = x₀ + (∫ r in (0 : ℝ)..t, b (x r)) + m t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun j => emPic b x₀ m j t) atTop (𝓝 (x t)) := by
  have hbc : Continuous b := (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) fun x y => by
    rw [Real.dist_eq, Real.dist_eq]; exact hb x y).continuous
  have hpc := em_pic_cont b hbc x₀ m hm
  set u : ℕ → ℝ → ℝ := fun j t => emPic b x₀ m j t - x t with hu
  have huc : ∀ j, Continuous (u j) := fun j => (hpc j).sub hx
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (huc 0).continuousOn
    (s := Set.Icc (0 : ℝ) T)
  have hbound := em_iter_bound u huc C L T hL (fun t ht => by simpa using hC t ht)
    (fun j t ht => by
      have e : u (j + 1) t = ∫ r in (0 : ℝ)..t, (b (emPic b x₀ m j r) - b (x r)) := by
        have hi1 : IntervalIntegrable (fun r => b (emPic b x₀ m j r)) volume 0 t :=
          (hbc.comp (hpc j)).intervalIntegrable _ _
        have hi2 : IntervalIntegrable (fun r => b (x r)) volume 0 t :=
          (hbc.comp hx).intervalIntegrable _ _
        simp only [hu, emPic]
        rw [hsol t ht, intervalIntegral.integral_sub hi1 hi2]
        ring
      rw [e]
      refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on ht.1
        (((hbc.comp (hpc j)).sub (hbc.comp hx)).abs.intervalIntegrable _ _)
        ((continuous_const.mul (huc j).abs).intervalIntegrable _ _) (fun r _ => hb _ _))
  intro t ht
  rw [← tendsto_sub_nhds_zero_iff]
  have hlim := (FloorSemiring.tendsto_pow_div_factorial_atTop (L * t)).const_mul C
  rw [mul_zero] at hlim
  refine squeeze_zero_norm (fun j => ?_) hlim
  rw [Real.norm_eq_abs]
  exact (hbound j t ht).trans_eq (by ring)

theorem em_pic_bound (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (x₀ T : ℝ) (m x : ℝ → ℝ) (hm : Continuous m) (hx : Continuous x)
    (hsol : ∀ t ∈ Set.Icc (0 : ℝ) T, x t = x₀ + (∫ r in (0 : ℝ)..t, b (x r)) + m t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, |x t| ≤
      |x₀| + |m t| + Real.exp (L * T) * ∫ r in (0 : ℝ)..T, |b (x₀ + m r)| := by
  have hbc : Continuous b := (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) fun x y => by
    rw [Real.dist_eq, Real.dist_eq]; exact hb x y).continuous
  have hpc := em_pic_cont b hbc x₀ m hm
  set D := ∫ r in (0 : ℝ)..T, |b (x₀ + m r)| with hD
  set v : ℕ → ℝ → ℝ := fun j t => emPic b x₀ m (j + 1) t - emPic b x₀ m j t with hv
  have hvc : ∀ j, Continuous (v j) := fun j => (hpc (j + 1)).sub (hpc j)
  have hbound := em_iter_bound v hvc D L T hL
    (fun t ht => by
      have e : v 0 t = ∫ r in (0 : ℝ)..t, b (x₀ + m r) := by simp only [hv, emPic]; ring
      rw [e]
      refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans ?_
      exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall fun r => abs_nonneg _)
        ((hbc.comp (continuous_const.add hm)).abs.intervalIntegrable _ _))
    (fun j t ht => by
      have e : v (j + 1) t = ∫ r in (0 : ℝ)..t,
          (b (emPic b x₀ m (j + 1) r) - b (emPic b x₀ m j r)) := by
        have hi1 : IntervalIntegrable (fun r => b (emPic b x₀ m (j + 1) r)) volume 0 t :=
          (hbc.comp (hpc (j + 1))).intervalIntegrable _ _
        have hi2 : IntervalIntegrable (fun r => b (emPic b x₀ m j r)) volume 0 t :=
          (hbc.comp (hpc j)).intervalIntegrable _ _
        simp only [hv]
        rw [show emPic b x₀ m (j + 1 + 1) t =
            x₀ + (∫ r in (0 : ℝ)..t, b (emPic b x₀ m (j + 1) r)) + m t from rfl,
          show emPic b x₀ m (j + 1) t =
            x₀ + (∫ r in (0 : ℝ)..t, b (emPic b x₀ m j r)) + m t from rfl,
          intervalIntegral.integral_sub hi1 hi2]
        ring
      rw [e]
      refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on ht.1
        (((hbc.comp (hpc (j + 1))).sub (hbc.comp (hpc j))).abs.intervalIntegrable _ _)
        ((continuous_const.mul (hvc j).abs).intervalIntegrable _ _) (fun r _ => hb _ _))
  intro t ht
  have hD0 : 0 ≤ D := intervalIntegral.integral_nonneg (ht.1.trans ht.2) (fun r _ => abs_nonneg _)
  have hLt : 0 ≤ L * t := mul_nonneg hL ht.1
  have hsum : ∀ J, |emPic b x₀ m J t - emPic b x₀ m 0 t| ≤ D * Real.exp (L * T) := by
    intro J
    have htel : emPic b x₀ m J t - emPic b x₀ m 0 t = ∑ j ∈ Finset.range J, v j t := by
      rw [Finset.sum_range_sub (fun j => emPic b x₀ m j t)]
    rw [htel]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hbound j t ht).trans ?_
    calc ∑ j ∈ Finset.range J, D * (L * t) ^ j / (Nat.factorial j : ℝ)
        = D * ∑ j ∈ Finset.range J, (L * t) ^ j / (Nat.factorial j : ℝ) := by
          rw [Finset.mul_sum]; congr 1; funext j; ring
      _ ≤ D * Real.exp (L * t) := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hLt J) hD0
      _ ≤ D * Real.exp (L * T) := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hL)) hD0
  have hconv := em_pic_conv b L hL hb x₀ T m x hm hx hsol t ht
  have hlim : |x t - emPic b x₀ m 0 t| ≤ D * Real.exp (L * T) :=
    le_of_tendsto ((hconv.sub_const _).abs) (Eventually.of_forall hsum)
  have h0 : emPic b x₀ m 0 t = x₀ + m t := rfl
  rw [h0] at hlim
  have := abs_add_le x₀ (m t)
  have h3 : |x t| ≤ |x t - (x₀ + m t)| + |x₀ + m t| := by
    have := abs_add_le (x t - (x₀ + m t)) (x₀ + m t); simpa using this
  linarith [mul_comm D (Real.exp (L * T))]

noncomputable def emDy (n : ℕ) (c : ℝ) : ℝ := (⌊c * 2 ^ n⌋₊ : ℝ) / 2 ^ n

noncomputable def emClamp (T s : ℝ) : ℝ := min (max s 0) T

noncomputable def emMhat {Ω : Type*} (I : ℝ → Ω → ℝ) (T : ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => I (emDy n (emClamp T s)) ω)

noncomputable def emXhat {Ω : Type*} (b : ℝ → ℝ) (x₀ : ℝ) (I : ℝ → Ω → ℝ) (T : ℝ)
    (s : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop (fun j => emPic b x₀ (fun r => emMhat I T r ω) j s)

theorem em_dy_nonneg (n : ℕ) (c : ℝ) : 0 ≤ emDy n c := by unfold emDy; positivity

theorem em_dy_le (n : ℕ) {c : ℝ} (hc : 0 ≤ c) : emDy n c ≤ c := by
  unfold emDy
  rw [div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem em_dy_tendsto {c : ℝ} (hc : 0 ≤ c) : Tendsto (fun n => emDy n c) atTop (𝓝 c) := by
  have hlow : ∀ n : ℕ, c - (1 / 2) ^ n ≤ emDy n c := by
    intro n
    unfold emDy
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [le_div_iff₀ h2, one_div, inv_pow, sub_mul, inv_mul_cancel₀ h2.ne']
    have := Nat.lt_floor_add_one (c * 2 ^ n)
    linarith
  have hlim : Tendsto (fun n : ℕ => c - (1 / 2 : ℝ) ^ n) atTop (𝓝 c) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_sub c
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow
    (fun n => em_dy_le n hc)

theorem em_clamp_mem {T : ℝ} (hT : 0 ≤ T) (s : ℝ) : emClamp T s ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_min (le_max_right _ _) hT, min_le_right _ _⟩

theorem em_clamp_of_mem {T s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) : emClamp T s = s := by
  unfold emClamp; rw [max_eq_left hs.1, min_eq_left hs.2]

theorem em_clamp_cont (T : ℝ) : Continuous (emClamp T) := by
  unfold emClamp; fun_prop

theorem em_param_integral {β : Type*} [MeasurableSpace β] (f : β → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f)) (τ : β → ℝ) (hτ : Measurable τ) :
    Measurable (fun y => ∫ r in (0 : ℝ)..τ y, f y r) := by
  have hS1 : MeasurableSet {p : β × ℝ | 0 < p.2 ∧ p.2 ≤ τ p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hτ.comp measurable_fst))
  have hS2 : MeasurableSet {p : β × ℝ | τ p.1 < p.2 ∧ p.2 ≤ 0} :=
    (measurableSet_lt (hτ.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have h1 := ((hf.indicator hS1).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable
  have h2 := ((hf.indicator hS2).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ))).measurable
  have key : ∀ y, ∫ r in (0 : ℝ)..τ y, f y r =
      (∫ r, Set.indicator {p : β × ℝ | 0 < p.2 ∧ p.2 ≤ τ p.1} (Function.uncurry f) (y, r)) -
      ∫ r, Set.indicator {p : β × ℝ | τ p.1 < p.2 ∧ p.2 ≤ 0} (Function.uncurry f) (y, r) := by
    intro y
    have e1 : (fun r => Set.indicator {p : β × ℝ | 0 < p.2 ∧ p.2 ≤ τ p.1} (Function.uncurry f) (y, r))
        = Set.indicator (Set.Ioc 0 (τ y)) (f y) := by
      funext r; simp only [Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioc, Function.uncurry_apply_pair]
      split_ifs <;> rfl
    have e2 : (fun r => Set.indicator {p : β × ℝ | τ p.1 < p.2 ∧ p.2 ≤ 0} (Function.uncurry f) (y, r))
        = Set.indicator (Set.Ioc (τ y) 0) (f y) := by
      funext r; simp only [Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioc, Function.uncurry_apply_pair]
      split_ifs <;> rfl
    rw [e1, e2, integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
    rfl
  simp_rw [key]
  exact h1.sub h2

theorem em_mhat_meas {Ω : Type*} [MeasurableSpace Ω] (I : ℝ → Ω → ℝ) (T t : ℝ) (hT0 : 0 ≤ T)
    (ht0 : 0 ≤ t) (hI : ∀ r, 0 ≤ r → r ≤ t → Measurable (I r)) :
    Measurable (fun p : ℝ × Ω => emMhat I T (min p.1 t) p.2) := by
  have hn : ∀ n : ℕ, Measurable (fun p : ℝ × Ω => I (emDy n (emClamp T (min p.1 t))) p.2) := by
    intro n
    set J : Ω × ℕ → ℝ := fun q => I (min ((q.2 : ℝ) / 2 ^ n) t) q.1 with hJ
    have hJm : Measurable J := measurable_from_prod_countable_left (fun k => by
      exact hI (min ((k : ℝ) / 2 ^ n) t) (le_min (by positivity) ht0) (min_le_right _ _))
    have hk : Measurable (fun s : ℝ => ⌊emClamp T (min s t) * 2 ^ n⌋₊) :=
      (((em_clamp_cont T).comp (continuous_id.min continuous_const)).mul
        continuous_const).measurable.nat_floor
    have hcomp := hJm.comp (measurable_snd.prodMk (hk.comp measurable_fst))
    have heq : (fun p : ℝ × Ω => I (emDy n (emClamp T (min p.1 t))) p.2) =
        J ∘ (fun p : ℝ × Ω => (p.2, ⌊emClamp T (min p.1 t) * 2 ^ n⌋₊)) := by
      funext p
      have hc0 : 0 ≤ emClamp T (min p.1 t) := le_min (le_max_right _ _) hT0
      have hct : emClamp T (min p.1 t) ≤ t :=
        (min_le_left _ _).trans (max_le (min_le_right _ _) ht0)
      have hle : emDy n (emClamp T (min p.1 t)) ≤ t := (em_dy_le n hc0).trans hct
      simp only [Function.comp, hJ]
      rw [show ((⌊emClamp T (min p.1 t) * 2 ^ n⌋₊ : ℕ) : ℝ) / 2 ^ n =
        emDy n (emClamp T (min p.1 t)) from rfl, min_eq_left hle]
    rw [heq]; exact hcomp
  exact (StronglyMeasurable.limUnder (fun n => (hn n).stronglyMeasurable)).measurable

theorem em_pic_meas {Ω : Type*} [MeasurableSpace Ω] (b : ℝ → ℝ) (hb : Continuous b) (x₀ : ℝ)
    (M : ℝ → Ω → ℝ) (t : ℝ) (ht0 : 0 ≤ t)
    (hM : Measurable (fun p : ℝ × Ω => M (min p.1 t) p.2)) :
    ∀ j, Measurable (fun p : ℝ × Ω => emPic b x₀ (fun r => M r p.2) j (min p.1 t)) := by
  intro j
  induction j with
  | zero => exact measurable_const.add hM
  | succ j ih =>
    have hint : Measurable (fun p : ℝ × Ω =>
        ∫ r in (0 : ℝ)..(min p.1 t), b (emPic b x₀ (fun r => M r p.2) j (min r t))) := by
      refine em_param_integral
        (fun (p : ℝ × Ω) (r : ℝ) => b (emPic b x₀ (fun r => M r p.2) j (min r t)))
        ?_ (fun p => min p.1 t) (measurable_fst.min measurable_const)
      exact hb.measurable.comp (ih.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    have heq : (fun p : ℝ × Ω => emPic b x₀ (fun r => M r p.2) (j + 1) (min p.1 t)) =
        fun p => x₀ + (∫ r in (0 : ℝ)..(min p.1 t),
          b (emPic b x₀ (fun r => M r p.2) j (min r t))) + M (min p.1 t) p.2 := by
      funext p
      show x₀ + (∫ r in (0 : ℝ)..(min p.1 t), b (emPic b x₀ (fun r => M r p.2) j r)) +
        M (min p.1 t) p.2 = _
      congr 2
      refine intervalIntegral.integral_congr (fun r hr => ?_)
      have : r ≤ t := by
        rw [Set.uIcc, Set.mem_Icc] at hr
        exact hr.2.trans (max_le ht0 (min_le_right _ _))
      simp only [min_eq_left this]
    rw [heq]
    exact (measurable_const.add hint).add hM

theorem em_xhat_meas {Ω : Type*} [MeasurableSpace Ω] (b : ℝ → ℝ) (hb : Continuous b) (x₀ : ℝ)
    (I : ℝ → Ω → ℝ) (T t : ℝ) (hT0 : 0 ≤ T) (ht0 : 0 ≤ t)
    (hI : ∀ r, 0 ≤ r → r ≤ t → Measurable (I r)) :
    Measurable (fun p : ℝ × Ω => emXhat b x₀ I T (min p.1 t) p.2) :=
  (StronglyMeasurable.limUnder (fun j => (em_pic_meas b hb x₀ (emMhat I T) t ht0
    (em_mhat_meas I T t hT0 ht0 hI) j).stronglyMeasurable)).measurable

theorem em_slice_meas {Ω : Type*} [MeasurableSpace Ω] (F : ℝ → Ω → ℝ) (t : ℝ)
    (hF : Measurable (fun p : ℝ × Ω => F (min p.1 t) p.2)) : Measurable (F t) := by
  have h : Measurable (fun ω : Ω => ((t : ℝ), ω)) := measurable_const.prodMk measurable_id
  have := hF.comp h
  simpa [Function.comp_def] using this



theorem em_lip_cont' (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) :
    Continuous b :=
  (LipschitzWith.of_dist_le_mul (K := ⟨L, hL⟩) fun x y => by
    rw [Real.dist_eq, Real.dist_eq]; exact hb x y).continuous

theorem em_mhat_clamp {Ω : Type*} (I : ℝ → Ω → ℝ) {T : ℝ} (hT : 0 ≤ T) (s : ℝ) (ω : Ω) :
    emMhat I T (min s T) ω = emMhat I T s ω := by
  have : emClamp T (min s T) = emClamp T s := by
    simp only [emClamp]
    rcases le_total s T with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, max_eq_left hT, min_self,
        min_eq_right (h.trans (le_max_left _ _))]
  simp only [emMhat, this]

theorem em_good {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (I : ℝ → Ω → ℝ) (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (x₀ T : ℝ) (hT : 0 ≤ T) (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T → (fun ω => X t ω) =ᵐ[P]
      fun ω => x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) + I t ω) :
    ∀ᵐ ω ∂P, Continuous (fun t => X t ω) ∧ Continuous (fun s => emMhat I T s ω) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T,
        X s ω = x₀ + (∫ r in (0 : ℝ)..s, b (X r ω)) + emMhat I T s ω := by
  have hbc := em_lip_cont' b L hL hb
  have hdy : ∀ᵐ ω ∂P, ∀ n k : ℕ, ((k : ℝ) / 2 ^ n ≤ T) →
      X ((k : ℝ) / 2 ^ n) ω = x₀ + (∫ s in (0 : ℝ)..((k : ℝ) / 2 ^ n), b (X s ω)) +
        I ((k : ℝ) / 2 ^ n) ω := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro k
    by_cases h : (k : ℝ) / 2 ^ n ≤ T
    · filter_upwards [hXeq _ (by positivity) h] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h' => absurd h' h
  filter_upwards [hXcont, hdy] with ω hc hd
  set g : ℝ → ℝ := fun s => X s ω - x₀ - ∫ r in (0 : ℝ)..s, b (X r ω) with hg
  have hgc : Continuous g := (hc.sub continuous_const).sub
    (intervalIntegral.continuous_primitive (fun a c => (hbc.comp hc).intervalIntegrable a c) 0)
  have hM : ∀ s, emMhat I T s ω = g (emClamp T s) := by
    intro s
    have hcm := em_clamp_mem hT s
    have htend : Tendsto (fun n => I (emDy n (emClamp T s)) ω) atTop
        (𝓝 (g (emClamp T s))) := by
      have h1 := (hgc.tendsto _).comp (em_dy_tendsto hcm.1)
      refine h1.congr (fun n => ?_)
      have hle : emDy n (emClamp T s) ≤ T := (em_dy_le n hcm.1).trans hcm.2
      have h2 := hd n ⌊emClamp T s * 2 ^ n⌋₊ hle
      change X (emDy n (emClamp T s)) ω = x₀ + (∫ r in (0 : ℝ)..(emDy n (emClamp T s)),
        b (X r ω)) + I (emDy n (emClamp T s)) ω at h2
      show g (emDy n (emClamp T s)) = I (emDy n (emClamp T s)) ω
      simp only [hg]
      rw [h2]; ring
    exact htend.limUnder_eq
  refine ⟨hc, ?_, fun s hs => ?_⟩
  · have : (fun s => emMhat I T s ω) = g ∘ emClamp T := funext hM
    rw [this]; exact hgc.comp (em_clamp_cont T)
  · rw [hM s, em_clamp_of_mem hs]; simp only [hg]; ring

theorem em_xhat_eq {Ω : Type*} (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) (x₀ T : ℝ) (I : ℝ → Ω → ℝ)
    (X : ℝ → Ω → ℝ) (ω : Ω)
    (hc : Continuous (fun t => X t ω)) (hm : Continuous (fun s => emMhat I T s ω))
    (hsol : ∀ s ∈ Set.Icc (0 : ℝ) T,
      X s ω = x₀ + (∫ r in (0 : ℝ)..s, b (X r ω)) + emMhat I T s ω) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, emXhat b x₀ I T s ω = X s ω :=
  fun s hs => (em_pic_conv b L hL hb x₀ T (fun r => emMhat I T r ω) (fun t => X t ω) hm hc
    hsol s hs).limUnder_eq

theorem em_adapted_abs {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (ℱ : MeasureTheory.Filtration ℝ mΩ)
    (I : ℝ → Ω → ℝ) (hIa : ∀ r, StronglyMeasurable[ℱ r] (I r))
    (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (x₀ T : ℝ) (hT : 0 ≤ T) (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T → (fun ω => X t ω) =ᵐ[P]
      fun ω => x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) + I t ω) :
    ∀ t : ℝ, 0 ≤ t → t ≤ T → AEStronglyMeasurable[ℱ t] (X t) P := by
  have hbc := em_lip_cont' b L hL hb
  intro t ht0 htT
  have hmeas : Measurable[ℱ t] (emXhat b x₀ I T t) :=
    @em_slice_meas Ω (ℱ t) (emXhat b x₀ I T) t
      (@em_xhat_meas Ω (ℱ t) b hbc x₀ I T t hT ht0
        (fun r _ hrt => ((hIa r).measurable).mono (ℱ.mono hrt) le_rfl))
  refine ⟨emXhat b x₀ I T t, hmeas.stronglyMeasurable, ?_⟩
  filter_upwards [em_good I b L hL hb x₀ T hT X hXcont hXeq] with ω hω
  exact (em_xhat_eq b L hL hb x₀ T I X ω hω.1 hω.2.1 hω.2.2 t ⟨ht0, htT⟩).symm

theorem em_mhat_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (I : ℝ → Ω → ℝ) (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (x₀ T : ℝ) (hT : 0 ≤ T) (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T → (fun ω => X t ω) =ᵐ[P]
      fun ω => x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) + I t ω)
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) T) :
    (fun ω => emMhat I T r ω) =ᵐ[P] I r := by
  filter_upwards [em_good I b L hL hb x₀ T hT X hXcont hXeq, hXeq r hr.1 hr.2] with ω hω h2
  have h1 := hω.2.2 r hr
  linarith

theorem em_path_sq {b : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) (x₀ T : ℝ) (hT : 0 ≤ T)
    (m x : ℝ → ℝ) (hm : Continuous m) (hx : Continuous x)
    (hsol : ∀ t ∈ Set.Icc (0 : ℝ) T, x t = x₀ + (∫ r in (0 : ℝ)..t, b (x r)) + m t)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    x t ^ 2 ≤ (3 * x₀ ^ 2 + 6 * Real.exp (L * T) ^ 2 * T ^ 2 * b x₀ ^ 2) + 3 * m t ^ 2 +
      (6 * Real.exp (L * T) ^ 2 * T * L ^ 2) * ∫ r in (0 : ℝ)..T, m r ^ 2 := by
  have hbc := em_lip_cont' b L hL hb
  have h1 := em_pic_bound b L hL hb x₀ T m x hm hx hsol t ht
  set E := Real.exp (L * T)
  set D := ∫ r in (0 : ℝ)..T, |b (x₀ + m r)|
  have hfc : Continuous (fun r => |b (x₀ + m r)|) := (hbc.comp (continuous_const.add hm)).abs
  have hD0 : 0 ≤ D := intervalIntegral.integral_nonneg hT (fun r _ => abs_nonneg _)
  have hcs := em_interval_cs (fun r => |b (x₀ + m r)|) 0 T hT (hfc.intervalIntegrable _ _)
    ((hfc.pow 2).intervalIntegrable _ _)
  have hpt : ∀ r, |b (x₀ + m r)| ^ 2 ≤ 2 * b x₀ ^ 2 + 2 * L ^ 2 * m r ^ 2 := by
    intro r
    have h := hb (x₀ + m r) x₀
    rw [add_sub_cancel_left] at h
    have h' : |b (x₀ + m r)| ≤ |b x₀| + L * |m r| := by
      have := abs_sub_abs_le_abs_sub (b (x₀ + m r)) (b x₀); linarith
    have h0 : 0 ≤ |b (x₀ + m r)| := abs_nonneg _
    calc |b (x₀ + m r)| ^ 2 ≤ (|b x₀| + L * |m r|) ^ 2 := pow_le_pow_left₀ h0 h' 2
      _ ≤ 2 * |b x₀| ^ 2 + 2 * (L * |m r|) ^ 2 := em_sq_add_le _ _
      _ = 2 * b x₀ ^ 2 + 2 * L ^ 2 * m r ^ 2 := by rw [mul_pow, sq_abs, sq_abs]; ring
  have hint : ∫ r in (0 : ℝ)..T, |b (x₀ + m r)| ^ 2 ≤ 2 * b x₀ ^ 2 * T +
      2 * L ^ 2 * ∫ r in (0 : ℝ)..T, m r ^ 2 := by
    have hm2 : IntervalIntegrable (fun r => m r ^ 2) volume 0 T := (hm.pow 2).intervalIntegrable _ _
    calc ∫ r in (0 : ℝ)..T, |b (x₀ + m r)| ^ 2
        ≤ ∫ r in (0 : ℝ)..T, (2 * b x₀ ^ 2 + 2 * L ^ 2 * m r ^ 2) :=
          intervalIntegral.integral_mono_on hT ((hfc.pow 2).intervalIntegrable _ _)
            (intervalIntegrable_const.add (hm2.const_mul _)) (fun r _ => hpt r)
      _ = 2 * b x₀ ^ 2 * T + 2 * L ^ 2 * ∫ r in (0 : ℝ)..T, m r ^ 2 := by
          have hc : ∫ r in (0 : ℝ)..T, 2 * L ^ 2 * m r ^ 2 =
              2 * L ^ 2 * ∫ r in (0 : ℝ)..T, m r ^ 2 := intervalIntegral.integral_const_mul _ _
          rw [intervalIntegral.integral_add intervalIntegrable_const (hm2.const_mul _), hc,
            intervalIntegral.integral_const, smul_eq_mul]
          ring
  have hI0 : 0 ≤ ∫ r in (0 : ℝ)..T, m r ^ 2 :=
    intervalIntegral.integral_nonneg hT (fun r _ => sq_nonneg _)
  have hD2 : D ^ 2 ≤ T * (2 * b x₀ ^ 2 * T + 2 * L ^ 2 * ∫ r in (0 : ℝ)..T, m r ^ 2) := by
    have := hcs.trans (mul_le_mul_of_nonneg_left hint (by linarith : (0 : ℝ) ≤ T - 0))
    simpa using this
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hx2 : x t ^ 2 ≤ (|x₀| + |m t| + E * D) ^ 2 := by
    rw [← sq_abs (x t)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : (|x₀| + |m t| + E * D) ^ 2 ≤ 3 * x₀ ^ 2 + 3 * m t ^ 2 + 3 * E ^ 2 * D ^ 2 := by
    have := sq_abs x₀; have := sq_abs (m t)
    nlinarith [sq_nonneg (|x₀| - |m t|), sq_nonneg (|x₀| - E * D), sq_nonneg (|m t| - E * D)]
  have h4 : 3 * E ^ 2 * D ^ 2 ≤ 3 * E ^ 2 *
      (T * (2 * b x₀ ^ 2 * T + 2 * L ^ 2 * ∫ r in (0 : ℝ)..T, m r ^ 2)) :=
    mul_le_mul_of_nonneg_left hD2 (by positivity)
  have key : 3 * x₀ ^ 2 + 3 * m t ^ 2 + 3 * E ^ 2 *
      (T * (2 * b x₀ ^ 2 * T + 2 * L ^ 2 * ∫ r in (0 : ℝ)..T, m r ^ 2)) =
      (3 * x₀ ^ 2 + 6 * E ^ 2 * T ^ 2 * b x₀ ^ 2) + 3 * m t ^ 2 +
      (6 * E ^ 2 * T * L ^ 2) * ∫ r in (0 : ℝ)..T, m r ^ 2 := by ring
  linarith

set_option maxHeartbeats 1000000 in
theorem em_moment_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (I : ℝ → Ω → ℝ) (hIm : ∀ r, Measurable (I r)) (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (x₀ T : ℝ) (hT : 0 ≤ T) (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T → (fun ω => X t ω) =ᵐ[P]
      fun ω => x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) + I t ω)
    (hXmom : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => X t ω ^ 2) P)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (I r ω ^ 2) ∂P ≤ ENNReal.ofReal K)
    (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hsq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, X t ω ^ 2 ≤ A + 3 * emMhat I T t ω ^ 2 +
      B * ∫ r in (0 : ℝ)..T, emMhat I T r ω ^ 2) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, X t ω ^ 2 ∂P ≤ A + 3 * K + B * (K * T) := by
  intro t ht
  have hgood := em_good I b L hL hb x₀ T hT X hXcont hXeq
  have hMm : Measurable (fun q : Ω × ℝ => emMhat I T q.2 q.1) := by
    have h := (em_mhat_meas I T T hT hT (fun r _ _ => hIm r)).comp measurable_swap
    have e : (fun q : Ω × ℝ => emMhat I T q.2 q.1) =
        (fun p : ℝ × Ω => emMhat I T (min p.1 T) p.2) ∘ Prod.swap := by
      funext q; simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, em_mhat_clamp I hT]
    rw [e]; exact h
  have hMt : Measurable (emMhat I T t) :=
    em_slice_meas (emMhat I T) t (em_mhat_meas I T t hT ht.1 (fun r _ _ => hIm r))
  have hMm2 : Measurable (fun q : Ω × ℝ => ENNReal.ofReal (emMhat I T q.2 q.1 ^ 2)) :=
    (hMm.pow_const 2).ennreal_ofReal
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : Ω → ℝ≥0∞, Λ = fun ω =>
      ∫⁻ r in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (emMhat I T r ω ^ 2) := ⟨_, rfl⟩
  have hΛm : Measurable Λ := by
    rw [hΛdef]
    exact Measurable.lintegral_prod_right'
      (f := fun q : Ω × ℝ => ENNReal.ofReal (emMhat I T q.2 q.1 ^ 2))
      (ν := volume.restrict (Set.Ioc (0 : ℝ) T)) hMm2
  have hpath : ∀ᵐ ω ∂P, ENNReal.ofReal (X t ω ^ 2) ≤ ENNReal.ofReal A +
      ENNReal.ofReal 3 * ENNReal.ofReal (emMhat I T t ω ^ 2) + ENNReal.ofReal B * Λ ω := by
    filter_upwards [hgood, hsq t ht] with ω hω h
    have hΛ : ENNReal.ofReal (∫ r in (0 : ℝ)..T, emMhat I T r ω ^ 2) = Λ ω := by
      rw [hΛdef, intervalIntegral.integral_of_le hT, ofReal_integral_eq_lintegral_ofReal]
      · exact ((hω.2.1.pow 2).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
      · exact ae_of_all _ fun r => sq_nonneg _
    have hint0 : 0 ≤ ∫ r in (0 : ℝ)..T, emMhat I T r ω ^ 2 :=
      intervalIntegral.integral_nonneg hT (fun r _ => sq_nonneg _)
    calc ENNReal.ofReal (X t ω ^ 2)
        ≤ ENNReal.ofReal (A + 3 * emMhat I T t ω ^ 2 +
            B * ∫ r in (0 : ℝ)..T, emMhat I T r ω ^ 2) := ENNReal.ofReal_le_ofReal h
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hB0 hint0),
            ENNReal.ofReal_add hA0 (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_mul hB0, hΛ]
  have hφ : ∫⁻ ω, ENNReal.ofReal (emMhat I T t ω ^ 2) ∂P ≤ ENNReal.ofReal K := by
    have he := em_mhat_ae_eq I b L hL hb x₀ T hT X hXcont hXeq t ht
    rw [lintegral_congr_ae (by filter_upwards [he] with ω hω; rw [hω])]
    exact hK t ht
  have hΛb : ∫⁻ ω, Λ ω ∂P ≤ ENNReal.ofReal K * ENNReal.ofReal T := by
    rw [hΛdef, lintegral_lintegral_swap (f := fun ω r => ENNReal.ofReal (emMhat I T r ω ^ 2)) hMm2.aemeasurable]
    calc ∫⁻ r in Set.Ioc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (emMhat I T r ω ^ 2) ∂P
        ≤ ∫⁻ r in Set.Ioc (0 : ℝ) T, ENNReal.ofReal K := by
          refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
          have he := em_mhat_ae_eq I b L hL hb x₀ T hT X hXcont hXeq r ⟨hr.1.le, hr.2⟩
          rw [lintegral_congr_ae (by filter_upwards [he] with ω hω; rw [hω])]
          exact hK r ⟨hr.1.le, hr.2⟩
      _ = ENNReal.ofReal K * ENNReal.ofReal T := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  have hlin : ∫⁻ ω, ENNReal.ofReal (X t ω ^ 2) ∂P ≤
      ENNReal.ofReal (A + 3 * K + B * (K * T)) := by
    calc ∫⁻ ω, ENNReal.ofReal (X t ω ^ 2) ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal A + ENNReal.ofReal 3 * ENNReal.ofReal (emMhat I T t ω ^ 2) +
            ENNReal.ofReal B * Λ ω) ∂P := lintegral_mono_ae hpath
      _ = ENNReal.ofReal A + ENNReal.ofReal 3 * ∫⁻ ω, ENNReal.ofReal (emMhat I T t ω ^ 2) ∂P +
            ENNReal.ofReal B * ∫⁻ ω, Λ ω ∂P := by
          rw [lintegral_add_right _ (hΛm.const_mul _), lintegral_add_left measurable_const,
            lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ (hMt.pow_const 2).ennreal_ofReal,
            lintegral_const_mul _ hΛm]
      _ ≤ ENNReal.ofReal A + ENNReal.ofReal 3 * ENNReal.ofReal K +
            ENNReal.ofReal B * (ENNReal.ofReal K * ENNReal.ofReal T) := by
          gcongr
      _ = ENNReal.ofReal (A + 3 * K + B * (K * T)) := by
          rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_add hA0 (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
    (hXmom t ht).1]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

theorem em_moment_abs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (I : ℝ → Ω → ℝ) (hIm : ∀ r, Measurable (I r)) (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (x₀ T : ℝ) (hT : 0 ≤ T) (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T → (fun ω => X t ω) =ᵐ[P]
      fun ω => x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) + I t ω)
    (hXmom : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => X t ω ^ 2) P)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (I r ω ^ 2) ∂P ≤ ENNReal.ofReal K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, X t ω ^ 2 ∂P ≤ M := by
  have hA0 : 0 ≤ 3 * x₀ ^ 2 + 6 * Real.exp (L * T) ^ 2 * T ^ 2 * b x₀ ^ 2 := by positivity
  have hB0 : 0 ≤ 6 * Real.exp (L * T) ^ 2 * T * L ^ 2 := by positivity
  refine ⟨_, add_nonneg (add_nonneg hA0 (by positivity)) (mul_nonneg hB0 (mul_nonneg hK0 hT)),
    em_moment_core I hIm b L hL hb x₀ T hT X hXcont hXeq hXmom K hK0 hK _ _ hA0 hB0
      (fun t ht => ?_)⟩
  filter_upwards [em_good I b L hL hb x₀ T hT X hXcont hXeq] with ω hω
  exact em_path_sq hL hb x₀ T hT (fun r => emMhat I T r ω) (fun t => X t ω) hω.2.1 hω.1
    hω.2.2 t ht

theorem em_version_abs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (I : ℝ → Ω → ℝ) (hIm : ∀ r, Measurable (I r)) (b : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (x₀ T : ℝ) (hT : 0 ≤ T) (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T → (fun ω => X t ω) =ᵐ[P]
      fun ω => x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) + I t ω)
    (hXmom : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => X t ω ^ 2) P)
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (I r ω ^ 2) ∂P ≤ ENNReal.ofReal K) :
    ∃ X' : ℝ → Ω → ℝ, Measurable (fun q : Ω × ℝ => X' q.2 q.1) ∧
      (∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T, X s ω = X' s ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun s => X' s ω)) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, (X t ω) ^ 2 ∂P ≤ M := by
  have hbc := em_lip_cont' b L hL hb
  have hgood := em_good I b L hL hb x₀ T hT X hXcont hXeq
  refine ⟨fun s ω => emXhat b x₀ I T (emClamp T s) ω, ?_, ?_, ?_,
    em_moment_abs I hIm b L hL hb x₀ T hT X hXcont hXeq hXmom K hK0 hK⟩
  · have hq : Measurable (fun q : Ω × ℝ => (max q.2 0, q.1)) :=
      (measurable_snd.max measurable_const).prodMk measurable_fst
    have h := (em_xhat_meas b hbc x₀ I T T hT hT (fun r _ _ => hIm r)).comp hq
    exact h
  · filter_upwards [hgood] with ω hω s hs
    show X s ω = emXhat b x₀ I T (emClamp T s) ω
    rw [em_clamp_of_mem hs]
    exact (em_xhat_eq b L hL hb x₀ T I X ω hω.1 hω.2.1 hω.2.2 s hs).symm
  · filter_upwards [hgood] with ω hω
    have e : (fun s => emXhat b x₀ I T (emClamp T s) ω) = (fun s => X s ω) ∘ emClamp T :=
      funext fun s => em_xhat_eq b L hL hb x₀ T I X ω hω.1 hω.2.1 hω.2.2 (emClamp T s)
        (em_clamp_mem hT s)
    rw [e]; exact hω.1.comp (em_clamp_cont T)


/-- A jointly measurable continuous version of the solution, and a uniform second moment. -/
theorem em_solution_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmom : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      Integrable (fun ω : Ω => (X t ω) ^ 2) P)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ), H ω s = σ (X s ω))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
        x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            W ℱ hW H hHmeas hHprog hHsq t ω) :
    ∃ X' : ℝ → Ω → ℝ, Measurable (fun q : Ω × ℝ => X' q.2 q.1) ∧
      (∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T, X s ω = X' s ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun s => X' s ω)) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, (X t ω) ^ 2 ∂P ≤ M := by
  obtain ⟨L, hL0, hb, -⟩ := hLip
  have hIa : ∀ r, StronglyMeasurable[ℱ r]
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq r) :=
    fun r => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted
      W ℱ hW H hHmeas hHprog hHsq r
  have hIm : ∀ r, Measurable
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq r) :=
    fun r => ((hIa r).mono (ℱ.le r)).measurable
  have hKfin := hHsq T hT
  refine em_version_abs _ hIm b L hL0 hb x₀ T hT.le X hXcont hXeq hXmom
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
    ENNReal.toReal_nonneg (fun r hr => ?_)
  have e1 : ∫⁻ ω, ENNReal.ofReal
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq r ω ^ 2) ∂P
      = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW H hHmeas hHprog
          hHsq r ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by simp_rw [em_nnsq]
  rw [e1, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_lintegral_sq W ℱ hW H hHmeas
    hHprog hHsq hr.1, ENNReal.ofReal_toReal hKfin.ne]
  exact lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc le_rfl hr.2)

open LevyStochCalc.Brownian.Ito in
/-- A version of the solution with mean-square increments `≤ C (t - s)`. -/
theorem em_solution_regularity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmom : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      Integrable (fun ω : Ω => (X t ω) ^ 2) P)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ), H ω s = σ (X s ω))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
        x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            W ℱ hW H hHmeas hHprog hHsq t ω) :
    ∃ X' : ℝ → Ω → ℝ, Measurable (fun q : Ω × ℝ => X' q.2 q.1) ∧
      (∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T, X s ω = X' s ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun s => X' s ω)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        ∫⁻ ω, ENNReal.ofReal ((X' t ω - X' s ω) ^ 2) ∂P ≤ ENNReal.ofReal (C * (t - s)) := by
  obtain ⟨L, hL0, hb, hσ⟩ := hLip
  obtain ⟨X', hX'm, hXX', hX'c, M, hM0, hM⟩ := em_solution_version P W ℱ hW T x₀ hT b σ ⟨L, hL0, hb, hσ⟩ X hXcont hXmom H hH hHmeas hHprog hHsq hXeq
  have hbc : Continuous b := em_lip_continuous b L hL0 hb
  have hσc : Continuous σ := em_lip_continuous σ L hL0 hσ
  have hK : ∀ f : ℝ → ℝ, 0 ≤ 2 * f 0 ^ 2 + 2 * L ^ 2 * M := fun f =>
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg L)) hM0)
  refine ⟨X', hX'm, hXX', hX'c, 2 * T * (2 * b 0 ^ 2 + 2 * L ^ 2 * M) +
    2 * (2 * σ 0 ^ 2 + 2 * L ^ 2 * M),
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT.le) (hK b))
      (mul_nonneg (by norm_num) (hK σ)), ?_⟩
  intro s t hs hst htT
  set I := stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq with hI
  -- second moments of Lipschitz images of the version
  have hlipmom : ∀ f : ℝ → ℝ, (∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) →
      ∀ u ∈ Set.Icc (0 : ℝ) T,
        ∫⁻ ω, ENNReal.ofReal ((f (X' u ω)) ^ 2) ∂P ≤ ENNReal.ofReal (2 * f 0 ^ 2 + 2 * L ^ 2 * M) := by
    intro f hf u hu
    have hpt : ∀ x, f x ^ 2 ≤ 2 * f 0 ^ 2 + 2 * L ^ 2 * x ^ 2 := by
      intro x
      have h1 := hf x 0
      rw [sub_zero] at h1
      have h2 : |f x| ≤ |f 0| + L * |x| := by linarith [abs_sub_abs_le_abs_sub (f x) (f 0)]
      have h3 : f x ^ 2 ≤ (|f 0| + L * |x|) ^ 2 := by
        rw [← sq_abs (f x)]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      calc f x ^ 2 ≤ (|f 0| + L * |x|) ^ 2 := h3
        _ ≤ 2 * |f 0| ^ 2 + 2 * (L * |x|) ^ 2 := em_sq_add_le _ _
        _ = 2 * f 0 ^ 2 + 2 * L ^ 2 * x ^ 2 := by rw [sq_abs, mul_pow, sq_abs]; ring
    have hXu : ∫⁻ ω, ENNReal.ofReal ((X' u ω) ^ 2) ∂P ≤ ENNReal.ofReal M := by
      have e : ∫⁻ ω, ENNReal.ofReal ((X' u ω) ^ 2) ∂P = ENNReal.ofReal (∫ ω, (X u ω) ^ 2 ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hXmom u hu)
          (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
        refine lintegral_congr_ae ?_
        filter_upwards [hXX'] with ω hω
        rw [hω u hu]
      rw [e]; exact ENNReal.ofReal_le_ofReal (hM u hu)
    have h2L : (0 : ℝ) ≤ 2 * L ^ 2 := mul_nonneg (by norm_num) (sq_nonneg L)
    calc ∫⁻ ω, ENNReal.ofReal ((f (X' u ω)) ^ 2) ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (2 * f 0 ^ 2)
            + ENNReal.ofReal (2 * L ^ 2) * ENNReal.ofReal ((X' u ω) ^ 2)) ∂P := by
          refine lintegral_mono (fun ω => ?_)
          rw [← ENNReal.ofReal_mul h2L, ← ENNReal.ofReal_add
            (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg h2L (sq_nonneg _))]
          exact ENNReal.ofReal_le_ofReal (by have := hpt (X' u ω); linarith)
      _ = ENNReal.ofReal (2 * f 0 ^ 2)
            + ENNReal.ofReal (2 * L ^ 2) * ∫⁻ ω, ENNReal.ofReal ((X' u ω) ^ 2) ∂P := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (2 * f 0 ^ 2) + ENNReal.ofReal (2 * L ^ 2) * ENNReal.ofReal M := by
          gcongr
      _ = ENNReal.ofReal (2 * f 0 ^ 2 + 2 * L ^ 2 * M) := by
          rw [← ENNReal.ofReal_mul h2L, ← ENNReal.ofReal_add
            (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg h2L hM0)]
  -- the cell integral of a Lipschitz image
  have hcell : ∀ f : ℝ → ℝ, (∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) →
      ∫⁻ ω, ∫⁻ u in Set.Ioc s t, ENNReal.ofReal ((f (X' u ω)) ^ 2) ∂volume ∂P
        ≤ ENNReal.ofReal (2 * f 0 ^ 2 + 2 * L ^ 2 * M) * ENNReal.ofReal (t - s) := by
    intro f hf
    have hfc := em_lip_continuous f L hL0 hf
    rw [lintegral_lintegral_swap ((show Measurable (Function.uncurry
      fun (ω : Ω) (u : ℝ) => ENNReal.ofReal ((f (X' u ω)) ^ 2)) from
      ENNReal.measurable_ofReal.comp ((hfc.measurable.comp hX'm).pow_const 2)).aemeasurable)]
    calc ∫⁻ u in Set.Ioc s t, ∫⁻ ω, ENNReal.ofReal ((f (X' u ω)) ^ 2) ∂P
        ≤ ∫⁻ u in Set.Ioc s t, ENNReal.ofReal (2 * f 0 ^ 2 + 2 * L ^ 2 * M) :=
          setLIntegral_mono' measurableSet_Ioc (fun u hu =>
            hlipmom f hf u ⟨hs.trans hu.1.le, hu.2.trans htT⟩)
      _ = ENNReal.ofReal (2 * f 0 ^ 2 + 2 * L ^ 2 * M) * ENNReal.ofReal (t - s) := by
          rw [setLIntegral_const, Real.volume_Ioc]
  -- pathwise decomposition
  have hdec : ∀ᵐ ω ∂P, X' t ω - X' s ω = (∫ u in s..t, b (X' u ω)) + (I t ω - I s ω) := by
    filter_upwards [hXeq t (hs.trans hst) htT, hXeq s hs (hst.trans htT), hXX', hX'c]
      with ω h1 h2 h3 hc
    have hcong : ∀ r, 0 ≤ r → r ≤ T →
        (∫ u in (0 : ℝ)..r, b (X u ω)) = ∫ u in (0 : ℝ)..r, b (X' u ω) := by
      intro r hr0 hrT
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le hr0] at hu
      show b (X u ω) = b (X' u ω)
      rw [h3 u ⟨hu.1, hu.2.trans hrT⟩]
    have e1 : X' t ω = x₀ + (∫ u in (0 : ℝ)..t, b (X' u ω)) + I t ω := by
      rw [← h3 t ⟨hs.trans hst, htT⟩, ← hcong t (hs.trans hst) htT]; exact h1
    have e2 : X' s ω = x₀ + (∫ u in (0 : ℝ)..s, b (X' u ω)) + I s ω := by
      rw [← h3 s ⟨hs, hst.trans htT⟩, ← hcong s hs (hst.trans htT)]; exact h2
    have e3 := intervalIntegral.integral_interval_sub_left (μ := volume) (f := fun u => b (X' u ω))
      ((hbc.comp hc).intervalIntegrable 0 t) ((hbc.comp hc).intervalIntegrable 0 s)
    beta_reduce at e3
    rw [e1, e2, ← e3]
    ring
  have hImt := stochasticIntegralBrownian_memLp W ℱ hW H hHmeas hHprog hHsq t
  have hIms := stochasticIntegralBrownian_memLp W ℱ hW H hHmeas hHprog hHsq s
  have hBm : Measurable (fun ω => I t ω - I s ω) :=
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hW H hHmeas hHprog hHsq t).mono
      (ℱ.le _)).measurable).sub
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hW H hHmeas hHprog hHsq s).mono
      (ℱ.le _)).measurable)
  have hts : 0 ≤ t - s := by linarith
  -- drift part
  have hdrift : ∫⁻ ω, ENNReal.ofReal (2 * (∫ u in s..t, b (X' u ω)) ^ 2) ∂P
      ≤ ENNReal.ofReal (2 * (t - s)) *
        (ENNReal.ofReal (2 * b 0 ^ 2 + 2 * L ^ 2 * M) * ENNReal.ofReal (t - s)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (hcell b hb) zero_le)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hX'c] with ω hc
    have hcont : Continuous (fun u => b (X' u ω)) := hbc.comp hc
    have hcs := em_interval_cs (fun u => b (X' u ω)) s t hst (hcont.intervalIntegrable _ _)
      ((hcont.pow 2).intervalIntegrable _ _)
    have hJ : ENNReal.ofReal (∫ u in s..t, (b (X' u ω)) ^ 2)
        = ∫⁻ u in Set.Ioc s t, ENNReal.ofReal ((b (X' u ω)) ^ 2) := by
      rw [intervalIntegral.integral_of_le hst]
      exact ofReal_integral_eq_lintegral_ofReal
        (((hcont.pow 2).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall (fun u => sq_nonneg _))
    have hJnn : 0 ≤ ∫ u in s..t, (b (X' u ω)) ^ 2 :=
      intervalIntegral.integral_nonneg hst (fun u _ => sq_nonneg _)
    rw [← hJ, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hts)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [hcs]
  -- diffusion part
  have hdiff : ∫⁻ ω, ENNReal.ofReal (2 * (I t ω - I s ω) ^ 2) ∂P
      ≤ ENNReal.ofReal 2 *
        (ENNReal.ofReal (2 * σ 0 ^ 2 + 2 * L ^ 2 * M) * ENNReal.ofReal (t - s)) := by
    have e1 : ∫⁻ ω, ENNReal.ofReal (2 * (I t ω - I s ω) ^ 2) ∂P
        = ENNReal.ofReal 2 * ENNReal.ofReal (∫ ω, (I t ω - I s ω) ^ 2 ∂P) := by
      have hBi : Integrable (fun ω => (I t ω - I s ω) ^ 2) P := (hImt.sub hIms).integrable_sq
      rw [ofReal_integral_eq_lintegral_ofReal hBi
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _)),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr (fun ω => ?_)
      rw [ENNReal.ofReal_mul (by norm_num)]
    rw [e1, em_ito_increment W ℱ hW H hHmeas hHprog hHsq hs hst]
    refine mul_le_mul_of_nonneg_left (le_trans ENNReal.ofReal_toReal_le ?_) zero_le
    refine le_trans (le_of_eq ?_) (hcell σ hσ)
    refine lintegral_congr_ae ?_
    filter_upwards [hXX'] with ω h3
    refine setLIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    rw [hH, h3 u ⟨hs.trans hu.1.le, hu.2.trans htT⟩, em_nnsq]
  calc ∫⁻ ω, ENNReal.ofReal ((X' t ω - X' s ω) ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * (∫ u in s..t, b (X' u ω)) ^ 2)
          + ENNReal.ofReal (2 * (I t ω - I s ω) ^ 2)) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hdec] with ω hω
        rw [hω, ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (sq_nonneg _))
          (mul_nonneg (by norm_num) (sq_nonneg _))]
        exact ENNReal.ofReal_le_ofReal (em_sq_add_le _ _)
    _ = ∫⁻ ω, ENNReal.ofReal (2 * (∫ u in s..t, b (X' u ω)) ^ 2) ∂P
          + ∫⁻ ω, ENNReal.ofReal (2 * (I t ω - I s ω) ^ 2) ∂P :=
        lintegral_add_right _ (ENNReal.measurable_ofReal.comp
          (measurable_const.mul (hBm.pow_const 2)))
    _ ≤ ENNReal.ofReal (2 * (t - s)) *
          (ENNReal.ofReal (2 * b 0 ^ 2 + 2 * L ^ 2 * M) * ENNReal.ofReal (t - s))
        + ENNReal.ofReal 2 *
          (ENNReal.ofReal (2 * σ 0 ^ 2 + 2 * L ^ 2 * M) * ENNReal.ofReal (t - s)) :=
        add_le_add hdrift hdiff
    _ = ENNReal.ofReal (2 * (t - s) * ((2 * b 0 ^ 2 + 2 * L ^ 2 * M) * (t - s))
          + 2 * ((2 * σ 0 ^ 2 + 2 * L ^ 2 * M) * (t - s))) := by
        rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg (by norm_num) hts)
            (mul_nonneg (hK b) hts)) (mul_nonneg (by norm_num) (mul_nonneg (hK σ) hts)),
          ENNReal.ofReal_mul (p := 2 * (t - s)) (q := (2 * b 0 ^ 2 + 2 * L ^ 2 * M) * (t - s))
            (mul_nonneg (by norm_num) hts),
          ENNReal.ofReal_mul (p := 2 * b 0 ^ 2 + 2 * L ^ 2 * M) (q := t - s) (hK b),
          ENNReal.ofReal_mul (p := 2) (q := (2 * σ 0 ^ 2 + 2 * L ^ 2 * M) * (t - s)) (by norm_num),
          ENNReal.ofReal_mul (p := 2 * σ 0 ^ 2 + 2 * L ^ 2 * M) (q := t - s) (hK σ)]
    _ ≤ ENNReal.ofReal ((2 * T * (2 * b 0 ^ 2 + 2 * L ^ 2 * M) +
          2 * (2 * σ 0 ^ 2 + 2 * L ^ 2 * M)) * (t - s)) := by
        apply ENNReal.ofReal_le_ofReal
        have key : (2 * T * (2 * b 0 ^ 2 + 2 * L ^ 2 * M) + 2 * (2 * σ 0 ^ 2 + 2 * L ^ 2 * M))
            * (t - s) - (2 * (t - s) * ((2 * b 0 ^ 2 + 2 * L ^ 2 * M) * (t - s))
            + 2 * ((2 * σ 0 ^ 2 + 2 * L ^ 2 * M) * (t - s)))
            = 2 * (2 * b 0 ^ 2 + 2 * L ^ 2 * M) * (t - s) * (T - (t - s)) := by ring
        rw [← sub_nonneg, key]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hK b)) hts) (by linarith)

/-- An `ℱ s`-measurable `L²` variable times a later Brownian increment is in `L²`
(independence factorises the second moment). -/
theorem em_memLp_mul_increment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : IsBrownianFiltration W ℱ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {ξ : Ω → ℝ} (hξm : StronglyMeasurable[ℱ s] ξ) (hξ : MemLp ξ 2 P) :
    MemLp (fun ω => ξ ω * (W.W t ω - W.W s ω)) 2 P := by
  set ΔW : Ω → ℝ := fun ω => W.W t ω - W.W s ω with hΔW
  have hΔm : Measurable ΔW := (W.measurable_eval t).sub (W.measurable_eval s)
  have hξmeas : Measurable ξ := (hξm.mono (ℱ.le s)).measurable
  have hind : IndepFun ξ ΔW P := by
    rw [IndepFun_iff]
    intro u v hu hv
    exact (Indep_iff _ _ _).1 (hW.indep hs hst) u v (hξm.measurable.comap_le u hu) hv
  have hΔ2 : MemLp ΔW 2 P :=
    (memLp_two_iff_integrable_sq hΔm.aestronglyMeasurable).2
      (Ito.brownian_increment_sq_integrable W hs hst)
  refine ⟨(hξmeas.mul hΔm).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  have h1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top).1 hξ.2
  have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top).1 hΔ2.2
  have hmul : ∀ ω, ‖ξ ω * ΔW ω‖ₑ ^ (ENNReal.toReal 2) =
      ‖ξ ω‖ₑ ^ (ENNReal.toReal 2) * ‖ΔW ω‖ₑ ^ (ENNReal.toReal 2) := fun ω => by
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  refine lt_of_eq_of_lt (lintegral_congr fun ω => hmul ω) ?_
  have hind2 := hind.comp (φ := fun x : ℝ => ‖x‖ₑ ^ (ENNReal.toReal 2))
    (ψ := fun x : ℝ => ‖x‖ₑ ^ (ENNReal.toReal 2)) (by fun_prop) (by fun_prop)
  have key := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (μ := P) (by fun_prop) (by fun_prop) hind2
  simp only [Function.comp_def] at key
  rw [show (fun ω => ‖ξ ω‖ₑ ^ (ENNReal.toReal 2) * ‖ΔW ω‖ₑ ^ (ENNReal.toReal 2)) =
      (fun ω => ‖ξ ω‖ₑ ^ (ENNReal.toReal 2)) * (fun ω => ‖ΔW ω‖ₑ ^ (ENNReal.toReal 2))
      from rfl, key]
  exact ENNReal.mul_lt_top h1 h2

open LevyStochCalc.Brownian.Ito in
theorem em_frozen_U_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hW : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s < t)
    (G : Ω → ℝ) (hGm : StronglyMeasurable[ℱ s] G) (hG2 : MemLp G 2 P) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq t ω
        - G ω * (W.W t ω - W.W s ω)‖₊ : ℝ≥0∞) ^ 2 ∂P ≤
      ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) t,
        (‖H ω r - (if s < r ∧ r ≤ t then G ω else 0)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    have := em_ito_sub_step_le W ℱ hW H hHmeas hHprog hHsq (N := 1) ![0, t] rfl
      (Fin.strictMono_iff_lt_succ.2 (fun i => by fin_cases i; simpa using hst))
      (by simpa using hst) ![G]
      (by intro i; fin_cases i; exact hGm) (by intro i; fin_cases i; exact hG2)
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · refine lintegral_congr fun ω => ?_
      simp
    · refine lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp <;> congr
  · have := em_ito_sub_step_le W ℱ hW H hHmeas hHprog hHsq (N := 2) ![0, s, t] rfl
      (Fin.strictMono_iff_lt_succ.2 (fun i => by fin_cases i <;> simp [hpos, hst]))
      (by simp; linarith) ![0, G]
      (by intro i; fin_cases i
          · exact stronglyMeasurable_const
          · exact hGm)
      (by intro i; fin_cases i
          · exact memLp_const 0
          · exact hG2)
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
    · refine lintegral_congr fun ω => ?_
      simp [Fin.sum_univ_two]
    · refine lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      symm
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, ite_self, zero_add]
      rfl

open LevyStochCalc.Brownian.Ito in
theorem em_frozen_increment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s < t)
    (G : Ω → ℝ) (hGm : StronglyMeasurable[ℱ s] G) (hG2 : MemLp G 2 P)
    (S : Ω → ℝ)
    (hS : ∀ ω, S ω =
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq t ω -
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq s ω -
      G ω * (W.W t ω - W.W s ω)) :
    MemLp S 2 P ∧
    ENNReal.ofReal (∫ ω, S ω ^ 2 ∂P) ≤
      ∫⁻ ω, ∫⁻ r in Set.Icc s t, ENNReal.ofReal ((H ω r - G ω) ^ 2) ∂volume ∂P ∧
    ∀ Z : Ω → ℝ, AEStronglyMeasurable[ℱ s] Z P → MemLp Z 2 P →
      ∫ ω, Z ω * S ω ∂P = 0 := by
  set I := stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq with hI
  have hIm : ∀ r, MemLp (I r) 2 P := fun r =>
    stochasticIntegralBrownian_memLp W ℱ hW H hHmeas hHprog hHsq r
  have hIa : ∀ r, StronglyMeasurable[ℱ r] (I r) := fun r =>
    stochasticIntegralBrownian_stronglyAdapted W ℱ hW H hHmeas hHprog hHsq r
  have hmart := martingale_stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq
  set ΔW : Ω → ℝ := fun ω => W.W t ω - W.W s ω with hΔW
  have hΔm : Measurable ΔW := (W.measurable_eval t).sub (W.measurable_eval s)
  have hΔ2 : MemLp ΔW 2 P :=
    (memLp_two_iff_integrable_sq hΔm.aestronglyMeasurable).2
      (Ito.brownian_increment_sq_integrable W hs hst)
  have hGW : MemLp (fun ω => G ω * ΔW ω) 2 P := em_memLp_mul_increment W ℱ hW hs hst hGm hG2
  have hSeq : S = fun ω => I t ω - I s ω - G ω * ΔW ω := funext hS
  have hS2 : MemLp S 2 P := by rw [hSeq]; exact ((hIm t).sub (hIm s)).sub hGW
  have horth : ∀ Z : Ω → ℝ, AEStronglyMeasurable[ℱ s] Z P → MemLp Z 2 P →
      ∫ ω, Z ω * S ω ∂P = 0 := by
    intro Z hZa hZ2
    set Z' := hZa.mk Z with hZ'
    have hZ'm : StronglyMeasurable[ℱ s] Z' := hZa.stronglyMeasurable_mk
    have hZZ' : Z =ᵐ[P] Z' := hZa.ae_eq_mk
    have hZ'2 : MemLp Z' 2 P := hZ2.ae_eq hZZ'
    have hi1 : Integrable (fun ω => Z' ω * I t ω) P := hZ'2.integrable_mul (hIm t)
    have hi2 : Integrable (fun ω => Z' ω * I s ω) P := hZ'2.integrable_mul (hIm s)
    have hi3 : Integrable (fun ω => Z' ω * (G ω * ΔW ω)) P := hZ'2.integrable_mul hGW
    have h1 : ∫ ω, Z' ω * I t ω ∂P = ∫ ω, Z' ω * I s ω ∂P := by
      have hc := condExp_mul_of_stronglyMeasurable_left hZ'm hi1 ((hIm t).integrable one_le_two)
      have h2 := hmart.condExp_ae_eq hst.le
      calc ∫ ω, Z' ω * I t ω ∂P = ∫ ω, (Z' * I t) ω ∂P := rfl
        _ = ∫ ω, (P[Z' * I t | ℱ s]) ω ∂P := (integral_condExp (ℱ.le s)).symm
        _ = ∫ ω, Z' ω * I s ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hc, h2] with ω h1 h2
          rw [h1, Pi.mul_apply, h2]
    have h3 : ∫ ω, Z' ω * (G ω * ΔW ω) ∂P = 0 := by
      have hZG : StronglyMeasurable[ℱ s] (Z' * G) := hZ'm.mul hGm
      have hprod : Integrable ((Z' * G) * ΔW) P := by
        refine hi3.congr (Eventually.of_forall fun ω => ?_)
        simp only [Pi.mul_apply]; ring
      have hc := condExp_mul_of_stronglyMeasurable_left hZG hprod (hΔ2.integrable one_le_two)
      have h0 := hW.condExp_increment_eq_zero hs hst
      calc ∫ ω, Z' ω * (G ω * ΔW ω) ∂P = ∫ ω, ((Z' * G) * ΔW) ω ∂P := by
            congr 1; funext ω; simp only [Pi.mul_apply]; ring
        _ = ∫ ω, (P[(Z' * G) * ΔW | ℱ s]) ω ∂P := (integral_condExp (ℱ.le s)).symm
        _ = 0 := by
          refine integral_eq_zero_of_ae ?_
          filter_upwards [hc, h0] with ω h1 h2
          rw [h1, Pi.mul_apply, h2]; simp
    calc ∫ ω, Z ω * S ω ∂P
        = ∫ ω, (Z' ω * I t ω - Z' ω * I s ω) - Z' ω * (G ω * ΔW ω) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hZZ'] with ω hω
          rw [hω, hS ω]; ring
      _ = 0 := by
          have hi12 : Integrable (fun ω => Z' ω * I t ω - Z' ω * I s ω) P := hi1.sub hi2
          rw [integral_sub hi12 hi3, integral_sub hi1 hi2, h1, h3]; ring
  refine ⟨hS2, ?_, horth⟩
  -- isometry bound
  set U : Ω → ℝ := fun ω => I t ω - G ω * ΔW ω with hU
  have hU2 : MemLp U 2 P := (hIm t).sub hGW
  have hUS : ∀ ω, U ω = S ω + I s ω := fun ω => by rw [hS ω]; ring
  have hcross : ∫ ω, I s ω * S ω ∂P = 0 := horth (I s) (hIa s).aestronglyMeasurable (hIm s)
  have hiSS : Integrable (fun ω => S ω ^ 2) P := hS2.integrable_sq
  have hiII : Integrable (fun ω => I s ω ^ 2) P := (hIm s).integrable_sq
  have hiIS : Integrable (fun ω => I s ω * S ω) P := (hIm s).integrable_mul hS2
  have hUreal : ∫ ω, U ω ^ 2 ∂P = ∫ ω, S ω ^ 2 ∂P + ∫ ω, I s ω ^ 2 ∂P := by
    have : (fun ω => U ω ^ 2) = fun ω => (S ω ^ 2 + 2 * (I s ω * S ω)) + I s ω ^ 2 := by
      funext ω; rw [hUS ω]; ring
    have hi2 : Integrable (fun ω => 2 * (I s ω * S ω)) P := hiIS.const_mul 2
    have hi12 : Integrable (fun ω => S ω ^ 2 + 2 * (I s ω * S ω)) P := hiSS.add hi2
    rw [this, integral_add hi12 hiII, integral_add hiSS hi2,
      integral_const_mul, hcross]
    ring
  have hlin : ∀ f : Ω → ℝ, MemLp f 2 P →
      ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) = ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro f hf
    rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
      (Eventually.of_forall fun ω => sq_nonneg _)]
    simp_rw [em_nnsq]
  set A := ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hA
  have hIsA : ENNReal.ofReal (∫ ω, I s ω ^ 2 ∂P) = A := by
    rw [hlin _ (hIm s), stochasticIntegralBrownian_lintegral_sq W ℱ hW H hHmeas hHprog hHsq hs]
  have hAfin : A ≠ ⊤ := by
    rw [← hIsA]; exact ENNReal.ofReal_ne_top
  have hsplit : ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) t,
      (‖H ω r - (if s < r ∧ r ≤ t then G ω else 0)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P =
      A + ∫⁻ ω, ∫⁻ r in Set.Ioc s t, (‖H ω r - G ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    have hinner : ∀ ω, ∫⁻ r in Set.Icc (0 : ℝ) t,
        (‖H ω r - (if s < r ∧ r ≤ t then G ω else 0)‖₊ : ℝ≥0∞) ^ 2 ∂volume =
        ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume +
        ∫⁻ r in Set.Ioc s t, (‖H ω r - G ω‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
      intro ω
      rw [← Set.Icc_union_Ioc_eq_Icc hs hst.le,
        lintegral_union measurableSet_Ioc
          (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))]
      congr 1
      · refine setLIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
        have : ¬ (s < r ∧ r ≤ t) := fun h => absurd h.1 (not_lt.mpr hr.2)
        simp [this]
      · refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
        simp [hr.1, hr.2]
    simp_rw [hinner]
    rw [lintegral_add_left]
    exact ((hHmeas.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) s)))
  have hkey : ENNReal.ofReal (∫ ω, S ω ^ 2 ∂P) + A ≤
      A + ∫⁻ ω, ∫⁻ r in Set.Ioc s t, (‖H ω r - G ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    have h1 := em_frozen_U_le W ℱ hW H hHmeas hHprog hHsq s t hs hst G hGm hG2
    rw [hsplit, ← hlin U hU2, hUreal, ENNReal.ofReal_add (integral_nonneg fun _ => sq_nonneg _)
      (integral_nonneg fun _ => sq_nonneg _), hIsA] at h1
    exact h1
  have h2 := (ENNReal.add_le_add_iff_right hAfin).1 (hkey.trans_eq (add_comm _ _))
  refine h2.trans (lintegral_mono fun ω => ?_)
  simp_rw [em_nnsq]
  exact lintegral_mono_set Set.Ioc_subset_Icc_self


namespace EMGridAux

lemma lip_cont {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    Continuous f := by
  have : LipschitzWith ⟨L, hL⟩ f := LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, Real.dist_eq]; exact hf x y
  exact this.continuous

lemma memLp_comp_lip {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    MemLp (fun ω => f (Y ω)) 2 P := by
  refine MemLp.of_le ((memLp_const |f 0|).add (hY.norm.const_mul L))
    ((lip_cont hL hf).comp_aestronglyMeasurable hY.1) (Eventually.of_forall fun ω => ?_)
  have h1 := hf (Y ω) 0
  simp only [sub_zero] at h1
  have h2 : |f (Y ω)| ≤ |f 0| + L * |Y ω| := by
    have := abs_sub_abs_le_abs_sub (f (Y ω)) (f 0); linarith
  simp only [Real.norm_eq_abs, Pi.add_apply, norm_abs_eq_norm] at *
  calc |f (Y ω)| ≤ |f 0| + L * |Y ω| := h2
    _ ≤ _ := le_abs_self _

lemma lip_sq {f : ℝ → ℝ} {L : ℝ} (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) (x y z : ℝ) :
    (f x - f y) ^ 2 ≤ 2 * L ^ 2 * ((x - z) ^ 2 + (z - y) ^ 2) := by
  have h := hf x y
  have h2 : (f x - f y) ^ 2 ≤ L ^ 2 * (x - y) ^ 2 := by
    calc (f x - f y) ^ 2 = |f x - f y| ^ 2 := (sq_abs _).symm
      _ ≤ (L * |x - y|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = L ^ 2 * (x - y) ^ 2 := by rw [mul_pow, sq_abs]
  have h3 : (x - y) ^ 2 ≤ 2 * ((x - z) ^ 2 + (z - y) ^ 2) := by
    nlinarith [sq_nonneg (x - z - (z - y))]
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  nlinarith

lemma young {h : ℝ} (hh : 0 < h) (u v : ℝ) :
    (u + v) ^ 2 ≤ (1 + h) * u ^ 2 + (1 + 1 / h) * v ^ 2 := by
  have key : (1 + h) * u ^ 2 + (1 + 1 / h) * v ^ 2 - (u + v) ^ 2 = (h * u - v) ^ 2 / h := by
    field_simp; ring
  have : 0 ≤ (h * u - v) ^ 2 / h := by positivity
  linarith

lemma sq_intervalIntegral_le {f : ℝ → ℝ} (hf : Continuous f) {s t : ℝ} (hst : s < t) :
    (∫ r in s..t, f r) ^ 2 ≤ (t - s) * ∫ r in s..t, f r ^ 2 := by
  have hpos : 0 < t - s := by linarith
  set m := ∫ r in s..t, f r with hm
  set A := ∫ r in s..t, f r ^ 2 with hA
  set c := m / (t - s) with hc
  have h0 : 0 ≤ ∫ r in s..t, (f r - c) ^ 2 :=
    intervalIntegral.integral_nonneg hst.le (fun r _ => sq_nonneg _)
  have hexp : ∫ r in s..t, (f r - c) ^ 2 = A - 2 * c * m + c ^ 2 * (t - s) := by
    have e1 : (fun r => (f r - c) ^ 2) = fun r => (f r ^ 2 - (2 * c) * f r) + c ^ 2 := by
      funext r; ring
    rw [e1, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp only [smul_eq_mul]; ring
    · exact (hf.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul hf).intervalIntegrable _ _
    · exact ((hf.pow 2).sub (continuous_const.mul hf)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  rw [hexp] at h0
  have e2 : c ^ 2 * (t - s) = c * m := by rw [hc]; field_simp
  have e3 : m ^ 2 = (t - s) * (c * m) := by rw [hc]; field_simp
  rw [e3]
  have : c * m ≤ A := by nlinarith
  exact mul_le_mul_of_nonneg_left this hpos.le

theorem step {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (Wf I X : ℝ → Ω → ℝ) (H : Ω → ℝ → ℝ)
    (b σ : ℝ → ℝ) (L K T x₀ : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (hσ : ∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmem : ∀ r : ℝ, 0 ≤ r → r ≤ T → MemLp (X r) 2 P)
    (hH : ∀ (ω : Ω) (r : ℝ), H ω r = σ (X r ω))
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω => x₀ + (∫ r in (0 : ℝ)..t, b (X r ω)) + I t ω)
    (hImem : ∀ t : ℝ, MemLp (I t) 2 P)
    (hadapt : ∀ t : ℝ, 0 ≤ t → t ≤ T → AEStronglyMeasurable[ℱ t] (X t) P)
    (hjoint : AEMeasurable (fun p : Ω × ℝ => X p.2 p.1)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
    (hKb : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∫ ω, (X t ω - X s ω) ^ 2 ∂P ≤ K * (t - s))
    (s t h : ℝ) (hs : 0 ≤ s) (hst : s < t) (htT : t ≤ T) (hh : t - s = h)
    (Y : Ω → ℝ) (hYm : StronglyMeasurable[ℱ s] Y) (hY2 : MemLp Y 2 P)
    (hC : ∀ G : Ω → ℝ, StronglyMeasurable[ℱ s] G → MemLp G 2 P → ∀ S : Ω → ℝ,
      (∀ ω, S ω = I t ω - I s ω - G ω * (Wf t ω - Wf s ω)) →
      MemLp S 2 P ∧
      ENNReal.ofReal (∫ ω, S ω ^ 2 ∂P) ≤
        ∫⁻ ω, ∫⁻ r in Set.Icc s t, ENNReal.ofReal ((H ω r - G ω) ^ 2) ∂volume ∂P ∧
      ∀ Z : Ω → ℝ, AEStronglyMeasurable[ℱ s] Z P → MemLp Z 2 P → ∫ ω, Z ω * S ω ∂P = 0) :
    ∫ ω, (X t ω - (Y ω + b (Y ω) * h + σ (Y ω) * (Wf t ω - Wf s ω))) ^ 2 ∂P ≤
      (1 + (1 + 4 * (1 + T) * L ^ 2 * (1 + K)) * h) * ∫ ω, (X s ω - Y ω) ^ 2 ∂P +
        (1 + 4 * (1 + T) * L ^ 2 * (1 + K)) * h ^ 2 := by
  have hh0 : 0 < h := by linarith
  have hhT : h ≤ T := by linarith
  have hbc : Continuous b := lip_cont hL hb
  have hσc : Continuous σ := lip_cont hL hσ
  have hs' : s ≤ T := by linarith
  have hXs := hXmem s hs hs'
  have hXt := hXmem t (by linarith) htT
  set e : Ω → ℝ := fun ω => X s ω - Y ω with he_def
  set S : Ω → ℝ := fun ω => I t ω - I s ω - σ (Y ω) * (Wf t ω - Wf s ω) with hS_def
  set D : Ω → ℝ := fun ω => X t ω - X s ω - (I t ω - I s ω) - b (Y ω) * h with hD_def
  have hG2 : MemLp (fun ω => σ (Y ω)) 2 P := memLp_comp_lip hL hσ hY2
  have hGm : StronglyMeasurable[ℱ s] (fun ω => σ (Y ω)) := hσc.comp_stronglyMeasurable hYm
  obtain ⟨hS2, hSiso, hSorth⟩ := hC _ hGm hG2 S (fun ω => rfl)
  have he2 : MemLp e 2 P := hXs.sub hY2
  have hbY : MemLp (fun ω => b (Y ω)) 2 P := memLp_comp_lip hL hb hY2
  have hD2 : MemLp D 2 P :=
    ((hXt.sub hXs).sub ((hImem t).sub (hImem s))).sub (hbY.mul_const h)
  have heS : ∫ ω, e ω * S ω ∂P = 0 :=
    hSorth e ((hadapt s hs hs').sub hYm.aestronglyMeasurable) he2
  set Φ : Ω → ℝ → ℝ := fun ω r => 2 * L ^ 2 * ((X r ω - X s ω) ^ 2 + e ω ^ 2) with hΦ
  set Ee := ∫ ω, e ω ^ 2 ∂P with hEe
  have hEe0 : 0 ≤ Ee := integral_nonneg (fun ω => sq_nonneg _)
  set Q := 2 * L ^ 2 * (K * h + Ee) * h with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hjoint' : AEMeasurable (fun p : Ω × ℝ => X p.2 p.1)
      (P.prod (volume.restrict (Set.Icc s t))) :=
    hjoint.mono_ac (Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
      (Measure.absolutelyContinuous_of_le
        (Measure.restrict_mono (Set.Icc_subset_Icc hs htT) le_rfl)))
  have hXsP : AEMeasurable (X s) P := hXs.1.aemeasurable
  have heP : AEMeasurable e P := he2.1.aemeasurable
  have hΦm : AEMeasurable (Function.uncurry fun ω r => ENNReal.ofReal (Φ ω r))
      (P.prod (volume.restrict (Set.Icc s t))) := by
    have h1 : AEMeasurable (fun p : Ω × ℝ => X s p.1)
        (P.prod (volume.restrict (Set.Icc s t))) :=
      hXsP.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEMeasurable (fun p : Ω × ℝ => e p.1)
        (P.prod (volume.restrict (Set.Icc s t))) :=
      heP.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((((hjoint'.sub h1).pow_const 2).add (h2.pow_const 2)).const_mul _)
  have hJ : ∫⁻ ω, ∫⁻ r in Set.Icc s t, ENNReal.ofReal (Φ ω r) ∂volume ∂P ≤
      ENNReal.ofReal Q := by
    rw [lintegral_lintegral_swap hΦm]
    have hin : ∀ r ∈ Set.Icc s t, ∫⁻ ω, ENNReal.ofReal (Φ ω r) ∂P ≤
        ENNReal.ofReal (2 * L ^ 2 * (K * h + Ee)) := by
      intro r hr
      have hr0 : 0 ≤ r := le_trans hs hr.1
      have hrT : r ≤ T := le_trans hr.2 htT
      have hXr := hXmem r hr0 hrT
      have hi1 : Integrable (fun ω => (X r ω - X s ω) ^ 2) P := (hXr.sub hXs).integrable_sq
      have hi2 : Integrable (fun ω => e ω ^ 2) P := he2.integrable_sq
      have hint : Integrable (fun ω => Φ ω r) P := (hi1.add hi2).const_mul _
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun ω => by simp only [Φ, Pi.zero_apply]; positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hcalc : ∫ ω, Φ ω r ∂P = 2 * L ^ 2 * (∫ ω, (X r ω - X s ω) ^ 2 ∂P + Ee) := by
        simp only [Φ]
        rw [integral_const_mul, integral_add hi1 hi2]
      rw [hcalc]
      have h1 := hKb s r hs hr.1 hrT
      have h2 : K * (r - s) ≤ K * h := mul_le_mul_of_nonneg_left (by linarith [hr.2]) hK
      have hL2 : 0 ≤ 2 * L ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) hL2
    calc ∫⁻ r in Set.Icc s t, ∫⁻ ω, ENNReal.ofReal (Φ ω r) ∂P
        ≤ ∫⁻ r in Set.Icc s t, ENNReal.ofReal (2 * L ^ 2 * (K * h + Ee)) :=
          setLIntegral_mono' measurableSet_Icc hin
      _ = ENNReal.ofReal (2 * L ^ 2 * (K * h + Ee)) * ENNReal.ofReal h := by
          rw [setLIntegral_const, Real.volume_Icc, hh]
      _ = ENNReal.ofReal Q := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  have hSb : ∫ ω, S ω ^ 2 ∂P ≤ Q := by
    have h1 : ENNReal.ofReal (∫ ω, S ω ^ 2 ∂P) ≤ ENNReal.ofReal Q := by
      refine hSiso.trans (le_trans (lintegral_mono fun ω => lintegral_mono fun r => ?_) hJ)
      apply ENNReal.ofReal_le_ofReal
      rw [hH]
      exact lip_sq hσ _ _ _
    exact (ENNReal.ofReal_le_ofReal_iff hQ0).1 h1
  have hDb : ∫ ω, D ω ^ 2 ∂P ≤ h * Q := by
    have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (D ω ^ 2) ≤
        ENNReal.ofReal h * ∫⁻ r in Set.Icc s t, ENNReal.ofReal (Φ ω r) := by
      filter_upwards [hXcont, hXeq t (by linarith) htT, hXeq s hs hs'] with ω hc ht hs2
      have hbX : Continuous (fun r => b (X r ω)) := hbc.comp hc
      have hfc : Continuous (fun r => b (X r ω) - b (Y ω)) := hbX.sub continuous_const
      have hDeq : D ω = ∫ r in s..t, (b (X r ω) - b (Y ω)) := by
        simp only [D]
        rw [ht, hs2, intervalIntegral.integral_sub (hbX.intervalIntegrable _ _)
          intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul,
          ← intervalIntegral.integral_interval_sub_left (hbX.intervalIntegrable 0 t)
            (hbX.intervalIntegrable 0 s), hh]
        ring
      have hΦc : Continuous (fun r => Φ ω r) := by
        simp only [Φ]
        exact continuous_const.mul (((hc.sub continuous_const).pow 2).add continuous_const)
      have hpt : ∀ r, (b (X r ω) - b (Y ω)) ^ 2 ≤ Φ ω r := fun r => by
        simp only [Φ, e]; exact lip_sq hb _ _ _
      have hmono : ∫ r in s..t, (b (X r ω) - b (Y ω)) ^ 2 ≤ ∫ r in s..t, Φ ω r :=
        intervalIntegral.integral_mono_on hst.le ((hfc.pow 2).intervalIntegrable _ _)
          (hΦc.intervalIntegrable _ _) (fun r _ => hpt r)
      have hcs := sq_intervalIntegral_le hfc hst
      rw [hDeq]
      calc ENNReal.ofReal ((∫ r in s..t, (b (X r ω) - b (Y ω))) ^ 2)
          ≤ ENNReal.ofReal (h * ∫ r in s..t, Φ ω r) := by
            apply ENNReal.ofReal_le_ofReal
            rw [← hh]
            calc _ ≤ (t - s) * ∫ r in s..t, (b (X r ω) - b (Y ω)) ^ 2 := hcs
              _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by linarith)
        _ = ENNReal.ofReal h * ENNReal.ofReal (∫ r in s..t, Φ ω r) := ENNReal.ofReal_mul hh0.le
        _ = ENNReal.ofReal h * ∫⁻ r in Set.Ioc s t, ENNReal.ofReal (Φ ω r) := by
            rw [intervalIntegral.integral_of_le hst.le, ofReal_integral_eq_lintegral_ofReal
              (hΦc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
              (Eventually.of_forall fun r => by simp only [Φ, Pi.zero_apply]; positivity)]
        _ ≤ ENNReal.ofReal h * ∫⁻ r in Set.Icc s t, ENNReal.ofReal (Φ ω r) := by
            gcongr
            exact Set.Ioc_subset_Icc_self
    have h1 : ENNReal.ofReal (∫ ω, D ω ^ 2 ∂P) ≤ ENNReal.ofReal (h * Q) := by
      rw [ofReal_integral_eq_lintegral_ofReal hD2.integrable_sq
        (Eventually.of_forall fun ω => by simp only [Pi.zero_apply]; positivity)]
      calc ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal h * (∫⁻ r in Set.Icc s t, ENNReal.ofReal (Φ ω r)) ∂P :=
            lintegral_mono_ae hae
        _ = ENNReal.ofReal h * ∫⁻ ω, ∫⁻ r in Set.Icc s t, ENNReal.ofReal (Φ ω r) ∂volume ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal h * ENNReal.ofReal Q := by gcongr
        _ = ENNReal.ofReal (h * Q) := (ENNReal.ofReal_mul hh0.le).symm
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hES : MemLp (fun ω => e ω + S ω) 2 P := he2.add hS2
  have hEDS : MemLp (fun ω => e ω + D ω + S ω) 2 P := (he2.add hD2).add hS2
  have hint_eS : Integrable (fun ω => e ω * S ω) P := by
    refine Integrable.mono' (he2.integrable_sq.add hS2.integrable_sq) (he2.1.mul hS2.1)
      (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
    nlinarith [sq_nonneg (|e ω| - |S ω|), sq_abs (e ω), sq_abs (S ω), abs_nonneg (e ω),
      abs_nonneg (S ω)]
  have hi_e : Integrable (fun ω => e ω ^ 2) P := he2.integrable_sq
  have hi_S : Integrable (fun ω => S ω ^ 2) P := hS2.integrable_sq
  have hi_D : Integrable (fun ω => D ω ^ 2) P := hD2.integrable_sq
  have hi_ES : Integrable (fun ω => (e ω + S ω) ^ 2) P := hES.integrable_sq
  have hi_EDS : Integrable (fun ω => (e ω + D ω + S ω) ^ 2) P := hEDS.integrable_sq
  have hsplit : ∫ ω, (e ω + S ω) ^ 2 ∂P = Ee + ∫ ω, S ω ^ 2 ∂P := by
    have : (fun ω => (e ω + S ω) ^ 2) = fun ω => (e ω ^ 2 + 2 * (e ω * S ω)) + S ω ^ 2 := by
      funext ω; ring
    have hi2 : Integrable (fun ω => 2 * (e ω * S ω)) P := hint_eS.const_mul 2
    have hia : Integrable (fun ω => e ω ^ 2 + 2 * (e ω * S ω)) P := hi_e.add hi2
    rw [this, integral_add hia hi_S, integral_add hi_e hi2, integral_const_mul, heS]
    ring
  have hpt : ∀ ω, (e ω + D ω + S ω) ^ 2 ≤
      (1 + h) * (e ω + S ω) ^ 2 + (1 + 1 / h) * D ω ^ 2 := fun ω => by
    have := young hh0 (e ω + S ω) (D ω)
    calc (e ω + D ω + S ω) ^ 2 = ((e ω + S ω) + D ω) ^ 2 := by ring
      _ ≤ _ := this
  have hmain : ∫ ω, (e ω + D ω + S ω) ^ 2 ∂P ≤
      (1 + h) * ∫ ω, (e ω + S ω) ^ 2 ∂P + (1 + 1 / h) * ∫ ω, D ω ^ 2 ∂P := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi_ES.const_mul _) (hi_D.const_mul _)]
    exact integral_mono hi_EDS ((hi_ES.const_mul _).add (hi_D.const_mul _)) hpt
  have hgoal : (fun ω => (X t ω - (Y ω + b (Y ω) * h + σ (Y ω) * (Wf t ω - Wf s ω))) ^ 2) =
      fun ω => (e ω + D ω + S ω) ^ 2 := by
    funext ω; simp only [e, D, S]; ring
  rw [hgoal]
  have hD' : (1 + 1 / h) * ∫ ω, D ω ^ 2 ∂P ≤ (1 + h) * Q := by
    have : (1 + 1 / h) * (h * Q) = (1 + h) * Q := by field_simp; ring
    calc _ ≤ (1 + 1 / h) * (h * Q) := mul_le_mul_of_nonneg_left hDb (by positivity)
      _ = _ := this
  have hS' : (1 + h) * ∫ ω, S ω ^ 2 ∂P ≤ (1 + h) * Q :=
    mul_le_mul_of_nonneg_left hSb (by linarith)
  rw [hsplit] at hmain
  have e1 : 2 * (1 + h) * Q ≤ (1 + T) * (4 * L ^ 2 * (K * h ^ 2 + Ee * h)) := by
    have : 2 * (1 + h) * Q = (1 + h) * (4 * L ^ 2 * (K * h ^ 2 + Ee * h)) := by
      rw [hQ]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hnn : 0 ≤ h * Ee * (4 * (1 + T) * L ^ 2 * K) + h ^ 2 * (1 + 4 * (1 + T) * L ^ 2) := by
    have : 0 ≤ 1 + T := by linarith
    positivity
  have key : (1 + h) * Ee + (1 + T) * (4 * L ^ 2 * (K * h ^ 2 + Ee * h)) +
      (h * Ee * (4 * (1 + T) * L ^ 2 * K) + h ^ 2 * (1 + 4 * (1 + T) * L ^ 2)) =
      (1 + (1 + 4 * (1 + T) * L ^ 2 * (1 + K)) * h) * Ee +
        (1 + 4 * (1 + T) * L ^ 2 * (1 + K)) * h ^ 2 := by ring
  linarith

end EMGridAux

namespace EMSchemeAux

lemma lip_cont {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    Continuous f := by
  have : LipschitzWith ⟨L, hL⟩ f := LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, Real.dist_eq]; exact hf x y
  exact this.continuous

lemma memLp_comp_lip {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    MemLp (fun ω => f (Y ω)) 2 P := by
  refine MemLp.of_le ((memLp_const |f 0|).add (hY.norm.const_mul L))
    ((lip_cont hL hf).comp_aestronglyMeasurable hY.1) (Eventually.of_forall fun ω => ?_)
  have h1 := hf (Y ω) 0
  simp only [sub_zero] at h1
  have h2 : |f (Y ω)| ≤ |f 0| + L * |Y ω| := by
    have := abs_sub_abs_le_abs_sub (f (Y ω)) (f 0); linarith
  simp only [Real.norm_eq_abs, Pi.add_apply] at *
  calc |f (Y ω)| ≤ |f 0| + L * |Y ω| := h2
    _ ≤ _ := le_abs_self _

/-- An `ℱ s`-measurable `L²` variable times a later Brownian increment is in `L²`
(independence factorises the second moment). -/
lemma memLp_mul_increment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : IsBrownianFiltration W ℱ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {ξ : Ω → ℝ} (hξm : StronglyMeasurable[ℱ s] ξ) (hξ : MemLp ξ 2 P) :
    MemLp (fun ω => ξ ω * (W.W t ω - W.W s ω)) 2 P := by
  set ΔW : Ω → ℝ := fun ω => W.W t ω - W.W s ω with hΔW
  have hΔm : Measurable ΔW := (W.measurable_eval t).sub (W.measurable_eval s)
  have hξmeas : Measurable ξ := (hξm.mono (ℱ.le s)).measurable
  have hind : IndepFun ξ ΔW P := by
    rw [IndepFun_iff]
    intro u v hu hv
    exact (Indep_iff _ _ _).1 (hW.indep hs hst) u v (hξm.measurable.comap_le u hu) hv
  have hΔ2 : MemLp ΔW 2 P :=
    (memLp_two_iff_integrable_sq hΔm.aestronglyMeasurable).2
      (Ito.brownian_increment_sq_integrable W hs hst)
  refine ⟨(hξmeas.mul hΔm).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  have h1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top).1 hξ.2
  have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top).1 hΔ2.2
  have hmul : ∀ ω, ‖ξ ω * ΔW ω‖ₑ ^ (ENNReal.toReal 2) =
      ‖ξ ω‖ₑ ^ (ENNReal.toReal 2) * ‖ΔW ω‖ₑ ^ (ENNReal.toReal 2) := fun ω => by
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  refine lt_of_eq_of_lt (lintegral_congr fun ω => hmul ω) ?_
  have hind2 := hind.comp (φ := fun x : ℝ => ‖x‖ₑ ^ (ENNReal.toReal 2))
    (ψ := fun x : ℝ => ‖x‖ₑ ^ (ENNReal.toReal 2)) (by fun_prop) (by fun_prop)
  have key := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (μ := P) (by fun_prop) (by fun_prop) hind2
  simp only [Function.comp_def] at key
  rw [show (fun ω => ‖ξ ω‖ₑ ^ (ENNReal.toReal 2) * ‖ΔW ω‖ₑ ^ (ENNReal.toReal 2)) =
      (fun ω => ‖ξ ω‖ₑ ^ (ENNReal.toReal 2)) * (fun ω => ‖ΔW ω‖ₑ ^ (ENNReal.toReal 2))
      from rfl, key]
  exact ENNReal.mul_lt_top h1 h2

end EMSchemeAux


theorem Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SolReg_Adapted
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmom : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      Integrable (fun ω : Ω => (X t ω) ^ 2) P)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ), H ω s = σ (X s ω))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
        x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            W ℱ hW H hHmeas hHprog hHsq t ω) :
    (∀ t : ℝ, 0 ≤ t → t ≤ T → AEStronglyMeasurable[ℱ t] (X t) P) := by
  obtain ⟨L, hL0, hb, -⟩ := hLip
  exact em_adapted_abs ℱ _ (fun r => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted
    W ℱ hW H hHmeas hHprog hHsq r) b L hL0 hb x₀ T hT.le X hXcont hXeq

theorem Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SolReg_JointMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmom : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      Integrable (fun ω : Ω => (X t ω) ^ 2) P)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ), H ω s = σ (X s ω))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
        x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            W ℱ hW H hHmeas hHprog hHsq t ω) :
    AEMeasurable (fun p : Ω × ℝ => X p.2 p.1) (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  obtain ⟨X', hX'm, hXX', -, -⟩ :=
    em_solution_regularity P W ℱ hW T x₀ hT b σ hLip X hXcont hXmom H hH hHmeas hHprog hHsq hXeq
  refine ⟨fun p => X' p.2 p.1, hX'm, ?_⟩
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := P)
    (ν := volume.restrict (Set.Icc (0 : ℝ) T))).ae hXX'
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := P)
    (ν := volume.restrict (Set.Icc (0 : ℝ) T))).ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [h1, h2] with p hp1 hp2
  exact hp1 p.2 hp2

theorem Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SolReg_MomentBound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmom : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      Integrable (fun ω : Ω => (X t ω) ^ 2) P)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ), H ω s = σ (X s ω))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
        x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            W ℱ hW H hHmeas hHprog hHsq t ω) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      ∫ ω, (X t ω - X s ω) ^ 2 ∂P ≤ K * (t - s) := by
  obtain ⟨X', hX'm, hXX', -, C, hC, hCb⟩ :=
    em_solution_regularity P W ℱ hW T x₀ hT b σ hLip X hXcont hXmom H hH hHmeas hHprog hHsq hXeq
  refine ⟨C, hC, fun s t hs hst htT => ?_⟩
  have hX'r : ∀ r, Measurable (X' r) := fun r =>
    hX'm.comp (measurable_id.prodMk measurable_const)
  have hae : (fun ω => (X t ω - X s ω) ^ 2) =ᵐ[P] fun ω => (X' t ω - X' s ω) ^ 2 := by
    filter_upwards [hXX'] with ω hω
    rw [hω t ⟨hs.trans hst, htT⟩, hω s ⟨hs, hst.trans htT⟩]
  rw [integral_congr_ae hae, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun ω => sq_nonneg _)
    (by have hm : Measurable (fun ω => (X' t ω - X' s ω) ^ 2) :=
          ((hX'r t).sub (hX'r s)).pow_const 2
        exact hm.aestronglyMeasurable)]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (by linarith)) (hCb s t hs hst htT)

theorem Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SolutionRegularity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmom : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      Integrable (fun ω : Ω => (X t ω) ^ 2) P)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ), H ω s = σ (X s ω))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
        x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            W ℱ hW H hHmeas hHprog hHsq t ω) :
    (∀ t : ℝ, 0 ≤ t → t ≤ T → AEStronglyMeasurable[ℱ t] (X t) P) ∧
    AEMeasurable (fun p : Ω × ℝ => X p.2 p.1) (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      ∫ ω, (X t ω - X s ω) ^ 2 ∂P ≤ K * (t - s) :=
  ⟨Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SolReg_Adapted P W ℱ hW T x₀ hT b σ hLip X hXcont hXmom H hH hHmeas hHprog hHsq hXeq,
   Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SolReg_JointMeasurable P W ℱ hW T x₀ hT b σ hLip X hXcont hXmom H hH hHmeas hHprog hHsq hXeq,
   Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SolReg_MomentBound P W ℱ hW T x₀ hT b σ hLip X hXcont hXmom H hH hHmeas hHprog hHsq hXeq⟩

theorem Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SchemeAdapted
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (E : (n : ℕ) → Fin (n + 1) → Ω → ℝ)
    (hE0 : ∀ (n : ℕ) (ω : Ω), E n 0 ω = x₀)
    (hErec : ∀ (n : ℕ), 0 < n →
      ∀ (k : Fin n) (ω : Ω),
        E n k.succ ω = E n k.castSucc ω +
          b (E n k.castSucc ω) * (T / n) +
          σ (E n k.castSucc ω) *
          (W.W ((((k.val + 1 : ℕ) : ℝ) * T / n)) ω -
            W.W (((k.val : ℝ) * T / n)) ω)) :
    ∀ (n : ℕ), 0 < n → ∀ k : Fin (n + 1),
      StronglyMeasurable[ℱ ((k.val : ℝ) * T / n)] (E n k) ∧ MemLp (E n k) 2 P := by
  obtain ⟨L, hL, hb, hσ⟩ := hLip
  have hbc := EMSchemeAux.lip_cont hL hb
  have hσc := EMSchemeAux.lip_cont hL hσ
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  suffices H : ∀ k (hk : k < n + 1),
      StronglyMeasurable[ℱ ((k : ℝ) * T / n)] (E n ⟨k, hk⟩) ∧ MemLp (E n ⟨k, hk⟩) 2 P from
    fun k => H k.val k.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : E n ⟨0, hk⟩ = fun _ => x₀ := funext fun ω => hE0 n ω
    rw [h0]
    exact ⟨stronglyMeasurable_const, memLp_const _⟩
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    obtain ⟨hm, h2⟩ := ih (by omega)
    have hs0 : (0 : ℝ) ≤ (k : ℝ) * T / n := by positivity
    have hst : (k : ℝ) * T / n < ((k + 1 : ℕ) : ℝ) * T / n := by
      rw [div_lt_div_iff_of_pos_right hnR]
      push_cast
      nlinarith
    have hrec : E n ⟨k + 1, hk⟩ = fun ω => E n ⟨k, by omega⟩ ω +
        b (E n ⟨k, by omega⟩ ω) * (T / n) +
        σ (E n ⟨k, by omega⟩ ω) *
          (W.W (((k + 1 : ℕ) : ℝ) * T / n) ω - W.W ((k : ℝ) * T / n) ω) := by
      funext ω
      exact hErec n hn ⟨k, hkn⟩ ω
    rw [hrec]
    have hmono : ℱ ((k : ℝ) * T / n) ≤ ℱ (((k + 1 : ℕ) : ℝ) * T / n) := ℱ.mono hst.le
    have hm' := hm.mono hmono
    constructor
    · refine (hm'.add ((hbc.comp_stronglyMeasurable hm').mul stronglyMeasurable_const)).add
        ((hσc.comp_stronglyMeasurable hm').mul ?_)
      exact (hW.stronglyMeasurable _).sub ((hW.stronglyMeasurable _).mono hmono)
    · exact (h2.add ((EMSchemeAux.memLp_comp_lip hL hb h2).mul_const _)).add
        (EMSchemeAux.memLp_mul_increment W ℱ hW hs0 hst
          (hσc.comp_stronglyMeasurable hm) (EMSchemeAux.memLp_comp_lip hL hσ h2))



theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T x₀ : ℝ) (hT : 0 < T)
    (b σ : ℝ → ℝ)
    (hLip : ∃ L : ℝ, 0 ≤ L ∧
      (∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) ∧
      (∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|))
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => X t ω))
    (hXmom : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      Integrable (fun ω : Ω => (X t ω) ^ 2) P)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ), H ω s = σ (X s ω))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXeq : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      (fun ω : Ω => X t ω) =ᵐ[P] fun ω : Ω =>
        x₀ + (∫ s in (0 : ℝ)..t, b (X s ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            W ℱ hW H hHmeas hHprog hHsq t ω)
    (E : (n : ℕ) → Fin (n + 1) → Ω → ℝ)
    (hE0 : ∀ (n : ℕ) (ω : Ω), E n 0 ω = x₀)
    (hErec : ∀ (n : ℕ), 0 < n →
      ∀ (k : Fin n) (ω : Ω),
        E n k.succ ω = E n k.castSucc ω +
          b (E n k.castSucc ω) * (T / n) +
          σ (E n k.castSucc ω) *
          (W.W ((((k.val + 1 : ℕ) : ℝ) * T / n)) ω -
            W.W (((k.val : ℝ) * T / n)) ω)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ), 0 < n →
      ∃ e : ℕ → ℝ,
        e 0 ≤ 0 ∧
          (∀ k : ℕ,
            e (k + 1) ≤ (1 + c * (T / n)) * e k + c * (T / n) ^ 2) ∧
          (∀ k : Fin (n + 1),
            e k.val = ∫ ω, (X ((k.val : ℝ) * T / n) ω - E n k ω) ^ 2 ∂P) := by
  obtain ⟨L, hL, hb, hσ⟩ := hLip
  obtain ⟨hadapt, hjoint, K, hK, hKb⟩ :=
    Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SolutionRegularity
      P W ℱ hW T x₀ hT b σ ⟨L, hL, hb, hσ⟩ X hXcont hXmom H hH hHmeas hHprog hHsq hXeq
  have hsch :=
    Xeroth_AppliedSDE_SarkkaSolin_euler_maruyama_grid_l2_local_error_SchemeAdapted
      P W ℱ hW T x₀ hT b σ ⟨L, hL, hb, hσ⟩ E hE0 hErec
  have hImem : ∀ t : ℝ, MemLp
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq t) 2 P :=
    fun t => (Lp.memLp _).ae_eq
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq W ℱ hW H hHmeas hHprog
        hHsq t).symm
  have hXmem : ∀ r : ℝ, 0 ≤ r → r ≤ T → MemLp (X r) 2 P := fun r h0 h1 =>
    (memLp_two_iff_integrable_sq ((hadapt r h0 h1).mono (ℱ.le r))).2 (hXmom r ⟨h0, h1⟩)
  have hI0 : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq 0
      =ᵐ[P] 0 := by
    have h := LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 W ℱ hW H hHmeas hHprog hHsq
      (le_refl (0 : ℝ))
    simp only [LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W _ (le_refl (0 : ℝ)),
      zero_sub] at h
    have h2 := tendsto_nhds_unique tendsto_const_nhds h
    have h3 := (eLpNorm_eq_zero_iff ((hImem 0).1.neg) two_ne_zero).1 h2
    filter_upwards [h3] with ω hω
    simpa using hω
  refine ⟨1 + 4 * (1 + T) * L ^ 2 * (1 + K), by positivity, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let e : ℕ → ℝ := fun k => if hk : k < n + 1 then
    ∫ ω, (X ((k : ℝ) * T / n) ω - E n ⟨k, hk⟩ ω) ^ 2 ∂P else 0
  have e_nonneg : ∀ k, 0 ≤ e k := by
    intro k
    simp only [e]
    split_ifs
    · exact integral_nonneg fun _ => sq_nonneg _
    · exact le_rfl
  refine ⟨e, ?_, ?_, ?_⟩
  · have h0 := hXeq 0 le_rfl hT.le
    simp only [e, dif_pos (Nat.succ_pos n)]
    apply le_of_eq
    apply integral_eq_zero_of_ae
    filter_upwards [h0, hI0] with ω hω hI
    simp only [Pi.zero_apply] at hI
    simp only [Nat.cast_zero, zero_mul, zero_div, Pi.zero_apply]
    rw [show (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 from rfl, hE0, hω, hI]
    simp
  · intro k
    by_cases hk : k + 1 < n + 1
    · have hkn : k < n := by omega
      have hk' : k < n + 1 := by omega
      have hY := hsch n hn ⟨k, hk'⟩
      have hs0 : (0 : ℝ) ≤ (k : ℝ) * T / n := by positivity
      have hst : (k : ℝ) * T / n < ((k + 1 : ℕ) : ℝ) * T / n := by
        rw [div_lt_div_iff_of_pos_right hnR]
        push_cast
        nlinarith
      have htT : ((k + 1 : ℕ) : ℝ) * T / n ≤ T := by
        rw [div_le_iff₀ hnR]
        have : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hkn
        nlinarith
      have hhh : ((k + 1 : ℕ) : ℝ) * T / n - (k : ℝ) * T / n = T / n := by
        push_cast; field_simp; ring
      have hstep := EMGridAux.step ℱ W.W
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW H hHmeas hHprog hHsq)
        X H b σ L K T x₀ hL hK hb hσ hXcont hXmem hH hXeq hImem hadapt hjoint hKb
        ((k : ℝ) * T / n) (((k + 1 : ℕ) : ℝ) * T / n) (T / n) hs0 hst htT hhh
        (E n ⟨k, hk'⟩) hY.1 hY.2
        (fun G hG hG2 S hS =>
          em_frozen_increment
            P W ℱ hW H hHmeas hHprog hHsq _ _ hs0 hst G hG hG2 S hS)
      have hEq : (fun ω => (X (((k + 1 : ℕ) : ℝ) * T / n) ω - E n ⟨k + 1, hk⟩ ω) ^ 2) =
          fun ω => (X (((k + 1 : ℕ) : ℝ) * T / n) ω - (E n ⟨k, hk'⟩ ω +
            b (E n ⟨k, hk'⟩ ω) * (T / n) + σ (E n ⟨k, hk'⟩ ω) *
              (W.W (((k + 1 : ℕ) : ℝ) * T / n) ω - W.W ((k : ℝ) * T / n) ω))) ^ 2 := by
        funext ω
        have := hErec n hn ⟨k, hkn⟩ ω
        rw [show (⟨k + 1, hk⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).succ from rfl, this]
        rfl
      show (if hk : k + 1 < n + 1 then
          ∫ ω, (X (((k + 1 : ℕ) : ℝ) * T / n) ω - E n ⟨k + 1, hk⟩ ω) ^ 2 ∂P else 0) ≤
        (1 + (1 + 4 * (1 + T) * L ^ 2 * (1 + K)) * (T / n)) *
          (if hk : k < n + 1 then ∫ ω, (X ((k : ℝ) * T / n) ω - E n ⟨k, hk⟩ ω) ^ 2 ∂P else 0) +
          (1 + 4 * (1 + T) * L ^ 2 * (1 + K)) * (T / n) ^ 2
      rw [dif_pos hk, dif_pos hk', hEq]
      exact hstep
    · have hk1 : e (k + 1) = 0 := by simp only [e, dif_neg hk]
      rw [hk1]
      have : 0 ≤ T / n := by positivity
      exact add_nonneg (mul_nonneg (by positivity) (e_nonneg k)) (by positivity)
  · intro k
    simp only [e, dif_pos k.isLt, Fin.eta]
