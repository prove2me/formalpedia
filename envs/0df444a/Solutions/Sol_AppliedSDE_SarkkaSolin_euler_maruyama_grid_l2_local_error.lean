-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_maruyama_grid_l2_local_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T22:45:32.369932+00:00
-- url     : https://prove2.me/submissions/57fa642a-b0e0-482d-b782-68792ea1d859
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_solution_aestronglyMeasurable
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_scheme_memLp_two
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_drift_local_error
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_maruyama_diffusion_local_error
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

/-- Second-moment expansion with one orthogonal pair: if `E[D M] = 0` and `r h = 1`, then
`E (D + A + M)² ≤ (1 + h) E D² + (2 + r) E A² + 2 E M²`. -/
theorem em_three_term_l2_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D A M : Ω → ℝ}
    (hD : MemLp D 2 P) (hA : MemLp A 2 P) (hM : MemLp M 2 P)
    {h r : ℝ} (hh : 0 < h) (hr : r * h = 1) (hDM : ∫ ω, D ω * M ω ∂P = 0) :
    ∫ ω, (D ω + A ω + M ω) ^ 2 ∂P ≤
      (1 + h) * ∫ ω, D ω ^ 2 ∂P + (2 + r) * ∫ ω, A ω ^ 2 ∂P + 2 * ∫ ω, M ω ^ 2 ∂P := by
  have iD : Integrable (fun ω => D ω ^ 2) P := hD.integrable_sq
  have iA : Integrable (fun ω => A ω ^ 2) P := hA.integrable_sq
  have iM : Integrable (fun ω => M ω ^ 2) P := hM.integrable_sq
  have iDM : Integrable (fun ω => D ω * M ω) P := hD.integrable_mul hM
  have hr0 : 0 < r := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have hS : MemLp (fun ω => D ω + A ω + M ω) 2 P := (hD.add hA).add hM
  have iS : Integrable (fun ω => (D ω + A ω + M ω) ^ 2) P := hS.integrable_sq
  have i1 : Integrable (fun ω => (1 + h) * D ω ^ 2) P := iD.const_mul _
  have i2 : Integrable (fun ω => (2 + r) * A ω ^ 2) P := iA.const_mul _
  have i3 : Integrable (fun ω => 2 * M ω ^ 2) P := iM.const_mul _
  have i4 : Integrable (fun ω => 2 * (D ω * M ω)) P := iDM.const_mul _
  have hpt : ∀ ω, (D ω + A ω + M ω) ^ 2 ≤
      (1 + h) * D ω ^ 2 + (2 + r) * A ω ^ 2 + 2 * M ω ^ 2 + 2 * (D ω * M ω) := by
    intro ω
    have h1 : 2 * D ω * A ω ≤ h * D ω ^ 2 + r * A ω ^ 2 := by
      have hnn := mul_nonneg hr0.le (sq_nonneg (h * D ω - A ω))
      have e : h * D ω ^ 2 + r * A ω ^ 2 - 2 * D ω * A ω = r * (h * D ω - A ω) ^ 2 := by
        linear_combination (-(h * D ω ^ 2 - 2 * D ω * A ω)) * hr
      linarith
    have h2 : 2 * A ω * M ω ≤ A ω ^ 2 + M ω ^ 2 := by nlinarith [sq_nonneg (A ω - M ω)]
    have e2 : (D ω + A ω + M ω) ^ 2 =
        D ω ^ 2 + A ω ^ 2 + M ω ^ 2 + 2 * D ω * A ω + 2 * A ω * M ω + 2 * (D ω * M ω) := by ring
    rw [e2]; linarith
  calc ∫ ω, (D ω + A ω + M ω) ^ 2 ∂P
      ≤ ∫ ω, ((1 + h) * D ω ^ 2 + (2 + r) * A ω ^ 2 + 2 * M ω ^ 2 + 2 * (D ω * M ω)) ∂P :=
        integral_mono iS (((i1.add i2).add i3).add i4) hpt
    _ = (1 + h) * ∫ ω, D ω ^ 2 ∂P + (2 + r) * ∫ ω, A ω ^ 2 ∂P + 2 * ∫ ω, M ω ^ 2 ∂P := by
        have s1 : ∫ ω, ((1 + h) * D ω ^ 2 + (2 + r) * A ω ^ 2 + 2 * M ω ^ 2 + 2 * (D ω * M ω)) ∂P =
            ∫ ω, ((1 + h) * D ω ^ 2 + (2 + r) * A ω ^ 2 + 2 * M ω ^ 2) ∂P +
              ∫ ω, 2 * (D ω * M ω) ∂P := integral_add ((i1.add i2).add i3) i4
        have s2 : ∫ ω, ((1 + h) * D ω ^ 2 + (2 + r) * A ω ^ 2 + 2 * M ω ^ 2) ∂P =
            ∫ ω, ((1 + h) * D ω ^ 2 + (2 + r) * A ω ^ 2) ∂P + ∫ ω, 2 * M ω ^ 2 ∂P :=
          integral_add (i1.add i2) i3
        have s3 : ∫ ω, ((1 + h) * D ω ^ 2 + (2 + r) * A ω ^ 2) ∂P =
            ∫ ω, (1 + h) * D ω ^ 2 ∂P + ∫ ω, (2 + r) * A ω ^ 2 ∂P := integral_add i1 i2
        rw [s1, s2, s3, integral_const_mul, integral_const_mul, integral_const_mul,
          integral_const_mul, hDM]
        ring

/-- A globally Lipschitz map preserves square integrability on a probability space. -/
theorem em_lipschitz_comp_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) {b : ℝ → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hbL : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|) :
    MemLp (fun ω => b (f ω)) 2 P := by
  have hbc : Continuous b := by
    have hl : LipschitzWith (Real.toNNReal L) b := LipschitzWith.of_dist_le_mul (fun x y => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0]; exact hbL x y)
    exact hl.continuous
  have h1 : MemLp (fun ω => b (f ω) - b 0) 2 P := by
    refine MemLp.of_le_mul (c := L) hf
      ((hbc.comp_aestronglyMeasurable hf.aestronglyMeasurable).sub aestronglyMeasurable_const)
      (ae_of_all _ (fun ω => ?_))
    have := hbL (f ω) 0
    rw [sub_zero] at this
    simpa [Real.norm_eq_abs] using this
  have h2 : MemLp (fun ω => (b (f ω) - b 0) + b 0) 2 P := h1.add (memLp_const (b 0))
  have hfun : (fun ω => (b (f ω) - b 0) + b 0) = fun ω => b (f ω) := by
    funext ω; ring
  rwa [hfun] at h2

/-- The platform Itô integral is square integrable at every time. -/
theorem em_ito_memLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ) (H : Ω → ℝ → ℝ)
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
      W ℱ hW H hHmeas hHprog hHsq t) 2 P :=
  (MeasureTheory.Lp.memLp _).ae_eq
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq
      W ℱ hW H hHmeas hHprog hHsq t).symm

/-- The platform Itô integral vanishes almost surely at time zero. -/
theorem em_ito_zero_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ) (H : Ω → ℝ → ℝ)
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
      W ℱ hW H hHmeas hHprog hHsq 0 =ᵐ[P] 0 := by
  obtain ⟨J, hJ⟩ : ∃ J : Ω → ℝ, J = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
      W ℱ hW H hHmeas hHprog hHsq 0 := ⟨_, rfl⟩
  have hJmem : MemLp J 2 P := hJ ▸ em_ito_memLp P W ℱ hW H hHmeas hHprog hHsq 0
  have ht := LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2
    W ℱ hW H hHmeas hHprog hHsq (le_refl (0 : ℝ))
  rw [← hJ] at ht ⊢
  have hconst : ∀ m : ℕ, eLpNorm (fun ω =>
      LevyStochCalc.Brownian.Ito.simpleIntegral W
        (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hHmeas hHprog hHsq m) 0 ω - J ω) 2 P =
      eLpNorm J 2 P := by
    intro m
    have hfun : (fun ω =>
        LevyStochCalc.Brownian.Ito.simpleIntegral W
          (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hHmeas hHprog hHsq m) 0 ω - J ω) = -J := by
      funext ω
      rw [LevyStochCalc.Brownian.Ito.simpleIntegral_eq_zero_of_nonpos W _ (le_refl (0 : ℝ)) ω,
        zero_sub, Pi.neg_apply]
    rw [hfun, eLpNorm_neg]
  simp only [hconst] at ht
  have h0 : eLpNorm J 2 P = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  exact (eLpNorm_eq_zero_iff hJmem.aestronglyMeasurable (by norm_num)).mp h0

set_option maxHeartbeats 1000000 in
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
  obtain ⟨I, hI⟩ : ∃ I : ℝ → Ω → ℝ, ∀ (t : ℝ) (ω : Ω), I t ω =
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
        W ℱ hW H hHmeas hHprog hHsq t ω := ⟨_, fun _ _ => rfl⟩
  have hXae := AppliedSDE.SarkkaSolin.euler_maruyama_solution_aestronglyMeasurable
    P W ℱ hW T x₀ hT b σ hLip X hXcont hXmom H hH hHmeas hHprog hHsq hXeq
  have hEmem := AppliedSDE.SarkkaSolin.euler_maruyama_scheme_memLp_two
    P W ℱ hW T x₀ hT b σ hLip E hE0 hErec
  obtain ⟨c₁, hc₁, h3⟩ := AppliedSDE.SarkkaSolin.euler_maruyama_drift_local_error
    P W ℱ hW T x₀ hT b σ hLip X hXcont hXmom H hH hHmeas hHprog hHsq hXeq I hI E hE0 hErec
  obtain ⟨c₂, hc₂, h4⟩ := AppliedSDE.SarkkaSolin.euler_maruyama_diffusion_local_error
    P W ℱ hW T x₀ hT b σ hLip X hXcont hXmom H hH hHmeas hHprog hHsq hXeq I hI E hE0 hErec
  obtain ⟨L, hL0, hbL, -⟩ := hLip
  -- square integrability of the building blocks
  have hIfun : ∀ t : ℝ, I t = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
      W ℱ hW H hHmeas hHprog hHsq t := fun t => funext (hI t)
  have hImem : ∀ t : ℝ, MemLp (I t) 2 P := by
    intro t
    rw [hIfun t]
    exact em_ito_memLp P W ℱ hW H hHmeas hHprog hHsq t
  have hXmem : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T → MemLp (X t) 2 P := fun t ht =>
    (memLp_two_iff_integrable_sq (hXae t ht)).mpr (hXmom t ht)
  have hbE : ∀ (n : ℕ), 0 < n → ∀ k : Fin (n + 1), MemLp (fun ω => b (E n k ω)) 2 P :=
    fun n hn k => em_lipschitz_comp_memLp (hEmem n hn k) hL0 hbL
  -- the stochastic integral vanishes at time zero, hence `X 0 = x₀` almost surely
  have hI0 : I 0 =ᵐ[P] 0 := by
    rw [hIfun 0]
    exact em_ito_zero_ae P W ℱ hW H hHmeas hHprog hHsq
  have hX0 : ∀ᵐ ω ∂P, X 0 ω = x₀ := by
    filter_upwards [hXeq 0 le_rfl hT.le, hI0] with ω h1 h2
    have h2' : I 0 ω = 0 := h2
    rw [h1, ← hI 0 ω, h2']
    simp
  -- the one-step estimate
  set C : ℝ := c₁ * (2 * T + 1) + 2 * c₂ with hC
  have hC0 : 0 ≤ C := by positivity
  have hstep : ∀ (n : ℕ), 0 < n → ∀ k : Fin n,
      ∫ ω, (X (((k.val + 1 : ℕ) : ℝ) * T / n) ω - E n k.succ ω) ^ 2 ∂P ≤
        (1 + (1 + C) * (T / n)) *
          (∫ ω, (X ((k.val : ℝ) * T / n) ω - E n k.castSucc ω) ^ 2 ∂P) +
          (1 + C) * (T / n) ^ 2 := by
    intro n hn k
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hkn : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
    have hk0 : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    have hh : 0 < T / n := div_pos hT hnR
    have hhT : T / n ≤ T := div_le_self hT.le (by exact_mod_cast hn)
    have ht0 : (k.val : ℝ) * T / n ∈ Set.Icc (0 : ℝ) T := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_iff₀ hnR]; nlinarith
    have ht1 : ((k.val + 1 : ℕ) : ℝ) * T / n ∈ Set.Icc (0 : ℝ) T := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_iff₀ hnR]; push_cast; nlinarith
    set t0 : ℝ := (k.val : ℝ) * T / n with ht0def
    set t1 : ℝ := ((k.val + 1 : ℕ) : ℝ) * T / n with ht1def
    have hEk := hEmem n hn k.castSucc
    have hEk1 := hEmem n hn k.succ
    have hbEk := hbE n hn k.castSucc
    have hD : MemLp (fun ω => X t0 ω - E n k.castSucc ω) 2 P := (hXmem t0 ht0).sub hEk
    have hA : MemLp (fun ω => (X t1 ω - X t0 ω) - (I t1 ω - I t0 ω) -
        b (E n k.castSucc ω) * (T / n)) 2 P :=
      (((hXmem t1 ht1).sub (hXmem t0 ht0)).sub ((hImem t1).sub (hImem t0))).sub
        (hbEk.mul_const (T / n))
    have hσW : MemLp (fun ω => σ (E n k.castSucc ω) * (W.W t1 ω - W.W t0 ω)) 2 P := by
      have hfun : (fun ω => σ (E n k.castSucc ω) * (W.W t1 ω - W.W t0 ω)) =
          fun ω => E n k.succ ω - E n k.castSucc ω - b (E n k.castSucc ω) * (T / n) := by
        funext ω
        rw [hErec n hn k ω]; ring
      rw [hfun]
      exact (hEk1.sub hEk).sub (hbEk.mul_const (T / n))
    have hM : MemLp (fun ω => (I t1 ω - I t0 ω) -
        σ (E n k.castSucc ω) * (W.W t1 ω - W.W t0 ω)) 2 P :=
      ((hImem t1).sub (hImem t0)).sub hσW
    have hr : (1 / (T / n)) * (T / n) = 1 := by field_simp
    have key := em_three_term_l2_bound hD hA hM hh hr (h4 n hn k).2
    have hsum : (fun ω => ((X t0 ω - E n k.castSucc ω) +
        ((X t1 ω - X t0 ω) - (I t1 ω - I t0 ω) - b (E n k.castSucc ω) * (T / n)) +
        ((I t1 ω - I t0 ω) - σ (E n k.castSucc ω) * (W.W t1 ω - W.W t0 ω))) ^ 2) =
        fun ω => (X t1 ω - E n k.succ ω) ^ 2 := by
      funext ω
      rw [hErec n hn k ω]; ring
    rw [hsum] at key
    have ha := h3 n hn k
    have hm := (h4 n hn k).1
    set e : ℝ := ∫ ω, (X t0 ω - E n k.castSucc ω) ^ 2 ∂P with he
    have he0 : 0 ≤ e := integral_nonneg (fun ω => sq_nonneg _)
    set a : ℝ := ∫ ω, ((X t1 ω - X t0 ω) - (I t1 ω - I t0 ω) -
        b (E n k.castSucc ω) * (T / n)) ^ 2 ∂P with ha_def
    set m : ℝ := ∫ ω, ((I t1 ω - I t0 ω) -
        σ (E n k.castSucc ω) * (W.W t1 ω - W.W t0 ω)) ^ 2 ∂P with hm_def
    set h : ℝ := T / n with hh_def
    set r : ℝ := 1 / h with hr_def
    have hr0 : 0 ≤ r := by positivity
    have ha' : (2 + r) * a ≤ (2 + r) * (c₁ * h ^ 2 * (e + h)) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    have e1 : (2 + r) * (c₁ * h ^ 2 * (e + h)) = c₁ * (2 * h + 1) * h * (e + h) := by
      linear_combination (c₁ * h * (e + h)) * hr
    have e2 : c₁ * (2 * h + 1) * h * (e + h) ≤ c₁ * (2 * T + 1) * h * (e + h) := by
      have h21 : 2 * h + 1 ≤ 2 * T + 1 := by linarith
      have hnn : 0 ≤ h * (e + h) := by positivity
      have := mul_le_mul_of_nonneg_left h21 hc₁
      nlinarith [mul_le_mul_of_nonneg_right this hnn]
    have e3 : (1 + (1 + C) * h) * e + (1 + C) * h ^ 2 =
        (1 + h) * e + c₁ * (2 * T + 1) * h * (e + h) + 2 * (c₂ * h * (e + h)) + h ^ 2 := by
      rw [hC]; ring
    have hm2 : 2 * m ≤ 2 * (c₂ * h * (e + h)) := by linarith
    nlinarith [sq_nonneg h]
  refine ⟨1 + C, by positivity, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : 0 < T / n := div_pos hT hnR
  let idx : ℕ → Fin (n + 1) := fun j => ⟨min j n, Nat.lt_succ_of_le (min_le_right j n)⟩
  refine ⟨fun j => ∫ ω, (X (((idx j).val : ℝ) * T / n) ω - E n (idx j) ω) ^ 2 ∂P, ?_, ?_, ?_⟩
  · have hidx0 : idx 0 = 0 := by
      apply Fin.ext; simp [idx]
    have hae : (fun ω => (X (((idx 0).val : ℝ) * T / n) ω - E n (idx 0) ω) ^ 2) =ᵐ[P]
        fun _ => (0 : ℝ) := by
      filter_upwards [hX0] with ω hω
      rw [hidx0]
      simp [hE0, hω]
    show ∫ ω, (X (((idx 0).val : ℝ) * T / n) ω - E n (idx 0) ω) ^ 2 ∂P ≤ 0
    rw [integral_congr_ae hae]; simp
  · intro k
    show ∫ ω, (X (((idx (k + 1)).val : ℝ) * T / n) ω - E n (idx (k + 1)) ω) ^ 2 ∂P ≤
      (1 + (1 + C) * (T / n)) *
        (∫ ω, (X (((idx k).val : ℝ) * T / n) ω - E n (idx k) ω) ^ 2 ∂P) +
        (1 + C) * (T / n) ^ 2
    by_cases hk : k < n
    · have h1 : idx (k + 1) = (⟨k, hk⟩ : Fin n).succ := by
        apply Fin.ext; simp [idx]; omega
      have h2 : idx k = (⟨k, hk⟩ : Fin n).castSucc := by
        apply Fin.ext; simp [idx]; omega
      have := hstep n hn ⟨k, hk⟩
      rw [h1, h2]
      simpa using this
    · have h1 : idx (k + 1) = idx k := by
        apply Fin.ext; simp [idx]; omega
      rw [h1]
      have hx : 0 ≤ ∫ ω, (X (((idx k).val : ℝ) * T / n) ω - E n (idx k) ω) ^ 2 ∂P :=
        integral_nonneg (fun ω => sq_nonneg _)
      have hp1 : 0 ≤ (1 + C) * (T / n) := by positivity
      nlinarith [mul_nonneg hp1 hx, mul_nonneg hp1 hh.le]
  · intro k
    have hidx : idx k.val = k := by
      apply Fin.ext; simp [idx]; omega
    show ∫ ω, (X (((idx k.val).val : ℝ) * T / n) ω - E n (idx k.val) ω) ^ 2 ∂P = _
    rw [hidx]
