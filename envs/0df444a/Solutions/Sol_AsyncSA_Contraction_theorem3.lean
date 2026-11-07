-- Prove2me | solution 1 for AsyncSA.Contraction.theorem3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:19:13.405052+00:00
-- url     : https://prove2.me/submissions/8907b470-bb34-47f1-a363-1d9257290418

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model
import Theorems.Thm_AsyncSA_Contraction_theorem1
import Theorems.Thm_AsyncSA_Contraction_lemma2
import Theorems.Thm_AsyncSA_Contraction_lemma8

open MeasureTheory Filter Topology
open AsyncSA.Contraction

namespace AsyncSA.Contraction.Thm3Aux

/-- The weighted maximum norm is the sup norm of the rescaled vector. -/
lemma wNorm_eq_norm {n : ℕ} (hn : 0 < n) (v z : Fin n → ℝ) (hv : ∀ i, 0 < v i) :
    wNorm v z = ‖fun i => z i / v i‖ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hb : BddAbove (Set.range fun i => |z i| / v i) := Finite.bddAbove_range _
  show (⨆ i, |z i| / v i) = _
  have h0 : 0 ≤ ⨆ i, |z i| / v i :=
    le_trans (div_nonneg (abs_nonneg _) (hv ⟨0, hn⟩).le) (le_ciSup hb ⟨0, hn⟩)
  apply le_antisymm
  · apply ciSup_le; intro i
    have := norm_le_pi_norm (fun i => z i / v i) i
    simpa [Real.norm_eq_abs, abs_div, abs_of_pos (hv i)] using this
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
    simp only [Real.norm_eq_abs, abs_div, abs_of_pos (hv i)]
    exact le_ciSup hb i

/-- The algorithm after the translation `x ↦ x - x*` and the coordinate scaling by `v`. -/
noncomputable def scaled {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (xstar v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) : Algorithm n Ω where
  n_pos := alg.n_pos
  F := fun y i => (alg.F (fun j => v j * y j + xstar j) i - xstar i) / v i
  x := fun t ω i => (alg.x t ω i - xstar i) / v i
  α := alg.α
  w := fun i t ω => alg.w i t ω / v i
  τ := alg.τ
  α_mem := alg.α_mem
  τ_le := alg.τ_le
  update := by
    intro i t ω
    have hfun : (fun j => v j * ((alg.x (alg.τ i j t ω) ω j - xstar j) / v j) + xstar j)
        = fun j => alg.x (alg.τ i j t ω) ω j := by
      funext j; field_simp [(hv j).ne']; ring
    dsimp only
    rw [hfun, alg.update i t ω]
    field_simp [(hv i).ne']
    ring

lemma prod_le_exp (a : ℕ → ℝ) (ha : ∀ s, a s ∈ Set.Icc (0:ℝ) 1) (S : Finset ℕ) :
    ∏ s ∈ S, (1 - a s) ≤ Real.exp (-∑ s ∈ S, a s) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro s _; linarith [(ha s).2]
  · intro s _; have := Real.add_one_le_exp (-a s); linarith

lemma eventually_prod_small (a : ℕ → ℝ) (ha : ∀ s, a s ∈ Set.Icc (0:ℝ) 1)
    (hdiv : Tendsto (fun T => ∑ t ∈ Finset.range T, a t) atTop atTop) (t0 : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t in atTop, ∏ s ∈ Finset.Ico t0 t, (1 - a s) < η := by
  have h1 : Tendsto (fun t => ∑ s ∈ Finset.Ico t0 t, a s) atTop atTop := by
    have := tendsto_atTop_add_const_right _ (-(∑ t ∈ Finset.range t0, a t)) hdiv
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop t0] with t ht
    rw [Finset.sum_Ico_eq_sub _ ht, sub_eq_add_neg]
  have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).eventually (gt_mem_nhds hη)
  filter_upwards [h2] with t ht
  exact lt_of_le_of_lt (prod_le_exp a ha _) ht

/-- The deterministic sample-path part of the proof of Theorem 3 (§6). -/
lemma pathwise {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (ω : Ω) (β : ℝ)
    (hβ : 0 ≤ β ∧ β < 1) (hF : ∀ y : Fin n → ℝ, ‖alg.F y‖ ≤ β * ‖y‖)
    (hbdd : ∃ M : ℝ, ∀ t j, |alg.x t ω j| ≤ M)
    (hτ : ∀ i j, Tendsto (fun t => alg.τ i j t ω) atTop atTop)
    (hdiv : ∀ i, Tendsto (fun T => ∑ t ∈ Finset.range T, alg.α i t ω) atTop atTop)
    (hW : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, ∀ t₀ t : ℕ, T ≤ t₀ → t₀ ≤ t →
        |tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t₀ t| ≤ δ) :
    Tendsto (fun t => alg.x t ω) atTop (𝓝 0) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  set γ := (1 + β) / 2 with hγ
  have hγ1 : γ < 1 := by linarith
  have hβγ : β < γ := by linarith
  have hγ0 : 0 < γ := by linarith
  have step : ∀ D : ℝ, 0 < D → ∀ t₀ : ℕ, (∀ t ≥ t₀, ∀ j, |alg.x t ω j| ≤ D) →
      ∃ t₁ : ℕ, ∀ t ≥ t₁, ∀ j, |alg.x t ω j| ≤ γ * D := by
    intro D hD t₀ hx
    set η := (γ - β) * D / 2 with hη
    have hη0 : 0 < η := by
      have : 0 < γ - β := by linarith
      positivity
    have hτev : ∀ᶠ t in atTop, ∀ i j, t₀ ≤ alg.τ i j t ω :=
      eventually_all.2 fun i => eventually_all.2 fun j =>
        (hτ i j).eventually (eventually_ge_atTop t₀)
    obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 hτev
    have hWev : ∀ᶠ t' in atTop, ∀ i, ∀ t, t' ≤ t →
        |tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t' t| ≤ η :=
      eventually_all.2 fun i => by
        obtain ⟨T, hT⟩ := hW i η hη0
        exact eventually_atTop.2 ⟨T, fun t' ht' t ht => hT t' t ht' ht⟩
    obtain ⟨τk, hτk1, hτk2, hτk3⟩ :=
      ((eventually_ge_atTop t₀).and ((eventually_ge_atTop s₀).and hWev)).exists
    let Y : Fin n → ℕ → ℝ := fun i t =>
      β * D + (D - β * D) * ∏ s ∈ Finset.Ico τk t, (1 - alg.α i s ω)
    have hYinit : ∀ i, Y i τk = D := by intro i; simp [Y]
    have hYstep : ∀ i t, τk ≤ t →
        Y i (t + 1) = (1 - alg.α i t ω) * Y i t + alg.α i t ω * β * D := by
      intro i t ht
      simp only [Y]
      rw [Finset.prod_Ico_succ_top ht]
      ring
    have hxi : ∀ t ≥ τk, ∀ i j : Fin n, |alg.xi i t ω j| ≤ D := by
      intro t ht i j
      exact hx _ (hs₀ t (le_trans hτk2 ht) i j) j
    have h8 := lemma8 alg ω β D t₀ τk Y ⟨hβ0, hβ1⟩ hD.le hF hτk1 hx hxi hYinit hYstep
    have hpos : 0 < D - β * D := by nlinarith
    have hprod : ∀ᶠ t in atTop, ∀ i,
        (D - β * D) * ∏ s ∈ Finset.Ico τk t, (1 - alg.α i s ω) ≤ η := by
      refine eventually_all.2 fun i => ?_
      filter_upwards [eventually_prod_small (fun s => alg.α i s ω) (fun s => alg.α_mem i s ω)
        (hdiv i) τk (div_pos hη0 hpos)] with t ht
      have := mul_lt_mul_of_pos_left ht hpos
      rw [mul_div_cancel₀ _ hpos.ne'] at this
      exact this.le
    obtain ⟨t₁, ht₁⟩ := eventually_atTop.1 (hprod.and (eventually_ge_atTop τk))
    refine ⟨t₁, fun t ht j => ?_⟩
    obtain ⟨hp, hτt⟩ := ht₁ t ht
    obtain ⟨hl, hu⟩ := h8 j t hτt
    have hWj := hτk3 j t hτt
    have hYj : Y j t ≤ β * D + η := by simp only [Y]; linarith [hp j]
    rw [abs_le] at hWj ⊢
    constructor
    · linarith [hWj.1]
    · linarith [hWj.2]
  obtain ⟨M, hM⟩ := hbdd
  set D₀ := |M| + 1 with hD₀def
  have hD₀ : 0 < D₀ := by positivity
  have iter : ∀ k : ℕ, ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ j, |alg.x t ω j| ≤ γ ^ k * D₀ := by
    intro k
    induction k with
    | zero => exact ⟨0, fun t _ j => by simp only [pow_zero, one_mul]; linarith [hM t j, le_abs_self M]⟩
    | succ k ih =>
      obtain ⟨t₀, ht₀⟩ := ih
      obtain ⟨t₁, ht₁⟩ := step _ (by positivity) t₀ ht₀
      refine ⟨t₁, fun t ht j => ?_⟩
      have e : γ ^ (k + 1) * D₀ = γ * (γ ^ k * D₀) := by ring
      rw [e]; exact ht₁ t ht j
  rw [tendsto_pi_nhds]
  intro j
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hD₀) hγ1
  obtain ⟨t₀, ht₀⟩ := iter k
  refine ⟨t₀, fun t ht => ?_⟩
  have h1 := ht₀ t ht j
  have h2 : γ ^ k * D₀ < ε := by rwa [lt_div_iff₀ hD₀] at hk
  simp only [Pi.zero_apply, Real.dist_eq, sub_zero]
  linarith

lemma runMax_nonneg {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (t : ℕ) (ω : Ω) :
    0 ≤ alg.runMax t ω := by
  unfold Algorithm.runMax
  exact Real.iSup_nonneg fun s => Real.iSup_nonneg fun j => abs_nonneg _

lemma runMax_le {n : ℕ} {Ω : Type*} (alg : Algorithm n Ω) (t : ℕ) (ω : Ω) (M : ℝ)
    (hM : ∀ t j, |alg.x t ω j| ≤ M) (hM0 : 0 ≤ M) : alg.runMax t ω ≤ M := by
  unfold Algorithm.runMax
  exact Real.iSup_le (fun s => Real.iSup_le (fun j => hM _ j) hM0) hM0

end AsyncSA.Contraction.Thm3Aux

open AsyncSA.Contraction.Thm3Aux in
theorem solution {n : ℕ} {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m₀) (alg : Algorithm n Ω)
    (xstar v : Fin n → ℝ) (β : ℝ)
    (h1 : alg.Assumption1 P) (h2 : alg.Assumption2 P 𝓕)
    (hx : alg.Adapted 𝓕) (h3 : alg.Assumption3 P)
    (h5 : Assumption5 alg.F xstar v β) :
    ∀ᵐ ω ∂P, Tendsto (fun t => alg.x t ω) atTop (𝓝 xstar) := by
  obtain ⟨hv, hβ0, hβ1, hcon⟩ := h5
  have hn := alg.n_pos
  -- Step 1: Assumption 5 implies Assumption 6, so Theorem 1 gives boundedness.
  have h6 : Assumption6 alg.F := by
    refine ⟨v, β, (1 + β) * ‖fun i => xstar i / v i‖, hv, hβ0, hβ1, fun x => ?_⟩
    have hc := hcon x
    rw [wNorm_eq_norm hn _ _ hv, wNorm_eq_norm hn _ _ hv] at hc
    rw [wNorm_eq_norm hn _ _ hv, wNorm_eq_norm hn _ _ hv]
    have e1 : (fun i => alg.F x i / v i) =
        (fun i => (alg.F x - xstar) i / v i) + fun i => xstar i / v i := by
      funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
    have e2 : (fun i => (x - xstar) i / v i) =
        (fun i => x i / v i) - fun i => xstar i / v i := by
      funext i; simp only [Pi.sub_apply]; ring
    rw [e1]
    calc _ ≤ ‖fun i => (alg.F x - xstar) i / v i‖ + ‖fun i => xstar i / v i‖ := norm_add_le _ _
      _ ≤ β * ‖fun i => (x - xstar) i / v i‖ + ‖fun i => xstar i / v i‖ := by linarith
      _ ≤ β * (‖fun i => x i / v i‖ + ‖fun i => xstar i / v i‖) +
            ‖fun i => xstar i / v i‖ := by
          rw [e2]; gcongr; exact norm_sub_le _ _
      _ = _ := by ring
  have hbdd := theorem1 P 𝓕 alg h1 h2 hx h3 h6
  -- Step 2: Lemma 2 for the rescaled noise of every coordinate.
  obtain ⟨cA, cB, hvar⟩ := h2.var_bound
  obtain ⟨C, hC⟩ := h3.sum_sq
  have hrun : ∀ t, Measurable[𝓕 t] (alg.runMax t) := by
    intro t
    unfold Algorithm.runMax
    refine Measurable.iSup fun s => Measurable.iSup fun j => ?_
    exact continuous_abs.measurable.comp
      ((hx s j).mono (𝓕.mono (Nat.lt_succ_iff.mp s.2)) le_rfl)
  have hnoise : ∀ i, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, ∀ t₀ t : ℕ, T ≤ t₀ → t₀ ≤ t →
      |tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω / v i) t₀ t| ≤ δ := by
    intro i
    have hvi := hv i
    refine lemma2 P 𝓕 (alg.α i) (fun t ω => alg.w i t ω / v i)
      (fun t ω => (cA + cB * alg.runMax t ω ^ 2) / v i ^ 2) C
      (fun t => h2.α_meas i t) (fun t => (h2.w_meas i t).div_const _) ?_ ?_ ?_
      (ae_of_all _ fun ω t => alg.α_mem i t ω) (h3.sum_inf i) (hC i) ?_
    · intro t
      exact (measurable_const.add (measurable_const.mul ((hrun t).pow_const 2))).div_const _
    · intro t S hS hfin
      have hfin' : ∫⁻ ω in S, ‖alg.w i t ω‖ₑ ∂P < ⊤ := by
        have e : ∀ ω, ‖alg.w i t ω‖ₑ = ‖alg.w i t ω / v i‖ₑ * ‖v i‖ₑ := by
          intro ω; rw [← enorm_mul, div_mul_cancel₀ _ hvi.ne']
        simp_rw [e]
        rw [lintegral_mul_const' _ _ enorm_ne_top]
        exact ENNReal.mul_lt_top hfin enorm_lt_top
      have := h2.mean_zero i t S hS hfin'
      dsimp only
      rw [integral_div, this, zero_div]
    · intro t
      obtain ⟨hnn, hle⟩ := hvar i t
      refine ⟨?_, fun S hS => ?_⟩
      · filter_upwards [hnn] with ω hω
        exact div_nonneg hω (by positivity)
      · have e1 : ∀ ω, ENNReal.ofReal ((alg.w i t ω / v i) ^ 2) =
            ENNReal.ofReal (alg.w i t ω ^ 2) * ENNReal.ofReal (1 / v i ^ 2) := by
          intro ω; rw [← ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; field_simp
        have e2 : ∀ ω, ENNReal.ofReal ((cA + cB * alg.runMax t ω ^ 2) / v i ^ 2) =
            ENNReal.ofReal (cA + cB * alg.runMax t ω ^ 2) * ENNReal.ofReal (1 / v i ^ 2) := by
          intro ω; rw [← ENNReal.ofReal_mul' (by positivity)]; congr 1; field_simp
        dsimp only
        simp_rw [e1, e2]
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul_of_nonneg_right (hle S hS) zero_le
    · filter_upwards [hbdd] with ω hω
      obtain ⟨M, hM⟩ := hω
      have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨0, hn⟩)
      refine ⟨(|cA| + |cB| * M ^ 2) / v i ^ 2, fun t => ?_⟩
      have hR0 : 0 ≤ alg.runMax t ω := runMax_nonneg alg t ω
      have hRM : alg.runMax t ω ≤ M := runMax_le alg t ω M hM hM0
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < v i ^ 2)]
      gcongr
      calc |cA + cB * alg.runMax t ω ^ 2| ≤ |cA| + |cB * alg.runMax t ω ^ 2| := abs_add_le _ _
        _ = |cA| + |cB| * alg.runMax t ω ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg (alg.runMax t ω))]
        _ ≤ _ := by gcongr
  -- Step 3: combine the almost-sure events and run the pathwise argument.
  have hτall : ∀ᵐ ω ∂P, ∀ i j, Tendsto (fun t => alg.τ i j t ω) atTop atTop :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h1 i j
  have hdivall : ∀ᵐ ω ∂P, ∀ i,
      Tendsto (fun T => ∑ t ∈ Finset.range T, alg.α i t ω) atTop atTop :=
    ae_all_iff.2 fun i => h3.sum_inf i
  have hnoiseall := ae_all_iff.2 hnoise
  filter_upwards [hbdd, hτall, hdivall, hnoiseall] with ω hb hτ hd hN
  have hF' : ∀ y, ‖(scaled alg xstar v hv).F y‖ ≤ β * ‖y‖ := by
    intro y
    have hc := hcon (fun j => v j * y j + xstar j)
    rw [wNorm_eq_norm hn _ _ hv, wNorm_eq_norm hn _ _ hv] at hc
    have e : (fun i => ((fun j => v j * y j + xstar j) - xstar) i / v i) = y := by
      funext i; simp only [Pi.sub_apply]; field_simp [(hv i).ne']; ring
    rw [e] at hc
    exact hc
  have hb' : ∃ M, ∀ t j, |(scaled alg xstar v hv).x t ω j| ≤ M := by
    obtain ⟨M, hM⟩ := hb
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨0, hn⟩)
    refine ⟨∑ j, (M + |xstar j|) / v j, fun t j => ?_⟩
    have hj : |(scaled alg xstar v hv).x t ω j| ≤ (M + |xstar j|) / v j := by
      show |(alg.x t ω j - xstar j) / v j| ≤ _
      rw [abs_div, abs_of_pos (hv j)]
      refine div_le_div_of_nonneg_right ?_ (hv j).le
      have hxj := hM t j
      rw [abs_le]
      constructor <;> linarith [le_abs_self (alg.x t ω j), neg_abs_le (alg.x t ω j),
        le_abs_self (xstar j), neg_abs_le (xstar j)]
    refine le_trans hj ?_
    exact Finset.single_le_sum (f := fun j => (M + |xstar j|) / v j)
      (fun j _ => div_nonneg (by positivity) (hv j).le) (Finset.mem_univ j)
  have hlim := pathwise (scaled alg xstar v hv) ω β ⟨hβ0, hβ1⟩ hF' hb' hτ hd hN
  have hcont : Continuous (fun y : Fin n → ℝ => fun i => v i * y i + xstar i) := by
    fun_prop
  have hc := (hcont.tendsto 0).comp hlim
  have e0 : (fun i => v i * (0 : Fin n → ℝ) i + xstar i) = xstar := by
    funext i; simp
  rw [e0] at hc
  refine hc.congr fun t => ?_
  funext i
  show v i * ((alg.x t ω i - xstar i) / v i) + xstar i = alg.x t ω i
  field_simp [(hv i).ne']
  ring
