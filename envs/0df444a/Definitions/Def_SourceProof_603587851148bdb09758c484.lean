-- Prove2me | Definitions.Def_SourceProof_603587851148bdb09758c484
-- name    : SourceProof_603587851148bdb09758c484
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:34:45.829183+00:00
-- url     : https://prove2.me/theorems/6c648a68-e23a-4dce-9774-eddada7bede9
-- title:
--   LevyStochCalc source module: SourceProof_603587851148bdb09758c484
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_of_sdeData` comes from the `LevyStochCalc.Ito.JumpSplittingRemainderVanishing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F000
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F001
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F002
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F004
import Definitions.Def_SourceProof_67ddefea84ca823233581ab0
import Definitions.Def_SourceProof_7eb93313fc9473428879f9ec
import Definitions.Def_SourceProof_939e239754a30a8726cdafe7

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vanishing remainders and the jump of a solution

Along a subsequence of the spanning sets of the intensity the compensated integrals of a finite
family of integrands cut to the complements of those sets vanish uniformly on every bounded
window, by Doob's `L²` maximal inequality against the Itô–Lévy isometry; passing to such a
subsequence in the splitting with remainder, the jump of a jump diffusion across an arrival time
carrying a mark of a spanning set is exactly the jump coefficient read at the left limit there.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma_of_sdeData` — the jump of a
  solution across an arrival time.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, step (II).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Poisson.Compensated

universe u v

section Uniform

open LevyStochCalc.Probability

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Uniform

section Solution

open LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
  {X : Setting.JumpDiffusion W N coeffs x₀}


theorem _root_.Prove2MeSourceProof.h_603587851148bdb09758c484 (S : BigJump.SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i)
    (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable S.ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i))
    (j₀ : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ spanningSets ν j₀) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j₀, g p ∂(N.N ω)
        = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ j : Fin K,
        X.X (θ j) ω
          = leftLimPathAt X.X (θ j) ω + coeffs.γ (θ j) (leftLimPathAt X.X (θ j) ω) (ε j) := by
  classical
  -- the continuous part at every level of the spanning sequence
  have hVex : ∀ k : ℕ, ∃ V : ℝ → Ω → Fin n → ℝ,
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion W S.ℱ S.isBrownian (fun i j ω s => coeffs.σ s (X.X s ω) i j)
        S.σ_meas S.σ_prog S.σ_sq (fun _ => x₀)
        (LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt coeffs ν X.X (spanningSets ν k)) V :=
    fun k => LevyStochCalc.Ito.JumpSplitting.exists_continuousPart S (measure_spanningSets_lt_top ν k).ne hℱ0 hnull0 hμm hμp
      hμq hγmL hγpL hγqL
  choose V hV using hVex
  have hXcad := X.cadlag_paths
  have hXright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X.X s ω) (𝓝[>] t) (𝓝 (X.X t ω)) := by
    filter_upwards [hXcad] with ω hω t ht
    exact (hω t ht).1
  -- the remainders
  set R : ℕ → Fin n → ℝ → Ω → ℝ := fun k i t ω =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
      (LevyStochCalc.Poisson.Compensated.markCut (spanningSets ν k)ᶜ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i)
      (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) (measurableSet_spanningSets ν k).compl)
      ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) (measurableSet_spanningSets ν k).compl)
      (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) (spanningSets ν k)ᶜ T' hT') t ω with hRdef
  have hRl : ∀ k i, ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ L : ℝ,
      Tendsto (fun s => R k i s ω) (𝓝[<] t) (𝓝 L) := fun k i => by
    filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_cadlag N S.ℱ S.isPoisson
      (LevyStochCalc.Poisson.Compensated.markCut (spanningSets ν k)ᶜ fun ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i)
      (LevyStochCalc.Poisson.Compensated.measurable_markCut (hγmL i) (measurableSet_spanningSets ν k).compl)
      ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b (hγpL i)) (measurableSet_spanningSets ν k).compl)
      (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut (hγqL i) (spanningSets ν k)ᶜ T' hT')] with ω hω t
    exact (hω t).2
  -- the jump relation with remainder at every level
  have hjumpk : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ spanningSets ν k) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν k, g p ∂(N.N ω)
        = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ (j : Fin K) (i : Fin n),
        X.X (θ j) ω i
          = LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω i + coeffs.γ (θ j) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω) (ε j) i
            + (R k i (θ j) ω - Function.leftLim (fun s => R k i s ω) (θ j)) := by
    intro k
    refine _root_.Prove2MeSourceProof.h_939e239754a30a8726cdafe7 coeffs N X.X (spanningSets ν k)
      (measurableSet_spanningSets ν k) (measure_spanningSets_lt_top ν k).ne T (V k)
      (Eventually.of_forall (hV k).continuous_path) (R k) ?_ ?_
    · exact MeasureTheory.ae_all_iff.mpr fun i => hRl k i
    · refine _root_.Prove2MeSourceProof.h_7eb93313fc9473428879f9ec coeffs N X.X x₀ S.ℱ
        S.isBrownian S.σ_meas S.σ_prog S.σ_sq S.isPoisson S.γ_meas S.γ_prog S.γ_sq hγmL hγpL
        hγqL X.X hXcad hXright S.sde (measurableSet_spanningSets ν k)
        (measure_spanningSets_lt_top ν k).ne hpredL hμm hμq (V k) ?_ ?_
      · intro t ht
        filter_upwards [(hV k).ae_eq t ht] with ω hω i
        exact congrFun hω i
      · refine Eventually.of_forall fun ω t _ i => ?_
        exact (((continuous_apply i).comp ((hV k).continuous_path ω)).tendsto t).mono_left
          nhdsWithin_le_nhds
  -- the remainders vanish uniformly along a subsequence
  obtain ⟨ks, hks, hunif⟩ :=
    _root_.Prove2MeSourceProof.h_67ddefea84ca823233581ab0 N S.ℱ
      S.isPoisson (fun i ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i) hγmL hγpL hγqL hT
  filter_upwards [LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jumpSumLeftAt_eq_sum coeffs N X.X (spanningSets ν j₀)
    (measurableSet_spanningSets ν j₀) (measure_spanningSets_lt_top ν j₀).ne T,
    MeasureTheory.ae_all_iff.mpr fun m => hjumpk (ks m), hunif,
    MeasureTheory.ae_all_iff.mpr fun m => MeasureTheory.ae_all_iff.mpr fun i => hRl (ks m) i]
    with ω hA hjω hu hRω
  obtain ⟨K, θ, ε, hmono, hmem, hg, -⟩ := hA
  refine ⟨K, θ, ε, hmono, hmem, hg, fun j => ?_⟩
  funext i
  simp only [Pi.add_apply]
  -- the discrepancy is bounded by twice any positive bound
  have hkey : ∀ δ : ℝ, 0 < δ →
      |X.X (θ j) ω i - (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω i
        + coeffs.γ (θ j) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω) (ε j) i)| ≤ 2 * δ := by
    intro δ hδ
    obtain ⟨m, hmδ, hmj⟩ := ((hu δ hδ).and (eventually_ge_atTop j₀)).exists
    have hsub : spanningSets ν j₀ ⊆ spanningSets ν (ks m) :=
      monotone_spanningSets ν (hmj.trans (hks m))
    obtain ⟨K', θ', ε', -, hmem', hg', hrel⟩ := hjω m
    -- the arrival is among the arrivals of the larger set
    obtain ⟨j', hj'⟩ : ∃ j' : Fin K', (θ' j', ε' j') = (θ j, ε j) := by
      set g : ℝ × E → ℝ := fun q => if q = (θ j, ε j) then 1 else 0 with hgdef
      have h1 : ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (ks m), g q ∂(N.N ω)
          = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j₀, g q ∂(N.N ω) := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (measurableSet_Ioc.prod (measurableSet_spanningSets ν _))
          (Set.prod_mono_right hsub) fun q hq => ?_
        have hne : q ≠ (θ j, ε j) := fun h => hq.2 (h ▸ ⟨(hmem j).1, (hmem j).2⟩)
        simp [hgdef, hne]
      have h2 : ∑ j' : Fin K', g (θ' j', ε' j') = ∑ j'' : Fin K, g (θ j'', ε j'') := by
        rw [← hg', ← hg, h1]
      have hpos : (0 : ℝ) < ∑ j'' : Fin K, g (θ j'', ε j'') := by
        refine lt_of_lt_of_le zero_lt_one ?_
        have hgj : g (θ j, ε j) = 1 := by simp [hgdef]
        calc (1 : ℝ) = g (θ j, ε j) := hgj.symm
          _ ≤ ∑ j'' : Fin K, g (θ j'', ε j'') :=
            Finset.single_le_sum (f := fun j'' => g (θ j'', ε j''))
              (fun j'' _ => by
                simp only [hgdef]
                split_ifs <;> norm_num) (Finset.mem_univ j)
      rw [← h2] at hpos
      obtain ⟨j', -, hj'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
      refine ⟨j', ?_⟩
      by_contra hne
      simp [hgdef, hne] at hj'
    have hθ : θ' j' = θ j := congrArg Prod.fst hj'
    have hε : ε' j' = ε j := congrArg Prod.snd hj'
    have hrel' := hrel j' i
    rw [hθ, hε] at hrel'
    have hbR : |R (ks m) i (θ j) ω| < δ :=
      hmδ i (θ j) ⟨(hmem j).1.1.le, (hmem j).1.2⟩
    have hbL : |Function.leftLim (fun s => R (ks m) i s ω) (θ j)| ≤ δ := by
      obtain ⟨L, hL⟩ := hRω m i (θ j)
      rw [leftLim_eq_of_tendsto hL]
      refine le_of_tendsto hL.abs ?_
      filter_upwards [Ioo_mem_nhdsLT (hmem j).1.1] with s hs
      exact (hmδ i s ⟨hs.1.le, hs.2.le.trans (hmem j).1.2⟩).le
    rw [hrel']
    calc |LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω i + coeffs.γ (θ j) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω) (ε j) i
          + (R (ks m) i (θ j) ω - Function.leftLim (fun s => R (ks m) i s ω) (θ j))
          - (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω i
            + coeffs.γ (θ j) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω) (ε j) i)|
        = |R (ks m) i (θ j) ω - Function.leftLim (fun s => R (ks m) i s ω) (θ j)| := by
          congr 1
          ring
      _ ≤ |R (ks m) i (θ j) ω| + |Function.leftLim (fun s => R (ks m) i s ω) (θ j)| :=
          abs_sub _ _
      _ ≤ δ + δ := add_le_add hbR.le hbL
      _ = 2 * δ := by ring
  have hc : |X.X (θ j) ω i - (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω i
      + coeffs.γ (θ j) (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X (θ j) ω) (ε j) i)| ≤ 0 := by
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    calc _ ≤ 2 * (δ / 4) := hkey (δ / 4) (by positivity)
      _ < 0 + δ := by linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hc (abs_nonneg _)))
end Solution

end LevyStochCalc.Ito.JumpSplitting


