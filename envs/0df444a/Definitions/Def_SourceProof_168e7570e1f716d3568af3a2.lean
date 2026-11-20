-- Prove2me | Definitions.Def_SourceProof_168e7570e1f716d3568af3a2
-- name    : SourceProof_168e7570e1f716d3568af3a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:45:26.051228+00:00
-- url     : https://prove2.me/theorems/31cc561c-8773-4722-af34-082a5a60c3e6
-- title:
--   LevyStochCalc source module: SourceProof_168e7570e1f716d3568af3a2
-- statement:
--   The original source theorem `ProbabilityTheory.countable_not_rightLimWithin_ae_eq` comes from the `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F000

/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rohit Manokaran, Rémy Degenne
-/

/-! # Cadlag modification of quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section CountableEvents

variable [OrderBot ι] {T : Set ι} {t : ι}

end CountableEvents

section RegularitySet

variable [OrderBot ι]

variable [TopologicalSpace ι] [OrderTopology ι]

end RegularitySet

variable [TopologicalSpace ι] [OrderBot ι] [OrderTopology ι]
  --[FirstCountableTopology ι] -- required for ∀ t : ι, (𝓝[>] t).IsCountablyGenerated
  [DenselyOrdered ι] [NoMaxOrder ι] -- required for ∀ t : ι, (𝓝[>] t).NeBot)

/-! ### Pathwise regularization

For a fixed path `h : ι → ℝ` admitting one-sided limits along a dense set `T`, the right-limit
regularization `r` is right-continuous and inherits the left limits of `h`. -/

section PathRegularization

variable {T : Set ι} {h r : ι → ℝ} {x : ι}

end PathRegularization

/-! ### Uncountable sets accumulate from the right -/

section Accumulation

end Accumulation

open Function


theorem _root_.Prove2MeSourceProof.h_168e7570e1f716d3568af3a2 [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hTc : T.Countable) (hTd : Dense T) :
    {t | ¬ (fun ω ↦ rightLimWithin (X · ω) T t) =ᵐ[μ] X t}.Countable := by
  -- every dense set is cofinal
  have hcof : ∀ T : Set ι, Dense T → ∀ x : ι, ∃ d ∈ T, x < d := fun T hTd x ↦ hTd.exists_gt x
  -- the right-limit value along `T`, by choice
  let R T' x ω : ℝ := Function.rightLimWithin (X · ω) T' x
  have hRspec T' x ω (h : ∃ l, Tendsto (X · ω) (𝓝[T' ∩ Set.Ioi x] x) (𝓝 l)) :
      Tendsto (X · ω) (𝓝[T' ∩ Set.Ioi x] x) (𝓝 (R T' x ω)) := by
    rw [Set.inter_comm] at h ⊢
    exact tendsto_rightLimWithin_of_tendsto h
  -- Stage 1: a.e. one-sided limits along D₀
  have hae₀ := ProbabilityTheory.ae_right_limit hX hTc (hcof T hTd)
  -- Stage 2: measurable versions of `R D₀ x`
  have hRm : ∀ x : ι, ∃ g : Ω → ℝ, Measurable g ∧ g =ᵐ[μ] R T x := by
    intro x
    have hne : (𝓝[T ∩ Set.Ioi x] x).NeBot := by
      rw [Set.inter_comm]; exact nhdsWithin_Ioi_inter_neBot hTd x
    obtain ⟨v, hv⟩ := exists_seq_tendsto (𝓝[T ∩ Set.Ioi x] x)
    have haet : ∀ᵐ ω ∂μ, Tendsto (fun j ↦ X (v j) ω) atTop (𝓝 (R T x ω)) := by
      filter_upwards [hae₀] with ω hω
      exact (hRspec T x ω (hω x)).comp hv
    obtain ⟨g, hgmeas, hgae⟩ := measurable_limit_of_tendsto_metrizable_ae
      (f := fun j ↦ X (v j)) (L := atTop) (fun j ↦ (hX.measurable (v j)).aemeasurable)
      (by filter_upwards [haet] with ω hω using ⟨_, hω⟩)
    refine ⟨g, hgmeas, ?_⟩
    filter_upwards [haet, hgae] with ω h1 h2
    exact tendsto_nhds_unique h2 h1
  choose Rm hRmMeas hRmae using hRm
  -- Stage 3: the set of points where `R D₀ x` and `X x` disagree is countable
  let Sset : Set ι := {x | ¬ R T x =ᵐ[μ] X x}
  change Sset.Countable
  by_contra hSunc
  set Sn : ℕ → Set ι := fun n ↦
    {x | ENNReal.ofReal (1 / (n + 1)) < μ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}} with hSn
  have hSsub : Sset ⊆ ⋃ n, Sn n := by
    intro x hx
    have hxm : ¬ Rm x =ᵐ[μ] X x := fun hcon ↦ hx ((hRmae x).symm.trans hcon)
    have hpos : μ {ω | Rm x ω ≠ X x ω} ≠ 0 := hxm
    have hBmono : Monotone (fun n : ℕ ↦ {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|}) := by
      intro n n' hnn' ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hω
      have : (n : ℝ) ≤ (n' : ℝ) := mod_cast hnn'
      gcongr
    have hBunion : {ω | Rm x ω ≠ X x ω} = ⋃ n : ℕ, {ω | 1 / (n + 1 : ℝ) < |Rm x ω - X x ω|} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hne
        have habs : 0 < |Rm x ω - X x ω| := abs_pos.2 (sub_ne_zero.2 hne)
        exact exists_nat_one_div_lt habs
      · rintro ⟨n, hn⟩ hcon
        rw [hcon, sub_self, abs_zero] at hn
        exact absurd hn (not_lt.2 (by positivity))
    have hexn : ∃ n₀ : ℕ, 0 < μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by
      by_contra! hcon
      simp only [nonpos_iff_eq_zero] at hcon
      refine hpos ?_
      rw [hBunion]
      refine le_antisymm ((measure_iUnion_le _).trans ?_) zero_le
      simp only [hcon, tsum_zero, Std.le_refl]
    obtain ⟨n₀, hn₀⟩ := hexn
    have hfin : μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} ≠ ⊤ := measure_ne_top μ _
    let ε : ℝ := (μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}).toReal
    have hεpos : 0 < ε := ENNReal.toReal_pos hn₀.ne' hfin
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hεpos
    let n := max n₀ n₁
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    rw [hSn]
    have hsub2 : {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|}
        ⊆ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} :=
      hBmono (le_max_left n₀ n₁)
    calc ENNReal.ofReal (1 / (n + 1))
        ≤ ENNReal.ofReal (1 / (n₁ + 1)) := by
          refine ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le (by positivity) ?_)
          gcongr
          exact mod_cast le_max_right n₀ n₁
      _ < ENNReal.ofReal ε := ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.2 hn₁
      _ = μ {ω | 1 / ((n₀ : ℝ) + 1) < |Rm x ω - X x ω|} := by rw [ENNReal.ofReal_toReal hfin]
      _ ≤ μ {ω | 1 / ((n : ℝ) + 1) < |Rm x ω - X x ω|} := measure_mono hsub2
  have hexSn : ∃ n, ¬ (Sn n).Countable := by
    by_contra! hcon
    exact hSunc ((Set.countable_iUnion hcon).mono hSsub)
  obtain ⟨n, hSnunc⟩ := hexSn
  obtain ⟨p, u, huSn, hup, hutend⟩ := ProbabilityTheory.exists_seq_gt_tendsto_of_not_countable hSnunc
  set T' : Set ι := T ∪ (Set.range u ∪ {p}) with hT'
  have hT'c : T'.Countable :=
    hTc.union ((Set.countable_range u).union (Set.countable_singleton p))
  have hT'd : Dense T' := hTd.mono Set.subset_union_left
  have haediff : ∀ᵐ ω ∂μ, Tendsto (fun k ↦ Rm (u k) ω - X (u k) ω) atTop (𝓝 0) := by
    have hcnt : ∀ᵐ ω ∂μ, ∀ k, Rm (u k) ω = R T (u k) ω := ae_all_iff.2 fun k ↦ hRmae (u k)
    filter_upwards [hae₀, ProbabilityTheory.ae_right_limit hX hT'c (hcof T' hT'd), hcnt] with ω hω₀ hω' hkeq
    have hL' := hRspec T' p ω (hω' p)
    have hXu : Tendsto (fun k ↦ X (u k) ω) atTop (𝓝 (R T' p ω)) := by
      refine hL'.comp ?_
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hutend, Filter.Eventually.of_forall fun k ↦ by grind⟩
    have hRu : Tendsto (fun k ↦ R T (u k) ω) atTop (𝓝 (R T' p ω)) :=
      ProbabilityTheory.tendsto_rightLim_comp_of_gt hTd Set.subset_union_left
        (fun y ↦ hRspec T y ω (hω₀ y)) hup hutend hL'
    have hsub := hRu.sub hXu
    rw [sub_self] at hsub
    refine Tendsto.congr (fun k ↦ ?_) hsub
    rw [hkeq k]
  have htim : TendstoInMeasure μ (fun k ω ↦ Rm (u k) ω - X (u k) ω) atTop
      (fun _ ↦ (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun k ↦ ((hRmMeas (u k)).sub (hX.measurable (u k))).aestronglyMeasurable) ?_
    filter_upwards [haediff] with ω hω using hω
  have hcontra := htim (ENNReal.ofReal (1 / (n + 1 : ℝ)))
    (by rw [ENNReal.ofReal_pos]; positivity)
  have hev : ∀ᶠ k in atTop,
      μ {ω | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ edist (Rm (u k) ω - X (u k) ω) 0}
        < ENNReal.ofReal (1 / (n + 1)) := by
    refine hcontra.eventually_lt_const ?_
    positivity
  obtain ⟨k, hk⟩ := hev.exists
  have hmem := huSn k
  rw [hSn, Set.mem_setOf_eq] at hmem
  have hsub3 : {ω | 1 / (n + 1 : ℝ) < |Rm (u k) ω - X (u k) ω|}
      ⊆ {ω | ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ edist (Rm (u k) ω - X (u k) ω) 0} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω ⊢
    rw [edist_dist, dist_zero_right, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal hω.le
  exact lt_irrefl _ ((hmem.trans_le (measure_mono hsub3)).trans hk)
/-! ## Right-continuous modification of a quasimartingale

For a real quasimartingale `X` we define a process `rightContModif X` with the following properties:
* `rightContModif X` is right-continuous
* `rightContModif X` has left limits almost everywhere
* for all `t` outside a countable set, `rightContModif X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `rightContModif X` is a modification of `X`.
* if the filtration is right-continuous, then `rightContModif X` is adapted.

Note that if `X` is not right-continuous in probability, we can still obtain a modification by
changing the value of `rightContModif X` on a countable set of times, with the drawback that the
right-continuity then holds only outside that countable set.

-/

/-! ## Càdlàg modification of a quasimartingale

For a real quasimartingale `X` we define a process `cadlagModif X` with the following properties:
* `cadlagModif X` is càdlàg
* for all `t` outside a countable set, `cadlagModif X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `cadlagModif X` is a modification of `X`.
* if the filtration is right-continuous and complete, then `cadlagModif X` is adapted.

TODO: if `t ↦ μ[X t]` is right-continuous (in particular if `X` is a martingale),
then `cadlagModif X` is a modification of `X` without the assumption that `X`
is right-continuous in probability.

-/

end ProbabilityTheory


