-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CadlagExitTime_F000
-- name    : LevyStochCalc_Ito_CadlagExitTime_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:19:19.556845+00:00
-- url     : https://prove2.me/theorems/67d3740e-fda9-4220-867e-9daf4ce7fbb2
-- title:
--   Source declarations: LevyStochCalc.Ito.CadlagExitTime
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CadlagExitTime. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F001
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace LevyStochCalc.Ito.CadlagExitTime
universe u v
section Comparison
variable {Ω : Type u} {σ : Ω → WithTop ℝ} {ω : Ω}
theorem exists_coe_le_of_lt {u : ℝ} (h : ((u : ℝ) : WithTop ℝ) < σ ω) :
    ∃ b : ℝ, u < b ∧ ((b : ℝ) : WithTop ℝ) ≤ σ ω := by
  by_cases htop : σ ω = ⊤
  · exact ⟨u + 1, by linarith, htop ▸ le_top⟩
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp htop
    refine ⟨a, ?_, ha.le⟩
    rw [← ha] at h
    exact_mod_cast h
theorem exists_lt_of_lt_coe {s : ℝ} (h : σ ω < ((s : ℝ) : WithTop ℝ)) :
    ∃ a : ℝ, ((a : ℝ) : WithTop ℝ) = σ ω ∧ a < s := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h)
  refine ⟨a, ha, ?_⟩
  rw [← ha] at h
  exact_mod_cast h
theorem isClosed_setOf_le_coe (σ : Ω → WithTop ℝ) (ω : Ω) :
    IsClosed {u : ℝ | σ ω ≤ ((u : ℝ) : WithTop ℝ)} := by
  by_cases htop : σ ω = ⊤
  · have hset : {u : ℝ | σ ω ≤ ((u : ℝ) : WithTop ℝ)} = (∅ : Set ℝ) := by
      ext u
      simp [htop]
    rw [hset]
    exact isClosed_empty
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp htop
    have hset : {u : ℝ | σ ω ≤ ((u : ℝ) : WithTop ℝ)} = Set.Ici a := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_Ici, ← ha, WithTop.coe_le_coe]
    rw [hset]
    exact isClosed_Ici
end Comparison
section Shift
variable {Ω : Type u} {E : Type v} [NormedAddCommGroup E]
open scoped Classical in
noncomputable def shiftAfter (σ : Ω → WithTop ℝ) (X : ℝ → Ω → E) (c : Ω → E) : Ω → ℝ → E :=
  fun ω s => if σ ω ≤ ((s : ℝ) : WithTop ℝ) then X s ω + c ω else 0
variable {σ : Ω → WithTop ℝ} {X : ℝ → Ω → E} {c : Ω → E} {ω : Ω}
theorem shiftAfter_of_le {s : ℝ} (h : σ ω ≤ ((s : ℝ) : WithTop ℝ)) :
    shiftAfter σ X c ω s = X s ω + c ω := if_pos h
theorem shiftAfter_of_not_le {s : ℝ} (h : ¬σ ω ≤ ((s : ℝ) : WithTop ℝ)) :
    shiftAfter σ X c ω s = 0 := if_neg h
theorem norm_shiftAfter_le {s M : ℝ} (hM : 0 ≤ M) (h : ‖X s ω + c ω‖ ≤ M) :
    ‖shiftAfter σ X c ω s‖ ≤ M := by
  rw [shiftAfter]
  split_ifs
  · exact h
  · simpa using hM
theorem continuousWithinAt_Ici_shiftAfter (hX : Continuous fun s => X s ω) (u : ℝ) :
    ContinuousWithinAt (shiftAfter σ X c ω) (Set.Ici u) u := by
  by_cases hu : σ ω ≤ ((u : ℝ) : WithTop ℝ)
  · have heq : ∀ v ∈ Set.Ici u, shiftAfter σ X c ω v = X v ω + c ω := fun v hv =>
      shiftAfter_of_le (hu.trans (by exact_mod_cast hv))
    exact ContinuousWithinAt.congr (hX.add continuous_const).continuousWithinAt heq
      (heq u Set.self_mem_Ici)
  · obtain ⟨b, hub, hb⟩ := exists_coe_le_of_lt (not_le.mp hu)
    have heq : ∀ᶠ v in 𝓝 u, shiftAfter σ X c ω v = 0 := by
      filter_upwards [eventually_lt_nhds hub] with v hv
      refine shiftAfter_of_not_le fun hcon => ?_
      have hbv : ((b : ℝ) : WithTop ℝ) ≤ ((v : ℝ) : WithTop ℝ) := hb.trans hcon
      have : b ≤ v := by exact_mod_cast hbv
      linarith
    exact ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const
      (heq.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds
theorem isClosed_exitSet_shiftAfter (hX : Continuous fun s => X s ω) {k : ℝ} (hk : 0 < k) :
    IsClosed (Probability.exitSet (shiftAfter σ X c) k ω) := by
  have hset : Probability.exitSet (shiftAfter σ X c) k ω
      = Set.Ici (0 : ℝ) ∩ ({u : ℝ | σ ω ≤ ((u : ℝ) : WithTop ℝ)}
        ∩ {u : ℝ | k ≤ ‖X u ω + c ω‖}) := by
    ext u
    simp only [Probability.exitSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici]
    constructor
    · rintro ⟨hu0, hku⟩
      by_cases hσu : σ ω ≤ ((u : ℝ) : WithTop ℝ)
      · exact ⟨hu0, hσu, by rwa [shiftAfter_of_le hσu] at hku⟩
      · rw [shiftAfter_of_not_le hσu, norm_zero] at hku
        exact absurd hku (not_le.mpr hk)
    · rintro ⟨hu0, hσu, hku⟩
      exact ⟨hu0, by rwa [shiftAfter_of_le hσu]⟩
  rw [hset]
  exact isClosed_Ici.inter ((isClosed_setOf_le_coe σ ω).inter
    (isClosed_le continuous_const (hX.add continuous_const).norm))
theorem exitTime_le_iff_of_isClosed {Y : Ω → ℝ → E} {k : ℝ}
    (hcl : IsClosed (Probability.exitSet Y k ω)) (t : ℝ) :
    Probability.exitTime Y k ω ≤ ((t : ℝ) : WithTop ℝ)
      ↔ ∃ s ∈ Set.Icc (0 : ℝ) t, k ≤ ‖Y ω s‖ := by
  classical
  constructor
  · intro hle
    rw [Probability.exitTime] at hle
    split_ifs at hle with h
    · have hmem : sInf (Probability.exitSet Y k ω) ∈ Probability.exitSet Y k ω :=
        hcl.csInf_mem h (Probability.bddBelow_exitSet Y k ω)
      have hst : sInf (Probability.exitSet Y k ω) ≤ t := by exact_mod_cast hle
      exact ⟨sInf (Probability.exitSet Y k ω), ⟨hmem.1, hst⟩, hmem.2⟩
    · exact absurd hle (by simp)
  · rintro ⟨s, ⟨hs0, hst⟩, hks⟩
    have hne : (Probability.exitSet Y k ω).Nonempty := ⟨s, hs0, hks⟩
    rw [Probability.exitTime, if_pos hne]
    have hle : sInf (Probability.exitSet Y k ω) ≤ t :=
      le_trans (csInf_le (Probability.bddBelow_exitSet Y k ω) ⟨hs0, hks⟩) hst
    exact_mod_cast hle
theorem exists_max_norm_shiftAfter (hX : Continuous fun s => X s ω) {t : ℝ} (ht : 0 ≤ t) :
    ∃ s₀ ∈ Set.Icc (0 : ℝ) t, ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖shiftAfter σ X c ω s‖ ≤ ‖shiftAfter σ X c ω s₀‖ := by
  by_cases hσt : σ ω ≤ ((t : ℝ) : WithTop ℝ)
  · have htop : σ ω ≠ ⊤ := fun h => by rw [h] at hσt; simp at hσt
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp htop
    have hat : a ≤ t := by rw [← ha] at hσt; exact_mod_cast hσt
    have hb0 : (0 : ℝ) ≤ max a 0 := le_max_right _ _
    have hbt : max a 0 ≤ t := max_le hat ht
    obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := max a 0) (b := t)).exists_isMaxOn
      (Set.nonempty_Icc.2 hbt) ((hX.add continuous_const).norm).continuousOn
    have hshift : ∀ u : ℝ, max a 0 ≤ u → shiftAfter σ X c ω u = X u ω + c ω := by
      intro u hu
      refine shiftAfter_of_le ?_
      rw [← ha]
      exact_mod_cast le_trans (le_max_left a 0) hu
    refine ⟨s₀, ⟨le_trans hb0 hs₀.1, hs₀.2⟩, fun s hs => ?_⟩
    by_cases hsb : max a 0 ≤ s
    · rw [hshift s hsb, hshift s₀ hs₀.1]
      exact hmax ⟨hsb, hs.2⟩
    · have hzero : shiftAfter σ X c ω s = 0 := by
        refine shiftAfter_of_not_le fun hcon => ?_
        rw [← ha] at hcon
        exact hsb (max_le (by exact_mod_cast hcon) hs.1)
      rw [hzero, norm_zero]
      exact norm_nonneg _
  · refine ⟨0, ⟨le_rfl, ht⟩, fun s hs => ?_⟩
    have hzero : shiftAfter σ X c ω s = 0 :=
      shiftAfter_of_not_le fun hcon => hσt (hcon.trans (by exact_mod_cast hs.2))
    rw [hzero, norm_zero]
    exact norm_nonneg _
theorem exists_gridPt_norm_gt (hX : Continuous fun s => X s ω) {t : ℝ} (ht : 0 ≤ t) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) t) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ‖shiftAfter σ X c ω s‖ - ε
      < ‖shiftAfter σ X c ω (Probability.gridPt t m)‖ := by
  rcases eq_or_lt_of_le hs.2 with hst | hst
  · obtain ⟨q, hq⟩ := exists_rat_gt t
    refine ⟨Denumerable.eqv ℚ q, ?_⟩
    have hg : Probability.gridPt t (Denumerable.eqv ℚ q) = t := by
      rw [Probability.gridPt, Equiv.symm_apply_apply, min_eq_left hq.le, max_eq_right ht]
    rw [hg, ← hst]
    linarith
  · have hcw : ContinuousWithinAt (fun v => ‖shiftAfter σ X c ω v‖) (Set.Ici s) s :=
      (continuousWithinAt_Ici_shiftAfter hX s).norm
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 hcw ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (by linarith : s < s + δ) hst)
    have hq2' := lt_min_iff.mp hq2
    refine ⟨Denumerable.eqv ℚ q, ?_⟩
    have hg : Probability.gridPt t (Denumerable.eqv ℚ q) = (q : ℝ) := by
      rw [Probability.gridPt, Equiv.symm_apply_apply, min_eq_right hq2'.2.le,
        max_eq_right (le_trans hs.1 hq1.le)]
    rw [hg]
    have hdist : dist ((q : ℝ)) s < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ) - s)]
      linarith [hq2'.1]
    have hclose := hδ' (Set.mem_Ici.2 hq1.le) hdist
    rw [Real.dist_eq] at hclose
    linarith [(abs_lt.mp hclose).1]
theorem exitTime_shiftAfter_le_iff_forall (hX : Continuous fun s => X s ω) {k : ℝ} (hk : 0 < k)
    {t : ℝ} (ht : 0 ≤ t) :
    Probability.exitTime (shiftAfter σ X c) k ω ≤ ((t : ℝ) : WithTop ℝ)
      ↔ ∀ n : ℕ, ∃ m : ℕ,
        k - ((n : ℝ) + 1)⁻¹ < ‖shiftAfter σ X c ω (Probability.gridPt t m)‖ := by
  rw [exitTime_le_iff_of_isClosed (isClosed_exitSet_shiftAfter hX hk)]
  constructor
  · rintro ⟨s, hs, hks⟩ n
    have hε : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    obtain ⟨m, hm⟩ := exists_gridPt_norm_gt hX ht hs hε
    exact ⟨m, lt_of_le_of_lt (sub_le_sub_right hks _) hm⟩
  · intro hall
    obtain ⟨s₀, hs₀, hmax⟩ := exists_max_norm_shiftAfter (σ := σ) (c := c) hX ht
    refine ⟨s₀, hs₀, ?_⟩
    by_contra hcon
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (not_le.mp hcon))
    obtain ⟨m, hm⟩ := hall n
    have hle := hmax _ (Probability.gridPt_mem_Icc ht m)
    rw [one_div] at hn
    exact absurd hn (not_lt.mpr (sub_lt_comm.mp (lt_of_lt_of_le hm hle)).le)
variable {mΩ : MeasurableSpace Ω} [MeasurableSpace E] {ℱ : Filtration ℝ mΩ}
theorem measurable_shiftAfter [MeasurableAdd₂ E] (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hX : ∀ r : ℝ, Measurable[ℱ r] (X r)) (hc : Measurable[hσ.measurableSpace] c) (r : ℝ) :
    Measurable[ℱ r] fun ω => shiftAfter σ X c ω r := by
  classical
  have hset : MeasurableSet[ℱ r] {ω : Ω | σ ω ≤ ((r : ℝ) : WithTop ℝ)} := hσ r
  have hc' : Measurable[ℱ r] fun ω => if σ ω ≤ ((r : ℝ) : WithTop ℝ) then c ω else 0 := by
    intro B hB
    by_cases h0 : (0 : E) ∈ B
    · have hpre : (fun ω => if σ ω ≤ ((r : ℝ) : WithTop ℝ) then c ω else 0) ⁻¹' B
          = (c ⁻¹' B ∩ {ω : Ω | σ ω ≤ ((r : ℝ) : WithTop ℝ)})
            ∪ {ω : Ω | σ ω ≤ ((r : ℝ) : WithTop ℝ)}ᶜ := by
        ext ω
        by_cases hω : σ ω ≤ ((r : ℝ) : WithTop ℝ) <;> simp [hω, h0]
      rw [hpre]
      exact MeasurableSet.union ((hc hB).2 r) (MeasurableSet.compl hset)
    · have hpre : (fun ω => if σ ω ≤ ((r : ℝ) : WithTop ℝ) then c ω else 0) ⁻¹' B
          = c ⁻¹' B ∩ {ω : Ω | σ ω ≤ ((r : ℝ) : WithTop ℝ)} := by
        ext ω
        by_cases hω : σ ω ≤ ((r : ℝ) : WithTop ℝ) <;> simp [hω, h0]
      rw [hpre]
      exact (hc hB).2 r
  have hsplit : (fun ω => shiftAfter σ X c ω r)
      = (fun ω => (if σ ω ≤ ((r : ℝ) : WithTop ℝ) then X r ω else 0)
        + if σ ω ≤ ((r : ℝ) : WithTop ℝ) then c ω else 0) := by
    funext ω
    rw [shiftAfter]
    split_ifs <;> simp
  rw [hsplit]
  exact Measurable.add (Measurable.ite hset (hX r) measurable_const) hc'
variable [OpensMeasurableSpace E]
theorem measurableSet_exitTime_shiftAfter_le
    (hadapt : ∀ r : ℝ, Measurable[ℱ r] fun ω => shiftAfter σ X c ω r)
    (hX : ∀ ω : Ω, Continuous fun s => X s ω) {k : ℝ} (hk : 0 < k) (t : ℝ) :
    MeasurableSet[ℱ t]
      {ω : Ω | Probability.exitTime (shiftAfter σ X c) k ω ≤ ((t : ℝ) : WithTop ℝ)} := by
  rcases lt_or_ge t 0 with ht | ht
  · have hempty : {ω : Ω | Probability.exitTime (shiftAfter σ X c) k ω ≤ ((t : ℝ) : WithTop ℝ)}
        = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      have h0 : ((0 : ℝ) : WithTop ℝ) ≤ ((t : ℝ) : WithTop ℝ) :=
        (Probability.coe_zero_le_exitTime (shiftAfter σ X c) k ω).trans hle
      exact absurd (by exact_mod_cast h0 : (0 : ℝ) ≤ t) (not_le.mpr ht)
    rw [hempty]
    exact @MeasurableSet.empty Ω (ℱ t)
  · have hset : {ω : Ω | Probability.exitTime (shiftAfter σ X c) k ω ≤ ((t : ℝ) : WithTop ℝ)}
        = ⋂ n : ℕ, ⋃ m : ℕ,
          {ω : Ω | k - ((n : ℝ) + 1)⁻¹ < ‖shiftAfter σ X c ω (Probability.gridPt t m)‖} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
      exact exitTime_shiftAfter_le_iff_forall (hX ω) hk ht
    rw [hset]
    have hmeas : ∀ m : ℕ,
        Measurable[ℱ t] fun ω => ‖shiftAfter σ X c ω (Probability.gridPt t m)‖ := by
      intro m
      have hnorm : Measurable[ℱ (Probability.gridPt t m)]
          fun ω => ‖shiftAfter σ X c ω (Probability.gridPt t m)‖ := by
        letI : MeasurableSpace Ω := ℱ (Probability.gridPt t m)
        exact (hadapt (Probability.gridPt t m)).norm
      exact hnorm.mono (ℱ.mono (Probability.gridPt_mem_Icc ht m).2) le_rfl
    letI : MeasurableSpace Ω := ℱ t
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
      measurableSet_lt measurable_const (hmeas m)
theorem isStoppingTime_exitTime_shiftAfter
    (hadapt : ∀ r : ℝ, Measurable[ℱ r] fun ω => shiftAfter σ X c ω r)
    (hX : ∀ ω : Ω, Continuous fun s => X s ω) {k : ℝ} (hk : 0 < k) :
    MeasureTheory.IsStoppingTime ℱ (Probability.exitTime (shiftAfter σ X c) k) := fun t =>
  measurableSet_exitTime_shiftAfter_le hadapt hX hk t
omit [MeasurableSpace E] [OpensMeasurableSpace E] in
theorem le_exitTime_shiftAfter {k T : ℝ}
    (h : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖shiftAfter σ X c ω s‖ < k) :
    ((T : ℝ) : WithTop ℝ) ≤ Probability.exitTime (shiftAfter σ X c) k ω := by
  classical
  rw [Probability.exitTime]
  split_ifs with hne
  · have hT : T ≤ sInf (Probability.exitSet (shiftAfter σ X c) k ω) := by
      refine le_csInf hne fun r hr => ?_
      by_contra hcon
      exact absurd hr.2 (not_le.mpr (h r ⟨hr.1, (not_le.mp hcon).le⟩))
    exact_mod_cast hT
  · exact le_top
omit [MeasurableSpace E] [OpensMeasurableSpace E] in
theorem norm_add_le_of_le_exitTime_shiftAfter (hX : Continuous fun s => X s ω) {k s : ℝ}
    (hs0 : 0 < s) (hσs : σ ω < ((s : ℝ) : WithTop ℝ))
    (hle : ((s : ℝ) : WithTop ℝ) ≤ Probability.exitTime (shiftAfter σ X c) k ω) :
    ‖X s ω + c ω‖ ≤ k := by
  classical
  obtain ⟨a, ha, has⟩ := exists_lt_of_lt_coe hσs
  have hbs : max a 0 < s := max_lt has hs0
  have hnot : ∀ u : ℝ, max a 0 < u → u < s → ‖X u ω + c ω‖ ≤ k := by
    intro u hbu hus
    have hu0 : (0 : ℝ) ≤ u := le_of_lt (lt_of_le_of_lt (le_max_right a 0) hbu)
    have hσu : σ ω ≤ ((u : ℝ) : WithTop ℝ) := by
      rw [← ha]
      exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_left a 0) hbu)
    by_contra hcon
    have hmem : u ∈ Probability.exitSet (shiftAfter σ X c) k ω := by
      refine ⟨hu0, ?_⟩
      rw [shiftAfter_of_le hσu]
      exact (not_le.mp hcon).le
    have hex : Probability.exitTime (shiftAfter σ X c) k ω ≤ ((u : ℝ) : WithTop ℝ) := by
      rw [Probability.exitTime, if_pos ⟨u, hmem⟩]
      exact_mod_cast csInf_le (Probability.bddBelow_exitSet (shiftAfter σ X c) k ω) hmem
    have hsu : ((s : ℝ) : WithTop ℝ) ≤ ((u : ℝ) : WithTop ℝ) := hle.trans hex
    exact absurd (by exact_mod_cast hsu : s ≤ u) (not_le.mpr hus)
  have hlim : Filter.Tendsto (fun u => ‖X u ω + c ω‖) (nhdsWithin s (Set.Iio s))
      (nhds ‖X s ω + c ω‖) :=
    ((hX.add continuous_const).norm.tendsto s).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u in nhdsWithin s (Set.Iio s), ‖X u ω + c ω‖ ≤ k := by
    have hgt : ∀ᶠ u in nhdsWithin s (Set.Iio s), max a 0 < u :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds hbs)
    filter_upwards [hgt, self_mem_nhdsWithin] with u hbu hus
    exact hnot u hbu hus
  exact le_of_tendsto hlim hev
end Shift
section Localise
open LevyStochCalc.Brownian.Ito
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
  {σ τ : Ω → WithTop ℝ} {X : ℝ → Ω → Fin n → ℝ} {c : Ω → Fin n → ℝ}
noncomputable def shiftExitTime (σ : Ω → WithTop ℝ) (X : ℝ → Ω → Fin n → ℝ) (c : Ω → Fin n → ℝ)
    (m : ℕ) : Ω → WithTop ℝ :=
  Probability.exitTime (shiftAfter σ X c) ((m : ℝ) + 1)
variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
theorem isStoppingTime_shiftExitTime
    (hadapt : ∀ r : ℝ, Measurable[ℱ r] fun ω => shiftAfter σ X c ω r)
    (hX : ∀ ω : Ω, Continuous fun s => X s ω) (m : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (shiftExitTime σ X c m) :=
  isStoppingTime_exitTime_shiftAfter hadapt hX (by positivity)
omit [MeasurableSpace Ω] in
theorem le_shiftExitTime_of_mem_boundedPathSet {T : ℝ} {m : ℕ} {ω : Ω}
    (hω : ω ∈ boundedPathSet (fun s ω => X s ω + c ω) T m) :
    ((T : ℝ) : WithTop ℝ) ≤ shiftExitTime σ X c m ω := by
  refine le_exitTime_shiftAfter fun s hs => ?_
  have hle : ‖shiftAfter σ X c ω s‖ ≤ (m : ℝ) :=
    norm_shiftAfter_le (Nat.cast_nonneg m) (hω s hs)
  linarith
omit [MeasurableSpace Ω] in
theorem norm_add_le_of_le_shiftExitTime {m : ℕ} {ω : Ω} (hX : Continuous fun s => X s ω) {s : ℝ}
    (hs0 : 0 < s) (hσs : σ ω < ((s : ℝ) : WithTop ℝ))
    (hle : ((s : ℝ) : WithTop ℝ) ≤ shiftExitTime σ X c m ω) :
    ‖X s ω + c ω‖ ≤ (m : ℝ) + 1 :=
  norm_add_le_of_le_exitTime_shiftAfter hX hs0 hσs hle
theorem coordDeriv_cutoffFun_eq {f : (Fin n → ℝ) → ℝ}
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf : ∀ z, HasFDerivAt f (f' z) z) {m : ℕ}
    {z : Fin n → ℝ} (hz : ‖z‖ ≤ (m : ℝ) + 1) (p : Fin n) :
    coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p z = coordDeriv f' p z := by
  have hk : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlt : ‖z‖ < 3 * ((m : ℝ) + 1) / 2 := by linarith
  rw [coordDeriv, coordDeriv, fderiv_cutoffFun hk hlt, (hf z).fderiv]
theorem stochasticIntegralBrownian_stopped_sub_congr_cutoff (W : Brownian.BrownianMotion P)
    (hℱ : Brownian.IsBrownianFiltration W ℱ) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hXc : ∀ ω : Ω, Continuous fun s => X s ω)
    (hadapt : ∀ r : ℝ, Measurable[ℱ r] fun ω => shiftAfter σ X c ω r)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (m : ℕ) (p : Fin n) (H : Ω → ℝ → ℝ)
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s =>
          coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω) * H ω s) ω s
        - Probability.stopped σ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω) * H ω s) ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ (fun ω s =>
          coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω) * H ω s) ω s
        - Probability.stopped σ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω) * H ω s) ω s)
    (hq₁ : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω) * H ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H ω s) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H ω s) ω s
        - Probability.stopped σ (fun ω s => coordDeriv f' p (X s ω + c ω) * H ω s) ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H ω s) ω s
        - Probability.stopped σ (fun ω s => coordDeriv f' p (X s ω + c ω) * H ω s) ω s)
    (hq₂ : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H ω s) ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ω ∈ boundedPathSet (fun s ω => X s ω + c ω) T m →
      stochasticIntegralBrownian W ℱ hℱ
          (fun ω s =>
            Probability.stopped τ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω) * H ω s) ω s
              - Probability.stopped σ (fun ω s =>
                  coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                    * H ω s) ω s)
          hm₁ hp₁ hq₁ T ω
        = stochasticIntegralBrownian W ℱ hℱ
          (fun ω s =>
            Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H ω s) ω s)
          hm₂ hp₂ hq₂ T ω :=
  JumpFormulaCutoff.stochasticIntegralBrownian_stopped_sub_congr_of_mem W ℱ hℱ
    (isStoppingTime_shiftExitTime hadapt hXc m) hστ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂
    (fun ω s hs0 hsρ hσs _ => by
      rw [coordDeriv_cutoffFun_eq hf
        (norm_add_le_of_le_shiftExitTime (hXc ω) hs0 hσs hsρ) p])
    hT fun _ hω => le_shiftExitTime_of_mem_boundedPathSet hω
theorem stochasticIntegralBrownian_stopped_sub_congr_cutoff_all
    (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (W.W k) ℱ) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hXc : ∀ ω : Ω, Continuous fun s => X s ω)
    (hadapt : ∀ r : ℝ, Measurable[ℱ r] fun ω => shiftAfter σ X c ω r)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hmSc : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSc : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSc : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∀ (m : ℕ) (p : Fin n) (k : Fin d)
      (hmg : Measurable (Function.uncurry fun ω s =>
        Probability.stopped τ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s))
      (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s =>
        Probability.stopped τ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s)
      (hqg : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s
            - Probability.stopped σ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      ∀ᵐ ω ∂P, ω ∈ boundedPathSet (fun s ω => X s ω + c ω) T m →
        stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s =>
              Probability.stopped τ (fun ω s =>
                  coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                    * H p k ω s) ω s
                - Probability.stopped σ (fun ω s =>
                    coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                      * H p k ω s) ω s)
            hmg hpg hqg T ω
          = stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s =>
              Probability.stopped τ
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
            (hmSc p k) (hpSc p k) (hqSc p k) T ω :=
  fun m p k hmg hpg hqg =>
    stochasticIntegralBrownian_stopped_sub_congr_cutoff (W.W k) (hcoord k) hστ hXc hadapt hf m p
      (H p k) hmg hpg hqg (hmSc p k) (hpSc p k) (hqSc p k) hT
end Localise
end LevyStochCalc.Ito.CadlagExitTime


