-- Prove2me | solution 1 for AddictivePlatforms.Compete.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:03:20.373338+00:00
-- url     : https://prove2.me/submissions/d9623e82-d5ab-431e-bfc2-7e23478ba7a4

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model
import Theorems.Thm_AddictivePlatforms_Compete_proposition_2_existence
import Theorems.Thm_AddictivePlatforms_Compete_proposition_2_step_1
import Theorems.Thm_AddictivePlatforms_Compete_lemma_B_4

open Set Filter Topology AddictivePlatforms.Compete
open scoped ENNReal

section Helpers

private lemma u_contOn_a (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {d : ℝ} (hd : 0 ≤ d) : ContinuousOn (fun a => u a d) (Ici 0) :=
  hS.assumption1.differentiableOn.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ha => ⟨ha, hd⟩)

private lemma u_contOn_d (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {a : ℝ} (ha : 0 ≤ a) : ContinuousOn (fun d => u a d) (Ici 0) :=
  hS.assumption1.differentiableOn.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hd => ⟨ha, hd⟩)

private lemma u_diffOn_a (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {d : ℝ} (hd : 0 ≤ d) : DifferentiableOn ℝ (fun a => u a d) (Ici 0) :=
  hS.assumption1.differentiableOn.comp
    (differentiable_id.prodMk (differentiable_const d)).differentiableOn
    (fun _ ha => ⟨ha, hd⟩)

private lemma u_hasDerivAt_a (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    HasDerivAt (fun x => u x d) (u1 u a d) a :=
  ((u_diffOn_a u C hS hd a ha.le).hasDerivWithinAt).hasDerivAt (Ici_mem_nhds ha)

private lemma C_hasDerivAt (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {a : ℝ} (ha : 0 < a) :
    HasDerivAt C (Cderiv C a) a :=
  ((hS.assumption2.differentiableOn a ha.le).hasDerivWithinAt).hasDerivAt (Ici_mem_nhds ha)

private lemma utility_diff_strictMono (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    StrictMonoOn (fun a => u a y - u a x) (Ici 0) := by
  have hy : 0 ≤ y := hx.trans hxy.le
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
    ((u_contOn_a u C hS hy).sub (u_contOn_a u C hS hx))
    (f' := fun a => u1 u a y - u1 u a x)
  · intro a ha
    have ha' : 0 < a := by simpa only [interior_Ici, mem_Ioi] using ha
    exact ((u_hasDerivAt_a u C hS ha' hy).sub (u_hasDerivAt_a u C hS ha' hx)).hasDerivWithinAt
  · intro a ha
    have ha' : 0 ≤ a := (show 0 < a by simpa only [interior_Ici, mem_Ioi] using ha).le
    exact sub_pos.mpr (hS.assumption1.strictMonoOn_u1 a ha' hx hy hxy)

private lemma exists_pos_gain_at_zero (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {Abar : ℝ≥0∞} (hAbar : 0 < Abar) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ Abar ∧ u 0 0 < u ε 0 - C ε := by
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < u1 u a 0 - Cderiv C a := by
    rcases hS.assumption2.limit_pos with ⟨L, hL, ht⟩ | ht
    · exact ht.eventually (Ioi_mem_nhds hL)
    · exact ht.eventually (eventually_gt_atTop 0)
  obtain ⟨δ, hδ, hδ_pos⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  obtain ⟨ε, hε_pos, hε_lt, hε_cap⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ENNReal.ofReal ε ≤ Abar := by
    by_cases htop : Abar = ⊤
    · refine ⟨δ / 2, half_pos hδ, half_lt_self hδ, ?_⟩
      simp [htop]
    · have hApos : 0 < Abar.toReal := ENNReal.toReal_pos hAbar.ne' htop
      refine ⟨min (δ / 2) Abar.toReal, lt_min (half_pos hδ) hApos,
        (min_le_left _ _).trans_lt (half_lt_self hδ), ?_⟩
      calc ENNReal.ofReal (min (δ / 2) Abar.toReal)
          ≤ ENNReal.ofReal Abar.toReal := ENNReal.ofReal_le_ofReal (min_le_right _ _)
        _ = Abar := ENNReal.ofReal_toReal htop
  have hmono : StrictMonoOn (fun a => u a 0 - C a) (Icc 0 ε) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 ε)
      (((u_contOn_a u C hS le_rfl).sub hS.assumption2.differentiableOn.continuousOn).mono
        Icc_subset_Ici_self)
      (f' := fun a => u1 u a 0 - Cderiv C a)
    · intro a ha
      rw [interior_Icc] at ha
      exact ((u_hasDerivAt_a u C hS ha.1 le_rfl).sub (C_hasDerivAt u C hS ha.1)).hasDerivWithinAt
    · intro a ha
      rw [interior_Icc] at ha
      apply hδ_pos
      · rw [Real.dist_eq, sub_zero, abs_of_pos ha.1]
        exact ha.2.trans hε_lt
      · exact ha.1
  have hlt := hmono ⟨le_rfl, hε_pos.le⟩ ⟨hε_pos.le, le_rfl⟩ hε_pos
  dsimp only at hlt
  rw [hS.C_zero, sub_zero] at hlt
  exact ⟨ε, hε_pos, hε_cap, hlt⟩

private lemma not_eq3_zero (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} (hK : 2 ≤ K) {Abar : ℝ≥0∞} (hAbar : 0 < Abar) :
    ¬ Eq3 u C Abar K 0 := by
  rintro ⟨AK, AK1, hAK, hAK1, heq⟩
  obtain ⟨ε, hε_pos, hε_cap, hε_gain⟩ := exists_pos_gain_at_zero u C hS hAbar
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  set y : ℝ := (K : ℝ) - 1
  have hy1 : (1 : ℝ) ≤ y := by
    have : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hypos : 0 < y := by linarith
  have hAK1_pos : 0 < AK1 := by
    have hw1 : 0 ≤ 1 / y := by positivity
    have hw2 : 0 ≤ 1 - 1 / y := by
      rw [sub_nonneg, div_le_one hypos]
      exact hy1
    have hconc := (hS.assumption1.concaveOn_a 0 le_rfl).2
      (show ε ∈ Ici (0 : ℝ) from hε_pos.le) (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
      hw1 hw2 (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero] at hconc
    have hmul : y * ((1 / y) * u ε 0 + (1 - 1 / y) * u 0 0) ≤ y * u (1 / y * ε) 0 :=
      mul_le_mul_of_nonneg_left hconc hypos.le
    have hsimp1 : y * ((1 / y) * u ε 0 + (1 - 1 / y) * u 0 0) = u ε 0 + (y - 1) * u 0 0 := by
      field_simp
    have hsimp2 : (1 / y) * ε = ε / y := by ring
    rw [hsimp1, hsimp2] at hmul
    have h0_lt : perspObj u C y 0 0 < perspObj u C y 0 ε := by
      unfold perspObj
      rw [zero_div, hS.C_zero, sub_zero]
      linarith
    have hle := hAK1.2.2 ε hε_pos.le hε_cap
    rcases hAK1.1.eq_or_lt with h0 | hpos
    · rw [← h0] at hle
      linarith
    · exact hpos
  have hne : AK1 / y ≠ 0 := (div_pos hAK1_pos hypos).ne'
  have hsc := (hS.strictConcaveOn_a 0 le_rfl).2
    (show AK1 / y ∈ Ici (0 : ℝ) from (div_pos hAK1_pos hypos).le)
    (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
    hne (div_pos hypos hKpos) (div_pos one_pos hKpos) (by field_simp [y]; ring)
  simp only [smul_eq_mul, mul_zero, add_zero] at hsc
  have harg : y / (K : ℝ) * (AK1 / y) = AK1 / (K : ℝ) := by field_simp [hypos.ne', hKpos.ne']
  rw [harg] at hsc
  have hmul := mul_lt_mul_of_pos_left hsc hKpos
  have hlhs : (K : ℝ) * (y / (K : ℝ) * u (AK1 / y) 0 + 1 / (K : ℝ) * u 0 0) =
      y * u (AK1 / y) 0 + u 0 0 := by field_simp [hKpos.ne']
  rw [hlhs] at hmul
  have hu00 : 0 ≤ u 0 0 := hS.assumption1.u_zero_zero_nonneg
  have hlt_persp : perspObj u C y 0 AK1 < perspObj u C (K : ℝ) 0 AK1 := by
    unfold perspObj
    linarith
  have hle_AK : perspObj u C (K : ℝ) 0 AK1 ≤ perspObj u C (K : ℝ) 0 AK :=
    hAK.2.2 AK1 hAK1.1 hAK1.2.1
  linarith

private lemma exists_max_on_set {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k)
    (J : Finset (Fin K)) :
    ∃ a : Fin K → ℝ, Feasible Abar (J, a) ∧
      ∀ a' : Fin K → ℝ, Feasible Abar (J, a') → payoff u C d (J, a') ≤ payoff u C d (J, a) := by
  by_cases hJ : J = ∅
  · subst hJ
    refine ⟨fun _ => 0, ⟨fun _ hk => by simp at hk, by simp⟩, fun a' _ => ?_⟩
    simp [payoff]
  · have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
    by_cases htop : Abar = ⊤
    · obtain ⟨a, ha_nn, ha_max⟩ := hE d hd J hJne
      refine ⟨a, ⟨ha_nn, by simp [htop]⟩, fun a' ha' => ha_max a' ha'.1⟩
    · set R : ℝ := Abar.toReal
      have hR : 0 ≤ R := ENNReal.toReal_nonneg
      let Sset : Set (Fin K → ℝ) :=
        (Set.pi Set.univ (fun _ : Fin K => Icc (0 : ℝ) R)) ∩ {a | ∑ k ∈ J, a k ≤ R}
      have hcomp : IsCompact Sset :=
        (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
          (isClosed_le (continuous_finsetSum J fun k _ => continuous_apply k) continuous_const)
      have hne_S : Sset.Nonempty := ⟨fun _ => 0, ⟨fun _ _ => ⟨le_rfl, hR⟩, by simp [hR]⟩⟩
      have hcont : ContinuousOn (fun a : Fin K → ℝ => payoff u C d (J, a)) Sset := by
        have h1 : ContinuousOn (fun a : Fin K → ℝ => ∑ k ∈ J, u (a k) (d k) - C (∑ k ∈ J, a k)) Sset := by
          apply ContinuousOn.sub
          · refine continuousOn_finsetSum J fun k _ => ?_
            exact (u_contOn_a u C hS (hd k)).comp (continuous_apply k).continuousOn
              (fun a ha => ha.1 k (mem_univ k) |>.1)
          · refine hS.assumption2.differentiableOn.continuousOn.comp
              (continuous_finsetSum J fun k _ => continuous_apply k).continuousOn ?_
            intro a ha
            exact Finset.sum_nonneg fun k _ => (ha.1 k (mem_univ k)).1
        refine h1.congr fun a _ => ?_
        simp [payoff, hJ]
      obtain ⟨a, haS, haMax⟩ := hcomp.exists_isMaxOn hne_S hcont
      have hfeas_a : Feasible Abar (J, a) := by
        refine ⟨fun k _ => (haS.1 k (mem_univ k)).1, ?_⟩
        calc ENNReal.ofReal (∑ k ∈ J, a k)
            ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal haS.2
          _ = Abar := ENNReal.ofReal_toReal htop
      refine ⟨a, hfeas_a, fun a' ha' => ?_⟩
      let a'' : Fin K → ℝ := fun k => if k ∈ J then a' k else 0
      have hsum_eq : ∑ k ∈ J, a'' k = ∑ k ∈ J, a' k :=
        Finset.sum_congr rfl fun k hk => if_pos hk
      have hsum_le : ∑ k ∈ J, a' k ≤ R :=
        (ENNReal.ofReal_le_iff_le_toReal htop).mp ha'.2
      have ha''S : a'' ∈ Sset := by
        refine ⟨fun k _ => ?_, by simp only [Set.mem_ofPred_eq, hsum_eq]; exact hsum_le⟩
        by_cases hk : k ∈ J
        · simp only [a'', if_pos hk, mem_Icc]
          exact ⟨ha'.1 k hk, (Finset.single_le_sum (fun j hj => ha'.1 j hj) hk).trans hsum_le⟩
        · simp only [a'', if_neg hk, mem_Icc]
          exact ⟨le_rfl, hR⟩
      have hpay_eq : payoff u C d (J, a'') = payoff u C d (J, a') := by
        simp only [payoff, if_neg hJ, hsum_eq]
        congr 1
        exact Finset.sum_congr rfl fun k hk => by simp [a'', hk]
      rw [← hpay_eq]
      exact haMax ha''S

private lemma exists_b4_max_finite {K : ℕ} [NeZero K] (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (hS : Standing u C) {Abar : ℝ≥0∞} (hfin : Abar ≠ ⊤)
    (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k) (y : ℝ) (S : Finset (Fin K)) :
    ∃ a : Fin K → ℝ, IsB4Max u C Abar d y S a := by
  set R : ℝ := Abar.toReal
  have hR : 0 ≤ R := ENNReal.toReal_nonneg
  let Sset : Set (Fin K → ℝ) :=
    (Set.pi Set.univ (fun _ : Fin K => Icc (0 : ℝ) R)) ∩ {a | ∑ k ∈ insert 0 S, a k ≤ R}
  have hcomp : IsCompact Sset :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      (isClosed_le (continuous_finsetSum (insert 0 S) fun k _ => continuous_apply k) continuous_const)
  have hne_S : Sset.Nonempty := ⟨fun _ => 0, ⟨fun _ _ => ⟨le_rfl, hR⟩, by simp [hR]⟩⟩
  have hcont : ContinuousOn (fun a : Fin K → ℝ => objB4 u C d y S a) Sset := by
    unfold objB4
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · refine continuousOn_finsetSum S fun k _ => ?_
        exact (u_contOn_a u C hS (hd k)).comp (continuous_apply k).continuousOn
          (fun a ha => (ha.1 k (mem_univ k)).1)
      · exact continuousOn_const.mul ((u_contOn_a u C hS (hd 0)).comp
          (continuous_apply 0).continuousOn (fun a ha => (ha.1 0 (mem_univ 0)).1))
    · refine hS.assumption2.differentiableOn.continuousOn.comp
        (continuous_finsetSum (insert 0 S) fun k _ => continuous_apply k).continuousOn ?_
      intro a ha
      exact Finset.sum_nonneg fun k _ => (ha.1 k (mem_univ k)).1
  obtain ⟨a, haS, haMax⟩ := hcomp.exists_isMaxOn hne_S hcont
  refine ⟨a, fun k _ => (haS.1 k (mem_univ k)).1, ?_, fun a' ha'_nn ha'_cap => ?_⟩
  · calc ENNReal.ofReal (∑ k ∈ insert 0 S, a k)
        ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal haS.2
      _ = Abar := ENNReal.ofReal_toReal hfin
  · let a'' : Fin K → ℝ := fun k => if k ∈ insert 0 S then a' k else 0
    have hsum_eq : ∑ k ∈ insert 0 S, a'' k = ∑ k ∈ insert 0 S, a' k :=
      Finset.sum_congr rfl fun k hk => if_pos hk
    have hsum_le : ∑ k ∈ insert 0 S, a' k ≤ R :=
      (ENNReal.ofReal_le_iff_le_toReal hfin).mp ha'_cap
    have ha''S : a'' ∈ Sset := by
      refine ⟨fun k _ => ?_, by simp only [Set.mem_ofPred_eq, hsum_eq]; exact hsum_le⟩
      by_cases hk : k ∈ insert 0 S
      · simp only [a'', if_pos hk, mem_Icc]
        exact ⟨ha'_nn k hk, (Finset.single_le_sum (fun j hj => ha'_nn j hj) hk).trans hsum_le⟩
      · simp only [a'', if_neg hk, mem_Icc]
        exact ⟨le_rfl, hR⟩
    have hobj_eq : objB4 u C d y S a'' = objB4 u C d y S a' := by
      unfold objB4
      rw [hsum_eq]
      have h0 : a'' 0 = a' 0 := if_pos (Finset.mem_insert_self 0 S)
      rw [h0]
      congr 2
      exact Finset.sum_congr rfl fun k hk => by simp [a'', hk]
    rw [← hobj_eq]
    exact haMax ha''S

private lemma exists_max_excluding {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k) (k : Fin K) :
    ∃ x : Choice K, k ∉ x.1 ∧ Feasible Abar x ∧
      ∀ y : Choice K, k ∉ y.1 → Feasible Abar y → payoff u C d y ≤ payoff u C d x := by
  classical
  let aOf : Finset (Fin K) → (Fin K → ℝ) :=
    fun J => Classical.choose (exists_max_on_set u C hS hE Abar d hd J)
  have haOf_spec : ∀ J : Finset (Fin K), Feasible Abar (J, aOf J) ∧
      ∀ a', Feasible Abar (J, a') → payoff u C d (J, a') ≤ payoff u C d (J, aOf J) :=
    fun J => Classical.choose_spec (exists_max_on_set u C hS hE Abar d hd J)
  let P : Finset (Finset (Fin K)) := (Finset.univ.erase k).powerset
  have hPne : P.Nonempty := ⟨∅, Finset.empty_mem_powerset _⟩
  obtain ⟨J0, hJ0P, hJ0max⟩ := Finset.exists_max_image P (fun J => payoff u C d (J, aOf J)) hPne
  have hkJ0 : k ∉ J0 := by
    have hsub : J0 ⊆ Finset.univ.erase k := Finset.mem_powerset.mp hJ0P
    intro hk
    exact (Finset.mem_erase.mp (hsub hk)).1 rfl
  refine ⟨(J0, aOf J0), hkJ0, (haOf_spec J0).1, fun y hky hyf => ?_⟩
  have hyP : y.1 ∈ P := Finset.mem_powerset.mpr fun j hj =>
    Finset.mem_erase.mpr ⟨fun hjk => hky (hjk ▸ hj), Finset.mem_univ j⟩
  exact ((haOf_spec y.1).2 y.2 hyf).trans (hJ0max y.1 hyP)

private lemma payoff_update_not_mem {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (d : Fin K → ℝ) (k : Fin K) (x : ℝ) (c : Choice K) (hk : k ∉ c.1) :
    payoff u C (Function.update d k x) c = payoff u C d c := by
  by_cases hne : c.1 = ∅
  · simp [payoff, hne]
  · simp only [payoff, if_neg hne]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≠ k := fun h => hk (h ▸ hj)
    rw [Function.update_of_ne hjk]

private lemma payoff_update_mem_diff {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (d : Fin K → ℝ) (k : Fin K) (x y : ℝ) (c : Choice K) (hk : k ∈ c.1) :
    payoff u C (Function.update d k y) c - payoff u C (Function.update d k x) c =
      u (c.2 k) y - u (c.2 k) x := by
  have hne : c.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨k, hk⟩
  simp only [payoff, if_neg hne, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · simp only [Function.update_self]
  · intro j _ hjk
    simp only [Function.update_of_ne hjk, sub_self]
  · intro hn
    exact (hn hk).elim

private lemma spe_pos_attention {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (hAbar : 0 < Abar)
    (d : Fin K → ℝ) (σ : ConsumerStrategy K) (hSPE : IsSPE u C Abar d σ) (k : Fin K) :
    k ∈ (σ d).1 ∧ 0 < (σ d).2 k := by
  classical
  rcases hSPE with ⟨hd, hopt, hno_dev⟩
  have hfeas_d : Feasible Abar (σ d) := (hopt d hd).1
  have hpay_nonneg : 0 ≤ platformPayoff k (σ d) := by
    unfold platformPayoff
    split_ifs with hk
    · exact hfeas_d.1 k hk
    · exact le_rfl
  by_contra hnot
  have hpay_zero : platformPayoff k (σ d) = 0 := by
    unfold platformPayoff at hpay_nonneg ⊢
    split_ifs with hk
    · have hle : (σ d).2 k ≤ 0 := by
        by_contra hlt
        exact hnot ⟨hk, lt_of_not_ge hlt⟩
      exact le_antisymm hle (hfeas_d.1 k hk)
    · rfl
  have hdev_zero : ∀ x : ℝ, 0 ≤ x → platformPayoff k (σ (Function.update d k x)) = 0 := by
    intro x hx
    have hd' : ∀ j, 0 ≤ Function.update d k x j := fun j => by
      by_cases hjk : j = k
      · subst hjk; simpa using hx
      · simpa [Function.update_of_ne hjk] using hd j
    have hfx := (hopt _ hd').1
    have hge : 0 ≤ platformPayoff k (σ (Function.update d k x)) := by
      unfold platformPayoff
      split_ifs with hk
      · exact hfx.1 k hk
      · exact le_rfl
    have hle : platformPayoff k (σ (Function.update d k x)) ≤ 0 := by
      rw [← hpay_zero]
      exact hno_dev k x hx
    exact le_antisymm hle hge
  obtain ⟨x0, hkx0, hfeas0, hmax0⟩ := exists_max_excluding u C hS hE Abar d hd k
  set V0 : ℝ := payoff u C d x0
  have hV0_nn : 0 ≤ V0 := by
    have h0 : payoff u C d (∅, fun _ => 0) ≤ V0 :=
      hmax0 (∅, fun _ => 0) (by simp) ⟨fun _ h => by simp at h, by simp⟩
    simpa [payoff] using h0
  have hdev_bound : ∀ x : ℝ, 0 ≤ x →
      payoff u C (Function.update d k x) (σ (Function.update d k x)) ≤ max V0 (u 0 x + V0) := by
    intro x hx
    set c := σ (Function.update d k x)
    have hd' : ∀ j, 0 ≤ Function.update d k x j := fun j => by
      by_cases hjk : j = k
      · subst hjk; simpa using hx
      · simpa [Function.update_of_ne hjk] using hd j
    have hfc : Feasible Abar c := (hopt _ hd').1
    by_cases hkc : k ∈ c.1
    · have hck0 : c.2 k = 0 := by
        have hz := hdev_zero x hx
        simpa [c, platformPayoff, hkc] using hz
      have hsub : payoff u C (Function.update d k x) c ≤ u 0 x + V0 := by
        by_cases hrest : c.1.erase k = ∅
        · have hc1 : c.1 = {k} := by
            ext j
            simp only [Finset.mem_singleton]
            constructor
            · intro hj
              by_contra hjk
              have : j ∈ c.1.erase k := Finset.mem_erase.mpr ⟨hjk, hj⟩
              rw [hrest] at this
              simp at this
            · rintro rfl; exact hkc
          have hne : c.1 ≠ ∅ := by rw [hc1]; simp
          rw [payoff, if_neg hne, hc1, Finset.sum_singleton, Finset.sum_singleton, hck0,
            Function.update_self, hS.C_zero, sub_zero]
          linarith
        · have hne : c.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨k, hkc⟩
          have hsum_a : ∑ j ∈ c.1, c.2 j = ∑ j ∈ c.1.erase k, c.2 j := by
            rw [← Finset.add_sum_erase _ _ hkc, hck0, zero_add]
          have hsum_u : ∑ j ∈ c.1, u (c.2 j) (Function.update d k x j) =
              u 0 x + ∑ j ∈ c.1.erase k, u (c.2 j) (d j) := by
            rw [← Finset.add_sum_erase _ _ hkc, hck0, Function.update_self]
            congr 1
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
          have hfeas_e : Feasible Abar (c.1.erase k, c.2) := by
            refine ⟨fun j hj => hfc.1 j (Finset.mem_of_mem_erase hj), ?_⟩
            rw [← hsum_a]
            exact hfc.2
          have hle_V0 : payoff u C d (c.1.erase k, c.2) ≤ V0 :=
            hmax0 (c.1.erase k, c.2) (Finset.notMem_erase k c.1) hfeas_e
          have heq_pay : payoff u C (Function.update d k x) c =
              u 0 x + payoff u C d (c.1.erase k, c.2) := by
            simp only [payoff, if_neg hne, if_neg hrest, hsum_u, hsum_a]
            ring
          linarith
      exact hsub.trans (le_max_right _ _)
    · rw [payoff_update_not_mem u C d k x c hkc]
      exact (hmax0 c hkc hfc).trans (le_max_left _ _)
  by_cases hex : ∃ j ∈ x0.1, 0 < x0.2 j
  · obtain ⟨j0, hj0, hpos0⟩ := hex
    have hjk0 : j0 ≠ k := fun h => hkx0 (h ▸ hj0)
    have hu0_nonneg : 0 ≤ u 0 (d j0) := by
      rcases (hd j0).eq_or_lt with hd0 | hdpos
      · rw [← hd0]; exact hS.assumption1.u_zero_zero_nonneg
      · have hineq : ∀ x ∈ Ico (0 : ℝ) (d j0), u (x0.2 j0) x - u (x0.2 j0) (d j0) ≤ u 0 x := by
          intro x hx
          have hd' : ∀ j, 0 ≤ Function.update d k x j := fun j => by
            by_cases hjk : j = k
            · subst hjk; simpa using hx.1
            · simpa [Function.update_of_ne hjk] using hd j
          let J'' := insert k (x0.1.erase j0)
          let a'' := Function.update x0.2 k (x0.2 j0)
          have hk_ne_e : k ∉ x0.1.erase j0 := fun h => hkx0 (Finset.mem_of_mem_erase h)
          have hsum_a : ∑ j ∈ J'', a'' j = ∑ j ∈ x0.1, x0.2 j := by
            rw [Finset.sum_insert hk_ne_e]
            have ha''_k : a'' k = x0.2 j0 := Function.update_self k (x0.2 j0) x0.2
            have hcongr : ∑ j ∈ x0.1.erase j0, a'' j = ∑ j ∈ x0.1.erase j0, x0.2 j :=
              Finset.sum_congr rfl fun j hj =>
                Function.update_of_ne (fun (h : j = k) => hk_ne_e (h ▸ hj)) (x0.2 j0) x0.2
            rw [ha''_k, hcongr, Finset.add_sum_erase _ _ hj0]
          have hfeas'' : Feasible Abar (J'', a'') := by
            refine ⟨fun j hj => ?_, by rw [hsum_a]; exact hfeas0.2⟩
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · simp [a'', hpos0.le]
            · have hjk : j ≠ k := fun h => hk_ne_e (h ▸ hj')
              simpa [a'', Function.update_of_ne hjk] using hfeas0.1 j (Finset.mem_of_mem_erase hj')
          have hne'' : J'' ≠ ∅ := Finset.insert_ne_empty _ _
          have hne0 : x0.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨j0, hj0⟩
          have hpay'' : payoff u C (Function.update d k x) (J'', a'') =
              V0 + u (x0.2 j0) x - u (x0.2 j0) (d j0) := by
            simp only [V0, payoff, if_neg hne'', if_neg hne0, hsum_a]
            rw [Finset.sum_insert hk_ne_e, Function.update_self]
            have ha''_k : a'' k = x0.2 j0 := Function.update_self k (x0.2 j0) x0.2
            have hcongr : ∑ j ∈ x0.1.erase j0, u (a'' j) (Function.update d k x j) =
                ∑ j ∈ x0.1.erase j0, u (x0.2 j) (d j) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hjk : j ≠ k := fun h => hk_ne_e (h ▸ hj)
              simp [a'', Function.update_of_ne hjk]
            rw [ha''_k, hcongr]
            have hsplit := Finset.add_sum_erase x0.1 (fun j => u (x0.2 j) (d j)) hj0
            linarith
          have hopt_le : payoff u C (Function.update d k x) (J'', a'') ≤
              max V0 (u 0 x + V0) :=
            ((hopt _ hd').2 (J'', a'') hfeas'').trans (hdev_bound x hx.1)
          have hstrict : V0 < payoff u C (Function.update d k x) (J'', a'') := by
            rw [hpay'']
            have hanti := hS.assumption1.strictAntiOn_d (x0.2 j0) hpos0.le hx.1 (hd j0) hx.2
            linarith
          have hle_right : payoff u C (Function.update d k x) (J'', a'') ≤ u 0 x + V0 := by
            rcases le_max_iff.mp hopt_le with h1 | h2
            · linarith
            · exact h2
          linarith
        have hcont_g : ContinuousWithinAt
            (fun x => u 0 x - (u (x0.2 j0) x - u (x0.2 j0) (d j0))) (Iio (d j0)) (d j0) := by
          have h1 : ContinuousOn (fun x => u 0 x - (u (x0.2 j0) x - u (x0.2 j0) (d j0))) (Ici 0) :=
            (u_contOn_d u C hS le_rfl).sub ((u_contOn_d u C hS hpos0.le).sub continuousOn_const)
          exact (h1.continuousAt (Ici_mem_nhds hdpos)).continuousWithinAt
        have hev : ∀ᶠ x in 𝓝[<] (d j0), 0 ≤ u 0 x - (u (x0.2 j0) x - u (x0.2 j0) (d j0)) := by
          have hmem : Ioo (0 : ℝ) (d j0) ∈ 𝓝[<] (d j0) := Ioo_mem_nhdsLT hdpos
          filter_upwards [hmem] with x hx
          linarith [hineq x ⟨hx.1.le, hx.2⟩]
        have hlim := ge_of_tendsto hcont_g.tendsto hev
        linarith
    -- Now deviate to x = d j0 and split attention on j0 equally between j0 and k
    have hd' : ∀ j, 0 ≤ Function.update d k (d j0) j := fun j => by
      by_cases hjk : j = k
      · subst hjk; simpa using hd j0
      · simpa [Function.update_of_ne hjk] using hd j
    let J''' := insert k x0.1
    let a''' := Function.update (Function.update x0.2 j0 (x0.2 j0 / 2)) k (x0.2 j0 / 2)
    have hsum_a : ∑ j ∈ J''', a''' j = ∑ j ∈ x0.1, x0.2 j := by
      rw [Finset.sum_insert hkx0]
      have ha_k : a''' k = x0.2 j0 / 2 := Function.update_self k _ _
      rw [← Finset.add_sum_erase _ _ hj0, ← Finset.add_sum_erase x0.1 x0.2 hj0]
      have ha_j0 : a''' j0 = x0.2 j0 / 2 := by
        simp [a''', Function.update_of_ne hjk0]
      have hcongr : ∑ j ∈ x0.1.erase j0, a''' j = ∑ j ∈ x0.1.erase j0, x0.2 j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j ≠ k := fun h => hkx0 (h ▸ Finset.mem_of_mem_erase hj)
        have hjj0 : j ≠ j0 := (Finset.mem_erase.mp hj).1
        simp [a''', Function.update_of_ne hjk, Function.update_of_ne hjj0]
      rw [ha_k, ha_j0, hcongr]
      ring
    have hfeas''' : Feasible Abar (J''', a''') := by
      refine ⟨fun j hj => ?_, by rw [hsum_a]; exact hfeas0.2⟩
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · simp [a''', (half_pos hpos0).le]
      · have hjk : j ≠ k := fun h => hkx0 (h ▸ hj')
        by_cases hjj0 : j = j0
        · subst hjj0; simp [a''', Function.update_of_ne hjk0, (half_pos hpos0).le]
        · simpa [a''', Function.update_of_ne hjk, Function.update_of_ne hjj0] using hfeas0.1 j hj'
    have hne''' : J''' ≠ ∅ := Finset.insert_ne_empty _ _
    have hne0 : x0.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨j0, hj0⟩
    have hpay''' : payoff u C (Function.update d k (d j0)) (J''', a''') =
        V0 + 2 * u (x0.2 j0 / 2) (d j0) - u (x0.2 j0) (d j0) := by
      simp only [V0, payoff, if_neg hne''', if_neg hne0, hsum_a]
      rw [Finset.sum_insert hkx0, Function.update_self]
      have ha_k : a''' k = x0.2 j0 / 2 := Function.update_self k _ _
      rw [← Finset.add_sum_erase x0.1 (fun j => u (a''' j) (Function.update d k (d j0) j)) hj0]
      rw [← Finset.add_sum_erase x0.1 (fun j => u (x0.2 j) (d j)) hj0]
      have ha_j0 : a''' j0 = x0.2 j0 / 2 := by simp [a''', Function.update_of_ne hjk0]
      have hd_j0 : Function.update d k (d j0) j0 = d j0 := Function.update_of_ne hjk0 _ _
      have hcongr : ∑ j ∈ x0.1.erase j0, u (a''' j) (Function.update d k (d j0) j) =
          ∑ j ∈ x0.1.erase j0, u (x0.2 j) (d j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk : j ≠ k := fun h => hkx0 (h ▸ Finset.mem_of_mem_erase hj)
        have hjj0 : j ≠ j0 := (Finset.mem_erase.mp hj).1
        simp [a''', Function.update_of_ne hjk, Function.update_of_ne hjj0]
      rw [ha_k, ha_j0, hd_j0, hcongr]
      ring
    have hsc := (hS.strictConcaveOn_a (d j0) (hd j0)).2
      (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
      (show x0.2 j0 ∈ Ici (0 : ℝ) from hpos0.le)
      hpos0.ne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul, mul_zero, zero_add] at hsc
    have hhalf : (1 / 2 : ℝ) * x0.2 j0 = x0.2 j0 / 2 := by ring
    rw [hhalf] at hsc
    have hstrict : max V0 (u 0 (d j0) + V0) <
        payoff u C (Function.update d k (d j0)) (J''', a''') := by
      rw [max_eq_right (by linarith), hpay''']
      linarith
    have hopt_le := ((hopt _ hd').2 (J''', a''') hfeas''').trans (hdev_bound (d j0) (hd j0))
    linarith
  · -- Case where x0.2 j = 0 for all j ∈ x0.1
    have hall0 : ∀ j ∈ x0.1, x0.2 j = 0 := by
      intro j hj
      have hle : x0.2 j ≤ 0 := by
        by_contra hlt
        exact hex ⟨j, hj, lt_of_not_ge hlt⟩
      exact le_antisymm hle (hfeas0.1 j hj)
    obtain ⟨ε, hε_pos, hε_cap, hε_gain⟩ := exists_pos_gain_at_zero u C hS hAbar
    have hd' : ∀ j, 0 ≤ Function.update d k 0 j := fun j => by
      by_cases hjk : j = k
      · subst hjk; simp
      · simpa [Function.update_of_ne hjk] using hd j
    let J' := insert k x0.1
    let a' := Function.update x0.2 k ε
    have hsum_x0 : ∑ j ∈ x0.1, x0.2 j = 0 := Finset.sum_eq_zero hall0
    have hsum_a' : ∑ j ∈ J', a' j = ε := by
      rw [Finset.sum_insert hkx0]
      have ha'_k : a' k = ε := Function.update_self k ε x0.2
      have h0 : ∑ j ∈ x0.1, a' j = 0 := Finset.sum_eq_zero fun j hj => by
        have hjk : j ≠ k := fun h => hkx0 (h ▸ hj)
        dsimp only [a']
        rw [Function.update_of_ne hjk, hall0 j hj]
      linarith
    have hfeas' : Feasible Abar (J', a') := by
      refine ⟨fun j hj => ?_, by rw [hsum_a']; exact hε_cap⟩
      change 0 ≤ a' j
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · simp [a', hε_pos.le]
      · have hjk : j ≠ k := fun h => hkx0 (h ▸ hj')
        dsimp only [a']
        rw [Function.update_of_ne hjk, hall0 j hj']
    have hne' : J' ≠ ∅ := Finset.insert_ne_empty _ _
    have hpay' : payoff u C (Function.update d k 0) (J', a') = V0 + (u ε 0 - C ε) := by
      by_cases h0 : x0.1 = ∅
      · have hV0 : V0 = 0 := by simp [V0, payoff, h0]
        rw [payoff, if_neg hne', hV0, zero_add, hsum_a']
        simp [J', h0, a']
      · simp only [V0, payoff, if_neg hne', if_neg h0, hsum_a', hsum_x0, hS.C_zero, sub_zero]
        rw [Finset.sum_insert hkx0, Function.update_self]
        have ha'_k : a' k = ε := Function.update_self k ε x0.2
        have hcongr : ∑ j ∈ x0.1, u (a' j) (Function.update d k 0 j) =
            ∑ j ∈ x0.1, u (x0.2 j) (d j) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjk : j ≠ k := fun h => hkx0 (h ▸ hj)
          simp [a', Function.update_of_ne hjk]
        rw [ha'_k, hcongr]
        ring
    have hu00 : 0 ≤ u 0 0 := hS.assumption1.u_zero_zero_nonneg
    have hstrict : max V0 (u 0 0 + V0) < payoff u C (Function.update d k 0) (J', a') := by
      rw [max_eq_right (by linarith), hpay']
      linarith
    have hopt_le := ((hopt _ hd').2 (J', a') hfeas').trans (hdev_bound 0 le_rfl)
    linarith

private lemma own_attention_monotone {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (hS : Standing u C) (Abar : ℝ≥0∞) (d : Fin K → ℝ) (k : Fin K)
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y)
    (a b : Choice K) (ha : ConsumerOpt u C Abar (Function.update d k x) a)
    (hb : ConsumerOpt u C Abar (Function.update d k y) b)
    (hka : k ∈ a.1) (hkb : k ∈ b.1) :
    a.2 k ≤ b.2 k := by
  have hab := ha.2 b hb.1
  have hba := hb.2 a ha.1
  have hdiffa := payoff_update_mem_diff u C d k x y a hka
  have hdiffb := payoff_update_mem_diff u C d k x y b hkb
  have hd : u (a.2 k) y - u (a.2 k) x ≤ u (b.2 k) y - u (b.2 k) x := by linarith
  by_contra hn
  have ht := utility_diff_strictMono u C hS hx hxy (hb.1.1 k hkb) (ha.1.1 k hka) (lt_of_not_ge hn)
  exact ht.not_ge hd

private lemma opt_eq_u1 {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    (Abar : ℝ≥0∞) (d : Fin K → ℝ) (hd : ∀ i, 0 ≤ d i) (a : Choice K)
    (ha : ConsumerOpt u C Abar d a) {k j : Fin K} (hjk : j ≠ k)
    (hk : k ∈ a.1) (hj : j ∈ a.1) (hak : 0 < a.2 k) (haj : 0 < a.2 j) :
    u1 u (a.2 k) (d k) = u1 u (a.2 j) (d j) := by
  classical
  let f : ℝ → ℝ := fun t => u (a.2 k + t) (d k) + u (a.2 j - t) (d j)
  have hloc : IsLocalMax f 0 := by
    set δ := min (a.2 k) (a.2 j)
    have hδ : 0 < δ := lt_min hak haj
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with t ht
    let b : Fin K → ℝ := Function.update (Function.update a.2 k (a.2 k + t)) j (a.2 j - t)
    have hkj : k ≠ j := hjk.symm
    have hbk : b k = a.2 k + t := by simp [b, Function.update_of_ne hkj]
    have hbj : b j = a.2 j - t := by simp [b]
    have hbi : ∀ i, i ≠ k → i ≠ j → b i = a.2 i := fun i hik hij => by
      simp [b, Function.update_of_ne hij, Function.update_of_ne hik]
    have hsum_b : ∑ i ∈ a.1, b i = ∑ i ∈ a.1, a.2 i := by
      have hj_e : j ∈ a.1.erase k := Finset.mem_erase.mpr ⟨hjk, hj⟩
      rw [← Finset.add_sum_erase _ _ hk, ← Finset.add_sum_erase (a.1.erase k) _ hj_e]
      rw [← Finset.add_sum_erase a.1 a.2 hk, ← Finset.add_sum_erase (a.1.erase k) a.2 hj_e]
      rw [hbk, hbj]
      have hrest : ∑ i ∈ (a.1.erase k).erase j, b i = ∑ i ∈ (a.1.erase k).erase j, a.2 i :=
        Finset.sum_congr rfl fun i hi =>
          hbi i (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1 (Finset.mem_erase.mp hi).1
      rw [hrest]
      ring
    have hfeas_b : Feasible Abar (a.1, b) := by
      have hδk : δ ≤ a.2 k := min_le_left _ _
      have hδj : δ ≤ a.2 j := min_le_right _ _
      refine ⟨fun i hi => ?_, by rw [hsum_b]; exact ha.1.2⟩
      change 0 ≤ b i
      by_cases hik : i = k
      · subst hik; rw [hbk]; linarith [ht.1]
      · by_cases hij : i = j
        · subst hij; rw [hbj]; linarith [ht.2]
        · rw [hbi i hik hij]; exact ha.1.1 i hi
    have hne : a.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨k, hk⟩
    have hle := ha.2 (a.1, b) hfeas_b
    have hdiff : payoff u C d (a.1, b) - payoff u C d a = f t - f 0 := by
      simp only [payoff, if_neg hne, hsum_b, sub_sub_sub_cancel_right]
      have hj_e : j ∈ a.1.erase k := Finset.mem_erase.mpr ⟨hjk, hj⟩
      rw [← Finset.add_sum_erase a.1 (fun i => u (b i) (d i)) hk,
          ← Finset.add_sum_erase (a.1.erase k) (fun i => u (b i) (d i)) hj_e]
      rw [← Finset.add_sum_erase a.1 (fun i => u (a.2 i) (d i)) hk,
          ← Finset.add_sum_erase (a.1.erase k) (fun i => u (a.2 i) (d i)) hj_e]
      rw [hbk, hbj]
      have hrest : ∑ i ∈ (a.1.erase k).erase j, u (b i) (d i) =
          ∑ i ∈ (a.1.erase k).erase j, u (a.2 i) (d i) :=
        Finset.sum_congr rfl fun i hi => by
          rw [hbi i (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1 (Finset.mem_erase.mp hi).1]
      rw [hrest]
      simp [f]
      ring
    linarith
  have hderiv : HasDerivAt f (u1 u (a.2 k) (d k) - u1 u (a.2 j) (d j)) 0 := by
    have h1 : HasDerivAt (fun t => u (a.2 k + t) (d k)) (u1 u (a.2 k) (d k) * 1) 0 := by
      have hu : HasDerivAt (fun x => u x (d k)) (u1 u (a.2 k) (d k)) (a.2 k + 0) := by
        simpa using u_hasDerivAt_a u C hS hak (hd k)
      have ha1 : HasDerivAt (fun t : ℝ => a.2 k + t) 1 0 := (hasDerivAt_id 0).const_add (a.2 k)
      exact hu.comp 0 ha1
    have h2 : HasDerivAt (fun t => u (a.2 j - t) (d j)) (u1 u (a.2 j) (d j) * (-1)) 0 := by
      have hu : HasDerivAt (fun x => u x (d j)) (u1 u (a.2 j) (d j)) (a.2 j - 0) := by
        simpa using u_hasDerivAt_a u C hS haj (hd j)
      have ha2 : HasDerivAt (fun t : ℝ => a.2 j - t) (-1) 0 := by
        simpa using (hasDerivAt_id 0).const_sub (a.2 j)
      exact hu.comp 0 ha2
    have h12 : HasDerivAt f (u1 u (a.2 k) (d k) * 1 + u1 u (a.2 j) (d j) * (-1)) 0 := h1.add h2
    rwa [mul_one, mul_neg_one, ← sub_eq_add_neg] at h12
  linarith [hloc.hasDerivAt_eq_zero hderiv]

private lemma spe_raise_excludes {K : ℕ} (hK : 2 ≤ K) (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (hS : Standing u C) (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (hAbar : 0 < Abar)
    (d : Fin K → ℝ) (σ : ConsumerStrategy K) (hSPE : IsSPE u C Abar d σ)
    (k : Fin K) {x : ℝ} (hdx : d k < x) :
    k ∉ (σ (Function.update d k x)).1 := by
  intro hkb
  have hd := hSPE.1
  have hopt := hSPE.2.1
  have hno_dev := hSPE.2.2
  have hx : 0 ≤ x := (hd k).trans hdx.le
  have hd' : ∀ i, 0 ≤ Function.update d k x i := fun i => by
    by_cases hik : i = k
    · subst hik; simpa using hx
    · simpa [Function.update_of_ne hik] using hd i
  have hpos_all : ∀ i, i ∈ (σ d).1 ∧ 0 < (σ d).2 i :=
    fun i => spe_pos_attention u C hS hE Abar hAbar d σ hSPE i
  have hka : k ∈ (σ d).1 := (hpos_all k).1
  have hupd_self : Function.update d k (d k) = d := Function.update_eq_self k d
  have ha_opt : ConsumerOpt u C Abar (Function.update d k (d k)) (σ d) := by
    rw [hupd_self]; exact hopt d hd
  have hb_opt : ConsumerOpt u C Abar (Function.update d k x) (σ (Function.update d k x)) :=
    hopt _ hd'
  have hle1 : (σ d).2 k ≤ (σ (Function.update d k x)).2 k :=
    own_attention_monotone u C hS Abar d k (d k) x (hd k) hdx _ _ ha_opt hb_opt hka hkb
  have hle2 : (σ (Function.update d k x)).2 k ≤ (σ d).2 k := by
    have hdev := hno_dev k x hx
    simpa [platformPayoff, hka, hkb] using hdev
  have heq_ak : (σ (Function.update d k x)).2 k = (σ d).2 k := le_antisymm hle2 hle1
  have ha_opt' : ConsumerOpt u C Abar (Function.update d k x) (σ d) := by
    refine ⟨(hopt d hd).1, fun y hy => ?_⟩
    have h1 := hb_opt.2 y hy
    have hdiff_a := payoff_update_mem_diff u C d k (d k) x (σ d) hka
    have hdiff_b := payoff_update_mem_diff u C d k (d k) x (σ (Function.update d k x)) hkb
    rw [hupd_self] at hdiff_a hdiff_b
    have h2 := (hopt d hd).2 (σ (Function.update d k x)) hb_opt.1
    rw [heq_ak] at hdiff_b
    linarith
  have hcard : 1 < Fintype.card (Fin K) := by simpa using (by omega : 1 < K)
  obtain ⟨j, hjk⟩ := Fintype.exists_ne_of_one_lt_card hcard k
  have hu1_d := opt_eq_u1 u C hS Abar d hd (σ d) (hopt d hd) hjk hka (hpos_all j).1
    (hpos_all k).2 (hpos_all j).2
  have hu1_x := opt_eq_u1 u C hS Abar (Function.update d k x) hd' (σ d) ha_opt' hjk hka
    (hpos_all j).1 (hpos_all k).2 (hpos_all j).2
  rw [Function.update_self, Function.update_of_ne hjk] at hu1_x
  have hstrict := hS.assumption1.strictMonoOn_u1 ((σ d).2 k) (hpos_all k).2.le (hd k) hx hdx
  linarith

private lemma spe_exists_drop_eq {K : ℕ} (hK : 2 ≤ K) (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (hS : Standing u C) (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (hAbar : 0 < Abar)
    (d : Fin K → ℝ) (σ : ConsumerStrategy K) (hSPE : IsSPE u C Abar d σ) (k : Fin K) :
    ∃ x0 : Choice K, k ∉ x0.1 ∧ Feasible Abar x0 ∧ payoff u C d x0 = payoff u C d (σ d) := by
  have hd := hSPE.1
  have hopt := hSPE.2.1
  obtain ⟨x0, hkx0, hfeas0, hmax0⟩ := exists_max_excluding u C hS hE Abar d hd k
  have hle : payoff u C d x0 ≤ payoff u C d (σ d) := (hopt d hd).2 x0 hfeas0
  have hpos_k := spe_pos_attention u C hS hE Abar hAbar d σ hSPE k
  have hupd_self : Function.update d k (d k) = d := Function.update_eq_self k d
  have hineq : ∀ x ∈ Ioi (d k),
      payoff u C d (σ d) + (u ((σ d).2 k) x - u ((σ d).2 k) (d k)) ≤ payoff u C d x0 := by
    intro x hx
    have hx_nn : 0 ≤ x := (hd k).trans (le_of_lt hx)
    have hd' : ∀ i, 0 ≤ Function.update d k x i := fun i => by
      by_cases hik : i = k
      · subst hik; simpa using hx_nn
      · simpa [Function.update_of_ne hik] using hd i
    have hexcl : k ∉ (σ (Function.update d k x)).1 :=
      spe_raise_excludes hK u C hS hE Abar hAbar d σ hSPE k hx
    have hdiff := payoff_update_mem_diff u C d k (d k) x (σ d) hpos_k.1
    rw [hupd_self] at hdiff
    have h1 : payoff u C (Function.update d k x) (σ d) ≤
        payoff u C (Function.update d k x) (σ (Function.update d k x)) :=
      (hopt _ hd').2 (σ d) (hopt d hd).1
    have h2 : payoff u C (Function.update d k x) (σ (Function.update d k x)) ≤ payoff u C d x0 := by
      rw [payoff_update_not_mem u C d k x _ hexcl]
      exact hmax0 _ hexcl (hopt _ hd').1
    linarith
  have hcont : ContinuousWithinAt
      (fun x => payoff u C d (σ d) + (u ((σ d).2 k) x - u ((σ d).2 k) (d k))) (Ioi (d k)) (d k) := by
    have h1 := (u_contOn_d u C hS hpos_k.2.le).continuousWithinAt (hd k)
    have h2 := h1.mono (Ioi_subset_Ici (hd k))
    exact continuousWithinAt_const.add (h2.sub continuousWithinAt_const)
  have hev : ∀ᶠ x in 𝓝[>] (d k),
      payoff u C d (σ d) + (u ((σ d).2 k) x - u ((σ d).2 k) (d k)) ≤ payoff u C d x0 :=
    eventually_nhdsWithin_of_forall hineq
  have hge : payoff u C d (σ d) ≤ payoff u C d x0 := by
    have hlim := le_of_tendsto hcont.tendsto hev
    linarith
  exact ⟨x0, hkx0, hfeas0, le_antisymm hle hge⟩

private lemma spe_erase_single_eq {K : ℕ} (hK : 2 ≤ K) (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (hS : Standing u C) (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (hAbar : 0 < Abar)
    (d : Fin K → ℝ) (σ : ConsumerStrategy K) (hSPE : IsSPE u C Abar d σ) (k : Fin K) :
    ∃ a : Fin K → ℝ, Feasible Abar (Finset.univ.erase k, a) ∧
      payoff u C d (Finset.univ.erase k, a) = payoff u C d (σ d) := by
  classical
  have : NeZero K := ⟨by omega⟩
  have hd := hSPE.1
  have hopt := hSPE.2.1
  obtain ⟨x0, hkx0, hfeas0, heq0⟩ := spe_exists_drop_eq hK u C hS hE Abar hAbar d σ hSPE k
  set S : Finset (Fin K) := x0.1
  have hSsub : S ⊆ Finset.univ.erase k := fun j hj =>
    Finset.mem_erase.mpr ⟨fun hjk => hkx0 (hjk ▸ hj), Finset.mem_univ j⟩
  by_cases hSeq : S = Finset.univ.erase k
  · rw [← hSeq]
    exact ⟨x0.2, hfeas0, heq0⟩
  have hSssub : S ⊂ Finset.univ.erase k := ssubset_iff_subset_ne.mpr ⟨hSsub, hSeq⟩
  let τ : Fin K ≃ Fin K := Equiv.swap (0 : Fin K) k
  let d' : Fin K → ℝ := d ∘ τ
  have hd' : ∀ i, 0 ≤ d' i := fun i => hd (τ i)
  let T_big : Finset (Fin K) := Finset.univ.erase (0 : Fin K)
  let T' : Finset (Fin K) := S.map τ.toEmbedding
  have hT'_sub : T' ⊂ T_big := by
    refine ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro i hi
      rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h0
      have hjk : j = k := by
        have := congrArg τ h0
        simpa [τ] using this
      exact hkx0 (hjk ▸ hj)
    · intro heq
      apply hSeq
      ext j
      constructor
      · exact fun hj => hSsub hj
      · intro hj
        have hτj : τ j ∈ T_big := by
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
          intro h0
          have hjk : j = k := by
            have := congrArg τ h0
            simpa [τ] using this
          exact (Finset.mem_erase.mp hj).1 hjk
        rw [← heq] at hτj
        rcases Finset.mem_map.mp hτj with ⟨m, hm, hm_eq⟩
        have : m = j := τ.injective hm_eq
        exact this ▸ hm
  have h0_not_T' : (0 : Fin K) ∉ T' := fun h =>
    (Finset.mem_erase.mp (hT'_sub.1 h)).1 rfl
  have hpos_all : ∀ i, i ∈ (σ d).1 ∧ 0 < (σ d).2 i :=
    fun i => spe_pos_attention u C hS hE Abar hAbar d σ hSPE i
  have hσ_univ : (σ d).1 = Finset.univ := by
    ext i; simp [(hpos_all i).1]
  let a1 : Fin K → ℝ := (σ d).2 ∘ τ
  let a4 : Fin K → ℝ := x0.2 ∘ τ
  have hsum_a1 : ∑ i ∈ Finset.univ, a1 i = ∑ i ∈ (σ d).1, (σ d).2 i := by
    rw [hσ_univ]
    exact Fintype.sum_equiv τ a1 (σ d).2 fun _ => rfl
  have hsum_a4 : ∑ i ∈ T', a4 i = ∑ j ∈ S, x0.2 j := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [a4, τ]
  -- Choose finite cap Abar' ≤ Abar large enough to hold a1 and a4
  let Abar' : ℝ≥0∞ :=
    if Abar = ⊤ then ENNReal.ofReal (max (∑ i ∈ Finset.univ, a1 i) (∑ i ∈ T', a4 i)) else Abar
  have hAbar'_fin : Abar' ≠ ⊤ := by
    dsimp [Abar']
    split_ifs with htop
    · exact ENNReal.ofReal_ne_top
    · exact htop
  have hAbar'_le : Abar' ≤ Abar := by
    dsimp [Abar']
    split_ifs with htop
    · simp [htop]
    · exact le_rfl
  have ha1_cap : ENNReal.ofReal (∑ i ∈ insert 0 T_big, a1 i) ≤ Abar' := by
    have hins : insert 0 T_big = Finset.univ := Finset.insert_erase (Finset.mem_univ 0)
    rw [hins]
    dsimp [Abar']
    split_ifs with htop
    · exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    · rw [hsum_a1]; exact (hopt d hd).1.2
  have ha4_cap : ENNReal.ofReal (∑ i ∈ T', a4 i) ≤ Abar' := by
    dsimp [Abar']
    split_ifs with htop
    · exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
    · rw [hsum_a4]; exact hfeas0.2
  let aB4 : ℝ → Finset (Fin K) → (Fin K → ℝ) := fun y T =>
    Classical.choose (exists_b4_max_finite u C hS hAbar'_fin d' hd' y T)
  have haB4 : ∀ y ∈ Icc (0 : ℝ) 1, ∀ T : Finset (Fin K), T ⊆ Finset.univ.erase 0 →
      IsB4Max u C Abar' d' y T (aB4 y T) := fun y _ T _ =>
    Classical.choose_spec (exists_b4_max_finite u C hS hAbar'_fin d' hd' y T)
  have hB4 := (AddictivePlatforms.Compete.lemma_B_4 u C hS Abar' d' hd' aB4 haB4
    T_big T' Subset.rfl hT'_sub).2
  -- Bound 1: payoff (σ d) ≤ objB4 1 T_big (aB4 1 T_big)
  have h1 : payoff u C d (σ d) ≤ objB4 u C d' 1 T_big (aB4 1 T_big) := by
    have hins : insert 0 T_big = Finset.univ := Finset.insert_erase (Finset.mem_univ 0)
    have hobj1 : objB4 u C d' 1 T_big a1 = payoff u C d (σ d) := by
      unfold objB4
      rw [hins, one_mul, hsum_a1]
      have hne_u : (σ d).1 ≠ ∅ := by rw [hσ_univ]; exact Finset.univ_nonempty.ne_empty
      simp only [payoff, if_neg hne_u]
      congr 1
      have hsum_u : ∑ i ∈ T_big, u (a1 i) (d' i) + u (a1 0) (d' 0) =
          ∑ i ∈ Finset.univ, u (a1 i) (d' i) := by
        dsimp only [T_big]
        rw [add_comm]
        exact Finset.add_sum_erase Finset.univ (fun i => u (a1 i) (d' i)) (Finset.mem_univ (0 : Fin K))
      rw [hsum_u, hσ_univ]
      exact Fintype.sum_equiv τ (fun i => u (a1 i) (d' i)) (fun i => u ((σ d).2 i) (d i))
        fun _ => rfl
    rw [← hobj1]
    exact (haB4 1 ⟨zero_le_one, le_rfl⟩ T_big Subset.rfl).2.2 a1
      (fun i _ => (hpos_all (τ i)).2.le) ha1_cap
  -- Bound 2: witness a_k := (aB4 0 T_big) ∘ τ on univ.erase k
  let ak : Fin K → ℝ := (aB4 0 T_big) ∘ τ
  have hTbig_map : (Finset.univ.erase k).map τ.toEmbedding = T_big := by
    ext i
    simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true, Equiv.coe_toEmbedding,
      T_big]
    constructor
    · rintro ⟨j, hjk, rfl⟩
      intro h0
      have : j = k := by have := congrArg τ h0; simpa [τ] using this
      exact hjk this
    · intro hi0
      refine ⟨τ i, ?_, by simp [τ]⟩
      intro hτk
      have : i = 0 := by have := congrArg τ hτk; simpa [τ] using this
      exact hi0 this
  have hB4_0_Tbig := haB4 0 ⟨le_rfl, zero_le_one⟩ T_big Subset.rfl
  have hsum_ak : ∑ j ∈ Finset.univ.erase k, ak j = ∑ i ∈ T_big, aB4 0 T_big i := by
    rw [← hTbig_map, Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [ak, τ, T_big]
  have hfeas_ak : Feasible Abar (Finset.univ.erase k, ak) := by
    refine ⟨fun j hj => ?_, ?_⟩
    · have hτj : τ j ∈ T_big := by
        rw [← hTbig_map]; exact Finset.mem_map_of_mem _ hj
      exact hB4_0_Tbig.1 (τ j) (Finset.mem_insert_of_mem hτj)
    · rw [hsum_ak]
      have h0nn : 0 ≤ aB4 0 T_big 0 := hB4_0_Tbig.1 0 (Finset.mem_insert_self 0 T_big)
      have hle_sum : ∑ i ∈ T_big, aB4 0 T_big i ≤ ∑ i ∈ insert 0 T_big, aB4 0 T_big i := by
        rw [Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
        linarith
      exact (ENNReal.ofReal_le_ofReal hle_sum).trans (hB4_0_Tbig.2.1.trans hAbar'_le)
  have h2 : objB4 u C d' 0 T_big (aB4 0 T_big) ≤ payoff u C d (Finset.univ.erase k, ak) := by
    have hcard : 1 < Fintype.card (Fin K) := by simpa using (by omega : 1 < K)
    obtain ⟨j1, hj1k⟩ := Fintype.exists_ne_of_one_lt_card hcard k
    have hne_ek : Finset.univ.erase k ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp ⟨j1, Finset.mem_erase.mpr ⟨hj1k, Finset.mem_univ j1⟩⟩
    have hsum_u : ∑ j ∈ Finset.univ.erase k, u (ak j) (d j) =
        ∑ i ∈ T_big, u (aB4 0 T_big i) (d' i) := by
      rw [← hTbig_map, Finset.sum_map]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [ak, d', τ, T_big]
    have h0nn : 0 ≤ aB4 0 T_big 0 := hB4_0_Tbig.1 0 (Finset.mem_insert_self 0 T_big)
    have hTsum_nn : 0 ≤ ∑ i ∈ T_big, aB4 0 T_big i :=
      Finset.sum_nonneg fun i hi => hB4_0_Tbig.1 i (Finset.mem_insert_of_mem hi)
    have hle_sum : ∑ i ∈ T_big, aB4 0 T_big i ≤ ∑ i ∈ insert 0 T_big, aB4 0 T_big i := by
      rw [Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
      linarith
    have hCle : C (∑ i ∈ T_big, aB4 0 T_big i) ≤ C (∑ i ∈ insert 0 T_big, aB4 0 T_big i) :=
      hS.assumption2.strictMonoOn.monotoneOn hTsum_nn (hTsum_nn.trans hle_sum) hle_sum
    unfold objB4
    simp only [payoff, if_neg hne_ek, zero_mul, add_zero, hsum_u, hsum_ak]
    linarith
  -- Bound 3: objB4 1 T' (aB4 1 T') ≤ payoff (σ d)
  have h3 : objB4 u C d' 1 T' (aB4 1 T') ≤ payoff u C d (σ d) := by
    have hB4_1_T' := haB4 1 ⟨zero_le_one, le_rfl⟩ T' hT'_sub.1
    let a3 : Fin K → ℝ := (aB4 1 T') ∘ τ
    have hmap_ins : (insert k S).map τ.toEmbedding = insert 0 T' := by
      ext i
      simp only [Finset.mem_map, Finset.mem_insert, Equiv.coe_toEmbedding, T']
      constructor
      · rintro ⟨j, rfl | hj, rfl⟩
        · left; simp [τ]
        · right; exact ⟨j, hj, rfl⟩
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨k, Or.inl rfl, by simp [τ]⟩
        · exact ⟨j, Or.inr hj, rfl⟩
    have hsum_a3 : ∑ j ∈ insert k S, a3 j = ∑ i ∈ insert 0 T', aB4 1 T' i := by
      rw [← hmap_ins, Finset.sum_map]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [a3, τ]
    have hfeas_a3 : Feasible Abar (insert k S, a3) := by
      refine ⟨fun j hj => ?_, ?_⟩
      · have hτj : τ j ∈ insert 0 T' := by
          rw [← hmap_ins]; exact Finset.mem_map_of_mem _ hj
        exact hB4_1_T'.1 (τ j) hτj
      · rw [hsum_a3]
        exact hB4_1_T'.2.1.trans hAbar'_le
    have hpay_eq : objB4 u C d' 1 T' (aB4 1 T') = payoff u C d (insert k S, a3) := by
      have hne_ins : insert k S ≠ ∅ := Finset.insert_ne_empty _ _
      unfold objB4
      simp only [payoff, if_neg hne_ins, one_mul, hsum_a3]
      congr 1
      have hsum_u1 : ∑ i ∈ T', u (aB4 1 T' i) (d' i) + u (aB4 1 T' 0) (d' 0) =
          ∑ i ∈ insert 0 T', u (aB4 1 T' i) (d' i) := by
        rw [add_comm, Finset.sum_insert h0_not_T']
      rw [hsum_u1, ← hmap_ins, Finset.sum_map]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [a3, d', τ]
    rw [hpay_eq]
    exact (hopt d hd).2 (insert k S, a3) hfeas_a3
  -- Bound 4: payoff (σ d) ≤ objB4 0 T' (aB4 0 T')
  have h4 : payoff u C d (σ d) ≤ objB4 u C d' 0 T' (aB4 0 T') := by
    let a4' : Fin K → ℝ := Function.update a4 0 0
    have hsum_a4' : ∑ i ∈ insert 0 T', a4' i = ∑ i ∈ T', a4 i := by
      rw [Finset.sum_insert h0_not_T']
      have ha4'_0 : a4' 0 = 0 := Function.update_self 0 0 a4
      rw [ha4'_0, zero_add]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi0 : i ≠ 0 := fun h => h0_not_T' (h ▸ hi)
      dsimp only [a4']
      rw [Function.update_of_ne hi0]
    have ha4'_nn : ∀ i ∈ insert 0 T', 0 ≤ a4' i := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · simp [a4']
      · have hi0 : i ≠ 0 := fun h => h0_not_T' (h ▸ hi')
        dsimp only [a4']
        rw [Function.update_of_ne hi0]
        rcases Finset.mem_map.mp hi' with ⟨j, hj, rfl⟩
        simpa [a4, τ] using hfeas0.1 j hj
    have ha4'_cap : ENNReal.ofReal (∑ i ∈ insert 0 T', a4' i) ≤ Abar' := by
      rw [hsum_a4']; exact ha4_cap
    have hobj4 : objB4 u C d' 0 T' a4' = payoff u C d x0 := by
      unfold objB4
      simp only [zero_mul, add_zero, hsum_a4', hsum_a4]
      by_cases hS0 : x0.1 = ∅
      · have hT0 : T' = ∅ := by simp [T', S, hS0]
        simp [payoff, S, hS0, hT0, hS.C_zero]
      · simp only [payoff, if_neg hS0]
        change ∑ i ∈ T', u (a4' i) (d' i) - C (∑ j ∈ S, x0.2 j) =
          ∑ j ∈ S, u (x0.2 j) (d j) - C (∑ j ∈ S, x0.2 j)
        congr 1
        rw [show T' = S.map τ.toEmbedding from rfl, Finset.sum_map]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hτj0 : τ j ≠ 0 := fun h0 => h0_not_T' (h0 ▸ Finset.mem_map_of_mem _ hj)
        simp [a4', a4, d', τ, Function.update_of_ne hτj0]
    rw [← heq0, ← hobj4]
    exact (haB4 0 ⟨le_rfl, zero_le_one⟩ T' hT'_sub.1).2.2 a4' ha4'_nn ha4'_cap
  have hge : payoff u C d (σ d) ≤ payoff u C d (Finset.univ.erase k, ak) := by linarith
  have hle : payoff u C d (Finset.univ.erase k, ak) ≤ payoff u C d (σ d) :=
    (hopt d hd).2 (Finset.univ.erase k, ak) hfeas_ak
  exact ⟨ak, hfeas_ak, le_antisymm hle hge⟩

private lemma spe_symmetric {K : ℕ} (hK : 2 ≤ K) (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (hS : Standing u C) (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (hAbar : 0 < Abar)
    (d : Fin K → ℝ) (σ : ConsumerStrategy K) (hSPE : IsSPE u C Abar d σ) :
    ∀ k₁ k₂ : Fin K, d k₁ = d k₂ := by
  have hnot_lt : ∀ k₁ k₂ : Fin K, ¬ d k₁ < d k₂ := by
    intro k₁ k₂ hlt
    have hk12 : k₁ ≠ k₂ := fun h => by subst h; exact lt_irrefl _ hlt
    obtain ⟨a₁, hfeas₁, heq₁⟩ := spe_erase_single_eq hK u C hS hE Abar hAbar d σ hSPE k₁
    let τ : Fin K ≃ Fin K := Equiv.swap k₁ k₂
    let J₁ : Finset (Fin K) := Finset.univ.erase k₁
    let J₂ : Finset (Fin K) := Finset.univ.erase k₂
    let a₂ : Fin K → ℝ := a₁ ∘ τ
    have hmap : J₂.map τ.toEmbedding = J₁ := by
      ext i
      simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true, Equiv.coe_toEmbedding,
        J₁, J₂]
      constructor
      · rintro ⟨j, hj2, rfl⟩
        intro h1
        have : j = k₂ := by have := congrArg τ h1; simpa [τ] using this
        exact hj2 this
      · intro hi1
        refine ⟨τ i, ?_, by simp [τ]⟩
        intro h2
        have : i = k₁ := by have := congrArg τ h2; simpa [τ] using this
        exact hi1 this
    have hsum_a : ∑ i ∈ J₂, a₂ i = ∑ i ∈ J₁, a₁ i := by
      rw [← hmap, Finset.sum_map]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [a₂, τ]
    have hfeas₂ : Feasible Abar (J₂, a₂) := by
      refine ⟨fun j hj => ?_, by rw [hsum_a]; exact hfeas₁.2⟩
      have hτj : τ j ∈ J₁ := by rw [← hmap]; exact Finset.mem_map_of_mem _ hj
      exact hfeas₁.1 (τ j) hτj
    have hk₂J₁ : k₂ ∈ J₁ := Finset.mem_erase.mpr ⟨hk12.symm, Finset.mem_univ k₂⟩
    have hk₁J₂ : k₁ ∈ J₂ := Finset.mem_erase.mpr ⟨hk12, Finset.mem_univ k₁⟩
    have hne₁ : J₁ ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨k₂, hk₂J₁⟩
    have hne₂ : J₂ ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨k₁, hk₁J₂⟩
    have hdiff : payoff u C d (J₂, a₂) - payoff u C d (J₁, a₁) =
        u (a₁ k₂) (d k₁) - u (a₁ k₂) (d k₂) := by
      simp only [payoff, if_neg hne₂, if_neg hne₁, hsum_a, sub_sub_sub_cancel_right]
      rw [← Finset.add_sum_erase J₂ (fun i => u (a₂ i) (d i)) hk₁J₂]
      rw [← Finset.add_sum_erase J₁ (fun i => u (a₁ i) (d i)) hk₂J₁]
      have ha2_k1 : a₂ k₁ = a₁ k₂ := by simp [a₂, τ]
      have hrest_set : J₂.erase k₁ = J₁.erase k₂ := by
        ext i; simp [J₁, J₂]; tauto
      have hrest_sum : ∑ i ∈ J₂.erase k₁, u (a₂ i) (d i) =
          ∑ i ∈ J₁.erase k₂, u (a₁ i) (d i) := by
        rw [hrest_set]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi2 : i ≠ k₂ := (Finset.mem_erase.mp hi).1
        have hi1 : i ≠ k₁ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1
        simp [a₂, τ, Equiv.swap_apply_of_ne_of_ne hi1 hi2]
      rw [ha2_k1, hrest_sum]
      ring
    have hanti := hS.assumption1.strictAntiOn_d (a₁ k₂) (hfeas₁.1 k₂ hk₂J₁)
      (hSPE.1 k₁) (hSPE.1 k₂) hlt
    have hle : payoff u C d (J₂, a₂) ≤ payoff u C d (σ d) :=
      (hSPE.2.1 d hSPE.1).2 (J₂, a₂) hfeas₂
    linarith
  intro k₁ k₂
  rcases lt_trichotomy (d k₁) (d k₂) with h | h | h
  · exact (hnot_lt k₁ k₂ h).elim
  · exact h
  · exact (hnot_lt k₂ k₁ h).elim

private lemma isPerspMax_of_const_opt {K : ℕ} (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ)
    (hS : Standing u C) (Abar : ℝ≥0∞) {d₀ : ℝ} (hd₀ : 0 ≤ d₀)
    (J : Finset (Fin K)) (hJ : J.Nonempty) (a : Fin K → ℝ)
    (hfeas : Feasible Abar (J, a))
    (hopt : ∀ a' : Fin K → ℝ, Feasible Abar (J, a') →
      payoff u C (fun _ => d₀) (J, a') ≤ payoff u C (fun _ => d₀) (J, a)) :
    IsPerspMax u C Abar (J.card : ℝ) d₀ (∑ k ∈ J, a k) ∧
      perspObj u C (J.card : ℝ) d₀ (∑ k ∈ J, a k) = payoff u C (fun _ => d₀) (J, a) := by
  set m : ℝ := (J.card : ℝ)
  have hm_def : (J.card : ℝ) = m := rfl
  have hm_pos : 0 < m := by rw [← hm_def]; exact_mod_cast hJ.card_pos
  set A : ℝ := ∑ k ∈ J, a k
  have hA_nn : 0 ≤ A := Finset.sum_nonneg fun k hk => hfeas.1 k hk
  have hjensen : ∑ k ∈ J, u (a k) d₀ ≤ m * u (A / m) d₀ := by
    have h1 := (hS.assumption1.concaveOn_a d₀ hd₀).le_map_sum
      (t := J) (w := fun _ => 1 / m) (p := a)
      (fun _ _ => by positivity)
      (by simp only [Finset.sum_const, nsmul_eq_mul, hm_def]; exact mul_one_div_cancel hm_pos.ne')
      (fun k hk => hfeas.1 k hk)
    simp only [smul_eq_mul] at h1
    have hmul := mul_le_mul_of_nonneg_left h1 hm_pos.le
    rw [Finset.mul_sum] at hmul
    have hlhs : ∑ k ∈ J, m * (1 / m * u (a k) d₀) = ∑ k ∈ J, u (a k) d₀ :=
      Finset.sum_congr rfl fun k _ => by field_simp [hm_pos.ne']
    have harg : ∑ k ∈ J, 1 / m * a k = A / m := by
      rw [← Finset.mul_sum]
      ring
    rw [hlhs, harg] at hmul
    exact hmul
  have hpay_le : payoff u C (fun _ => d₀) (J, a) ≤ perspObj u C m d₀ A := by
    have hne : J ≠ ∅ := hJ.ne_empty
    simp only [payoff, if_neg hne, perspObj]
    linarith
  have hunif : ∀ A' : ℝ, 0 ≤ A' → ENNReal.ofReal A' ≤ Abar →
      perspObj u C m d₀ A' ≤ payoff u C (fun _ => d₀) (J, a) := by
    intro A' hA' hcap'
    let b : Fin K → ℝ := fun _ => A' / m
    have hsum_b : ∑ k ∈ J, b k = A' := by
      simp only [b, Finset.sum_const, nsmul_eq_mul, hm_def]
      exact mul_div_cancel₀ A' hm_pos.ne'
    have hfeas_b : Feasible Abar (J, b) :=
      ⟨fun _ _ => div_nonneg hA' hm_pos.le, by rw [hsum_b]; exact hcap'⟩
    have hpay_b : payoff u C (fun _ => d₀) (J, b) = perspObj u C m d₀ A' := by
      simp only [payoff, if_neg hJ.ne_empty, perspObj, b, hsum_b, Finset.sum_const, nsmul_eq_mul,
        hm_def]
    rw [← hpay_b]
    exact hopt b hfeas_b
  have heq : perspObj u C m d₀ A = payoff u C (fun _ => d₀) (J, a) :=
    le_antisymm (hunif A hA_nn hfeas.2) hpay_le
  refine ⟨⟨hA_nn, hfeas.2, fun A' hA' hcap' => ?_⟩, heq⟩
  rw [heq]
  exact hunif A' hA' hcap'

end Helpers

theorem solution (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) (K : ℕ) (hK : 2 ≤ K)
    (hE : UncOptExists u C K) (Abar : ℝ≥0∞) (hAbar : 0 < Abar) :
    ∃ dstar : ℝ, 0 < dstar ∧ Eq3 u C Abar K dstar ∧
      (∃ σ : ConsumerStrategy K, IsSPE u C Abar (fun _ : Fin K => dstar) σ) ∧
      ∀ (d : Fin K → ℝ) (σ : ConsumerStrategy K), IsSPE u C Abar d σ → ∀ k, d k = dstar := by
  obtain ⟨dstar, hdstar_pos, hdstar_eq3, hσ_ex⟩ :=
    AddictivePlatforms.Compete.proposition_2_existence u C hS K hK hE Abar hAbar
  obtain ⟨d_uniq, _, huniq⟩ :=
    AddictivePlatforms.Compete.proposition_2_step_1 u C hS K hK hE Abar hAbar
  refine ⟨dstar, hdstar_pos, hdstar_eq3, hσ_ex, ?_⟩
  intro d σ hSPE
  have : NeZero K := ⟨by omega⟩
  have hsym := spe_symmetric hK u C hS hE Abar hAbar d σ hSPE
  set d₀ : ℝ := d 0
  have hd_eq : d = fun _ : Fin K => d₀ := funext fun k => hsym k 0
  have hd₀ : 0 ≤ d₀ := hSPE.1 0
  have hpos_all := fun i => spe_pos_attention u C hS hE Abar hAbar d σ hSPE i
  have hσ_univ : (σ d).1 = Finset.univ := by
    ext i; simp [(hpos_all i).1]
  have hσ_eq : (Finset.univ, (σ d).2) = σ d := Prod.ext hσ_univ.symm rfl
  have hfeas_u : Feasible Abar (Finset.univ, (σ d).2) := by
    rw [hσ_eq]; exact (hSPE.2.1 d hSPE.1).1
  have hopt_u : ∀ a' : Fin K → ℝ, Feasible Abar (Finset.univ, a') →
      payoff u C (fun _ => d₀) (Finset.univ, a') ≤
        payoff u C (fun _ => d₀) (Finset.univ, (σ d).2) := by
    intro a' ha'
    rw [← hd_eq, hσ_eq]
    exact (hSPE.2.1 d hSPE.1).2 (Finset.univ, a') ha'
  obtain ⟨hAK, hvalK⟩ := isPerspMax_of_const_opt u C hS Abar hd₀
    Finset.univ Finset.univ_nonempty (σ d).2 hfeas_u hopt_u
  obtain ⟨a0, hfeas0, heq0⟩ := spe_erase_single_eq hK u C hS hE Abar hAbar d σ hSPE 0
  have hcard1 : 1 < Fintype.card (Fin K) := by simpa using (by omega : 1 < K)
  obtain ⟨j1, hj10⟩ := Fintype.exists_ne_of_one_lt_card hcard1 0
  have hne0 : (Finset.univ.erase (0 : Fin K)).Nonempty :=
    ⟨j1, Finset.mem_erase.mpr ⟨hj10, Finset.mem_univ j1⟩⟩
  have hopt_e : ∀ a' : Fin K → ℝ, Feasible Abar (Finset.univ.erase 0, a') →
      payoff u C (fun _ => d₀) (Finset.univ.erase 0, a') ≤
        payoff u C (fun _ => d₀) (Finset.univ.erase 0, a0) := by
    intro a' ha'
    rw [← hd_eq, heq0]
    exact (hSPE.2.1 d hSPE.1).2 (Finset.univ.erase 0, a') ha'
  obtain ⟨hAK1, hvalK1⟩ := isPerspMax_of_const_opt u C hS Abar hd₀
    (Finset.univ.erase 0) hne0 a0 hfeas0 hopt_e
  have hcard_u : ((Finset.univ : Finset (Fin K)).card : ℝ) = (K : ℝ) := by simp
  have hcard_e : ((Finset.univ.erase (0 : Fin K)).card : ℝ) = (K : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin]
    have hK1 : 1 ≤ K := by omega
    rw [Nat.cast_sub hK1, Nat.cast_one]
  rw [hcard_u] at hAK hvalK
  rw [hcard_e] at hAK1 hvalK1
  have heq3_d₀ : Eq3 u C Abar K d₀ := by
    refine ⟨∑ k ∈ Finset.univ, (σ d).2 k, ∑ k ∈ Finset.univ.erase 0, a0 k, hAK, hAK1, ?_⟩
    rw [hvalK, hvalK1, ← hd_eq, hσ_eq, heq0]
  have hd₀_pos : 0 < d₀ := by
    rcases hd₀.eq_or_lt with h0 | hpos
    · rw [← h0] at heq3_d₀
      exact (not_eq3_zero u C hS hK hAbar heq3_d₀).elim
    · exact hpos
  have hd₀_eq : d₀ = dstar := by
    have h1 := huniq d₀ ⟨hd₀_pos, heq3_d₀⟩
    have h2 := huniq dstar ⟨hdstar_pos, hdstar_eq3⟩
    linarith
  intro k
  exact (hsym k 0).trans hd₀_eq
