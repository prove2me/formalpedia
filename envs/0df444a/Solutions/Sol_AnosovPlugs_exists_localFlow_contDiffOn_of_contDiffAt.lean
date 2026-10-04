-- Prove2me | solution 1 for AnosovPlugs.exists_localFlow_contDiffOn_of_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:37:14.99386+00:00
-- url     : https://prove2.me/submissions/94783424-1527-49a1-bd46-4e670304252f

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_exists_flow_contDiffOn_of_lipschitz

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-- A bump function times `v` is a globally `C¹`, globally Lipschitz field that equals `v`
on a closed ball around `z₀`. -/
theorem lc_cutoff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {v : E → E} {z₀ : E} (hv : ContDiffAt ℝ 1 v z₀) :
    ∃ r > (0 : ℝ), ∃ vt : E → E, ContDiff ℝ 1 vt ∧ (∃ K, LipschitzWith K vt) ∧
      ∀ z ∈ Metric.closedBall z₀ r, vt z = v z := by
  obtain ⟨R, hR, hRv⟩ := Metric.eventually_nhds_iff_ball.mp (hv.eventually (by simp))
  let f : ContDiffBump z₀ := ⟨R / 3, R / 2, by positivity, by linarith⟩
  set vt : E → E := fun z => f z • v z with hvt_def
  have hC : ContDiff ℝ 1 vt := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Metric.ball z₀ R
    · exact f.contDiffAt.smul (hRv y hy)
    · have hy' : y ∉ tsupport f := by
        rw [f.tsupport_eq]
        intro hc
        apply hy
        rw [Metric.mem_ball]
        have := Metric.mem_closedBall.mp hc
        have h2 : f.rOut = R / 2 := rfl
        linarith
      have hev : f =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy'
      have hev' : vt =ᶠ[𝓝 y] fun _ => (0 : E) := by
        filter_upwards [hev] with z hz
        simp [hvt_def, hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev'
  have hcs : HasCompactSupport vt := f.hasCompactSupport.smul_right
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hC (by simp)
  refine ⟨R / 3, by positivity, vt, hC, ⟨K, hK⟩, fun z hz => ?_⟩
  have h1 : f z = 1 := f.one_of_mem_closedBall hz
  simp [hvt_def, h1]

open Metric

theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {v : E → E} {z₀ : E} (hv : ContDiffAt ℝ 1 v z₀) {G : Set E} (hG : IsOpen G) (hz₀ : z₀ ∈ G) :
    ∃ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∃ αE : E × ℝ → E,
      (∀ z ∈ Metric.ball z₀ ρ, αE (z, 0) = z ∧ ∀ t ∈ Icc (-ε) ε,
        HasDerivAt (fun s => αE (z, s)) (v (αE (z, t))) t ∧ αE (z, t) ∈ G) ∧
      ContDiffOn ℝ 1 αE (Metric.ball z₀ ρ ×ˢ Ioo (-ε) ε) ∧
      (∀ z ∈ Metric.ball z₀ ρ, ∀ h : ℝ, |h| ≤ ε → ∀ f : ℝ → E, f 0 = z →
        (∀ τ ∈ uIcc 0 h, HasDerivWithinAt f (v (f τ)) (uIcc 0 h) τ) →
        (∀ τ ∈ uIcc 0 h, f τ ∈ Metric.ball z₀ ρ) → ∀ τ ∈ uIcc 0 h, f τ = αE (z, τ)) := by
  obtain ⟨r, hr, vt, hvt, ⟨K, hK⟩, heq⟩ := lc_cutoff hv
  obtain ⟨ε, hε, α₂, h0, hd, hC⟩ := AnosovPlugs.exists_flow_contDiffOn_of_lipschitz vt hvt K hK
  set αE : E × ℝ → E := fun p => α₂ p.1 p.2 with hαE
  have hKv : LipschitzOnWith K v (closedBall z₀ r) := fun x hx y hy => by
    rw [← heq x hx, ← heq y hy]; exact hK x y
  set G' := G ∩ ball z₀ r with hG'
  have hG'o : IsOpen G' := hG.inter isOpen_ball
  have hz₀G' : z₀ ∈ G' := ⟨hz₀, mem_ball_self hr⟩
  have h00 : αE (z₀, 0) = z₀ := h0 z₀
  have hcont : ContinuousAt αE (z₀, 0) :=
    hC.continuousOn.continuousAt (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds (by linarith) hε))
  have hpre : αE ⁻¹' G' ∈ 𝓝 (z₀, (0 : ℝ)) :=
    hcont.preimage_mem_nhds (by rw [h00]; exact hG'o.mem_nhds hz₀G')
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  rw [← ball_prod_same] at hδsub
  refine ⟨min (δ / 2) (ε / 2), lt_min (by linarith) (by linarith), min δ r,
    lt_min hδ hr, αE, ?_⟩
  have hε1 : min (δ / 2) (ε / 2) ≤ δ / 2 := min_le_left _ _
  have hε2 : min (δ / 2) (ε / 2) ≤ ε / 2 := min_le_right _ _
  have hρ1 : min δ r ≤ δ := min_le_left _ _
  have hρ2 : min δ r ≤ r := min_le_right _ _
  have hmain : ∀ z ∈ ball z₀ (min δ r), αE (z, 0) = z ∧ ∀ t ∈ Icc (-min (δ / 2) (ε / 2))
      (min (δ / 2) (ε / 2)), HasDerivAt (fun s => αE (z, s)) (v (αE (z, t))) t ∧
        αE (z, t) ∈ G' := by
    intro z hz
    refine ⟨h0 z, fun t ht => ?_⟩
    have hG'mem : αE (z, t) ∈ G' := by
      apply hδsub
      refine ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz) hρ1), ?_⟩
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    refine ⟨?_, hG'mem⟩
    have hdt := hd z t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [heq _ (ball_subset_closedBall hG'mem.2)] at hdt
    exact hdt
  refine ⟨fun z hz => ⟨(hmain z hz).1, fun t ht => ⟨((hmain z hz).2 t ht).1,
    ((hmain z hz).2 t ht).2.1⟩⟩, ?_, ?_⟩
  · exact hC.mono (prod_mono (subset_univ _) (Ioo_subset_Ioo (by linarith) (by linarith)))
  · intro z hz h hh f hf0 hfd hfb τ hτ
    have hsub : uIcc 0 h ⊆ Icc (-min (δ / 2) (ε / 2)) (min (δ / 2) (ε / 2)) := by
      obtain ⟨hh1, hh2⟩ := abs_le.mp hh
      apply uIcc_subset_Icc
      · constructor <;> linarith
      · exact ⟨hh1, hh2⟩
    have hgd : ∀ t ∈ uIcc 0 h, HasDerivAt (fun s => αE (z, s)) (v (αE (z, t))) t :=
      fun t ht => ((hmain z hz).2 t (hsub ht)).1
    have hgs : ∀ t ∈ uIcc 0 h, αE (z, t) ∈ closedBall z₀ r := fun t ht =>
      ball_subset_closedBall ((hmain z hz).2 t (hsub ht)).2.2
    have hfs : ∀ t ∈ uIcc 0 h, f t ∈ closedBall z₀ r := fun t ht =>
      mem_closedBall.mpr (le_trans (le_of_lt (mem_ball.mp (hfb t ht))) hρ2)
    have hfc : ContinuousOn f (uIcc 0 h) := fun t ht => (hfd t ht).continuousWithinAt
    have hgc : ContinuousOn (fun s => αE (z, s)) (uIcc 0 h) := fun t ht =>
      (hgd t ht).continuousAt.continuousWithinAt
    have hfg0 : f 0 = αE (z, 0) := by rw [hf0, (hmain z hz).1]
    rcases le_or_gt 0 h with h0' | h0'
    · rw [uIcc_of_le h0'] at hτ hgd hgs hfs hfc hgc hfd
      exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => v)
        (s := fun _ => closedBall z₀ r) (K := K) (fun _ _ => hKv) hfc
        (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ht))
        (fun t ht => hfs t (Ico_subset_Icc_self ht)) hgc
        (fun t ht => (hgd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
        (fun t ht => hgs t (Ico_subset_Icc_self ht)) hfg0 hτ
    · rw [uIcc_of_ge h0'.le] at hτ hgd hgs hfs hfc hgc hfd
      exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => v)
        (s := fun _ => closedBall z₀ r) (K := K) (fun _ _ => hKv) hfc
        (fun t ht => (hfd t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ht))
        (fun t ht => hfs t (Ioc_subset_Icc_self ht)) hgc
        (fun t ht => (hgd t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
        (fun t ht => hgs t (Ioc_subset_Icc_self ht)) hfg0 hτ
