-- Prove2me | solution 1 for AnosovPlugs.contDiff_continuousMap_comp_left
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T09:37:13.6961+00:00
-- url     : https://prove2.me/submissions/1ab546ce-4ec8-44a9-b624-3d89014565ee

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set AnosovPlugs

/-- Pointwise application `C(X, E →L F) × C(X, E) → C(X, F)` as a bounded bilinear map. -/
noncomputable def nm_Phi (X : Type) [TopologicalSpace X] [CompactSpace X]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    C(X, E →L[ℝ] F) →L[ℝ] C(X, E) →L[ℝ] C(X, F) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun (g : C(X, E →L[ℝ] F)) (h : C(X, E)) =>
        (⟨fun s => g s (h s), g.continuous.clm_apply h.continuous⟩ : C(X, F)))
      (by intros; ext; simp) (by intros; ext; simp)
      (by intros; ext; simp) (by intros; ext; simp))
    1 (by
      intro g h
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun s => ?_
      exact ((g s).le_opNorm (h s)).trans
        (mul_le_mul (g.norm_coe_le_norm s) (h.norm_coe_le_norm s) (norm_nonneg _)
          (norm_nonneg g)))

theorem nm_Phi_apply {X : Type} [TopologicalSpace X] [CompactSpace X]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : C(X, E →L[ℝ] F)) (h : C(X, E)) (s : X) :
    nm_Phi X E F g h s = g s (h s) := rfl

theorem solution
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : E → F) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (fun β : C(X, E) => (⟨v ∘ β, hv.continuous.comp β.continuous⟩ : C(X, F))) := by
  have hDc : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hd : Differentiable ℝ v := hv.differentiable one_ne_zero
  let Dv : C(E, E →L[ℝ] F) := ⟨fderiv ℝ v, hDc⟩
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun β => nm_Phi X E F (Dv.comp β),
    (nm_Phi X E F).continuous.comp (ContinuousMap.continuous_postcomp Dv), fun β₀ => ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδc⟩ := Metric.mem_uniformity_dist.1
    ((isCompact_range β₀.continuous).uniformContinuousAt_of_continuousAt (fderiv ℝ v)
      (fun a _ => hDc.continuousAt) (Metric.dist_mem_uniformity hc))
  filter_upwards [Metric.ball_mem_nhds (0 : C(X, E)) hδ] with h hh
  rw [mem_ball_zero_iff] at hh
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun s => ?_
  have hs : ‖h s‖ < δ := (h.norm_coe_le_norm s).trans_lt hh
  have key : ‖v (β₀ s + h s) - v (β₀ s) - fderiv ℝ v (β₀ s) (β₀ s + h s - β₀ s)‖ ≤
      c * ‖β₀ s + h s - β₀ s‖ := by
    refine Convex.norm_image_sub_le_of_norm_fderiv_le' (s := Metric.ball (β₀ s) δ)
      (fun x _ => hd x) ?_ (convex_ball _ _) (Metric.mem_ball_self hδ) (by simpa using hs)
    intro x hx
    have h1 : dist (β₀ s) x < δ := by rw [dist_comm]; exact hx
    have h2 : dist (fderiv ℝ v (β₀ s)) (fderiv ℝ v x) < c := hδc h1 ⟨s, rfl⟩
    rw [dist_eq_norm, norm_sub_rev] at h2
    exact h2.le
  simp only [add_sub_cancel_left] at key
  calc _ = ‖v (β₀ s + h s) - v (β₀ s) - fderiv ℝ v (β₀ s) (h s)‖ := rfl
    _ ≤ c * ‖h s‖ := key
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_left (h.norm_coe_le_norm s) hc.le
