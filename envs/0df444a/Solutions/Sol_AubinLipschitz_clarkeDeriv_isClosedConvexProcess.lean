-- Prove2me | solution 1 for AubinLipschitz.clarkeDeriv_isClosedConvexProcess
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:16:38.923376+00:00
-- url     : https://prove2.me/submissions/7ee5db2d-e697-46fc-80a9-5a5e92ee4760

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_IsClosedConvexProcess

set_option autoImplicit false

namespace AubinLipschitz.ClarkeConeProof

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem clarkeCone_zero_mem (K : Set E) (z₀ : E) : (0 : E) ∈ clarkeCone K z₀ := by
  intro ε hε
  exact ⟨1, one_pos, 1, one_pos, fun x hx h _ _ =>
    ⟨0, mem_closedBall_self hε.le, by simpa using hx.1⟩⟩

theorem clarkeCone_smul_mem (K : Set E) (z₀ : E) {v : E} (hv : v ∈ clarkeCone K z₀)
    {c : ℝ} (hc : 0 < c) : c • v ∈ clarkeCone K z₀ := by
  intro ε hε
  obtain ⟨α, hα, β, hβ, H⟩ := hv (ε / c) (div_pos hε hc)
  refine ⟨α, hα, β / c, div_pos hβ hc, fun x hx h hh hhβ => ?_⟩
  have hhc : h * c ≤ β := by rwa [le_div_iff₀ hc] at hhβ
  obtain ⟨u, hu, hxu⟩ := H x hx (h * c) (mul_pos hh hc) hhc
  refine ⟨c • u, ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm] at hu ⊢
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc.le]
    calc c * ‖u - v‖ ≤ c * (ε / c) := mul_le_mul_of_nonneg_left hu hc.le
      _ = ε := by field_simp
  · rwa [smul_smul]

theorem clarkeCone_add_mem (K : Set E) (z₀ : E) {v w : E} (hv : v ∈ clarkeCone K z₀)
    (hw : w ∈ clarkeCone K z₀) : v + w ∈ clarkeCone K z₀ := by
  intro ε hε
  obtain ⟨αv, hαv, βv, hβv, Hv⟩ := hv (ε / 2) (half_pos hε)
  obtain ⟨αw, hαw, βw, hβw, Hw⟩ := hw (ε / 2) (half_pos hε)
  have hM0 : 0 < ‖v‖ + ε / 2 + 1 := by positivity
  refine ⟨min αv (αw / 2), by positivity, min (min βv βw) (αw / 2 / (‖v‖ + ε / 2 + 1)),
    by positivity, fun x hx h hh hhβ => ?_⟩
  have hhv : h ≤ βv := hhβ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhw : h ≤ βw := hhβ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhM : h * (‖v‖ + ε / 2 + 1) ≤ αw / 2 := by
    have := hhβ.trans (min_le_right _ _)
    rwa [le_div_iff₀ hM0] at this
  have hxz : ‖x - z₀‖ ≤ min αv (αw / 2) := by
    have := hx.2
    rwa [mem_closedBall, dist_eq_norm] at this
  have hxv : x ∈ K ∩ closedBall z₀ αv :=
    ⟨hx.1, by rw [mem_closedBall, dist_eq_norm]; exact hxz.trans (min_le_left _ _)⟩
  obtain ⟨u, hu, hxu⟩ := Hv x hxv h hh hhv
  rw [mem_closedBall, dist_eq_norm] at hu
  have hu' : ‖u‖ ≤ ‖v‖ + ε / 2 + 1 := by
    calc ‖u‖ = ‖(u - v) + v‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - v‖ + ‖v‖ := norm_add_le _ _
      _ ≤ ‖v‖ + ε / 2 + 1 := by linarith
  have hx' : x + h • u ∈ K ∩ closedBall z₀ αw := by
    refine ⟨hxu, ?_⟩
    rw [mem_closedBall, dist_eq_norm]
    have hx2 : ‖x - z₀‖ ≤ αw / 2 := hxz.trans (min_le_right _ _)
    calc ‖x + h • u - z₀‖ = ‖(x - z₀) + h • u‖ := by congr 1; abel
      _ ≤ ‖x - z₀‖ + ‖h • u‖ := norm_add_le _ _
      _ = ‖x - z₀‖ + h * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hh.le]
      _ ≤ αw / 2 + h * (‖v‖ + ε / 2 + 1) := by
          have := mul_le_mul_of_nonneg_left hu' hh.le
          linarith
      _ ≤ αw := by linarith
  obtain ⟨u', hu'', hxu'⟩ := Hw (x + h • u) hx' h hh hhw
  refine ⟨u + u', ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm] at hu'' ⊢
    calc ‖u + u' - (v + w)‖ = ‖(u - v) + (u' - w)‖ := by congr 1; abel
      _ ≤ ‖u - v‖ + ‖u' - w‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add hu hu''
      _ = ε := by ring
  · rw [smul_add, ← add_assoc]
    exact hxu'

theorem clarkeCone_isClosed (K : Set E) (z₀ : E) : IsClosed (clarkeCone K z₀) := by
  refine isClosed_of_closure_subset fun v hv => ?_
  intro ε hε
  obtain ⟨v', hv'C, hvv'⟩ := Metric.mem_closure_iff.mp hv (ε / 2) (half_pos hε)
  obtain ⟨α, hα, β, hβ, H⟩ := hv'C (ε / 2) (half_pos hε)
  refine ⟨α, hα, β, hβ, fun x hx h hh hhβ => ?_⟩
  obtain ⟨u, hu, hxu⟩ := H x hx h hh hhβ
  refine ⟨u, ?_, hxu⟩
  rw [mem_closedBall] at hu ⊢
  calc dist u v ≤ dist u v' + dist v' v := dist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hu (by rw [dist_comm]; exact hvv'.le)
    _ = ε := by ring

theorem clarkeCone_convex (K : Set E) (z₀ : E) : Convex ℝ (clarkeCone K z₀) := by
  intro v hv w hw a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hw
  rcases hb.eq_or_lt with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hv
  exact clarkeCone_add_mem K z₀ (clarkeCone_smul_mem K z₀ hv ha')
    (clarkeCone_smul_mem K z₀ hw hb')

end AubinLipschitz.ClarkeConeProof

open AubinLipschitz AubinLipschitz.ClarkeConeProof

set_option linter.unusedVariables false in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Set Y) (x₀ : X) (y₀ : Y) (h₀ : y₀ ∈ F x₀) :
    IsClosedConvexProcess (clarkeDeriv F x₀ y₀) := by
  have hg : graphOf (clarkeDeriv F x₀ y₀) = clarkeCone (graphOf F) (x₀, y₀) := by
    ext ⟨u, v⟩
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hg]; exact clarkeCone_isClosed _ _
  · rw [hg]; exact clarkeCone_convex _ _
  · rw [hg]; exact ⟨0, clarkeCone_zero_mem _ _⟩
  · intro c hc z hz
    rw [hg] at hz ⊢
    exact clarkeCone_smul_mem _ _ hz hc
