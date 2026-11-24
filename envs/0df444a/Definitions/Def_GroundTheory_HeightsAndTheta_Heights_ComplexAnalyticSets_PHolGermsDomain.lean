-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:29.028215+00:00
-- url     : https://prove2.me/theorems/4c1fe10f-9f8c-432a-9347-a4d16b29375a
-- title:
--   PHol Germs Domain
-- statement:
--   Definitions and structural lemmas for PHol Germs Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolGermsDomain.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric
noncomputable section
def HolGermsDomain.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsDomain (holGerms w)
theorem eventually_zero_or_of_mul_eventually_zero {σ : Type} [Fintype σ] {w : σ → ℂ}
    {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w)
    (hfg : ∀ᶠ z in 𝓝 w, f z * g z = 0) :
    (∀ᶠ z in 𝓝 w, f z = 0) ∨ ∀ᶠ z in 𝓝 w, g z = 0 := by
  obtain ⟨r₁, hr₁, hf'⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hg'⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨r₃, hr₃, hfg'⟩ := Metric.eventually_nhds_iff_ball.1 hfg
  have hr : 0 < min r₁ (min r₂ r₃) := lt_min hr₁ (lt_min hr₂ hr₃)
  have hU1 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₁ := ball_subset_ball (min_le_left _ _)
  have hU2 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₂ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hU3 : ball w (min r₁ (min r₂ r₃)) ⊆ ball w r₃ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  by_cases h : ∀ z ∈ ball w (min r₁ (min r₂ r₃)), f z = 0
  · left
    filter_upwards [ball_mem_nhds w hr] with x hx
    exact h x hx
  · right
    push Not at h
    obtain ⟨z, hz, hfz⟩ := h
    have hgz : g =ᶠ[𝓝 z] 0 := by
      have h1 : ∀ᶠ x in 𝓝 z, f x ≠ 0 := (hf' z (hU1 hz)).continuousAt.eventually_ne hfz
      have h2 : ∀ᶠ x in 𝓝 z, x ∈ ball w (min r₁ (min r₂ r₃)) := isOpen_ball.mem_nhds hz
      filter_upwards [h1, h2] with x hx1 hx2
      have h3 := hfg' x (hU3 hx2)
      simpa [hx1] using h3
    have hEq := (hg'.mono hU2).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball w _).isPreconnected hz hgz
    filter_upwards [ball_mem_nhds w hr] with x hx
    simpa using hEq hx
theorem HolGermsDomain.proof : HolGermsDomain.Statement := by
  intro σ _ w
  have : NoZeroDivisors (holGerms w) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    have h1 : ∀ᶠ z in 𝓝 w, f z * g z = 0 := (Germ.coe_eq.1 h0).mono fun z hz => by simpa using hz
    rcases eventually_zero_or_of_mul_eventually_zero hf hg h1 with h | h
    · left
      apply Subtype.ext
      change (a : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      rw [← hfa]
      exact Germ.coe_eq.2 (h.mono fun z hz => by simpa using hz)
    · right
      apply Subtype.ext
      change (b : Germ (𝓝 w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      rw [← hgb]
      exact Germ.coe_eq.2 (h.mono fun z hz => by simpa using hz)
  exact NoZeroDivisors.to_isDomain _
instance holGerms_isDomain {σ : Type} [Fintype σ] (w : σ → ℂ) : IsDomain (holGerms w) :=
  HolGermsDomain.proof σ w
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


