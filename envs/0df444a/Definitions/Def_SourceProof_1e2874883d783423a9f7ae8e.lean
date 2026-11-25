-- Prove2me | Definitions.Def_SourceProof_1e2874883d783423a9f7ae8e
-- name    : SourceProof_1e2874883d783423a9f7ae8e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:32.824866+00:00
-- url     : https://prove2.me/theorems/df1e086a-0d9f-59ab-a588-535bd6e39069
-- title:
--   StochLean source theorem: ProbabilityTheory.isPredictableStoppingTime_restricted_of_eventual_events

import Definitions.Def_SourceProof_0a28bfe8bb403463b49115a5
import Definitions.Def_SourceProof_0f898d148d7720c2d3ef9d37
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_5f682bdcd01340f68959a08f
import Definitions.Def_SourceProof_7a200839927b2232bfb83618
import Definitions.Def_SourceProof_94fc4811fced36c599242ba4
import Definitions.Def_SourceProof_cf4eebeacf06bc4488688354

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Restricting announcing data using eventually correct events

Tail infima of event-restricted announcing terms, capped by integers, announce
the restricted target. Initial completeness repairs the exceptional event by
zero; right continuity makes the countable tail infima stopping times.
In particular, infinity is still announced by finite terms outside the event.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {τ : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_1e2874883d783423a9f7ae8e
    (hσ : ∀ n, IsStoppingTime F (σ n)) (hmono : ∀ ω, Monotone (fun n ↦ σ n ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)))
    (hτ : IsStoppingTime F τ) (hF : F.IsUsual P)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) {B : ℕ → Set Ω}
    (hstrict : ∀ n ω, ω ∈ A → 0 < τ ω → σ n ω < τ ω)
    (hB : ∀ n, MeasurableSet[(hσ n).measurableSpace] (B n))
    (hBA : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ B n ↔ ω ∈ A)) :
    IsPredictableStoppingTime F (restrictedStoppingTime τ A) P := by
  classical
  let : F.IsRightContinuous := (_root_.Prove2MeSourceProof.h_94fc4811fced36c599242ba4 hF)
  let E : Set Ω := {ω | Tendsto (fun n ↦ σ n ω) atTop (𝓝 (τ ω)) ∧
    ∀ᶠ n in atTop, (ω ∈ B n ↔ ω ∈ A)}
  have hEae : ∀ᵐ ω ∂P, ω ∈ E := hlim.and hBA
  have hE : MeasurableSet[F 0] E := by
    have hEc : MeasurableSet[F 0] Eᶜ := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) _ (ae_iff.mp hEae)
    simpa only [compl_compl] using hEc.compl
  let η (n : ℕ) (ω : Ω) := ⨅ k ≥ n, ProbabilityTheory.restrictedStoppingTime (σ k) (B k) ω
  let π (n : ℕ) : Ω → WithTop ℝ≥0 :=
    E.piecewise (fun ω ↦ Min.min (η n ω) ((n : ℝ≥0) : WithTop ℝ≥0)) (fun _ ↦ 0)
  have hη (n : ℕ) : IsStoppingTime F (η n) := by
    exact IsStoppingTime.biInf (s := Ici n) (Set.to_countable _)
      (fun k _ ↦ (_root_.Prove2MeSourceProof.h_cf4eebeacf06bc4488688354 (hσ k)) (hB k))
  have hηmono (ω : Ω) : Monotone (fun n ↦ η n ω) := by
    intro n m hnm
    exact le_iInf₂ fun k hk ↦ iInf₂_le_of_le k (hnm.trans hk) le_rfl
  have hηlower (n : ℕ) (ω : Ω) : σ n ω ≤ η n ω := by
    exact le_iInf₂ fun k hk ↦ (hmono ω hk).trans
      (_root_.Prove2MeSourceProof.h_0f898d148d7720c2d3ef9d37 (σ k) (B k) ω)
  have hchoose {ω : Ω} (hω : ω ∈ E) (hωA : ω ∈ A) (n : ℕ) :
      ∃ k, n ≤ k ∧ ω ∈ B k := by
    have hb : ∀ᶠ k in atTop, ω ∈ B k := hω.2.mono fun _ hk ↦ hk.mpr hωA
    exact ((eventually_ge_atTop n).and hb).exists
  have hηupper {ω : Ω} (hω : ω ∈ E) (hωA : ω ∈ A) (n : ℕ) : η n ω ≤ τ ω := by
    obtain ⟨k, hkn, hk⟩ := hchoose hω hωA n
    calc
      _ ≤ ProbabilityTheory.restrictedStoppingTime (σ k) (B k) ω := iInf₂_le _ hkn
      _ = σ k ω := _root_.Prove2MeSourceProof.h_0a28bfe8bb403463b49115a5 (σ k) hk
      _ ≤ τ ω := (hmono ω).ge_of_tendsto hω.1 k
  have hπ (n : ℕ) : IsStoppingTime F (π n) :=
    ((hη n).min_const n).piecewise_of_le (isStoppingTime_const F 0)
      (fun _ ↦ bot_le) (fun _ ↦ bot_le) hE
  refine ⟨(_root_.Prove2MeSourceProof.h_cf4eebeacf06bc4488688354 hτ) hA, π, hπ, fun ω n m hnm ↦ ?_,
    fun n ω ht ↦ ?_, ?_⟩
  · by_cases hω : ω ∈ E
    · simp only [π, Set.piecewise, if_pos hω]
      exact min_le_min (hηmono ω hnm) (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hnm))
    · simp only [π, Set.piecewise, if_neg hω, le_refl]
  · by_cases hω : ω ∈ E
    · simp only [π, Set.piecewise, if_pos hω]
      by_cases hωA : ω ∈ A
      · rw [_root_.Prove2MeSourceProof.h_0a28bfe8bb403463b49115a5 τ hωA] at ht ⊢
        obtain ⟨k, hkn, hk⟩ := hchoose hω hωA n
        calc
          _ ≤ η n ω := min_le_left _ _
          _ ≤ ProbabilityTheory.restrictedStoppingTime (σ k) (B k) ω := iInf₂_le _ hkn
          _ = σ k ω := _root_.Prove2MeSourceProof.h_0a28bfe8bb403463b49115a5 (σ k) hk
          _ < τ ω := hstrict k ω hωA ht
      · rw [_root_.Prove2MeSourceProof.h_7a200839927b2232bfb83618 τ hωA]
        exact (min_le_right _ _).trans_lt (WithTop.coe_lt_top _)
    · simpa only [π, Set.piecewise, if_neg hω] using ht
  · filter_upwards [hEae] with ω hω
    have hn : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0) : WithTop ℝ≥0)) atTop (𝓝 ⊤) :=
      WithTop.tendsto_coe_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))
    by_cases hωA : ω ∈ A
    · rw [_root_.Prove2MeSourceProof.h_0a28bfe8bb403463b49115a5 τ hωA]
      have hlim : Tendsto (fun n ↦ η n ω) atTop (𝓝 (τ ω)) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le hω.1 tendsto_const_nhds
          (fun n ↦ hηlower n ω) (fun n ↦ hηupper hω hωA n)
      simpa only [π, Set.piecewise, if_pos hω, min_top_right] using hlim.min hn
    · rw [_root_.Prove2MeSourceProof.h_7a200839927b2232bfb83618 τ hωA]
      have hb : ∀ᶠ k in atTop, ω ∉ B k := hω.2.mono fun _ hk ↦ mt hk.mp hωA
      obtain ⟨N, hN⟩ := eventually_atTop.mp hb
      apply hn.congr'
      filter_upwards [eventually_ge_atTop N] with n hnN
      have he : η n ω = ⊤ := by
        apply top_unique
        exact le_iInf₂ fun k hk ↦ le_of_eq
          (_root_.Prove2MeSourceProof.h_7a200839927b2232bfb83618 (σ k) (hN k (hnN.trans hk))).symm
      simp only [π, Set.piecewise, if_pos hω, he, min_top_left]
end ProbabilityTheory


