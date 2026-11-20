-- Prove2me | Definitions.Def_SourceProof_a05b300f3542b3c3884120f0
-- name    : SourceProof_a05b300f3542b3c3884120f0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:01:17.564465+00:00
-- url     : https://prove2.me/theorems/cce2af7b-2c80-4685-8c86-bfead8ae9785
-- title:
--   LevyStochCalc source module: SourceProof_a05b300f3542b3c3884120f0
-- statement:
--   The original source theorem `ProbabilityTheory.mul_measureReal_exists_lt_le` comes from the `BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F001

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

variable {F : Finset ι} {t : ι} {k l : ℕ}

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name


theorem _root_.Prove2MeSourceProof.h_a05b300f3542b3c3884120f0 [IsFiniteMeasure μ]
    {g : ι → Ω → ℝ} (hg : StronglyAdapted 𝓕 g) (hgint : ∀ s, Integrable (g s) μ)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) {K : ℝ}
    (hK : ∀ W : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) →
      ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ ≤ K) :
    lam * μ.real {ω | ∃ k ≤ n, lam < g (idx k) ω}
      ≤ K + ∫ ω, |g (idx 0) ω| ∂μ + ∫ ω, |g (idx n) ω| ∂μ := by
  set f : ℕ → Ω → ℝ := fun k ω ↦ g (idx k) ω with hf
  set W : ℕ → Ω → ℝ := fun k ↦ {ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 with hW
  have hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1 := by
    intro k _ ω
    by_cases h : ω ∈ {ω' | ∀ j ≤ k, f j ω' ≤ lam}
    · exact Or.inr (by rw [hW]; simp [Set.indicator_of_mem h])
    · exact Or.inl (by rw [hW]; simp [Set.indicator_of_notMem h])
  have hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k) := by
    intro k _
    have hset : MeasurableSet[𝓕 (idx k)] {ω' | ∀ j ≤ k, f j ω' ≤ lam} := by
      have : {ω' | ∀ j ≤ k, f j ω' ≤ lam} = ⋂ j ∈ Iic k, f j ⁻¹' Set.Iic lam := by
        ext ω'
        simp [Set.mem_iInter]
      rw [this]
      refine MeasurableSet.biInter (Iic k).countable_toSet fun j hj ↦ ?_
      have hj' : j ≤ k := mem_Iic.1 hj
      exact (𝓕.mono (hidx hj')) _ ((hg (idx j)).measurable measurableSet_Iic)
    exact (measurable_const.indicator hset)
  have hWb : ∀ k, k < n → ∀ ω, ‖W k ω‖ ≤ 1 := by
    intro k hk ω
    rcases hW01 k hk ω with h | h <;> simp [h]
  -- the stopped value
  set tau : Ω → ℕ := fun ω ↦ hittingBtwn f (Set.Ioi lam) 0 n ω with htau
  set ftau : Ω → ℝ := fun ω ↦ f (tau ω) ω with hftau
  have htel : ∀ ω, ftau ω = f 0 ω
      + ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) := by
    intro ω
    rw [hftau, htau]
    have hterm k : W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
        = ({ω' | ∀ j ≤ k, f j ω' ≤ lam}.indicator 1 ω : ℝ) * (f (k + 1) ω - f k ω) := rfl
    simp_rw [hterm]
    rw [ProbabilityTheory.sum_indicator_mul_sub_eq_stopped f lam n ω]
    ring
  have hint_sum : Integrable
      (fun ω ↦ ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
    ProbabilityTheory.integrable_sum_weight_increments hgint
      (fun k hk ↦ ((hWmeas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable) hWb
  have hint_ftau : Integrable ftau μ := by
    have : ftau = fun ω ↦ f 0 ω
        + ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) := funext htel
    rw [this]
    exact (hgint _).add hint_sum
  -- the event
  set H : Set Ω := {ω | ∃ k ≤ n, lam < g (idx k) ω} with hH
  have hHmeas : MeasurableSet H := by
    have : H = ⋃ k ∈ Iic n, (g (idx k)) ⁻¹' Set.Ioi lam := by ext; simp [hH]
    rw [this]
    exact MeasurableSet.biUnion (Iic n).countable_toSet fun k _ ↦
      (𝓕.le _) _ ((hg (idx k)).measurable measurableSet_Ioi)
  -- on `H`, the stopped value exceeds `lam`
  have hHval : ∀ ω ∈ H, lam < ftau ω := by
    intro ω hω
    obtain ⟨k, hk, hkval⟩ := hω
    have hexists : ∃ j ∈ Set.Icc 0 n, f j ω ∈ Set.Ioi lam := ⟨k, ⟨Nat.zero_le k, hk⟩, hkval⟩
    exact hittingBtwn_mem_set hexists
  -- off `H`, the stopped value is the terminal value
  have hHcval : ∀ ω ∉ H, ftau ω = f n ω := by
    intro ω hω
    have hno : ∀ j, j ≤ n → f j ω ≤ lam := by
      intro j hj
      by_contra hlt
      exact hω ⟨j, hj, not_le.1 hlt⟩
    have h1 : tau ω = n := by
      refine le_antisymm (hittingBtwn_le ω) (not_lt.1 fun hlt ↦ ?_)
      obtain ⟨j, hj, hjs⟩ := (hittingBtwn_lt_iff n le_rfl).1 hlt
      exact absurd hjs (not_lt.2 (hno j hj.2.le))
    change f (tau ω) ω = f n ω
    rw [h1]
  -- assemble
  have hsplit : ∫ ω, ftau ω ∂μ = (∫ ω in H, ftau ω ∂μ) + ∫ ω in Hᶜ, ftau ω ∂μ :=
    (integral_add_compl hHmeas hint_ftau).symm
  have hlower : lam * μ.real H ≤ ∫ ω in H, ftau ω ∂μ := by
    calc lam * μ.real H = ∫ _ in H, lam ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω in H, ftau ω ∂μ := by
          refine setIntegral_mono_on (integrable_const lam).integrableOn
            hint_ftau.integrableOn hHmeas fun ω hω ↦ (hHval ω hω).le
  have hcompl : -(∫ ω, |g (idx n) ω| ∂μ) ≤ ∫ ω in Hᶜ, ftau ω ∂μ := by
    have heq : ∫ ω in Hᶜ, ftau ω ∂μ = ∫ ω in Hᶜ, f n ω ∂μ :=
      setIntegral_congr_fun hHmeas.compl fun ω hω ↦ hHcval ω hω
    rw [heq, neg_le]
    calc -∫ ω in Hᶜ, f n ω ∂μ ≤ |∫ ω in Hᶜ, f n ω ∂μ| := neg_le_abs _
      _ ≤ ∫ ω in Hᶜ, |f n ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |g (idx n) ω| ∂μ :=
          setIntegral_le_integral (hgint _).abs (ae_of_all _ fun ω ↦ abs_nonneg _)
  have htotal : ∫ ω, ftau ω ∂μ ≤ K + ∫ ω, |g (idx 0) ω| ∂μ := by
    have : ∫ ω, ftau ω ∂μ = (∫ ω, f 0 ω ∂μ)
        + ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ := by
      rw [← integral_add (hgint _) hint_sum]
      exact integral_congr_ae (ae_of_all _ htel)
    rw [this]
    have h0 : ∫ ω, f 0 ω ∂μ ≤ ∫ ω, |g (idx 0) ω| ∂μ :=
      integral_mono (hgint _) (hgint _).abs fun ω ↦ le_abs_self _
    have hsum := hK W hW01 hWmeas
    linarith
  linarith [hsplit, hlower, hcompl, htotal]
end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

variable [OrderBot ι]

end CountableEvents

end ProbabilityTheory


