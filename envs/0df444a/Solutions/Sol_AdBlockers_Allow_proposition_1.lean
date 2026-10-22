-- Prove2me | solution 1 for AdBlockers.Allow.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:47:57.245724+00:00
-- url     : https://prove2.me/submissions/10bc95e2-a087-4057-a6fc-cc802924ccb3

import Mathlib
import Definitions.Def_AdBlockers_Allow_Model
import Theorems.Thm_AdBlockers_Allow_case_1_ads_ads
import Theorems.Thm_AdBlockers_Allow_case_2_fee_fee
import Theorems.Thm_AdBlockers_Allow_case_5_allow_allow
import Theorems.Thm_AdBlockers_Allow_case_8_ban_allow
import Theorems.Thm_AdBlockers_Allow_case_9_fee_allow
import Theorems.Thm_AdBlockers_Allow_conditions_equivalence
import Theorems.Thm_AdBlockers_Allow_g_strictAntiOn
import Theorems.Thm_AdBlockers_Allow_moreover_equivalences

namespace AdBlockers.Allow

lemma ab_swap {lam μ β γ : ℝ} {s₁ s₂ : Plan} {d₁ d₂ : ℝ}
    (h : IsStage2NE lam μ β γ s₁ s₂ d₁ d₂) : IsStage2NE lam μ β γ s₂ s₁ d₂ d₁ := by
  obtain ⟨a, b, c, d⟩ := h
  exact ⟨b, a, d, c⟩

/-- The (Allow, Allow) equilibrium under the two conditions of p. 44. -/
lemma ab_equilibrium (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) (hγ : 0 < γ)
    (h1 : (lam + μ) * (3 * lam + 2 * μ) ^ 2 / (2 * (3 * lam + 4 * μ) ^ 2) ≤ lam / (2 * β))
    (h2 : (lam + μ * (γ / β)) / (3 * lam + 4 * μ * (γ / β)) ^ 2 ≤ lam / (3 * lam + 2 * μ) ^ 2) :
    IsEquilibrium lam μ β γ .allow .allow (1 / β) (1 / β) ∧
      rev₁ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) ∧
      rev₂ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) := by
  obtain ⟨hAA, hr1, hr2, -⟩ := case_5_allow_allow lam μ β γ hlam hβ
  obtain ⟨e₁, e₂, hBA, hBAr⟩ := case_8_ban_allow lam μ β γ hlam hμ hβ hγ h2
  obtain ⟨hFA, hFAr1, -⟩ := case_9_fee_allow lam μ β γ hlam hμ hβ
  refine ⟨⟨hAA, ?_, ?_⟩, hr1, hr2⟩
  · intro s'
    cases s' with
    | ban => exact ⟨e₁, e₂, hBA, by rw [hr1]; exact hBAr⟩
    | allow => exact ⟨1 / β, 1 / β, hAA, le_rfl⟩
    | fee => exact ⟨_, _, hFA, by rw [hFAr1, hr1]; exact h1⟩
  · intro s'
    cases s' with
    | ban => exact ⟨e₂, e₁, ab_swap hBA, by rw [hr2]; exact hBAr⟩
    | allow => exact ⟨1 / β, 1 / β, hAA, le_rfl⟩
    | fee => exact ⟨_, _, ab_swap hFA, by rw [hr2]; show rev₁ _ _ _ _ _ _ _ _ ≤ _; rw [hFAr1]; exact h1⟩

end AdBlockers.Allow

open AdBlockers.Allow

theorem solution (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β) (hγ : 0 < γ) :
    (β ≤ lam * (3 * lam + 4 * μ) ^ 2 / ((lam + μ) * (3 * lam + 2 * μ) ^ 2) →
      (lam + μ * (γ / β)) / (3 * lam + 4 * μ * (γ / β)) ^ 2 ≤ lam / (3 * lam + 2 * μ) ^ 2 →
      IsEquilibrium lam μ β γ .allow .allow (1 / β) (1 / β) ∧
        rev₁ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) ∧
        rev₂ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β)) ∧
    (2 + μ / lam ≤ γ / β → β ≤ lam / (lam + μ) →
      IsEquilibrium lam μ β γ .allow .allow (1 / β) (1 / β) ∧
        rev₁ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) ∧
        rev₂ lam μ β γ .allow .allow (1 / β) (1 / β) = lam / (2 * β) ∧
        (∀ a : ℝ, IsStage2NE lam μ β γ BenchPlan.ads.toPlan BenchPlan.ads.toPlan a a →
          rev₁ lam μ β γ BenchPlan.ads.toPlan BenchPlan.ads.toPlan a a ≤ lam / (2 * β) ∧
          rev₂ lam μ β γ BenchPlan.ads.toPlan BenchPlan.ads.toPlan a a ≤ lam / (2 * β)) ∧
        (∀ p : ℝ, IsStage2NE lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan p p →
          rev₁ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan p p ≤ lam / (2 * β) ∧
          rev₂ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan p p ≤ lam / (2 * β))) := by
  obtain ⟨ce1, -⟩ := conditions_equivalence lam μ β γ hlam hμ hβ hγ
  obtain ⟨me1, me2⟩ := moreover_equivalences lam μ β γ hlam hμ hβ hγ
  refine ⟨fun hb hg => ab_equilibrium lam μ β γ hlam hμ hβ hγ (ce1.2 hb) hg, ?_⟩
  intro hr hb
  -- first condition from the second set
  have hb' : β ≤ lam * (3 * lam + 4 * μ) ^ 2 / ((lam + μ) * (3 * lam + 2 * μ) ^ 2) := by
    refine le_trans hb ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (3 * lam + 2 * μ) ^ 2 ≤ (3 * lam + 4 * μ) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    have hl : 0 ≤ lam * (lam + μ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hl]
  -- second condition from monotonicity of g
  have hx0 : (0 : ℝ) ≤ 2 + μ / lam := by positivity
  have hg := (g_strictAntiOn lam μ hlam hμ).antitoneOn (Set.mem_Ici.2 hx0)
    (Set.mem_Ici.2 (le_trans hx0 hr)) hr
  try simp only at hg
  have hgx : (lam + μ * (2 + μ / lam)) / (3 * lam + 4 * μ * (2 + μ / lam)) ^ 2 ≤
      lam / (3 * lam + 2 * μ) ^ 2 := by
    have e1 : lam + μ * (2 + μ / lam) = (lam + μ) ^ 2 / lam := by field_simp; ring
    have e2 : 3 * lam + 4 * μ * (2 + μ / lam) = (3 * lam + 2 * μ) * (lam + 2 * μ) / lam := by
      field_simp; ring
    have e3 : (lam + μ) ^ 2 / lam / ((3 * lam + 2 * μ) * (lam + 2 * μ) / lam) ^ 2 =
        lam * (lam + μ) ^ 2 / ((3 * lam + 2 * μ) * (lam + 2 * μ)) ^ 2 := by
      field_simp
    rw [e1, e2, e3, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (lam + μ) ^ 2 ≤ (lam + 2 * μ) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    have hp : 0 ≤ lam * (3 * lam + 2 * μ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left this hp
    nlinarith
  obtain ⟨hE, hr1, hr2⟩ := ab_equilibrium lam μ β γ hlam hμ hβ hγ (ce1.2 hb') (le_trans hg hgx)
  refine ⟨hE, hr1, hr2, ?_, ?_⟩
  · intro a ha
    obtain ⟨-, h1, h2⟩ := case_1_ads_ads lam μ β γ hlam hμ hβ hγ a ha
    rw [h1, h2]; exact ⟨me1.2 hr, me1.2 hr⟩
  · intro p hp
    obtain ⟨-, h1, h2, huniq⟩ := case_2_fee_fee lam μ β γ hlam hμ
    obtain ⟨rfl, -⟩ := huniq p p hp
    rw [h1, h2]; exact ⟨me2.2 hb, me2.2 hb⟩
