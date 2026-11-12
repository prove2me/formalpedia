-- Prove2me | solution 1 for AgreementTop736.Exact.exact_agreement_soundness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:27:07.411981+00:00
-- url     : https://prove2.me/submissions/8fb0b6ab-bdf5-4ca3-afee-d0da20e2f377

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized
import Theorems.Thm_AgreementTop736_Exact_eq5_nonpolarity_lower_bound
import Theorems.Thm_AgreementTop736_Exact_sec3_1_nonpolarity_upper_bound

section
set_option autoImplicit false
namespace AgreementTop736.Exact
open Finset Scheme

namespace Dev.Goal

lemma rho_pos {V : Type*} [Fintype V] [DecidableEq V] (S : Scheme V) (hS : S.IsValid) : 0 < S.ρ := by
  unfold Scheme.ρ
  have h1 := hS.n_pos
  have h2 := hS.n_lt_N
  have : (0:ℝ) < S.n := by exact_mod_cast h1
  have : (0:ℝ) < S.N := by exact_mod_cast (h1.trans h2)
  positivity

lemma rho_lt_one {V : Type*} [Fintype V] [DecidableEq V] (S : Scheme V) (hS : S.IsValid) : S.ρ < 1 := by
  unfold Scheme.ρ
  have h1 := hS.n_pos
  have h2 := hS.n_lt_N
  have : (0:ℝ) < S.N := by exact_mod_cast (h1.trans h2)
  rw [div_lt_one this]
  exact_mod_cast h2

end Dev.Goal

open AgreementTop736.Exact.Dev.Goal in
theorem chk_exact_agreement_soundness {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) (h2 : S.VarianceBound)
    {γ : ℝ} (hγ : 0 < γ) (h3 : S.HasConditionedGap γ) (F : Finset V → V → α) :
    (∃ g : V → α, S.IsCoordMajority F g) ∧
    ∀ g : V → α, S.IsCoordMajority F g →
      S.disagreementProb F g ≤ (8 / γ + 64 * (1 - S.ρ) / (S.ρ * γ ^ 2)) * S.rejectionProb F := by
  refine ⟨?_, ?_⟩
  · by_cases hV : Nonempty V
    · obtain ⟨v⟩ := hV
      have : Nonempty α := ⟨F ∅ v⟩
      have : ∀ x : V, ∃ s : α, ∀ t : α, S.labelFreq F x t ≤ S.labelFreq F x s := by
        intro x
        obtain ⟨s, -, hs⟩ := Finset.exists_max_image (Finset.univ : Finset α) (fun t => S.labelFreq F x t)
          Finset.univ_nonempty
        exact ⟨s, fun t => hs t (Finset.mem_univ t)⟩
      choose g hg using this
      exact ⟨g, fun x _ t => hg x t⟩
    · refine ⟨fun x => (hV ⟨x⟩).elim, fun x => (hV ⟨x⟩).elim⟩
  · intro g hg
    have hρ0 := rho_pos S hS
    have hρ1 := rho_lt_one S hS
    set ρ := S.ρ with hρ
    set a : ℝ := 8 * (1 - ρ) / (ρ * γ) with ha_def
    have hρ1' : 0 < 1 - ρ := by linarith
    have ha : 0 < a := by positivity
    have e5 := eq5_nonpolarity_lower_bound S hS h1 hγ h3 F g hg ha
    have e7 := sec3_1_nonpolarity_upper_bound S hS h2 F g ha
    set Vr := S.Vreg F g a with hVr
    set τ := S.rejectionProb F with hτ
    have hcoef : 4 * (1 - ρ) / a = ρ * γ / 2 := by
      rw [ha_def]; field_simp; ring
    rw [hcoef] at e7
    have hV : Vr ≤ 8 * τ / γ := by
      have : ρ * γ / 2 * Vr ≤ 4 * ρ * τ := by nlinarith
      rw [le_div_iff₀ hγ]
      have h' : ρ * (γ / 2 * Vr) ≤ ρ * (4 * τ) := by nlinarith
      have := le_of_mul_le_mul_left h' hρ0
      nlinarith
    have hdis : S.disagreementProb F g ≤ (1 + a) * Vr := by
      unfold Scheme.disagreementProb
      rw [hVr]
      unfold Scheme.Vreg
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro K _
      have hμ := hS.μ_nonneg K
      have : (if ∃ x ∈ K, F K x ≠ g x then (1:ℝ) else 0) ≤
          (1 + a) * ((errCount F g K : ℝ) / ((errCount F g K : ℝ) + a)) := by
        split_ifs with hc
        · obtain ⟨x, hxK, hx⟩ := hc
          have hm : (1:ℝ) ≤ errCount F g K := by
            have : 0 < errCount F g K := Finset.card_pos.mpr ⟨x, by simp [hxK, hx]⟩
            exact_mod_cast this
          rw [← mul_div_assoc, le_div_iff₀ (by linarith)]
          nlinarith
        · have : (0:ℝ) ≤ (errCount F g K : ℝ) / ((errCount F g K : ℝ) + a) := by positivity
          positivity
      calc S.μ K * _ ≤ S.μ K * ((1 + a) * ((errCount F g K : ℝ) / ((errCount F g K : ℝ) + a))) :=
            mul_le_mul_of_nonneg_left this hμ
        _ = _ := by ring
    have hfin : (8 / γ + 64 * (1 - ρ) / (ρ * γ ^ 2)) = (1 + a) * (8 / γ) := by
      rw [ha_def]; field_simp; ring
    rw [hfin]
    calc S.disagreementProb F g ≤ (1 + a) * Vr := hdis
      _ ≤ (1 + a) * (8 * τ / γ) := mul_le_mul_of_nonneg_left hV (by linarith)
      _ = (1 + a) * (8 / γ) * τ := by ring

end AgreementTop736.Exact
end

theorem solution : type_of% @AgreementTop736.Exact.chk_exact_agreement_soundness := @AgreementTop736.Exact.chk_exact_agreement_soundness
