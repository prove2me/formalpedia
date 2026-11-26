-- Prove2me | solution 1 for Arxiv2405_10327.weak_form_gamma_zero_equals_constrained
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:46:40.233663+00:00
-- url     : https://prove2.me/submissions/881e382e-d9fe-4fd7-a763-cf948319895c

import Mathlib
import Definitions.Def_Arxiv2405_10327_Basic

set_option autoImplicit false

open Filter Topology

namespace S74WG
open Arxiv2405_10327

lemma hp_sum {d M : ℕ} (v : Fin M → Vec d) :
    ∑ i, hardPenalty (v i) = if ∀ i, v i = 0 then (0 : EReal) else ⊤ := by
  split_ifs with h
  · exact Finset.sum_eq_zero (fun i _ => by simp [hardPenalty, h i])
  · push Not at h
    obtain ⟨j, hj⟩ := h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have h1 : hardPenalty (v j) = ⊤ := by simp [hardPenalty, hj]
    have h2 : (0 : EReal) ≤ ∑ i ∈ Finset.univ.erase j, hardPenalty (v i) :=
      Finset.sum_nonneg (fun i _ => by unfold hardPenalty; split_ifs <;> simp)
    rw [h1]
    exact EReal.top_add_of_ne_bot (ne_bot_of_le_ne_bot (by simp) h2)

end S74WG

open Arxiv2405_10327 S74WG in
theorem solution {d m p M : ℕ} {C : Type*}
    (hM : 0 < M) (σ : ℝ) (hσ : 0 < σ)
    (F : Vec d → Vec m) (yobs : Vec m)
    (fInv : Vec d → C → Vec d) (ybar : C) (hfInv : ∀ c, Function.Bijective (fun u => fInv u c))
    (h : Vec p → Vec d → Vec d) (hh : ∀ φ, Function.Bijective (h φ) ∧ Differentiable ℝ (h φ))
    (z : Fin M → Vec d) :
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      Tendsto (fun γ : ℝ => ((weakObjective σ γ F yobs fInv ybar h z x φ : ℝ) : EReal)) (𝓝[>] 0)
        (𝓝 (weakObjectiveHard σ F yobs fInv ybar h z x φ))) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      weakObjectiveHard σ F yobs fInv ybar h z x φ =
        if ∀ i, x i = corrected fInv ybar (h φ) (z i) then
          ((strongSampleObjective σ F yobs fInv ybar h z φ : ℝ) : EReal) else ⊤) ∧
    ((⨅ (x : Fin M → Vec d) (φ : Vec p), weakObjectiveHard σ F yobs fInv ybar h z x φ) =
      ⨅ φ : Vec p, ((strongSampleObjective σ F yobs fInv ybar h z φ : ℝ) : EReal)) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      (∀ (x' : Fin M → Vec d) (φ' : Vec p),
          weakObjectiveHard σ F yobs fInv ybar h z x φ ≤ weakObjectiveHard σ F yobs fInv ybar h z x' φ') ↔
        ((∀ i, x i = corrected fInv ybar (h φ) (z i)) ∧
          ∀ φ' : Vec p, strongSampleObjective σ F yobs fInv ybar h z φ ≤
            strongSampleObjective σ F yobs fInv ybar h z φ')) := by
  have hMpos : (0:ℝ) < 1 / (M : ℝ) := by
    have : (0:ℝ) < M := by exact_mod_cast hM
    positivity
  -- part 2
  have P2 : ∀ (x : Fin M → Vec d) (φ : Vec p),
      weakObjectiveHard σ F yobs fInv ybar h z x φ =
        if ∀ i, x i = corrected fInv ybar (h φ) (z i) then
          ((strongSampleObjective σ F yobs fInv ybar h z φ : ℝ) : EReal) else ⊤ := by
    intro x φ
    unfold weakObjectiveHard
    rw [hp_sum]
    by_cases hx : ∀ i, x i = corrected fInv ybar (h φ) (z i)
    · have h0 : ∀ i, x i - corrected fInv ybar (h φ) (z i) = 0 := fun i => by rw [hx i, sub_self]
      rw [if_pos h0, if_pos hx, add_zero]
      congr 2
      unfold strongIntegrand
      refine Finset.sum_congr rfl (fun i _ => by rw [hx i])
    · have h0 : ¬ ∀ i, x i - corrected fInv ybar (h φ) (z i) = 0 := by
        intro hc; exact hx (fun i => sub_eq_zero.1 (hc i))
      rw [if_neg h0, if_neg hx, EReal.coe_add_top]
  -- Hard ≥ strong always, with equality at corrected
  have hge : ∀ (x : Fin M → Vec d) (φ : Vec p),
      ((strongSampleObjective σ F yobs fInv ybar h z φ : ℝ) : EReal) ≤
        weakObjectiveHard σ F yobs fInv ybar h z x φ := by
    intro x φ; rw [P2]; split_ifs <;> simp
  have heq : ∀ φ : Vec p,
      weakObjectiveHard σ F yobs fInv ybar h z (fun i => corrected fInv ybar (h φ) (z i)) φ =
        ((strongSampleObjective σ F yobs fInv ybar h z φ : ℝ) : EReal) := by
    intro φ; rw [P2, if_pos (fun i => rfl)]
  refine ⟨fun x φ => ?_, P2, ?_, fun x φ => ?_⟩
  · by_cases hx : ∀ i, x i = corrected fInv ybar (h φ) (z i)
    · have hc : ∀ γ : ℝ, weakObjective σ γ F yobs fInv ybar h z x φ =
          (1 / (M : ℝ)) * ∑ i, (dataMisfit σ F yobs (x i) + latentTerm (h φ) (z i)) := by
        intro γ
        unfold weakObjective
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hx i, sub_self, norm_zero]; ring
      have hH : weakObjectiveHard σ F yobs fInv ybar h z x φ =
          (((1 / (M : ℝ)) * ∑ i, (dataMisfit σ F yobs (x i) + latentTerm (h φ) (z i)) : ℝ) : EReal) := by
        unfold weakObjectiveHard
        rw [hp_sum, if_pos (fun i => by rw [hx i, sub_self]), add_zero]
      simp_rw [hc, hH]
      exact tendsto_const_nhds
    · have hH : weakObjectiveHard σ F yobs fInv ybar h z x φ = ⊤ := by rw [P2, if_neg hx]
      rw [hH]
      push Not at hx
      obtain ⟨j, hj⟩ := hx
      set A := ∑ i, (dataMisfit σ F yobs (x i) + latentTerm (h φ) (z i)) with hA
      set S := ∑ i, ‖x i - corrected fInv ybar (h φ) (z i)‖ ^ 2 with hS
      have hSpos : 0 < S := by
        rw [hS, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have h1 : 0 < ‖x j - corrected fInv ybar (h φ) (z j)‖ ^ 2 := by
          have : x j - corrected fInv ybar (h φ) (z j) ≠ 0 := sub_ne_zero.2 hj
          positivity
        have h2 : 0 ≤ ∑ i ∈ Finset.univ.erase j, ‖x i - corrected fInv ybar (h φ) (z i)‖ ^ 2 :=
          Finset.sum_nonneg (fun i _ => by positivity)
        linarith
      have hform : ∀ γ : ℝ, weakObjective σ γ F yobs fInv ybar h z x φ =
          (1 / (M : ℝ)) * (A + S / 2 * (γ⁻¹) ^ 2) := by
        intro γ
        unfold weakObjective
        rw [hA, hS, Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [inv_pow]; ring
      simp_rw [hform]
      refine EReal.tendsto_coe_atTop.comp ?_
      refine Tendsto.const_mul_atTop hMpos ?_
      refine tendsto_atTop_add_const_left _ A ?_
      refine Tendsto.const_mul_atTop (by positivity) ?_
      exact (tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero
  · rw [iInf_comm]
    congr 1
    funext φ
    apply le_antisymm
    · exact (iInf_le _ (fun i => corrected fInv ybar (h φ) (z i))).trans (le_of_eq (heq φ))
    · exact le_iInf (fun x => hge x φ)
  · constructor
    · intro hmin
      have hx : ∀ i, x i = corrected fInv ybar (h φ) (z i) := by
        by_contra hx
        have h1 := hmin (fun i => corrected fInv ybar (h φ) (z i)) φ
        rw [heq, P2, if_neg hx] at h1
        exact EReal.coe_ne_top _ (top_le_iff.1 h1)
      refine ⟨hx, fun φ' => ?_⟩
      have h1 := hmin (fun i => corrected fInv ybar (h φ') (z i)) φ'
      rw [heq, P2, if_pos hx] at h1
      exact EReal.coe_le_coe_iff.1 h1
    · rintro ⟨hx, hφ⟩ x' φ'
      rw [P2, if_pos hx]
      exact (EReal.coe_le_coe_iff.2 (hφ φ')).trans (hge x' φ')
