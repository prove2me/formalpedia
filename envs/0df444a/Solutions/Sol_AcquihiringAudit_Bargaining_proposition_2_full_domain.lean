-- Prove2me | solution 1 for AcquihiringAudit.Bargaining.proposition_2_full_domain
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T08:36:39.395288+00:00
-- url     : https://prove2.me/submissions/649220c2-7f97-4e41-af04-97f1f5cbc816

import Mathlib
import Definitions.Def_AcquihiringAudit_Bargaining_vUpperExtended

set_option autoImplicit false

namespace AcqP2Full

open AcquihiringMonopsony

/-- Characterisation of every direct-hiring continuation equilibrium (Bertrand outcome). -/
theorem dh_char (P : Baseline.Params) (hP : P.Standing) (σ : Baseline.DHProfile)
    (h : Baseline.IsDHEquilibrium P σ) :
    (σ.acceptA σ.wa σ.ws = true ∧ σ.wa = P.vs + P.b ∧ σ.ws = P.vs ∧ P.vs + P.b ≤ P.va) ∨
    (σ.acceptA σ.wa σ.ws = false ∧ σ.wa = P.va ∧ σ.ws = P.va - P.b ∧ P.va ≤ P.vs + P.b) := by
  obtain ⟨hb, hva, hvs⟩ := hP
  obtain ⟨⟨hwa1, hwa2⟩, ⟨hws1, hws2⟩, h3, h4, h5, h6⟩ := h
  have stay : ∀ x y, x < y + P.b → σ.acceptA x y = false := by
    intro x y hxy
    cases hc : σ.acceptA x y
    · rfl
    · exact absurd (h3 _ _ hc) (by linarith)
  have go : ∀ x y, y + P.b < x → σ.acceptA x y = true := by
    intro x y hxy
    cases hc : σ.acceptA x y
    · exact absurd (h4 _ _ hc) (by linarith)
    · rfl
  cases hacc : σ.acceptA σ.wa σ.ws
  · right
    have hle : σ.wa ≤ σ.ws + P.b := h4 _ _ hacc
    have hA : P.va ≤ σ.ws + P.b := by
      by_contra hcon
      push Not at hcon
      set x := (P.va + σ.ws + P.b) / 2 with hx
      have hx1 : σ.ws + P.b < x := by rw [hx]; linarith
      have hgo := go x σ.ws hx1
      have := h5 x (by linarith)
      simp only [Baseline.dhPayoffA, hgo, hacc] at this
      simp at this
      linarith
    have hwsl : P.wl < σ.ws := by linarith
    have hS : σ.ws ≤ σ.wa - P.b := by
      by_contra hcon
      push Not at hcon
      set y := max P.wl ((σ.ws + σ.wa - P.b) / 2) with hy
      have hy1 : P.wl ≤ y := le_max_left _ _
      have hy2 : (σ.ws + σ.wa - P.b) / 2 ≤ y := le_max_right _ _
      have hy3 : y < σ.ws := max_lt hwsl (by linarith)
      have hst := stay σ.wa y (by linarith)
      have := h6 y hy1
      simp only [Baseline.dhPayoffS, hst, hacc] at this
      simp at this
      linarith
    refine ⟨rfl, by linarith, by linarith, by linarith⟩
  · left
    have hge : σ.ws + P.b ≤ σ.wa := h3 _ _ hacc
    have hS : P.vs ≤ σ.wa - P.b := by
      by_contra hcon
      push Not at hcon
      set y := (σ.wa - P.b + P.vs) / 2 with hy
      have hy1 : σ.wa - P.b < y := by rw [hy]; linarith
      have hst := stay σ.wa y (by linarith)
      have := h6 y (by linarith)
      simp only [Baseline.dhPayoffS, hst, hacc] at this
      simp at this
      linarith
    have hA : σ.wa ≤ σ.ws + P.b := by
      by_contra hcon
      push Not at hcon
      set x := (σ.wa + σ.ws + P.b) / 2 with hx
      have hx1 : σ.ws + P.b < x := by rw [hx]; linarith
      have hgo := go x σ.ws hx1
      have := h5 x (by linarith)
      simp only [Baseline.dhPayoffA, hgo, hacc] at this
      simp at this
      linarith
    refine ⟨rfl, by linarith, by linarith, by linarith⟩

/-- Payoffs in every direct-hiring continuation equilibrium. -/
theorem dh_pay (P : Baseline.Params) (hP : P.Standing) (σ : Baseline.DHProfile)
    (h : Baseline.IsDHEquilibrium P σ) :
    (σ.acceptA σ.wa σ.ws = true ∧ σ.wa = P.vs + P.b ∧
      Baseline.dhPayoffA P σ.acceptA σ.wa σ.ws = P.va - (P.vs + P.b) ∧
      Baseline.dhPayoffS P σ.acceptA σ.wa σ.ws = 0 ∧
      Baseline.dhPayoffE P σ.acceptA σ.wa σ.ws = P.vs + P.b ∧ P.vs + P.b ≤ P.va) ∨
    (σ.acceptA σ.wa σ.ws = false ∧ Baseline.dhPayoffA P σ.acceptA σ.wa σ.ws = 0 ∧
      Baseline.dhPayoffS P σ.acceptA σ.wa σ.ws = P.vs + P.b - P.va ∧
      Baseline.dhPayoffE P σ.acceptA σ.wa σ.ws = P.va ∧ P.va ≤ P.vs + P.b) := by
  rcases dh_char P hP σ h with ⟨ha, hwa, hws, hv⟩ | ⟨ha, hwa, hws, hv⟩
  · left
    refine ⟨ha, hwa, ?_, ?_, ?_, hv⟩
    · unfold Baseline.dhPayoffA; rw [ha, if_pos rfl, hwa]
    · unfold Baseline.dhPayoffS; rw [ha, if_pos rfl]
    · unfold Baseline.dhPayoffE; rw [ha, if_pos rfl, hwa]
  · right
    refine ⟨ha, ?_, ?_, ?_, hv⟩
    · unfold Baseline.dhPayoffA; rw [ha, if_neg Bool.false_ne_true]
    · unfold Baseline.dhPayoffS; rw [ha, if_neg Bool.false_ne_true, hws]; ring
    · unfold Baseline.dhPayoffE; rw [ha, if_neg Bool.false_ne_true, hws]; ring

/-- Existence of a direct-hiring continuation equilibrium (Bertrand construction). -/
theorem dh_exists (P : Baseline.Params) (hP : P.Standing) :
    ∃ σ : Baseline.DHProfile, Baseline.IsDHEquilibrium P σ := by
  obtain ⟨hb, hva, hvs⟩ := hP
  by_cases hcase : P.vs + P.b ≤ P.va
  · refine ⟨⟨P.vs + P.b, P.vs, fun x y => decide (y + P.b ≤ x)⟩, ?_⟩
    refine ⟨⟨by linarith, hcase⟩, ⟨by linarith, le_rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro x y h
      simpa using h
    · intro x y h
      simp only [decide_eq_false_iff_not, not_le] at h
      exact h.le
    · intro x _
      unfold Baseline.dhPayoffA
      by_cases h1 : P.vs + P.b ≤ x
      · simp only [h1, decide_true, if_true, le_refl]
        linarith
      · simp only [h1, decide_false, le_refl, decide_true, if_true]
        simp only [Bool.false_eq_true, if_false]
        linarith
    · intro y _
      unfold Baseline.dhPayoffS
      by_cases h1 : y + P.b ≤ P.vs + P.b
      · simp only [h1, decide_true, if_true, le_refl]
      · simp only [h1, decide_false, le_refl, decide_true, if_true]
        simp only [Bool.false_eq_true, if_false]
        linarith
  · push Not at hcase
    refine ⟨⟨P.va, P.va - P.b, fun x y => decide (y + P.b < x)⟩, ?_⟩
    refine ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, by linarith⟩, ?_, ?_, ?_, ?_⟩
    · intro x y h
      simp only [decide_eq_true_eq] at h
      exact h.le
    · intro x y h
      simp only [decide_eq_false_iff_not, not_lt] at h
      exact h
    · intro x _
      unfold Baseline.dhPayoffA
      have h0 : ¬ (P.va - P.b + P.b < P.va) := by linarith
      by_cases h1 : P.va - P.b + P.b < x
      · simp only [h1, h0, decide_true, decide_false, if_true, Bool.false_eq_true, if_false]
        linarith
      · simp only [h1, h0, decide_false, Bool.false_eq_true, if_false, le_refl]
    · intro y _
      unfold Baseline.dhPayoffS
      have h0 : ¬ (P.va - P.b + P.b < P.va) := by linarith
      by_cases h1 : y + P.b < P.va
      · simp only [h1, h0, decide_true, decide_false, if_true, Bool.false_eq_true, if_false]
        linarith
      · simp only [h1, h0, decide_false, Bool.false_eq_true, if_false]
        linarith

theorem main (P : Baseline.Params) (hP : P.Standing) (α δ : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hprod0 : 0 < α * δ) (hprod1 : α * δ < 1) :
    (∃ σ : Baseline.DHProfile, Baseline.IsDHEquilibrium P σ) ∧
    (Bargaining.vLower P δ < P.vs ∧
      (P.vs + P.b : EReal) < AcquihiringAudit.Bargaining.vUpperExtended P α δ) ∧
    (∀ σD σF : Baseline.DHProfile, Baseline.IsDHEquilibrium P σD → Baseline.IsDHEquilibrium P σF →
      (AcquihiringAudit.Bargaining.vUpperExtended P α δ < (P.va : EReal) →
        Bargaining.ahPayoffA P α δ σF < Baseline.dhPayoffA P σD.acceptA σD.wa σD.ws ∧
        σD.acceptA σD.wa σD.ws = true ∧ σD.wa = P.vs + P.b) ∧
      (Bargaining.vLower P δ < P.va → (P.va : EReal) < AcquihiringAudit.Bargaining.vUpperExtended P α δ →
        Baseline.dhPayoffA P σD.acceptA σD.wa σD.ws < Bargaining.ahPayoffA P α δ σF ∧
        Bargaining.AcquisitionOccurs P δ σF ∧ Bargaining.ahPayoffE P δ σF = P.wl) ∧
      (P.va < Bargaining.vLower P δ →
        ¬ Bargaining.AcquisitionOccurs P δ σF ∧
        σD.acceptA σD.wa σD.ws = false ∧ σF.acceptA σF.wa σF.ws = false) ∧
      Bargaining.ahPayoffE P δ σF ≤ Baseline.dhPayoffE P σD.acceptA σD.wa σD.ws ∧
      (Bargaining.ahPayoffE P δ σF < Baseline.dhPayoffE P σD.acceptA σD.wa σD.ws ↔
        Bargaining.AcquisitionOccurs P δ σF ∨ δ < 1)) := by
  have hPs := hP
  obtain ⟨hb, hva, hvs⟩ := hP
  obtain ⟨hα, hδ⟩ : 0 < α ∧ 0 < δ := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hprod0 with h | h
    · exact h
    · exact absurd h.1 (not_lt.mpr hα0)
  have hKpos : 0 < δ * (P.vs - P.wl) + P.b := by
    have := mul_pos hδ (show (0:ℝ) < P.vs - P.wl by linarith); linarith
  have hαK : 0 < α * (δ * (P.vs - P.wl) + P.b) := mul_pos hα hKpos
  have hvU : α < 1 → δ < 1 → Bargaining.vUpper P α δ =
      P.vs + P.b + α * (δ * (P.vs - P.wl) + P.b) / ((1 - α) * (1 - δ)) := by
    intro _ _; unfold Bargaining.vUpper; ring
  have hQgt : (P.va : EReal) < AcquihiringAudit.Bargaining.vUpperExtended P α δ →
      (P.va - P.vs - P.b) * ((1 - α) * (1 - δ)) < α * (δ * (P.vs - P.wl) + P.b) := by
    intro h
    unfold AcquihiringAudit.Bargaining.vUpperExtended at h
    split_ifs at h with hc
    · have h' : P.va < Bargaining.vUpper P α δ := EReal.coe_lt_coe_iff.mp h
      have hdpos : 0 < (1 - α) * (1 - δ) := mul_pos (by linarith [hc.1]) (by linarith [hc.2])
      rw [hvU hc.1 hc.2] at h'
      rw [← lt_div_iff₀ hdpos]; linarith
    · have hz : (1 - α) * (1 - δ) = 0 := by
        rcases not_and_or.mp hc with h1 | h1
        · rw [show α = 1 by linarith [not_lt.mp h1]]; ring
        · rw [show δ = 1 by linarith [not_lt.mp h1]]; ring
      rw [hz, mul_zero]; exact hαK
  have hQlt : AcquihiringAudit.Bargaining.vUpperExtended P α δ < (P.va : EReal) →
      α * (δ * (P.vs - P.wl) + P.b) < (P.va - P.vs - P.b) * ((1 - α) * (1 - δ)) ∧
        P.vs + P.b < P.va := by
    intro h
    unfold AcquihiringAudit.Bargaining.vUpperExtended at h
    split_ifs at h with hc
    · have h' : Bargaining.vUpper P α δ < P.va := EReal.coe_lt_coe_iff.mp h
      have hdpos : 0 < (1 - α) * (1 - δ) := mul_pos (by linarith [hc.1]) (by linarith [hc.2])
      rw [hvU hc.1 hc.2] at h'
      have hq : α * (δ * (P.vs - P.wl) + P.b) < (P.va - P.vs - P.b) * ((1 - α) * (1 - δ)) := by
        rw [← div_lt_iff₀ hdpos]; linarith
      have hpos := div_pos hαK hdpos
      exact ⟨hq, by linarith⟩
    · exact absurd h not_top_lt
  have h1δ : (0:ℝ) < 1 + δ := by linarith
  have hLgt : Bargaining.vLower P δ < P.va → P.vs + δ * (P.wl + P.b) < P.va * (1 + δ) := by
    intro h; unfold Bargaining.vLower at h; rwa [div_lt_iff₀ h1δ] at h
  have hLlt : P.va < Bargaining.vLower P δ → P.va * (1 + δ) < P.vs + δ * (P.wl + P.b) := by
    intro h; unfold Bargaining.vLower at h; rwa [lt_div_iff₀ h1δ] at h
  have c1L : Bargaining.vLower P δ < P.vs := by
    unfold Bargaining.vLower; rw [div_lt_iff₀ h1δ]
    have := mul_pos hδ (show (0:ℝ) < P.vs - (P.wl + P.b) by linarith); linarith
  have c1U : ((P.vs + P.b : ℝ) : EReal) < AcquihiringAudit.Bargaining.vUpperExtended P α δ := by
    unfold AcquihiringAudit.Bargaining.vUpperExtended
    split_ifs with hc
    · rw [EReal.coe_lt_coe_iff]
      have hdpos : 0 < (1 - α) * (1 - δ) := mul_pos (by linarith [hc.1]) (by linarith [hc.2])
      rw [hvU hc.1 hc.2]
      have := div_pos hαK hdpos; linarith
    · exact EReal.coe_lt_top _
  refine ⟨dh_exists P hPs, ⟨c1L, by exact_mod_cast c1U⟩, ?_⟩
  intro σD σF hD hF
  have hδvs : 0 < δ * (P.vs - P.wl) := mul_pos hδ (by linarith)
  have htA : Bargaining.threatA P δ σF = δ * Baseline.dhPayoffA P σF.acceptA σF.wa σF.ws := rfl
  have htS : Bargaining.threatS P δ σF =
      δ * Baseline.dhPayoffS P σF.acceptA σF.wa σF.ws + (1 - δ) * (P.vs - P.wl) := rfl
  have hocc_def : Bargaining.AcquisitionOccurs P δ σF ↔
      Bargaining.threatA P δ σF + Bargaining.threatS P δ σF < P.va - P.wl := Iff.rfl
  have hpay_occ : Bargaining.AcquisitionOccurs P δ σF → Bargaining.ahPayoffA P α δ σF =
      Bargaining.threatA P δ σF +
        α * (P.va - P.wl - (Bargaining.threatA P δ σF + Bargaining.threatS P δ σF)) := by
    intro hocc; unfold Bargaining.ahPayoffA Bargaining.price; rw [if_pos hocc]; ring
  have hE_occ : Bargaining.AcquisitionOccurs P δ σF → Bargaining.ahPayoffE P δ σF = P.wl := by
    intro hocc; unfold Bargaining.ahPayoffE; rw [if_pos hocc]
  have hE_nocc : ¬ Bargaining.AcquisitionOccurs P δ σF → Bargaining.ahPayoffE P δ σF =
      δ * Baseline.dhPayoffE P σF.acceptA σF.wa σF.ws + (1 - δ) * (P.wl + P.b) := by
    intro hocc; unfold Bargaining.ahPayoffE; rw [if_neg hocc]
  rcases dh_pay P hPs σD hD with ⟨hDa, hDwa, hDA, -, hDE, hDv⟩ | ⟨hDa, hDA, -, hDE, hDv⟩
  · rcases dh_pay P hPs σF hF with ⟨hFa, -, hFA, hFS, hFE, hFv⟩ | ⟨hFa, hFA, hFS, hFE, hFv⟩
    · -- D accepts, F accepts
      rw [hFA] at htA
      rw [hFS] at htS
      rw [htA, htS] at hocc_def hpay_occ
      rw [hDA, hDE]
      have hX : 0 ≤ (1 - δ) * (P.va - (P.vs + P.b)) := mul_nonneg (by linarith) (by linarith)
      have hocc : Bargaining.AcquisitionOccurs P δ σF := hocc_def.mpr (by linarith)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hU
        have hq := (hQlt hU).1
        refine ⟨?_, hDa, hDwa⟩
        rw [hpay_occ hocc]
        linarith
      · intro _ hU
        have hq := hQgt hU
        refine ⟨?_, hocc, hE_occ hocc⟩
        rw [hpay_occ hocc]
        linarith
      · intro hL; exfalso; linarith
      · rw [hE_occ hocc]; linarith
      · rw [hE_occ hocc]; exact ⟨fun _ => Or.inl hocc, fun _ => by linarith⟩
    · -- D accepts, F rejects: va = vs + b
      have hveq : P.va = P.vs + P.b := le_antisymm hFv hDv
      rw [hFA] at htA
      rw [hFS, show P.vs + P.b - P.va = 0 by linarith] at htS
      rw [htA, htS] at hocc_def hpay_occ
      rw [hDA, hDE]
      have hocc : Bargaining.AcquisitionOccurs P δ σF := hocc_def.mpr (by linarith)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hU; exfalso; linarith [(hQlt hU).2]
      · intro _ _
        refine ⟨?_, hocc, hE_occ hocc⟩
        rw [hpay_occ hocc]
        have hs := hocc_def.mp hocc
        have := mul_pos hα (sub_pos.mpr hs)
        linarith
      · intro hL; exfalso; linarith
      · rw [hE_occ hocc]; linarith
      · rw [hE_occ hocc]; exact ⟨fun _ => Or.inl hocc, fun _ => by linarith⟩
  · rcases dh_pay P hPs σF hF with ⟨hFa, -, hFA, hFS, hFE, hFv⟩ | ⟨hFa, hFA, hFS, hFE, hFv⟩
    · -- D rejects, F accepts: va = vs + b
      have hveq : P.va = P.vs + P.b := le_antisymm hDv hFv
      rw [hFA, show P.va - (P.vs + P.b) = 0 by linarith] at htA
      rw [hFS] at htS
      rw [htA, htS] at hocc_def hpay_occ
      rw [hDA, hDE]
      have hocc : Bargaining.AcquisitionOccurs P δ σF := hocc_def.mpr (by linarith)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hU; exfalso; linarith [(hQlt hU).2]
      · intro _ _
        refine ⟨?_, hocc, hE_occ hocc⟩
        rw [hpay_occ hocc]
        have hs := hocc_def.mp hocc
        have := mul_pos hα (sub_pos.mpr hs)
        linarith
      · intro hL; exfalso; linarith
      · rw [hE_occ hocc]; linarith
      · rw [hE_occ hocc]; exact ⟨fun _ => Or.inl hocc, fun _ => by linarith⟩
    · -- D rejects, F rejects
      rw [hFA] at htA
      rw [hFS] at htS
      rw [hFE] at hE_nocc
      rw [htA, htS] at hocc_def hpay_occ
      rw [hDA, hDE]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro hU; exfalso; linarith [(hQlt hU).2]
      · intro hL _
        have hL' := hLgt hL
        have hocc : Bargaining.AcquisitionOccurs P δ σF := hocc_def.mpr (by linarith)
        refine ⟨?_, hocc, hE_occ hocc⟩
        rw [hpay_occ hocc]
        have hs := hocc_def.mp hocc
        have := mul_pos hα (sub_pos.mpr hs)
        linarith
      · intro hL
        have hL' := hLlt hL
        refine ⟨?_, hDa, hFa⟩
        rw [hocc_def]; intro h; linarith
      · by_cases hocc : Bargaining.AcquisitionOccurs P δ σF
        · rw [hE_occ hocc]; linarith
        · rw [hE_nocc hocc]
          have := mul_nonneg (show (0:ℝ) ≤ 1 - δ by linarith)
            (show (0:ℝ) ≤ P.va - (P.wl + P.b) by linarith)
          linarith
      · by_cases hocc : Bargaining.AcquisitionOccurs P δ σF
        · rw [hE_occ hocc]; exact ⟨fun _ => Or.inl hocc, fun _ => by linarith⟩
        · rw [hE_nocc hocc]
          constructor
          · intro h
            right
            by_contra hc
            have h1 : δ = 1 := le_antisymm hδ1 (not_lt.mp hc)
            rw [h1] at h
            linarith
          · rintro (h | h)
            · exact absurd h hocc
            · have := mul_pos (show (0:ℝ) < 1 - δ by linarith)
                (show (0:ℝ) < P.va - (P.wl + P.b) by linarith)
              linarith

end AcqP2Full

open AcquihiringMonopsony.Baseline AcquihiringMonopsony.Bargaining AcquihiringAudit.Bargaining in
theorem solution (P : Params) (hP : P.Standing) (α δ : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hprod0 : 0 < α * δ) (hprod1 : α * δ < 1) :
    (∃ σ : DHProfile, IsDHEquilibrium P σ) ∧
    (vLower P δ < P.vs ∧ (P.vs + P.b : EReal) < vUpperExtended P α δ) ∧
    (∀ σD σF : DHProfile, IsDHEquilibrium P σD → IsDHEquilibrium P σF →
      (vUpperExtended P α δ < (P.va : EReal) →
        ahPayoffA P α δ σF < dhPayoffA P σD.acceptA σD.wa σD.ws ∧
        σD.acceptA σD.wa σD.ws = true ∧ σD.wa = P.vs + P.b) ∧
      (vLower P δ < P.va → (P.va : EReal) < vUpperExtended P α δ →
        dhPayoffA P σD.acceptA σD.wa σD.ws < ahPayoffA P α δ σF ∧
        AcquisitionOccurs P δ σF ∧ ahPayoffE P δ σF = P.wl) ∧
      (P.va < vLower P δ →
        ¬ AcquisitionOccurs P δ σF ∧
        σD.acceptA σD.wa σD.ws = false ∧ σF.acceptA σF.wa σF.ws = false) ∧
      ahPayoffE P δ σF ≤ dhPayoffE P σD.acceptA σD.wa σD.ws ∧
      (ahPayoffE P δ σF < dhPayoffE P σD.acceptA σD.wa σD.ws ↔
        AcquisitionOccurs P δ σF ∨ δ < 1)) := by
  exact AcqP2Full.main P hP α δ hα0 hα1 hδ0 hδ1 hprod0 hprod1
