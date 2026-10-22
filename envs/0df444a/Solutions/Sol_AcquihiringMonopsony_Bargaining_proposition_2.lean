-- Prove2me | solution 1 for AcquihiringMonopsony.Bargaining.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:04:51.95785+00:00
-- url     : https://prove2.me/submissions/5ac4742d-972b-427e-8068-0c1f9d8ac3f1

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model
import Definitions.Def_AcquihiringMonopsony_Bargaining_NashSplit

set_option autoImplicit false

namespace AcqP2Helpers

open AcquihiringMonopsony

/-- Characterisation of every direct-hiring continuation equilibrium (Bertrand outcome). -/
theorem dh_char (P : Baseline.Params) (hP : P.Standing) (σ : Baseline.DHProfile)
    (h : Baseline.IsDHEquilibrium P σ) :
    (σ.acceptA σ.wa σ.ws = true ∧ σ.wa = P.vs + P.b ∧ σ.ws = P.vs ∧ P.vs + P.b ≤ P.va) ∨
    (σ.acceptA σ.wa σ.ws = false ∧ σ.wa = P.va ∧ σ.ws = P.va - P.b ∧ P.va ≤ P.vs + P.b) := by
  obtain ⟨hb, hva, hvs⟩ := hP
  obtain ⟨⟨hwa1, hwa2⟩, ⟨hws1, hws2⟩, h3, h4, h5, h6⟩ := h
  -- if the startup's offer plus benefit beats x, the employee stays
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
  · -- employee stays
    right
    have hle : σ.wa ≤ σ.ws + P.b := h4 _ _ hacc
    -- acquirer cannot profit: va ≤ ws + b
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
    -- startup cannot profit: ws ≤ wa - b
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
  · -- employee joins the acquirer
    left
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
    (σ.acceptA σ.wa σ.ws = true ∧ Baseline.dhPayoffA P σ.acceptA σ.wa σ.ws = P.va - (P.vs + P.b) ∧
      Baseline.dhPayoffS P σ.acceptA σ.wa σ.ws = 0 ∧ Baseline.dhPayoffE P σ.acceptA σ.wa σ.ws = P.vs + P.b ∧
      P.vs + P.b ≤ P.va) ∨
    (σ.acceptA σ.wa σ.ws = false ∧ Baseline.dhPayoffA P σ.acceptA σ.wa σ.ws = 0 ∧
      Baseline.dhPayoffS P σ.acceptA σ.wa σ.ws = P.vs + P.b - P.va ∧
      Baseline.dhPayoffE P σ.acceptA σ.wa σ.ws = P.va ∧ P.va ≤ P.vs + P.b) := by
  rcases dh_char P hP σ h with ⟨ha, hwa, hws, hv⟩ | ⟨ha, hwa, hws, hv⟩
  · left
    refine ⟨ha, ?_, ?_, ?_, hv⟩
    · unfold Baseline.dhPayoffA; rw [ha, if_pos rfl, hwa]
    · unfold Baseline.dhPayoffS; rw [ha, if_pos rfl]
    · unfold Baseline.dhPayoffE; rw [ha, if_pos rfl, hwa]
  · right
    refine ⟨ha, ?_, ?_, ?_, hv⟩
    · unfold Baseline.dhPayoffA; rw [ha, if_neg Bool.false_ne_true]
    · unfold Baseline.dhPayoffS; rw [ha, if_neg Bool.false_ne_true, hws]; ring
    · unfold Baseline.dhPayoffE; rw [ha, if_neg Bool.false_ne_true, hws]; ring

end AcqP2Helpers

open AcquihiringMonopsony AcquihiringMonopsony.Bargaining in
theorem solution (P : Baseline.Params) (hP : P.Standing) (α δ : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (σD σF : Baseline.DHProfile) (hD : Baseline.IsDHEquilibrium P σD)
    (hF : Baseline.IsDHEquilibrium P σF) :
    (P.vs + P.b < vUpper P α δ ∧ vLower P δ < P.vs) ∧
    (vUpper P α δ < P.va →
      ahPayoffA P α δ σF < Baseline.dhPayoffA P σD.acceptA σD.wa σD.ws ∧ σD.acceptA σD.wa σD.ws = true) ∧
    (vLower P δ < P.va → P.va < vUpper P α δ →
      Baseline.dhPayoffA P σD.acceptA σD.wa σD.ws < ahPayoffA P α δ σF ∧ AcquisitionOccurs P δ σF) ∧
    (P.va < vLower P δ →
      ¬ AcquisitionOccurs P δ σF ∧ σD.acceptA σD.wa σD.ws = false ∧
        σF.acceptA σF.wa σF.ws = false) ∧
    ahPayoffE P δ σF < Baseline.dhPayoffE P σD.acceptA σD.wa σD.ws := by
  have hPs := hP
  obtain ⟨hb, hva, hvs⟩ := hP
  have hKpos : 0 < δ * (P.vs - P.wl) + P.b := by
    have := mul_pos hδ0 (show (0:ℝ) < P.vs - P.wl by linarith); linarith
  have hdpos : 0 < (1 - α) * (1 - δ) := mul_pos (by linarith) (by linarith)
  have hvU : vUpper P α δ = P.vs + P.b + α * (δ * (P.vs - P.wl) + P.b) / ((1 - α) * (1 - δ)) := by
    unfold vUpper; ring
  have hUlt : vUpper P α δ < P.va →
      α * (δ * (P.vs - P.wl) + P.b) < (P.va - P.vs - P.b) * ((1 - α) * (1 - δ)) := by
    intro h; rw [hvU] at h; rw [← div_lt_iff₀ hdpos]; linarith
  have hUgt : P.va < vUpper P α δ →
      (P.va - P.vs - P.b) * ((1 - α) * (1 - δ)) < α * (δ * (P.vs - P.wl) + P.b) := by
    intro h; rw [hvU] at h; rw [← lt_div_iff₀ hdpos]; linarith
  have h1δ : (0:ℝ) < 1 + δ := by linarith
  have hLgt : vLower P δ < P.va → P.vs + δ * (P.wl + P.b) < P.va * (1 + δ) := by
    intro h; unfold vLower at h; rwa [div_lt_iff₀ h1δ] at h
  have hLlt : P.va < vLower P δ → P.va * (1 + δ) < P.vs + δ * (P.wl + P.b) := by
    intro h; unfold vLower at h; rwa [lt_div_iff₀ h1δ] at h
  have c1 : P.vs + P.b < vUpper P α δ ∧ vLower P δ < P.vs := by
    refine ⟨?_, ?_⟩
    · rw [hvU]; have := div_pos (mul_pos hα0 hKpos) hdpos; linarith
    · unfold vLower; rw [div_lt_iff₀ h1δ]
      have := mul_pos hδ0 (show (0:ℝ) < P.vs - (P.wl + P.b) by linarith); linarith
  have hδvs : 0 < δ * (P.vs - P.wl) := mul_pos hδ0 (by linarith)
  have htA : threatA P δ σF = δ * Baseline.dhPayoffA P σF.acceptA σF.wa σF.ws := rfl
  have htS : threatS P δ σF =
      δ * Baseline.dhPayoffS P σF.acceptA σF.wa σF.ws + (1 - δ) * (P.vs - P.wl) := rfl
  have hocc_def : AcquisitionOccurs P δ σF ↔ threatA P δ σF + threatS P δ σF < P.va - P.wl := Iff.rfl
  have hpay_occ : AcquisitionOccurs P δ σF → ahPayoffA P α δ σF =
      threatA P δ σF + α * (P.va - P.wl - (threatA P δ σF + threatS P δ σF)) := by
    intro hocc; unfold ahPayoffA price; rw [if_pos hocc]; ring
  have hE_occ : AcquisitionOccurs P δ σF → ahPayoffE P δ σF = P.wl := by
    intro hocc; unfold ahPayoffE; rw [if_pos hocc]
  have hE_nocc : ¬ AcquisitionOccurs P δ σF → ahPayoffE P δ σF =
      δ * Baseline.dhPayoffE P σF.acceptA σF.wa σF.ws + (1 - δ) * (P.wl + P.b) := by
    intro hocc; unfold ahPayoffE; rw [if_neg hocc]
  rcases AcqP2Helpers.dh_pay P hPs σD hD with ⟨hDa, hDA, -, hDE, hDv⟩ | ⟨hDa, hDA, -, hDE, hDv⟩
  · rcases AcqP2Helpers.dh_pay P hPs σF hF with ⟨hFa, hFA, hFS, hFE, hFv⟩ | ⟨hFa, hFA, hFS, hFE, hFv⟩
    · -- D accepts, F accepts
      rw [hFA] at htA
      rw [hFS] at htS
      rw [hFE] at hE_nocc
      rw [htA, htS] at hocc_def hpay_occ
      rw [hDA, hDE]
      have hX : 0 ≤ (1 - δ) * (P.va - (P.vs + P.b)) := mul_nonneg (by linarith) (by linarith)
      have hocc : AcquisitionOccurs P δ σF := hocc_def.mpr (by linarith)
      refine ⟨c1, ?_, ?_, ?_, ?_⟩
      · intro hU
        have hU' := hUlt hU
        refine ⟨?_, hDa⟩
        rw [hpay_occ hocc]
        linarith
      · intro _ hU
        have hU' := hUgt hU
        refine ⟨?_, hocc⟩
        rw [hpay_occ hocc]
        linarith
      · intro hL; exfalso; linarith [c1.2]
      · rw [hE_occ hocc]; linarith
    · -- D accepts, F rejects: va = vs + b
      have hveq : P.va = P.vs + P.b := le_antisymm hFv hDv
      rw [hFA] at htA
      rw [hFS, show P.vs + P.b - P.va = 0 by linarith] at htS
      rw [htA, htS] at hocc_def hpay_occ
      rw [hDA, hDE]
      have hocc : AcquisitionOccurs P δ σF := hocc_def.mpr (by linarith)
      refine ⟨c1, ?_, ?_, ?_, ?_⟩
      · intro hU; exfalso; linarith [c1.1]
      · intro _ _
        refine ⟨?_, hocc⟩
        rw [hpay_occ hocc]
        have hs := hocc_def.mp hocc
        have := mul_pos hα0 (sub_pos.mpr hs)
        linarith
      · intro hL; exfalso; linarith [c1.2]
      · rw [hE_occ hocc]; linarith
  · rcases AcqP2Helpers.dh_pay P hPs σF hF with ⟨hFa, hFA, hFS, hFE, hFv⟩ | ⟨hFa, hFA, hFS, hFE, hFv⟩
    · -- D rejects, F accepts: va = vs + b
      have hveq : P.va = P.vs + P.b := le_antisymm hDv hFv
      rw [hFA, show P.va - (P.vs + P.b) = 0 by linarith] at htA
      rw [hFS] at htS
      rw [htA, htS] at hocc_def hpay_occ
      rw [hDA, hDE]
      have hocc : AcquisitionOccurs P δ σF := hocc_def.mpr (by linarith)
      refine ⟨c1, ?_, ?_, ?_, ?_⟩
      · intro hU; exfalso; linarith [c1.1]
      · intro _ _
        refine ⟨?_, hocc⟩
        rw [hpay_occ hocc]
        have hs := hocc_def.mp hocc
        have := mul_pos hα0 (sub_pos.mpr hs)
        linarith
      · intro hL; exfalso; linarith [c1.2]
      · rw [hE_occ hocc]; linarith
    · -- D rejects, F rejects
      rw [hFA] at htA
      rw [hFS] at htS
      rw [hFE] at hE_nocc
      rw [htA, htS] at hocc_def hpay_occ
      rw [hDA, hDE]
      refine ⟨c1, ?_, ?_, ?_, ?_⟩
      · intro hU; exfalso; linarith [c1.1]
      · intro hL _
        have hL' := hLgt hL
        have hocc : AcquisitionOccurs P δ σF := hocc_def.mpr (by linarith)
        refine ⟨?_, hocc⟩
        rw [hpay_occ hocc]
        have hs := hocc_def.mp hocc
        have := mul_pos hα0 (sub_pos.mpr hs)
        linarith
      · intro hL
        have hL' := hLlt hL
        refine ⟨?_, hDa, hFa⟩
        rw [hocc_def]; intro h; linarith
      · by_cases hocc : AcquisitionOccurs P δ σF
        · rw [hE_occ hocc]; linarith
        · rw [hE_nocc hocc]
          have := mul_pos (show (0:ℝ) < 1 - δ by linarith) (show (0:ℝ) < P.va - (P.wl + P.b) by linarith)
          linarith
