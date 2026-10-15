-- Prove2me | solution 1 for AcquihiringMonopsony.Baseline.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-14T19:52:52.117037+00:00
-- url     : https://prove2.me/submissions/88f9cab8-66bd-4484-a9ed-14d44a76f97c

import Definitions.Def_AcquihiringMonopsony_Baseline_Model
namespace AcquihiringMonopsony.Baseline

lemma dh_accept_wa (P : Params) (hP : P.Standing) (σ : DHProfile) (hD : IsDHEquilibrium P σ)
    (h : σ.acceptA σ.wa σ.ws = true) : P.vs + P.b ≤ σ.wa := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7, h8⟩ := hD
  by_contra hc
  push_neg at hc
  set y := (max (σ.wa - P.b) P.wl + P.vs) / 2 with hy
  have hm1 : σ.wa - P.b ≤ max (σ.wa - P.b) P.wl := le_max_left _ _
  have hm2 : P.wl ≤ max (σ.wa - P.b) P.wl := le_max_right _ _
  have hm3 : max (σ.wa - P.b) P.wl < P.vs := max_lt (by linarith) (by linarith)
  have hyl : P.wl ≤ y := by rw [hy]; linarith
  have hacc : σ.acceptA σ.wa y = false := by
    cases hc' : σ.acceptA σ.wa y
    · rfl
    · have := h5 _ _ hc'; rw [hy] at this; linarith
  have := h8 y hyl
  simp only [dhPayoffS, hacc, h] at this
  simp at this
  rw [hy] at this; linarith

lemma dh_reject_ws (P : Params) (hP : P.Standing) (σ : DHProfile) (hD : IsDHEquilibrium P σ)
    (h : σ.acceptA σ.wa σ.ws = false) : P.va ≤ σ.ws + P.b := by
  obtain ⟨hP1, hP2, hP3⟩ := hP
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7, h8⟩ := hD
  by_contra hc
  push_neg at hc
  set x := (max (σ.ws + P.b) P.wl + P.va) / 2 with hx
  have hm1 : σ.ws + P.b ≤ max (σ.ws + P.b) P.wl := le_max_left _ _
  have hm2 : P.wl ≤ max (σ.ws + P.b) P.wl := le_max_right _ _
  have hm3 : max (σ.ws + P.b) P.wl < P.va := max_lt hc (by linarith)
  have hxl : P.wl ≤ x := by rw [hx]; linarith
  have hacc : σ.acceptA x σ.ws = true := by
    cases hc' : σ.acceptA x σ.ws
    · have := h6 _ _ hc'; rw [hx] at this; linarith
    · rfl
  have := h7 x hxl
  simp only [dhPayoffA, hacc, h] at this
  simp at this
  rw [hx] at this; linarith

theorem proposition_1 (P : Params) (hP : P.Standing)
    (σD : DHProfile) (hD : IsDHEquilibrium P σD) (σA : AHProfile) (hA : IsAHEquilibrium P σA) :
    (P.vs < P.va → σA.acceptBid σA.p = true ∧
      dhPayoffA P σD.acceptA σD.wa σD.ws < ahPayoffA P σA σA.p) ∧
    (P.va < P.vs → σA.acceptBid σA.p = false ∧ σD.acceptA σD.wa σD.ws = false) ∧
    ahPayoffE P σA < dhPayoffE P σD.acceptA σD.wa σD.ws ∧
    ((P.va ≠ P.vs + P.b → ∃ σ : DHProfile, IsDHEquilibrium P σ) ∧
      (P.va ≠ P.vs → ∃ σ : AHProfile, IsAHEquilibrium P σ)) := by
  have hPs := hP
  obtain ⟨hP1, hP2, hP3⟩ := hP
  have hD' := hD
  obtain ⟨⟨d1, d2⟩, ⟨d3, d4⟩, d5, d6, d7, d8⟩ := hD'
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩, a5, a6, a7, a8⟩ := hA
  have hwa : σA.wa = P.wl := le_antisymm (a2 _ le_rfl) a1
  have hws : σA.ws = P.wl := le_antisymm (a4 _ le_rfl) a3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hlt
    have hacc : σA.acceptBid σA.p = true := by
      cases hc : σA.acceptBid σA.p
      · exfalso
        set q := (P.vs + P.va) / 2 - P.wl with hq
        have hqa : σA.acceptBid q = true := by
          cases hc' : σA.acceptBid q
          · have := a6 _ hc'; rw [hws, hq] at this; linarith
          · rfl
        have := a8 q
        simp only [ahPayoffA, hqa, hc] at this
        simp at this
        rw [hwa, hq] at this; linarith
      · rfl
    refine ⟨hacc, ?_⟩
    -- p ≤ vs - wl
    have hp : σA.p ≤ P.vs - P.wl := by
      by_contra hc
      push_neg at hc
      set q := (P.vs - P.wl + σA.p) / 2 with hq
      have hqa : σA.acceptBid q = true := by
        cases hc' : σA.acceptBid q
        · have := a6 _ hc'; rw [hws, hq] at this; linarith
        · rfl
      have := a8 q
      simp only [ahPayoffA, hqa, hacc] at this
      simp at this
      rw [hq] at this; linarith
    simp only [ahPayoffA, hacc, dhPayoffA, if_true]
    rw [hwa]
    cases hd : σD.acceptA σD.wa σD.ws
    · simp; linarith
    · have := dh_accept_wa P hPs σD hD hd
      simp; linarith
  · intro hlt
    refine ⟨?_, ?_⟩
    · cases hc : σA.acceptBid σA.p
      · rfl
      · have := a5 _ hc; rw [hws] at this; rw [hwa] at a7; linarith
    · cases hd : σD.acceptA σD.wa σD.ws
      · rfl
      · have := dh_accept_wa P hPs σD hD hd; linarith
  · have hle : ahPayoffE P σA ≤ P.wl + P.b := by
      unfold ahPayoffE
      split_ifs <;> linarith
    unfold dhPayoffE
    cases hd : σD.acceptA σD.wa σD.ws
    · have := dh_reject_ws P hPs σD hD hd
      simp; linarith
    · have := dh_accept_wa P hPs σD hD hd
      simp; linarith
  · intro hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨⟨P.va, P.va - P.b, fun x y => decide (y + P.b < x)⟩, ?_⟩
      refine ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, by linarith⟩, ?_, ?_, ?_, ?_⟩
      · intro x y h; simp at h; linarith
      · intro x y h; simp at h; linarith
      · intro x _
        simp only [dhPayoffA]
        split_ifs with h1 h2 <;> simp_all <;> linarith
      · intro y _
        simp only [dhPayoffS]
        split_ifs with h1 h2 <;> simp_all <;> linarith
    · refine ⟨⟨P.vs + P.b, P.vs, fun x y => decide (y + P.b ≤ x)⟩, ?_⟩
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, le_rfl⟩, ?_, ?_, ?_, ?_⟩
      · intro x y h; simp at h; linarith
      · intro x y h; simp at h; linarith
      · intro x _
        simp only [dhPayoffA]
        split_ifs with h1 h2 <;> simp_all <;> linarith
      · intro y _
        simp only [dhPayoffS]
        split_ifs with h1 h2 <;> simp_all <;> linarith
  · intro hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨⟨P.va - P.wl, fun q => decide (P.vs - P.wl ≤ q), P.wl, P.wl⟩, ?_⟩
      refine ⟨⟨le_rfl, fun x hx => hx⟩, ⟨le_rfl, fun y hy => hy⟩, ?_, ?_, le_rfl, ?_⟩
      · intro q h; simp at h; linarith
      · intro q h; simp at h; linarith
      · intro q
        simp only [ahPayoffA]
        split_ifs with h1 h2 <;> simp_all <;> linarith
    · refine ⟨⟨P.vs - P.wl, fun q => decide (P.vs - P.wl ≤ q), P.wl, P.wl⟩, ?_⟩
      refine ⟨⟨le_rfl, fun x hx => hx⟩, ⟨le_rfl, fun y hy => hy⟩, ?_, ?_, by linarith, ?_⟩
      · intro q h; simp at h; linarith
      · intro q h; simp at h; linarith
      · intro q
        simp only [ahPayoffA]
        split_ifs with h1 h2 <;> simp_all <;> linarith

end AcquihiringMonopsony.Baseline


-- Platform entry point: restates the target verbatim.
namespace AcquihiringMonopsony.Baseline

/-- Proposition 1 (p. 6). Fix any continuation equilibrium `σD` of the direct-hiring subgame and
any continuation equilibrium `σA` of the acquihiring subgame.
1. If `v_a > v_s`, the acquirer hires the employee through acquihiring: the bid is accepted, and
   acquihiring gives the acquirer a strictly larger payoff than direct hiring.
2. If `v_a < v_s`, the acquirer does not hire the employee by either mode.
3. The employee strictly prefers the direct-hiring outcome to the acquihiring outcome.
4. Continuation equilibria of both subgames exist (away from the knife edges
   `v_a = v_s + b` and `v_a = v_s` respectively), so 1–3 are not vacuous. -/
theorem _root_.solution (P : Params) (hP : P.Standing)
    (σD : DHProfile) (hD : IsDHEquilibrium P σD) (σA : AHProfile) (hA : IsAHEquilibrium P σA) :
    (P.vs < P.va → σA.acceptBid σA.p = true ∧
      dhPayoffA P σD.acceptA σD.wa σD.ws < ahPayoffA P σA σA.p) ∧
    (P.va < P.vs → σA.acceptBid σA.p = false ∧ σD.acceptA σD.wa σD.ws = false) ∧
    ahPayoffE P σA < dhPayoffE P σD.acceptA σD.wa σD.ws ∧
    ((P.va ≠ P.vs + P.b → ∃ σ : DHProfile, IsDHEquilibrium P σ) ∧
      (P.va ≠ P.vs → ∃ σ : AHProfile, IsAHEquilibrium P σ)) := by
  apply @AcquihiringMonopsony.Baseline.proposition_1 <;> assumption

end AcquihiringMonopsony.Baseline
