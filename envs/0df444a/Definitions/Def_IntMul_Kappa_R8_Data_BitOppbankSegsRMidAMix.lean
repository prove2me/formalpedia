-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidAMix
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidAMix
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:27:12.736205+00:00
-- url     : https://prove2.me/theorems/0f17291c-1629-4ae7-8f95-e6bb2198c6ef
-- title:
--   SegsR midA MovesV_midAMixOf with fresh bound 18359
-- statement:
--   # SegsR midA MovesV_midAMixOf with fresh bound 18359
--
--   Abstract append lemma `MovesV_midAMixOf` for a sublist of the densified midAPack, with fresh-extra bound `start + (gs.map gateNf).sum ≤ 18359`, midA membership, and a Nodup hypothesis on `gateLowsOf gs` (Nodup of the full midA lows is still to be certified). Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidAMix`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidAMix. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD.

-- Later-segs midA helper only; not a full-word W1F / segsR / preloadHits certificate.
-- Imports densified MidADataD (not raw-n MidAData).
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBMix
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADataD
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidAFacts
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgGlue
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem MovesV_midAMixOf (f : ℕ → ℕ)
    (gs : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (start : ℕ)
    (hmem : ∀ g ∈ gs, g ∈ midAPack)
    (hstart : leafSlotBound ≤ start)
    (hsum : start + (gs.map gateNf).sum ≤ 18359)
    (hPiv : ∀ g ∈ gs, f (wS (gatePiv g)) = cND (gateTp g))
    (hBp : ∀ g ∈ gs, f (wS (gateBp g - 1)) = cND (gateTb g))
    (hFr : ∀ q, start ≤ q → wS q < wAuxEnd → f (wS q) = 0)
    (hNd : (gateLowsOf gs).Nodup)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f (gateMixOf gs start)).2 ∧
      ∀ x, (genF f (gateMixOf gs start)).1 x < SupG.codeBound := by
  induction gs generalizing f start with
  | nil =>
    constructor
    · intro ch hc; cases hc
    · intro x; simpa [gateMixOf, genF] using hf x
  | cons g gs ih =>
    have hg : g ∈ midAPack := hmem g (List.mem_cons.2 (Or.inl rfl))
    have hb := midA_bounds_of_mem hg
    have harg := argRel_of_midA_mem hg
    have hbp : 1 ≤ gateBp g := hb.2.1
    have htp : gateTp g < v := hb.2.2.2.2.1
    have htb : gateTb g < v := hb.2.2.2.2.2.1
    have hnf : gateNf g ≤ 5 := hb.2.2.2.1
    have hn : gateN g ≤ 61313 := hb.2.2.2.2.2.2
    have hpivlt : gatePiv g < leafSlotBound := hb.1
    have hbp1lt : gateBp g - 1 < leafSlotBound := hb.2.2.1
    have hF : ∀ o ∈ List.range' start (gateNf g), f (wS o) = 0 := by
      intro o ho
      have ⟨hlo, hhi⟩ := mem_range'_bounds ho
      have hbound : o < 20000 := by
        have : o < start + gateNf g := hhi
        have hsumg := hsum
        rw [map_gateNf_cons] at hsumg
        omega
      exact hFr o hlo (wS_lt_aux_of_lt hbound)
    have hone :=
      MovesV_midAt f g start hbp htp htb
        (hPiv g (List.mem_cons.2 (Or.inl rfl)))
        (hBp g (List.mem_cons.2 (Or.inl rfl)))
        hF harg.1 harg.2 hn hf
    have hmix : gateMixOf (g :: gs) start =
        gateAtOf g start :: gateMixOf gs (start + gateNf g) := rfl
    have happ := genF_append f [gateAtOf g start] (gateMixOf gs (start + gateNf g))
    simp only [List.singleton_append] at happ
    rw [hmix, happ]
    set f' := (genF f [gateAtOf g start]).1
    have hf' : ∀ x, f' x < SupG.codeBound := hone.2
    have hndc : (gatePiv g :: (gateBp g - 1) :: gateLowsOf gs).Nodup := by
      simpa [gateLowsOf_cons] using hNd
    have hnd1 := List.nodup_cons.1 hndc
    have hnd2 := List.nodup_cons.1 hnd1.2
    have hNd' : (gateLowsOf gs).Nodup := hnd2.2
    have hnin_p : gatePiv g ∉ gateLowsOf gs :=
      fun hin => hnd1.1 (List.mem_cons.2 (Or.inr hin))
    have hnin_b : gateBp g - 1 ∉ gateLowsOf gs := hnd2.1
    have hmem' : ∀ g' ∈ gs, g' ∈ midAPack :=
      fun g' hg' => hmem g' (List.mem_cons_of_mem _ hg')
    have hstart' : leafSlotBound ≤ start + gateNf g :=
      Nat.le_trans hstart (Nat.le_add_right _ _)
    have hsum' : start + gateNf g + (gs.map gateNf).sum ≤ 18359 := by
      have hsumg := hsum
      rw [map_gateNf_cons] at hsumg
      omega
    have hnot_touch_low {q : ℕ} (hq : q < leafSlotBound)
        (hnq : q ≠ gatePiv g) (hnb : q ≠ gateBp g - 1) :
        wS q ∉ (gateAtOf g start).2.1 := by
      intro hin
      have hcases := (mem_gateAtOf_touch (x := wS q) hbp).1 hin
      rcases hcases with hxp | hxb | ⟨o, ho, hxo⟩
      · exact hnq (wS_inj hxp)
      · exact hnb (wS_inj hxb)
      · have ⟨hlo, _⟩ := mem_range'_bounds ho
        have : q = o := wS_inj hxo
        have : leafSlotBound ≤ q := Nat.le_trans hstart (this ▸ hlo)
        exact Nat.not_lt.2 this hq
    have hPiv' : ∀ g' ∈ gs, f' (wS (gatePiv g')) = cND (gateTp g') := by
      intro g' hg'
      have hg'p := hmem' g' hg'
      have hp' := (midA_bounds_of_mem hg'p).1
      have hne1 : gatePiv g' ≠ gatePiv g := by
        intro heq
        apply hnin_p
        have : gatePiv g' ∈ gateLowsOf gs :=
          List.mem_flatMap.2 ⟨g', hg', by simp⟩
        exact heq ▸ this
      have hne2 : gatePiv g' ≠ gateBp g - 1 := by
        intro heq
        apply hnin_b
        have : gatePiv g' ∈ gateLowsOf gs :=
          List.mem_flatMap.2 ⟨g', hg', by simp⟩
        exact heq ▸ this
      have hstay := gateAt_untouched f g start (wS (gatePiv g'))
        (hnot_touch_low hp' hne1 hne2)
      unfold f' at *
      exact hstay.trans (hPiv g' (List.mem_cons_of_mem _ hg'))
    have hBp' : ∀ g' ∈ gs, f' (wS (gateBp g' - 1)) = cND (gateTb g') := by
      intro g' hg'
      have hg'p := hmem' g' hg'
      have hb' := (midA_bounds_of_mem hg'p).2.2.1
      have hne1 : gateBp g' - 1 ≠ gatePiv g := by
        intro heq
        apply hnin_p
        have : gateBp g' - 1 ∈ gateLowsOf gs :=
          List.mem_flatMap.2 ⟨g', hg', by simp⟩
        exact heq ▸ this
      have hne2 : gateBp g' - 1 ≠ gateBp g - 1 := by
        intro heq
        apply hnin_b
        have : gateBp g' - 1 ∈ gateLowsOf gs :=
          List.mem_flatMap.2 ⟨g', hg', by simp⟩
        exact heq ▸ this
      have hstay := gateAt_untouched f g start (wS (gateBp g' - 1))
        (hnot_touch_low hb' hne1 hne2)
      unfold f' at *
      exact hstay.trans (hBp g' (List.mem_cons_of_mem _ hg'))
    have hFr' : ∀ q, start + gateNf g ≤ q → wS q < wAuxEnd → f' (wS q) = 0 := by
      intro q hq hqw
      have hnot : wS q ∉ (gateAtOf g start).2.1 := by
        intro hin
        have hcases := (mem_gateAtOf_touch (x := wS q) hbp).1 hin
        rcases hcases with hxp | hxb | ⟨o, ho, hxo⟩
        · have hqeq : q = gatePiv g := wS_inj hxp
          have hle : leafSlotBound ≤ q :=
            Nat.le_trans hstart (Nat.le_trans (Nat.le_add_right start (gateNf g)) hq)
          have hlt : q < leafSlotBound := hqeq ▸ hpivlt
          exact (Nat.not_le_of_gt hlt) hle
        · have hqeq : q = gateBp g - 1 := wS_inj hxb
          have hle : leafSlotBound ≤ q :=
            Nat.le_trans hstart (Nat.le_trans (Nat.le_add_right start (gateNf g)) hq)
          have hlt : q < leafSlotBound := hqeq ▸ hbp1lt
          exact (Nat.not_le_of_gt hlt) hle
        · have ⟨_, hhi⟩ := mem_range'_bounds ho
          have : q = o := wS_inj hxo
          omega
      have hstay := gateAt_untouched f g start (wS q) hnot
      unfold f' at *
      have hlo : start ≤ q := Nat.le_trans (Nat.le_add_right start (gateNf g)) hq
      exact hstay.trans (hFr q hlo hqw)
    have ⟨hMVrest, hBrest⟩ :=
      ih f' (start + gateNf g) hmem' hstart' hsum' hPiv' hBp' hFr' hNd' hf'
    constructor
    · exact MovesV_append.2 ⟨hone.1, hMVrest⟩
    · exact hBrest


