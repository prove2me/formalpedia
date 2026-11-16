-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBMix
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBMix
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:39:11.625909+00:00
-- url     : https://prove2.me/theorems/d2da8d46-fd03-452a-8893-7bd737d3148f
-- title:
--   Block-0 gate-mix MovesV and $f_3$ state lemmas
-- statement:
--   # Block-0 gate-mix MovesV and $f_3$ state lemmas
--
--   The `MovesV` certificate for the full block-0 gate-mix sequence, together with the evaluation of the $f_3$ state at gate pivots and bases. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBMix`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBMix split. Prefix / block-0 helper only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState3a
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBData1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBData2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBArgData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecArgEq
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecArgLRRel
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecPackBounds
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecIsChain
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBLemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Block-0 CoreB decide/proof split. Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

/-!
Block-0 gateMix MovesV and f3-state lemmas. Prefix / block-0 helper only; not a full-word W1F certificate.
-/

theorem argRel_of_gate_mem {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hg : g ∈ gatePack) :
    argRel (gateTp g) (gateN g) = true ∧
      argRel (gateTb g) (gateN g) = true := by
  have hl : (gateTp g, gateN g) ∈ gateArgLeft := by
    rw [← gateArgLeft_eq]
    exact List.mem_map.2 ⟨g, hg, rfl⟩
  have hr : (gateTb g, gateN g) ∈ gateArgRight := by
    rw [← gateArgRight_eq]
    exact List.mem_map.2 ⟨g, hg, rfl⟩
  exact ⟨gateArgLeft_argRel _ hl, gateArgRight_argRel _ hr⟩


theorem gateNf_sum : (gatePack.map gateNf).sum = 3547 := rfl

theorem mem_range'_bounds {start n o : ℕ} (h : o ∈ List.range' start n) :
    start ≤ o ∧ o < start + n := by
  rcases (List.mem_range' (step := 1)).1 h with ⟨i, hi, heq⟩
  have : o = start + i := by
    simpa [Nat.mul_one] using heq
  subst this
  exact ⟨Nat.le_add_right start i, Nat.add_lt_add_left hi start⟩

theorem gateAt_untouched (f : ℕ → ℕ) (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (start x : ℕ)
    (hx : x ∉ (gateAtOf g start).2.1) :
    (genF f [gateAtOf g start]).1 x = f x := by
  have hgen := genF_singleton f (gateAtOf g start)
  rw [hgen, gateAtOf_code]
  exact foldl_mvF_untouched (cND (gateN g)) (gateAtOf g start).2.1 f [] hx

def gateLowsOf (gs : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) : List ℕ :=
  gs.flatMap (fun g => [gatePiv g, gateBp g - 1])

theorem gateLowsOf_cons (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
    (gs : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) :
    gateLowsOf (g :: gs) = gatePiv g :: (gateBp g - 1) :: gateLowsOf gs :=
  rfl

theorem map_gateNf_cons (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
    (gs : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) :
    ((g :: gs).map gateNf).sum = gateNf g + (gs.map gateNf).sum :=
  rfl

theorem MovesV_gateMixOf (f : ℕ → ℕ)
    (gs : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) (start : ℕ)
    (hmem : ∀ g ∈ gs, g ∈ gatePack)
    (hstart : leafSlotBound ≤ start)
    (hsum : start + (gs.map gateNf).sum ≤ 14646)
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
    have hg : g ∈ gatePack := hmem g (List.mem_cons.2 (Or.inl rfl))
    have hb := gate_bounds_of_mem hg
    have harg := argRel_of_gate_mem hg
    have hbp : 1 ≤ gateBp g := hb.2.1
    have htp : gateTp g < v := hb.2.2.2.2.1
    have htb : gateTb g < v := hb.2.2.2.2.2.1
    have hnf : gateNf g ≤ 5 := hb.2.2.2.1
    have hn : gateN g ≤ 20278 := hb.2.2.2.2.2.2
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
      MovesV_gateAt f g start hbp htp htb
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
    have hmem' : ∀ g' ∈ gs, g' ∈ gatePack :=
      fun g' hg' => hmem g' (List.mem_cons_of_mem _ hg')
    have hstart' : leafSlotBound ≤ start + gateNf g :=
      Nat.le_trans hstart (Nat.le_add_right _ _)
    have hsum' : start + gateNf g + (gs.map gateNf).sum ≤ 14646 := by
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
      have hp' := (gate_bounds_of_mem hg'p).1
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
      have hb' := (gate_bounds_of_mem hg'p).2.2.1
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


theorem gateMix_sum_ok :
    leafSlotBound + (gatePack.map gateNf).sum ≤ 14646 := by
  have hb : leafSlotBound = 11099 := rfl
  rw [hb, gateNf_sum]

theorem f3_state_piv {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hg : g ∈ gatePack)
    (hown : srcS (gateTp g) ≤ gatePiv g ∧ gatePiv g < leafHi (gateTp g)) :
    (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 (wS (gatePiv g)) =
      cND (gateTp g) :=
  f3_low (gate_bounds_of_mem hg).2.2.2.2.1 hown

theorem f3_state_bp {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hg : g ∈ gatePack)
    (hown : srcS (gateTb g) ≤ gateBp g - 1 ∧ gateBp g - 1 < leafHi (gateTb g)) :
    (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 (wS (gateBp g - 1)) =
      cND (gateTb g) :=
  f3_low (gate_bounds_of_mem hg).2.2.2.2.2.1 hown

theorem MovesV_gateMix (f : ℕ → ℕ)
    (hPiv : ∀ g ∈ gatePack, f (wS (gatePiv g)) = cND (gateTp g))
    (hBp : ∀ g ∈ gatePack, f (wS (gateBp g - 1)) = cND (gateTb g))
    (hFr : ∀ q, leafSlotBound ≤ q → wS q < wAuxEnd → f (wS q) = 0)
    (hNd : (gateLowsOf gatePack).Nodup)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f gateMix).2 ∧
      ∀ x, (genF f gateMix).1 x < SupG.codeBound := by
  unfold gateMix
  exact MovesV_gateMixOf f gatePack leafSlotBound
    (fun _ hg => hg) (Nat.le_refl _) gateMix_sum_ok hPiv hBp hFr hNd hf


