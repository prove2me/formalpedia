-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBLemmas
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBLemmas
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:36:16.227519+00:00
-- url     : https://prove2.me/theorems/1964cf17-b445-492d-989b-2f4b39ccebd3
-- title:
--   Block-0 gate instruction and pack-slot lemmas
-- statement:
--   # Block-0 gate instruction and pack-slot lemmas
--
--   Instruction shape, nest-OK, `MovesV` at a single gate, and the correspondence between pack elements and slot-certificate records. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBLemmas`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBLemmas split. Prefix / block-0 helper only; not a full-word W1F certificate.

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
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecPackBounds
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecSlotMatch
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
Block-0 gate instruction lemmas and pack/slot correspondence. Prefix / block-0 helper only; not a full-word W1F certificate.
-/

theorem gateAtOf_code (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (start : ℕ) :
    (gateAtOf g start).1 = cND (gateN g) := rfl

theorem gateBp_ne_zero {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    (h : 1 ≤ gateBp g) : gateBp g ≠ 0 :=
  Nat.ne_of_gt (Nat.lt_of_succ_le h)

theorem gateAtOf_touch (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (start : ℕ)
    (hbp : 1 ≤ gateBp g) :
    (gateAtOf g start).2.1 =
      [wS (gatePiv g), wS (gateBp g - 1)] ++
        (gateExtras g start).flatMap (fun o => [wS o, wS (gatePiv g)]) := by
  have hnz : gateBp g ≠ 0 := gateBp_ne_zero hbp
  simp [gateAtOf, mk, recEl, touch, gateExtras, hnz, List.flatMap_map]

theorem mem_gateAtOf_touch {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} {start x : ℕ}
    (hbp : 1 ≤ gateBp g) :
    x ∈ (gateAtOf g start).2.1 ↔
      x = wS (gatePiv g) ∨ x = wS (gateBp g - 1) ∨
        ∃ o ∈ List.range' start (gateNf g), x = wS o := by
  rw [gateAtOf_touch g start hbp]
  constructor
  · intro hx
    rcases List.mem_append.1 hx with h | h
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
      exact h.imp_right Or.inl
    · rcases List.mem_flatMap.1 h with ⟨o, ho, hx'⟩
      have : x = wS o ∨ x = wS (gatePiv g) := by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx'
        exact hx'
      rcases this with hxo | hxp
      · unfold gateExtras at ho
        rcases List.mem_cons.1 ho with hbp1 | hf
        · have : o = gateBp g - 1 := hbp1
          rw [this] at hxo
          exact Or.inr (Or.inl hxo)
        · exact Or.inr (Or.inr ⟨o, hf, hxo⟩)
      · exact Or.inl hxp
  · intro hx
    rcases hx with hxp | hxb | ⟨o, ho, hxo⟩
    · exact List.mem_append.2 (Or.inl (by simp [hxp]))
    · exact List.mem_append.2 (Or.inl (by simp [hxb]))
    · refine List.mem_append.2 (Or.inr ?_)
      refine List.mem_flatMap.2 ⟨o, ?_, ?_⟩
      · exact List.mem_cons.2 (Or.inr ho)
      · simp [hxo]


theorem exists_of_map_eq {α β γ : Type*} {A : List α} {B : List β}
    {f : α → γ} {g : β → γ} (h : A.map f = B.map g) {a : α} (ha : a ∈ A) :
    ∃ b ∈ B, f a = g b := by
  induction A generalizing B with
  | nil => cases ha
  | cons a' A ih =>
    cases B with
    | nil =>
      cases h
    | cons b' B =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mem_cons] at ha
      rcases ha with ha | ha
      · subst ha
        exact ⟨b', List.mem_cons.2 (Or.inl rfl), h.1⟩
      · rcases ih h.2 ha with ⟨b, hb, heq⟩
        exact ⟨b, List.mem_cons.2 (Or.inr hb), heq⟩

theorem exists_slot_of_pack {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hg : g ∈ gatePack) :
    ∃ p ∈ gateSlotCert,
      gateTp g = slotTp p ∧ gatePiv g = slotPiv p ∧
        gateTb g = slotTb p ∧ gateBp g - 1 = slotBp1 p := by
  rcases exists_of_map_eq gateSlotCert_matches_pack hg with ⟨p, hp, heq⟩
  refine ⟨p, hp, ?_⟩
  exact ⟨congrArg Prod.fst heq,
    congrArg (fun x => x.2.1) heq,
    congrArg (fun x => x.2.2.1) heq,
    congrArg (fun x => x.2.2.2) heq⟩

theorem nestOK_of_argRel_owners {t n : ℕ}
    (ht : t < v) (hn : n ≤ 20278) (harg : argRel t n = true) :
    nestOK (cND t) (cND n) = true := by
  have hv : v = 1771 := rfl
  have ht' : t < 62478 := by omega
  have hn' : n < 62478 := by omega
  exact nestOK_of_argRel_ND (isND_cND ht') (isND_cND hn') harg

theorem MovesV_gateAt (f : ℕ → ℕ) (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (start : ℕ)
    (hbp : 1 ≤ gateBp g)
    (htp : gateTp g < v) (htb : gateTb g < v)
    (hP : f (wS (gatePiv g)) = cND (gateTp g))
    (hB : f (wS (gateBp g - 1)) = cND (gateTb g))
    (hF : ∀ o ∈ List.range' start (gateNf g), f (wS o) = 0)
    (hargP : argRel (gateTp g) (gateN g) = true)
    (hargB : argRel (gateTb g) (gateN g) = true)
    (hn : gateN g ≤ 20278)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f [gateAtOf g start]).2 ∧
      ∀ x, (genF f [gateAtOf g start]).1 x < SupG.codeBound := by
  have hgen := genF_singleton f (gateAtOf g start)
  have hcode := gateAtOf_code g start
  have hcB : cND (gateN g) < SupG.codeBound := cND_lt_bound_of_le hn
  have hold := (foldl_mvF_old (cND (gateN g)) (gateAtOf g start).2.1 f).1
  have hmem := foldl_mvF_mem (cND (gateN g)) (gateAtOf g start).2.1 f
  rw [hgen, hcode]
  constructor
  · intro ch hch mv hmv
    simp only [List.mem_singleton] at hch
    subst ch
    have hmv' : mv ∈ ((gateAtOf g start).2.1.foldl (mvF (cND (gateN g))) (f, [])).2 :=
      List.mem_reverse.1 hmv
    have hold0 : mv.2 = f mv.1 := hold mv hmv'
    have hin := hmem mv hmv'
    have hcases := (mem_gateAtOf_touch (x := mv.1) hbp).1 hin
    rcases hcases with hxp | hrest
    · have holdv : mv.2 = cND (gateTp g) := by rw [hold0, hxp, hP]
      rw [holdv]
      exact ⟨nestOK_of_argRel_owners htp hn hargP, cND_lt_bound htp, hcB⟩
    · rcases hrest with hxb | hf
      · have holdv : mv.2 = cND (gateTb g) := by rw [hold0, hxb, hB]
        rw [holdv]
        exact ⟨nestOK_of_argRel_owners htb hn hargB, cND_lt_bound htb, hcB⟩
      · rcases hf with ⟨o, ho, hxo⟩
        have holdz : mv.2 = 0 := by rw [hold0, hxo]; exact hF o ho
        rw [holdz]
        refine ⟨nestOK_of_le1 (Or.inl (Nat.zero_le 1)), ?_, hcB⟩
        have : SupG.codeBound = 64251 := SupG.codeBound_eq
        omega
  · intro x
    have hx := (foldl_mvF_old (cND (gateN g)) (gateAtOf g start).2.1 f).2 x
    rcases hx with hx | hx
    · rw [hx]; exact hf x
    · rw [hx]; exact hcB


theorem gate_bounds_of_mem {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hg : g ∈ gatePack) :
    gatePiv g < leafSlotBound ∧
      1 ≤ gateBp g ∧ gateBp g - 1 < leafSlotBound ∧
      gateNf g ≤ 5 ∧
      gateTp g < v ∧ gateTb g < v ∧
      gateN g ≤ 20278 := by
  have h := gatePack_simple_bounds g hg
  have hv : v = 1771 := rfl
  have hb : leafSlotBound = 11099 := rfl
  refine ⟨?_, h.2.1, ?_, h.2.2.2.1, ?_, ?_, h.2.2.2.2.2.2⟩
  · exact hb ▸ h.1
  · exact hb ▸ h.2.2.1
  · exact hv ▸ h.2.2.2.2.1
  · exact hv ▸ h.2.2.2.2.2.1


