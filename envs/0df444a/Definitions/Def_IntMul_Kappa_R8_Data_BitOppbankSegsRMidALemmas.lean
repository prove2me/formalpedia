-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidALemmas
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidALemmas
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:23:32.00334+00:00
-- url     : https://prove2.me/theorems/5b26cea5-b1c2-4613-8ab3-8c0bcbdf26f5
-- title:
--   SegsR midA bound lift, nestOK, and MovesV_midAt
-- statement:
--   # SegsR midA bound lift, nestOK, and MovesV_midAt
--
--   MidA lemmas with the loosened node bound n ≤ 61313: cND_lt_bound_of_le_mid, nestOK_of_argRel_owners_mid, midA_bounds_of_mem, and MovesV_midAt. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidALemmas`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidALemmas. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD.

-- Later-segs midA helper only; not a full-word W1F / segsR / preloadHits certificate.
-- Imports densified MidADataD (not raw-n MidAData).
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBLemmas
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADataD
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecPackBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem cND_lt_bound_of_le_mid {t : ℕ} (ht : t ≤ 61313) :
    cND t < SupG.codeBound := by
  rw [cND_eq]
  have : SupG.codeBound = 64251 := SupG.codeBound_eq
  omega

theorem nestOK_of_argRel_owners_mid {t n : ℕ}
    (ht : t < v) (hn : n ≤ 61313) (harg : argRel t n = true) :
    nestOK (cND t) (cND n) = true := by
  have hv : v = 1771 := rfl
  have ht' : t < 62478 := by omega
  have hn' : n < 62478 := by omega
  exact nestOK_of_argRel_ND (isND_cND ht') (isND_cND hn') harg

theorem midA_bounds_of_mem {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hg : g ∈ midAPack) :
    gatePiv g < leafSlotBound ∧
      1 ≤ gateBp g ∧ gateBp g - 1 < leafSlotBound ∧
      gateNf g ≤ 5 ∧
      gateTp g < v ∧ gateTb g < v ∧
      gateN g ≤ 61313 := by
  have h := midAPack_simple_bounds g hg
  have hv : v = 1771 := rfl
  have hb : leafSlotBound = 11099 := rfl
  refine ⟨?_, h.2.1, ?_, h.2.2.2.1, ?_, ?_, h.2.2.2.2.2.2⟩
  · exact hb ▸ h.1
  · exact hb ▸ h.2.2.1
  · exact hv ▸ h.2.2.2.2.1
  · exact hv ▸ h.2.2.2.2.2.1

theorem MovesV_midAt (f : ℕ → ℕ) (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (start : ℕ)
    (hbp : 1 ≤ gateBp g)
    (htp : gateTp g < v) (htb : gateTb g < v)
    (hP : f (wS (gatePiv g)) = cND (gateTp g))
    (hB : f (wS (gateBp g - 1)) = cND (gateTb g))
    (hF : ∀ o ∈ List.range' start (gateNf g), f (wS o) = 0)
    (hargP : argRel (gateTp g) (gateN g) = true)
    (hargB : argRel (gateTb g) (gateN g) = true)
    (hn : gateN g ≤ 61313)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f [gateAtOf g start]).2 ∧
      ∀ x, (genF f [gateAtOf g start]).1 x < SupG.codeBound := by
  have hgen := genF_singleton f (gateAtOf g start)
  have hcode := gateAtOf_code g start
  have hcB : cND (gateN g) < SupG.codeBound := cND_lt_bound_of_le_mid hn
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
      exact ⟨nestOK_of_argRel_owners_mid htp hn hargP, cND_lt_bound htp, hcB⟩
    · rcases hrest with hxb | hf
      · have holdv : mv.2 = cND (gateTb g) := by rw [hold0, hxb, hB]
        rw [holdv]
        exact ⟨nestOK_of_argRel_owners_mid htb hn hargB, cND_lt_bound htb, hcB⟩
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


