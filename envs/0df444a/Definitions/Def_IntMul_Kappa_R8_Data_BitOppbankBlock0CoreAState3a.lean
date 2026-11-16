-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState3a
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState3a
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:22:38.287207+00:00
-- url     : https://prove2.me/theorems/a34e2645-954a-4140-92cf-f3b83146a6c3
-- title:
--   Block-0 f2/f3 prefix state after copy-out and leaf-mix
-- statement:
--   # Block-0 $f_2$ and $f_3$ prefix states
--
--   The composed generator state after the prefix, the copy-out sequence, and the leaf-mix sequence: on each leaf interval the state equals the corresponding source code $cND t$, and on high slots it remains zero. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   Depends on the published `Block0CoreAData`, `Block0CoreABits`, `Block0CoreACopy`, `Block0CoreALeaf`, `Block0CoreAState1`, and `Block0CoreAState2` packs.
--
--   ## Formalization Note
--
--   Lean identifiers: `f2_hP`, `f2_hE`, `f2_high`, `f3_low`, `f3_high`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: CoreA State3a split. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAState2
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
Block-0 `f2`/`f3` post-leafMix state lemmas.
Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem srcS_vals_getElem_eq {t : ℕ} (ht : t < srcS_vals.length) :
    srcS_vals[t]! = srcS_vals[t]'ht :=
  List.getElem!_of_getElem? (List.getElem?_eq_getElem ht)


theorem leafHi_le_srcS_of_lt {t t' : ℕ} (hlt : t < t') (ht' : t' < v) :
    leafHi t ≤ srcS t' := by
  have ht : t < v := Nat.lt_trans hlt ht'
  have ht1le : t + 1 ≤ t' := Nat.succ_le_of_lt hlt
  by_cases hnv : t + 1 = v
  · omega
  · have hts : t + 1 < v := srcS_succ_lt_of_ne ht hnv
    have hHi : leafHi t = srcS (t + 1) := leafHi_succ hts
    have hle : srcS (t + 1) ≤ srcS t' := by
      rcases Nat.eq_or_lt_of_le ht1le with heq | hlt'
      · rw [heq]
      · exact Nat.le_of_lt (srcS_lt_of_lt hlt' ht')
    exact hHi ▸ hle

theorem leaf_owner_unique {q t t' : ℕ}
    (ht : t < v) (ht' : t' < v)
    (hq : srcS t ≤ q ∧ q < leafHi t)
    (hq' : srcS t' ≤ q ∧ q < leafHi t') : t = t' := by
  rcases Nat.lt_trichotomy t t' with h | h | h
  · have : leafHi t ≤ srcS t' := leafHi_le_srcS_of_lt h ht'
    omega
  · exact h
  · have : leafHi t' ≤ srcS t := leafHi_le_srcS_of_lt h ht
    omega

theorem srcS_lt_slotBound {t : ℕ} (ht : t < v) : srcS t < leafSlotBound := by
  have : srcS t < 11091 := srcS_lt ht
  have : leafSlotBound = 11099 := rfl
  omega

theorem copyoND_wS_high (f : ℕ → ℕ)
    (hS : ∀ t, t < v → f (wS (srcS t)) = 0)
    (hX : ∀ t, t < v → f (wX t) = 0 ∨ f (wX t) = cND t)
    (hf : ∀ x, f x < SupG.codeBound)
    {q : ℕ} (hq : leafSlotBound ≤ q) :
    (genF f copyoND).1 (wS q) = f (wS q) :=
  copyoND_wS_other f hS hX hf (fun t ht =>
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (srcS_lt_slotBound ht) hq))

theorem wS_lt_aux_of_lt {q : ℕ} (hq : q < 20000) : wS q < wAuxEnd := by
  have : wS q = wEnt + q := wS_eq q
  have : wEnt = 3542 := rfl
  have : wAuxEnd = 31336 := rfl
  omega

theorem f2_hP :
    ∀ t, t < v →
      (genF (genF initR preF).1 copyoND).1 (wS (srcS t)) = cND t := by
  have hpre := genF_codes_le1 preF initR preF_codes_le1 (fun _ => initR_lt _)
  intro t ht
  exact copyoND_get_srcS (genF initR preF).1
    (fun t ht => preF_wS t ht) (fun t ht => preF_wX t ht) hpre.2 ht

theorem f2_hE :
    ∀ t, t < v → ∀ o ∈ leafExtras t,
      (genF (genF initR preF).1 copyoND).1 (wS o) = 0 := by
  have hpre := genF_codes_le1 preF initR preF_codes_le1 (fun _ => initR_lt _)
  intro t ht o ho
  have hnone : ∀ t', t' < v → srcS t' ≠ o :=
    fun t' ht' => leafExtras_ne_srcS ht ht' ho
  have hq : wS o < wAuxEnd := leafExtras_wS_lt_aux ht ho
  have h := copyoND_wS_other (genF initR preF).1
    (fun t ht => preF_wS t ht) (fun t ht => preF_wX t ht) hpre.2 hnone
  exact h.trans (preF_wS_any o hq)

theorem f2_high {q : ℕ} (hq : leafSlotBound ≤ q) (hqw : wS q < wAuxEnd) :
    (genF (genF initR preF).1 copyoND).1 (wS q) = 0 := by
  have hpre := genF_codes_le1 preF initR preF_codes_le1 (fun _ => initR_lt _)
  have h := copyoND_wS_high (genF initR preF).1
    (fun t ht => preF_wS t ht) (fun t ht => preF_wX t ht) hpre.2 hq
  exact h.trans (preF_wS_any q hqw)

theorem f3_low {t q : ℕ} (ht : t < v) (hin : srcS t ≤ q ∧ q < leafHi t) :
    (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 (wS q) = cND t :=
  leafMix_state_low (genF (genF initR preF).1 copyoND).1 f2_hP f2_hE ht hin

theorem f3_high {q : ℕ} (hq : leafSlotBound ≤ q) (hqw : wS q < wAuxEnd) :
    (genF (genF (genF initR preF).1 copyoND).1 leafMix).1 (wS q) = 0 :=
  leafMix_state_high (genF (genF initR preF).1 copyoND).1
    (fun q hq hqw => f2_high hq hqw) hq hqw


