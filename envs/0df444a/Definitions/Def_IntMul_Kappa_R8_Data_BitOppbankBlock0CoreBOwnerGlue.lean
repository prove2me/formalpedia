-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBOwnerGlue
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBOwnerGlue
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:37:12.878171+00:00
-- url     : https://prove2.me/theorems/a1d6d5b3-3566-4b88-8514-5d594e5f228d
-- title:
--   Glued block-0 owner-certificate specification
-- statement:
--   # Glued block-0 owner-certificate specification
--
--   The twelve owner-certificate chunks are assembled into a single specification relating each owner record to `srcS_vals`. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBOwnerGlue`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBOwnerGlue split. Prefix / block-0 helper only; not a full-word W1F certificate.

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
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner00
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner01
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner02
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner03
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner04
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner05
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner06
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner07
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner08
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner09
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner10
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreBDecOwner11
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
Glued owner-certificate specification. Prefix / block-0 helper only; not a full-word W1F certificate.
-/

theorem forall_mem_append {α : Type*} {P : α → Prop} {A B : List α}
    (hA : ∀ p ∈ A, P p) (hB : ∀ p ∈ B, P p) : ∀ p ∈ A ++ B, P p := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact hA p h
  · exact hB p h

theorem gateOwnerCert_spec :
    ∀ p ∈ gateOwnerCert,
      p.1 < 1771 ∧ srcS_vals[p.1]! = p.2.1 ∧
        (if p.1 + 1 = 1771 then 11099 else srcS_vals[p.1 + 1]!) = p.2.2 := by
  rw [gateOwnerCert_split]
  have h := forall_mem_append gateOwnerCert_spec_00 gateOwnerCert_spec_01
  have h := forall_mem_append h gateOwnerCert_spec_02
  have h := forall_mem_append h gateOwnerCert_spec_03
  have h := forall_mem_append h gateOwnerCert_spec_04
  have h := forall_mem_append h gateOwnerCert_spec_05
  have h := forall_mem_append h gateOwnerCert_spec_06
  have h := forall_mem_append h gateOwnerCert_spec_07
  have h := forall_mem_append h gateOwnerCert_spec_08
  have h := forall_mem_append h gateOwnerCert_spec_09
  have h := forall_mem_append h gateOwnerCert_spec_10
  exact forall_mem_append h gateOwnerCert_spec_11


theorem ownerCert_srcS {t src hi : ℕ}
    (h : (t, src, hi) ∈ gateOwnerCert) :
    t < v ∧ srcS t = src ∧ leafHi t = hi := by
  have hs := gateOwnerCert_spec (t, src, hi) h
  have hv : v = 1771 := rfl
  have ht : t < v := hv ▸ hs.1
  refine ⟨ht, ?src, ?hi⟩
  · have hget := srcS_get ht
    have htL : t < srcS_vals.length := by
      rw [srcS_vals_len]; exact hs.1
    rw [hget, ← srcS_vals_getElem_eq htL]
    exact hs.2.1
  · unfold leafHi
    have hb : leafSlotBound = 11099 := rfl
    split_ifs with htv
    · have : t + 1 = 1771 := hv ▸ htv
      simpa [this, hb] using hs.2.2
    · have ht1 : t + 1 < v := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt ht) htv
      have hget1 := srcS_get ht1
      have ht1L : t + 1 < srcS_vals.length := by
        rw [srcS_vals_len]; exact hv ▸ ht1
      have hne : t + 1 ≠ 1771 := fun heq => htv (hv ▸ heq)
      have hs2 : srcS_vals[t + 1]! = hi := by
        simpa [hne] using hs.2.2
      rw [hget1, ← srcS_vals_getElem_eq ht1L, hs2]


