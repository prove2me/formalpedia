-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0Slots
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0Slots
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:38:21.762209+00:00
-- url     : https://prove2.me/theorems/84342e11-87f6-4ed6-b051-e9105ee5853c
-- title:
--   Block-0 gate slot owners
-- statement:
--   # Block-0 gate slot owners
--
--   Glue pack: `gateSlotCert_owners` for the 1301 block-0 gate slots, assembled from the published Data / A / B1–B3 / C1–C3 / C2 chunk-certificate packs. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: block-0 helper glue. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsA
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsB1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsB2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsB3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsC1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsC2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsC3

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData
open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsA
open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsB1
open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsB2
open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsB3
open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsC1
open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsC2
open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsC3

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0Slots

theorem slot_owners_00 :
    ∀ p ∈ slot_c00,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  slot_c00_owners

theorem slot_owners_01 :
    ∀ p ∈ slot_c00 ++ slot_c01,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_00 slot_c01_owners

theorem slot_owners_02 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_01 slot_c02_owners

theorem slot_owners_03 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_02 slot_c03_owners

theorem slot_owners_04 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_03 slot_c04_owners

theorem slot_owners_05 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04 ++ slot_c05,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_04 slot_c05_owners

theorem slot_owners_06 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04 ++ slot_c05 ++ slot_c06,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_05 slot_c06_owners

theorem slot_owners_07 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04 ++ slot_c05 ++ slot_c06 ++ slot_c07,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_06 slot_c07_owners

theorem slot_owners_08 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04 ++ slot_c05 ++ slot_c06 ++ slot_c07 ++ slot_c08,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_07 slot_c08_owners

theorem slot_owners_09 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04 ++ slot_c05 ++ slot_c06 ++ slot_c07 ++ slot_c08 ++ slot_c09,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_08 slot_c09_owners

theorem slot_owners_10 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04 ++ slot_c05 ++ slot_c06 ++ slot_c07 ++ slot_c08 ++ slot_c09 ++ slot_c10,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_09 slot_c10_owners

theorem slot_owners_11 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04 ++ slot_c05 ++ slot_c06 ++ slot_c07 ++ slot_c08 ++ slot_c09 ++ slot_c10 ++ slot_c11,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_10 slot_c11_owners

theorem slot_owners_12 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04 ++ slot_c05 ++ slot_c06 ++ slot_c07 ++ slot_c08 ++ slot_c09 ++ slot_c10 ++ slot_c11 ++ slot_c12,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_11 slot_c12_owners

theorem slot_owners_13 :
    ∀ p ∈ slot_c00 ++ slot_c01 ++ slot_c02 ++ slot_c03 ++ slot_c04 ++ slot_c05 ++ slot_c06 ++ slot_c07 ++ slot_c08 ++ slot_c09 ++ slot_c10 ++ slot_c11 ++ slot_c12 ++ slot_c13,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) :=
  forall_mem_append slot_owners_12 slot_c13_owners

theorem gateSlotCert_owners :
    ∀ p ∈ gateSlotCert,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  rw [slot_split]
  exact slot_owners_13

/-- Re-export so official-sol qualified names stay defeq to the Data literals. -/
abbrev srcS_vals := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.srcS_vals
abbrev gateSlotCert := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.gateSlotCert
abbrev srcAt := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.srcAt
abbrev hiAt := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.hiAt
abbrev slotTp := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotTp
abbrev slotTb := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotTb
abbrev slotSrcP := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotSrcP
abbrev slotHiP := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotHiP
abbrev slotSrcB := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotSrcB
abbrev slotHiB := _root_.IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData.slotHiB

end IntMul.Kappa.R8.Bit.Oppbank.Block0Slots


