-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsB1
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsB1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:29:21.063347+00:00
-- url     : https://prove2.me/theorems/2b446ad5-fa36-4973-8603-868533ae9552
-- title:
--   Block-0 slot-owner certificates, chunks 5–6
-- statement:
--   # Block-0 slot owners, chunks 5–6
--
--   Map-`rfl` owner certificates for chunks 5–6 of `gateSlotCert`. Depends on published `Block0SlotsData`. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: block-0 chunk certificates. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsData

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsB1

theorem slot_c05_srcP :
    slot_c05.map slotSrcP = slot_c05.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c05_hiP :
    slot_c05.map slotHiP = slot_c05.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c05_srcB :
    slot_c05.map slotSrcB = slot_c05.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c05_hiB :
    slot_c05.map slotHiB = slot_c05.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c05_owners :
    ∀ p ∈ slot_c05,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c05_srcP p hp,
    forall_of_map_eq slot_c05_hiP p hp,
    forall_of_map_eq slot_c05_srcB p hp,
    forall_of_map_eq slot_c05_hiB p hp⟩

theorem slot_c06_srcP :
    slot_c06.map slotSrcP = slot_c06.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c06_hiP :
    slot_c06.map slotHiP = slot_c06.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c06_srcB :
    slot_c06.map slotSrcB = slot_c06.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c06_hiB :
    slot_c06.map slotHiB = slot_c06.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c06_owners :
    ∀ p ∈ slot_c06,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c06_srcP p hp,
    forall_of_map_eq slot_c06_hiP p hp,
    forall_of_map_eq slot_c06_srcB p hp,
    forall_of_map_eq slot_c06_hiB p hp⟩

end IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsB1


