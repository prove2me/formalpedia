-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsB2
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsB2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:33:16.185545+00:00
-- url     : https://prove2.me/theorems/9e325cd7-b48b-4dcf-9477-f08b1b9dba0e
-- title:
--   Block-0 slot-owner certificates, chunk 7
-- statement:
--   # Block-0 slot certificates, chunk 7
--
--   Chunk certificates for the published `Block0SlotsData` pack. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: block-0 chunk certificates. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsData

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsB2

theorem slot_c07_srcP :
    slot_c07.map slotSrcP = slot_c07.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c07_hiP :
    slot_c07.map slotHiP = slot_c07.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c07_srcB :
    slot_c07.map slotSrcB = slot_c07.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c07_hiB :
    slot_c07.map slotHiB = slot_c07.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c07_owners :
    ∀ p ∈ slot_c07,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c07_srcP p hp,
    forall_of_map_eq slot_c07_hiP p hp,
    forall_of_map_eq slot_c07_srcB p hp,
    forall_of_map_eq slot_c07_hiB p hp⟩

end IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsB2


