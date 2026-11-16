-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsC3
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsC3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:33:08.874033+00:00
-- url     : https://prove2.me/theorems/9a8e9aae-ccef-4a89-a5f3-268c76bb3c38
-- title:
--   Block-0 slot-owner certificates, chunk 11
-- statement:
--   # Block-0 slot certificates, chunk 11
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

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsC3

theorem slot_c11_srcP :
    slot_c11.map slotSrcP = slot_c11.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c11_hiP :
    slot_c11.map slotHiP = slot_c11.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c11_srcB :
    slot_c11.map slotSrcB = slot_c11.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c11_hiB :
    slot_c11.map slotHiB = slot_c11.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c11_owners :
    ∀ p ∈ slot_c11,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c11_srcP p hp,
    forall_of_map_eq slot_c11_hiP p hp,
    forall_of_map_eq slot_c11_srcB p hp,
    forall_of_map_eq slot_c11_hiB p hp⟩

end IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsC3


