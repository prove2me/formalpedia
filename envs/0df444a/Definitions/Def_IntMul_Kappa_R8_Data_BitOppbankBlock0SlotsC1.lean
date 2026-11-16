-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsC1
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsC1
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:33:42.606135+00:00
-- url     : https://prove2.me/theorems/accb1c56-4015-4ab8-a206-817cf3ccf195
-- title:
--   Block-0 slot-owner certificates, chunk 10
-- statement:
--   # Block-0 slot certificates, chunk 10
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

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsC1

theorem slot_c10_srcP :
    slot_c10.map slotSrcP = slot_c10.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c10_hiP :
    slot_c10.map slotHiP = slot_c10.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c10_srcB :
    slot_c10.map slotSrcB = slot_c10.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c10_hiB :
    slot_c10.map slotHiB = slot_c10.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c10_owners :
    ∀ p ∈ slot_c10,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c10_srcP p hp,
    forall_of_map_eq slot_c10_hiP p hp,
    forall_of_map_eq slot_c10_srcB p hp,
    forall_of_map_eq slot_c10_hiB p hp⟩

end IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsC1


