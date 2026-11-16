-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsB3
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsB3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:34:25.942623+00:00
-- url     : https://prove2.me/theorems/d8b18578-697f-4210-9067-faa96bf72d11
-- title:
--   Block-0 slot-owner certificates, chunks 8–9
-- statement:
--   # Block-0 slot certificates, chunks 8–9
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

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsB3

theorem slot_c08_srcP :
    slot_c08.map slotSrcP = slot_c08.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c08_hiP :
    slot_c08.map slotHiP = slot_c08.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c08_srcB :
    slot_c08.map slotSrcB = slot_c08.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c08_hiB :
    slot_c08.map slotHiB = slot_c08.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c08_owners :
    ∀ p ∈ slot_c08,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c08_srcP p hp,
    forall_of_map_eq slot_c08_hiP p hp,
    forall_of_map_eq slot_c08_srcB p hp,
    forall_of_map_eq slot_c08_hiB p hp⟩

theorem slot_c09_srcP :
    slot_c09.map slotSrcP = slot_c09.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c09_hiP :
    slot_c09.map slotHiP = slot_c09.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c09_srcB :
    slot_c09.map slotSrcB = slot_c09.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c09_hiB :
    slot_c09.map slotHiB = slot_c09.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c09_owners :
    ∀ p ∈ slot_c09,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c09_srcP p hp,
    forall_of_map_eq slot_c09_hiP p hp,
    forall_of_map_eq slot_c09_srcB p hp,
    forall_of_map_eq slot_c09_hiB p hp⟩

end IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsB3


