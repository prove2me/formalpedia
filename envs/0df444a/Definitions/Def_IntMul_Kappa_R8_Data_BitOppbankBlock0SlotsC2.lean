-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsC2
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsC2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:28:09.517376+00:00
-- url     : https://prove2.me/theorems/5dcaf722-d5d6-47be-bfb4-f0007c2efd1e
-- title:
--   Block-0 slot-owner certificates, chunks 12–13
-- statement:
--   # Block-0 slot owners, chunks 12–13
--
--   Map-`rfl` owner certificates for chunks 12–13 of `gateSlotCert`. Depends on published `Block0SlotsData`. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: block-0 chunk certificates. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsData

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsC2

theorem slot_c12_srcP :
    slot_c12.map slotSrcP = slot_c12.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c12_hiP :
    slot_c12.map slotHiP = slot_c12.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c12_srcB :
    slot_c12.map slotSrcB = slot_c12.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c12_hiB :
    slot_c12.map slotHiB = slot_c12.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c12_owners :
    ∀ p ∈ slot_c12,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c12_srcP p hp,
    forall_of_map_eq slot_c12_hiP p hp,
    forall_of_map_eq slot_c12_srcB p hp,
    forall_of_map_eq slot_c12_hiB p hp⟩

theorem slot_c13_srcP :
    slot_c13.map slotSrcP = slot_c13.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c13_hiP :
    slot_c13.map slotHiP = slot_c13.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c13_srcB :
    slot_c13.map slotSrcB = slot_c13.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c13_hiB :
    slot_c13.map slotHiB = slot_c13.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c13_owners :
    ∀ p ∈ slot_c13,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c13_srcP p hp,
    forall_of_map_eq slot_c13_hiP p hp,
    forall_of_map_eq slot_c13_srcB p hp,
    forall_of_map_eq slot_c13_hiB p hp⟩

end IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsC2


