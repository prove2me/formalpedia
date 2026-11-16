-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsA
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsA
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T16:18:46.139701+00:00
-- url     : https://prove2.me/theorems/39601702-7333-4baa-a02a-93e01dacbf1f
-- title:
--   Block-0 slot-owner certificates, chunks 0–4
-- statement:
--   # Block-0 slot owners, chunks 0–4
--
--   Four `rfl` map equalities and the derived owner statement for each of the first five 100-row chunks of `gateSlotCert`, against `srcS_vals`. Depends on the published `Block0SlotsData` pack. Prefix / block-0 helper only; not a full-word W1F certificate.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: block-0 slot chunk certificates. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0SlotsData

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

open IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsData

namespace IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsA

theorem slot_c00_srcP :
    slot_c00.map slotSrcP = slot_c00.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c00_hiP :
    slot_c00.map slotHiP = slot_c00.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c00_srcB :
    slot_c00.map slotSrcB = slot_c00.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c00_hiB :
    slot_c00.map slotHiB = slot_c00.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c00_owners :
    ∀ p ∈ slot_c00,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c00_srcP p hp,
    forall_of_map_eq slot_c00_hiP p hp,
    forall_of_map_eq slot_c00_srcB p hp,
    forall_of_map_eq slot_c00_hiB p hp⟩

theorem slot_c01_srcP :
    slot_c01.map slotSrcP = slot_c01.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c01_hiP :
    slot_c01.map slotHiP = slot_c01.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c01_srcB :
    slot_c01.map slotSrcB = slot_c01.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c01_hiB :
    slot_c01.map slotHiB = slot_c01.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c01_owners :
    ∀ p ∈ slot_c01,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c01_srcP p hp,
    forall_of_map_eq slot_c01_hiP p hp,
    forall_of_map_eq slot_c01_srcB p hp,
    forall_of_map_eq slot_c01_hiB p hp⟩

theorem slot_c02_srcP :
    slot_c02.map slotSrcP = slot_c02.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c02_hiP :
    slot_c02.map slotHiP = slot_c02.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c02_srcB :
    slot_c02.map slotSrcB = slot_c02.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c02_hiB :
    slot_c02.map slotHiB = slot_c02.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c02_owners :
    ∀ p ∈ slot_c02,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c02_srcP p hp,
    forall_of_map_eq slot_c02_hiP p hp,
    forall_of_map_eq slot_c02_srcB p hp,
    forall_of_map_eq slot_c02_hiB p hp⟩

theorem slot_c03_srcP :
    slot_c03.map slotSrcP = slot_c03.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c03_hiP :
    slot_c03.map slotHiP = slot_c03.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c03_srcB :
    slot_c03.map slotSrcB = slot_c03.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c03_hiB :
    slot_c03.map slotHiB = slot_c03.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c03_owners :
    ∀ p ∈ slot_c03,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c03_srcP p hp,
    forall_of_map_eq slot_c03_hiP p hp,
    forall_of_map_eq slot_c03_srcB p hp,
    forall_of_map_eq slot_c03_hiB p hp⟩

theorem slot_c04_srcP :
    slot_c04.map slotSrcP = slot_c04.map (fun p => srcAt (slotTp p)) := rfl

theorem slot_c04_hiP :
    slot_c04.map slotHiP = slot_c04.map (fun p => hiAt (slotTp p)) := rfl

theorem slot_c04_srcB :
    slot_c04.map slotSrcB = slot_c04.map (fun p => srcAt (slotTb p)) := rfl

theorem slot_c04_hiB :
    slot_c04.map slotHiB = slot_c04.map (fun p => hiAt (slotTb p)) := rfl

theorem slot_c04_owners :
    ∀ p ∈ slot_c04,
      slotSrcP p = srcAt (slotTp p) ∧ slotHiP p = hiAt (slotTp p) ∧
        slotSrcB p = srcAt (slotTb p) ∧ slotHiB p = hiAt (slotTb p) := by
  intro p hp
  refine ⟨forall_of_map_eq slot_c04_srcP p hp,
    forall_of_map_eq slot_c04_hiP p hp,
    forall_of_map_eq slot_c04_srcB p hp,
    forall_of_map_eq slot_c04_hiB p hp⟩

end IntMul.Kappa.R8.Bit.Oppbank.Block0SlotsA


