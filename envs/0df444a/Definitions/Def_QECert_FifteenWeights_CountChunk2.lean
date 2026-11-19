-- Prove2me | Definitions.Def_QECert_FifteenWeights_CountChunk2
-- name    : QECert_FifteenWeights_CountChunk2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:58:50.80085+00:00
-- url     : https://prove2.me/theorems/4d9ee2e4-0d3f-4129-bde9-949403820521
-- title:
--   Code
-- statement:
--   Definitions and structural lemmas for Code, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean

import Definitions.Def_QECert_FifteenWeights_CoreWeights
set_option autoImplicit false
set_option maxHeartbeats 200000
open QEC QEC.Coding QEC.Distillation.BK15
open scoped BigOperators
namespace QEC.Distillation.BK15.CertifiedWeights
theorem block_count_2_0 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 0)).card = 0 := by
  decide +kernel

theorem block_count_2_1 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 1)).card = 0 := by
  decide +kernel

theorem block_count_2_2 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 2)).card = 0 := by
  decide +kernel

theorem block_count_2_3 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 3)).card = 0 := by
  decide +kernel

theorem block_count_2_4 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 4)).card = 12 := by
  decide +kernel

theorem block_count_2_5 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 5)).card = 0 := by
  decide +kernel

theorem block_count_2_6 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 6)).card = 0 := by
  decide +kernel

theorem block_count_2_7 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 7)).card = 0 := by
  decide +kernel

theorem block_count_2_8 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 8)).card = 48 := by
  decide +kernel

theorem block_count_2_9 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 9)).card = 0 := by
  decide +kernel

theorem block_count_2_10 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 10)).card = 0 := by
  decide +kernel

theorem block_count_2_11 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 11)).card = 0 := by
  decide +kernel

theorem block_count_2_12 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 12)).card = 4 := by
  decide +kernel

theorem block_count_2_13 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 13)).card = 0 := by
  decide +kernel

theorem block_count_2_14 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 14)).card = 0 := by
  decide +kernel

theorem block_count_2_15 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 2 j = 15)).card = 0 := by
  decide +kernel

end QEC.Distillation.BK15.CertifiedWeights


