-- Prove2me | Definitions.Def_QECert_FifteenWeights_CountChunk5
-- name    : QECert_FifteenWeights_CountChunk5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:59:11.197859+00:00
-- url     : https://prove2.me/theorems/dd06f6c6-f289-4dc7-bb42-1fb4076f474d
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
theorem block_count_5_0 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 0)).card = 0 := by
  decide +kernel

theorem block_count_5_1 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 1)).card = 0 := by
  decide +kernel

theorem block_count_5_2 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 2)).card = 0 := by
  decide +kernel

theorem block_count_5_3 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 3)).card = 0 := by
  decide +kernel

theorem block_count_5_4 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 4)).card = 6 := by
  decide +kernel

theorem block_count_5_5 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 5)).card = 0 := by
  decide +kernel

theorem block_count_5_6 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 6)).card = 20 := by
  decide +kernel

theorem block_count_5_7 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 7)).card = 0 := by
  decide +kernel

theorem block_count_5_8 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 8)).card = 24 := by
  decide +kernel

theorem block_count_5_9 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 9)).card = 0 := by
  decide +kernel

theorem block_count_5_10 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 10)).card = 12 := by
  decide +kernel

theorem block_count_5_11 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 11)).card = 0 := by
  decide +kernel

theorem block_count_5_12 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 12)).card = 2 := by
  decide +kernel

theorem block_count_5_13 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 13)).card = 0 := by
  decide +kernel

theorem block_count_5_14 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 14)).card = 0 := by
  decide +kernel

theorem block_count_5_15 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 5 j = 15)).card = 0 := by
  decide +kernel

end QEC.Distillation.BK15.CertifiedWeights


