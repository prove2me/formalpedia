-- Prove2me | Definitions.Def_QECert_FifteenWeights_CountChunk7
-- name    : QECert_FifteenWeights_CountChunk7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:59:37.944203+00:00
-- url     : https://prove2.me/theorems/0d2654cf-6c16-4c78-b418-36d16f439422
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
theorem block_count_7_0 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 0)).card = 0 := by
  decide +kernel

theorem block_count_7_1 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 1)).card = 0 := by
  decide +kernel

theorem block_count_7_2 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 2)).card = 0 := by
  decide +kernel

theorem block_count_7_3 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 3)).card = 0 := by
  decide +kernel

theorem block_count_7_4 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 4)).card = 6 := by
  decide +kernel

theorem block_count_7_5 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 5)).card = 0 := by
  decide +kernel

theorem block_count_7_6 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 6)).card = 20 := by
  decide +kernel

theorem block_count_7_7 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 7)).card = 0 := by
  decide +kernel

theorem block_count_7_8 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 8)).card = 24 := by
  decide +kernel

theorem block_count_7_9 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 9)).card = 0 := by
  decide +kernel

theorem block_count_7_10 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 10)).card = 12 := by
  decide +kernel

theorem block_count_7_11 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 11)).card = 0 := by
  decide +kernel

theorem block_count_7_12 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 12)).card = 2 := by
  decide +kernel

theorem block_count_7_13 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 13)).card = 0 := by
  decide +kernel

theorem block_count_7_14 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 14)).card = 0 := by
  decide +kernel

theorem block_count_7_15 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 7 j = 15)).card = 0 := by
  decide +kernel

end QEC.Distillation.BK15.CertifiedWeights


