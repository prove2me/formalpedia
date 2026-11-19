-- Prove2me | Definitions.Def_QECert_FifteenWeights_CountChunk1
-- name    : QECert_FifteenWeights_CountChunk1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:57:34.482332+00:00
-- url     : https://prove2.me/theorems/9d85411a-31b4-4b5e-ba78-6f043e5fca03
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
theorem block_count_1_0 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 0)).card = 0 := by
  decide +kernel

theorem block_count_1_1 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 1)).card = 0 := by
  decide +kernel

theorem block_count_1_2 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 2)).card = 0 := by
  decide +kernel

theorem block_count_1_3 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 3)).card = 0 := by
  decide +kernel

theorem block_count_1_4 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 4)).card = 12 := by
  decide +kernel

theorem block_count_1_5 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 5)).card = 0 := by
  decide +kernel

theorem block_count_1_6 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 6)).card = 0 := by
  decide +kernel

theorem block_count_1_7 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 7)).card = 0 := by
  decide +kernel

theorem block_count_1_8 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 8)).card = 48 := by
  decide +kernel

theorem block_count_1_9 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 9)).card = 0 := by
  decide +kernel

theorem block_count_1_10 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 10)).card = 0 := by
  decide +kernel

theorem block_count_1_11 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 11)).card = 0 := by
  decide +kernel

theorem block_count_1_12 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 12)).card = 4 := by
  decide +kernel

theorem block_count_1_13 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 13)).card = 0 := by
  decide +kernel

theorem block_count_1_14 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 14)).card = 0 := by
  decide +kernel

theorem block_count_1_15 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 1 j = 15)).card = 0 := by
  decide +kernel

end QEC.Distillation.BK15.CertifiedWeights


