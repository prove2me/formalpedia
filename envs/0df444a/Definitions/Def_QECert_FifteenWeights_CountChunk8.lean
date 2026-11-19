-- Prove2me | Definitions.Def_QECert_FifteenWeights_CountChunk8
-- name    : QECert_FifteenWeights_CountChunk8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:59:35.654351+00:00
-- url     : https://prove2.me/theorems/92231a59-99d4-49dd-98b0-243734c90466
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
theorem block_count_8_0 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 0)).card = 0 := by
  decide +kernel

theorem block_count_8_1 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 1)).card = 0 := by
  decide +kernel

theorem block_count_8_2 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 2)).card = 0 := by
  decide +kernel

theorem block_count_8_3 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 3)).card = 0 := by
  decide +kernel

theorem block_count_8_4 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 4)).card = 6 := by
  decide +kernel

theorem block_count_8_5 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 5)).card = 0 := by
  decide +kernel

theorem block_count_8_6 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 6)).card = 20 := by
  decide +kernel

theorem block_count_8_7 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 7)).card = 0 := by
  decide +kernel

theorem block_count_8_8 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 8)).card = 24 := by
  decide +kernel

theorem block_count_8_9 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 9)).card = 0 := by
  decide +kernel

theorem block_count_8_10 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 10)).card = 12 := by
  decide +kernel

theorem block_count_8_11 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 11)).card = 0 := by
  decide +kernel

theorem block_count_8_12 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 12)).card = 2 := by
  decide +kernel

theorem block_count_8_13 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 13)).card = 0 := by
  decide +kernel

theorem block_count_8_14 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 14)).card = 0 := by
  decide +kernel

theorem block_count_8_15 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 8 j = 15)).card = 0 := by
  decide +kernel

end QEC.Distillation.BK15.CertifiedWeights


