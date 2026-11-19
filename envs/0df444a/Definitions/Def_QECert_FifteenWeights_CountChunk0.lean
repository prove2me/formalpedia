-- Prove2me | Definitions.Def_QECert_FifteenWeights_CountChunk0
-- name    : QECert_FifteenWeights_CountChunk0
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:57:42.891108+00:00
-- url     : https://prove2.me/theorems/e3c388ed-86a9-4168-b680-34376e173baa
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
theorem block_count_0_0 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 0)).card = 1 := by
  decide +kernel

theorem block_count_0_1 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 1)).card = 0 := by
  decide +kernel

theorem block_count_0_2 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 2)).card = 0 := by
  decide +kernel

theorem block_count_0_3 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 3)).card = 0 := by
  decide +kernel

theorem block_count_0_4 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 4)).card = 9 := by
  decide +kernel

theorem block_count_0_5 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 5)).card = 0 := by
  decide +kernel

theorem block_count_0_6 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 6)).card = 0 := by
  decide +kernel

theorem block_count_0_7 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 7)).card = 0 := by
  decide +kernel

theorem block_count_0_8 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 8)).card = 51 := by
  decide +kernel

theorem block_count_0_9 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 9)).card = 0 := by
  decide +kernel

theorem block_count_0_10 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 10)).card = 0 := by
  decide +kernel

theorem block_count_0_11 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 11)).card = 0 := by
  decide +kernel

theorem block_count_0_12 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 12)).card = 3 := by
  decide +kernel

theorem block_count_0_13 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 13)).card = 0 := by
  decide +kernel

theorem block_count_0_14 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 14)).card = 0 := by
  decide +kernel

theorem block_count_0_15 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 0 j = 15)).card = 0 := by
  decide +kernel

end QEC.Distillation.BK15.CertifiedWeights


