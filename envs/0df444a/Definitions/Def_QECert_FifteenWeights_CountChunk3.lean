-- Prove2me | Definitions.Def_QECert_FifteenWeights_CountChunk3
-- name    : QECert_FifteenWeights_CountChunk3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T00:58:40.254049+00:00
-- url     : https://prove2.me/theorems/b2581c25-2276-4bd0-bc90-1e2e1542d9af
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
theorem block_count_3_0 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 0)).card = 0 := by
  decide +kernel

theorem block_count_3_1 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 1)).card = 0 := by
  decide +kernel

theorem block_count_3_2 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 2)).card = 0 := by
  decide +kernel

theorem block_count_3_3 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 3)).card = 0 := by
  decide +kernel

theorem block_count_3_4 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 4)).card = 0 := by
  decide +kernel

theorem block_count_3_5 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 5)).card = 0 := by
  decide +kernel

theorem block_count_3_6 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 6)).card = 40 := by
  decide +kernel

theorem block_count_3_7 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 7)).card = 0 := by
  decide +kernel

theorem block_count_3_8 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 8)).card = 0 := by
  decide +kernel

theorem block_count_3_9 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 9)).card = 0 := by
  decide +kernel

theorem block_count_3_10 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 10)).card = 24 := by
  decide +kernel

theorem block_count_3_11 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 11)).card = 0 := by
  decide +kernel

theorem block_count_3_12 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 12)).card = 0 := by
  decide +kernel

theorem block_count_3_13 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 13)).card = 0 := by
  decide +kernel

theorem block_count_3_14 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 14)).card = 0 := by
  decide +kernel

theorem block_count_3_15 : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock 3 j = 15)).card = 0 := by
  decide +kernel

end QEC.Distillation.BK15.CertifiedWeights


