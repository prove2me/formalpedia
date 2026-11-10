-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback_EmbeddedReadout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:03:27.20385+00:00
-- url     : https://prove2.me/theorems/420d5839-2e9a-4e47-863d-a4484dcad3a7
-- title:
--   Embedded Readout
-- statement:
--   Definitions and structural lemmas for Embedded Readout, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXErrorPullback/EmbeddedReadout.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXErrorPullback
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)
abbrev Data := rxData S depth i h
def embeddedSyndrome (h : i.val % 2 = 0)
    (tau : (indexedFamily S depth).Syndrome i.castSucc) :
    (indexedFamily S depth).Syndrome i.succ :=
  ⟨((indexedDecoderData S depth).rxMap i).map2 tau.val, by
    obtain ⟨a,ha⟩ := tau.property
    refine ⟨((indexedDecoderData S depth).rxMap i).map1 a, ?_⟩
    have hc := LinearMap.congr_fun (((indexedDecoderData S depth).rxMap i).commutes_coboundary1) a
    change (indexedFamily S depth).coboundary1 i.succ
      (((indexedDecoderData S depth).rxMap i).map1 a) =
      ((indexedDecoderData S depth).rxMap i).map2
        ((indexedFamily S depth).coboundary1 i.castSucc a) at hc
    rw [ha] at hc
    exact hc⟩
end QEC.Coding.BDL26RXErrorPullback


