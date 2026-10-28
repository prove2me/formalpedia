-- Prove2me | Definitions.Def_BitDFT_ExtractionReady
-- name    : BitDFT_ExtractionReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:51:18.076341+00:00
-- url     : https://prove2.me/theorems/f60f9d3f-a120-4a9b-a508-cd98ffb283c3
-- title:
--   Allocate and position a fresh scratch tape after vector initialization
-- statement:
--   Extend the vector-initialization machine by one fresh scratch tape, identify its tape indices with the signed extractor layout, and compose it with the existing rewind controller on the scratch tape. On the fresh tape this controller moves from its marker to the first data cell in one step.
-- source:
--   Actual-machine initialization for the exact Fourier output scaler.

import Definitions.Def_BitDFT_VectorReady
import Definitions.Def_BitDFT_SignedBlockPlacement

noncomputable section
namespace BitDFT.ExtractionReady
open IntMul MachineSequence
abbrev extended (M : MultitapeTM) := TapeExtension.machine (VectorReady.machine M) 1

theorem tape_count (M : MultitapeTM) : (extended M).k = 5+(M.k+3) := by
  change (4+(M.k+3))+1 = 5+(M.k+3)
  omega

abbrev preparation (M : MultitapeTM) :=
  TapeCountTransport.machine (extended M) (5+(M.k+3)) (tape_count M)
abbrev scratch (M : MultitapeTM) : Fin (preparation M).k := SignedBlockPlacement.scratchTape M.k
abbrev advance (M : MultitapeTM) := RewindTape.control (preparation M) (scratch M)
abbrev machine (M : MultitapeTM) := (sequence (native (preparation M)) (advance M)).machine

def prepared (M : MultitapeTM) (c : (VectorReady.machine M).Cfg) : (preparation M).Cfg :=
  TapeCountTransport.embed (extended M) (5+(M.k+3)) (tape_count M)
    (TapeExtension.embed (VectorReady.machine M) 1
      (fun _ => (VectorReady.machine M).tapeOf []) (fun _ => 0) c)

def final (M : MultitapeTM) (c : (VectorReady.machine M).Cfg) : (machine M).Cfg :=
  rightCfg (native (preparation M)) (advance M)
    (RewindTape.frame (preparation M) (scratch M) (prepared M c) true 1)
end BitDFT.ExtractionReady


