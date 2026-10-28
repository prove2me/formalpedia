-- Prove2me | Definitions.Def_BitDFT_FirstCoordinate
-- name    : BitDFT_FirstCoordinate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T19:00:35.936985+00:00
-- url     : https://prove2.me/theorems/d9ac45c7-5ef5-451f-9b8d-8d2bc36952b6
-- title:
--   Compose vector preparation with signed-coordinate extraction
-- statement:
--   Run the vector and scratch preparation machine, then hand control to the routed signed-coordinate extractor. The extractor reads the existing vector tape and writes to the new scratch tape, using the prepared counter and template tapes. The same machine operates for every precision and vector length.
-- source:
--   Actual-machine initialization for the exact Fourier output scaler.

import Definitions.Def_BitDFT_ExtractionReady

noncomputable section
namespace BitDFT.FirstCoordinate
open IntMul MachineSequence
abbrev storage (M : MultitapeTM) := ExtractionReady.machine M
abbrev extractor (M : MultitapeTM) := SignedBlockPlacement.machine (VectorReady.machine M) M.k

def control (M : MultitapeTM) : Controller (storage M) where
  K := (extractor M).K
  entry := (extractor M).qStart
  exit := (extractor M).qHalt
  distinct := (extractor M).start_ne_halt
  transition := (extractor M).δ
  marker := (extractor M).start_preserved
  noMarker := (extractor M).start_only_at_start
  frozen := (extractor M).halt_fixed
  readonly := (extractor M).input_readonly

abbrev machine (M : MultitapeTM) := (sequence (native (storage M)) (control M)).machine

def start (M : MultitapeTM) (c : (VectorReady.machine M).Cfg) : (control M).machine.Cfg :=
  handoff (native (storage M)) (control M) (ExtractionReady.final M c)

def final (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ) (sign : Bool) (x y : List Bool) : (machine M).Cfg :=
  rightCfg (native (storage M)) (control M)
    (SignedBlockPlacement.embed (VectorReady.machine M) M.k (start M c).cells (start M c).head
      (WorkRelocation.embed SignedBlock.machine rootCells rootHead (SignedBlock.final [] [] sign x y)))
end BitDFT.FirstCoordinate


