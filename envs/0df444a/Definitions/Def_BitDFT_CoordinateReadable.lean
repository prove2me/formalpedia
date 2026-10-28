-- Prove2me | Definitions.Def_BitDFT_CoordinateReadable
-- name    : BitDFT_CoordinateReadable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T19:07:30.190567+00:00
-- url     : https://prove2.me/theorems/0e22953c-625b-4729-8e23-8272d0d043d9
-- title:
--   Rewind the extracted signed record for arithmetic processing
-- statement:
--   Compose the first-coordinate machine with a rewind controller on its scratch tape. The controller preserves every tape cell and every other tape head, and moves the scratch head to the first data cell.
-- source:
--   Actual-machine initialization for the exact Fourier output scaler.

import Definitions.Def_BitDFT_FirstCoordinate

noncomputable section
namespace BitDFT.CoordinateReadable
open IntMul MachineSequence
abbrev preparation (M : MultitapeTM) := FirstCoordinate.machine M
abbrev scratch (M : MultitapeTM) : Fin (preparation M).k := SignedBlockPlacement.scratchTape M.k
abbrev rewind (M : MultitapeTM) := RewindTape.control (preparation M) (scratch M)
abbrev machine (M : MultitapeTM) := (sequence (native (preparation M)) (rewind M)).machine

def final (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ) (sign : Bool) (x y : List Bool) : (machine M).Cfg :=
  rightCfg (native (preparation M)) (rewind M)
    (RewindTape.frame (preparation M) (scratch M)
      (FirstCoordinate.final M c rootCells rootHead sign x y) true 1)
end BitDFT.CoordinateReadable


