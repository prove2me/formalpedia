-- Prove2me | Definitions.Def_BitDFT_ReaderOutputStageRun
-- name    : BitDFT_ReaderOutputStageRun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T16:30:32.223576+00:00
-- url     : https://prove2.me/theorems/640c1c6b-10b7-492d-87b1-abedf63d78da
-- title:
--   Host frame for composing reader outputs with coordinate staging
-- statement:
--   Defines the shared host addresses and the exact controller entry frame used to connect Fourier-coordinate and header-reader outputs to the multiplier operand-staging controller.
-- source:
--   Reuses the accepted reader-output frame and operand-pair staging theorem.

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_TripleAlphabet
import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_BitDFT_OperandStage
import Theorems.Thm_BitDFT_ReaderHostFrame_reader_outputs_to_operand_frame
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

namespace BitDFT.ReaderHostFrame
abbrev tracked (M : MultitapeTM) := IntMul.TrackedBankedCall.machine M
abbrev host (A M H : MultitapeTM) :=
  BankedTripleAlphabetHost.multiplierMachine A (tracked M) H
end BitDFT.ReaderHostFrame

namespace BitDFT.ReaderOutputStageRun
def entryFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) :
    (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .skipSign
  cells := fun i => if i = coord then N.tapeOf (source.map N.bitSym)
    else if i = out then N.tapeOf [] else base.cells i
  head := fun i => if i = coord ∨ i = out then 1 else base.head i
end BitDFT.ReaderOutputStageRun
end


