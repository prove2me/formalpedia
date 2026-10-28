-- Prove2me | Definitions.Def_BitDFT_ReaderOutputStageSupport
-- name    : BitDFT_ReaderOutputStageSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T18:11:11.507984+00:00
-- url     : https://prove2.me/theorems/aa503f19-9b7a-4373-ae7e-9d60ee9dc250
-- title:
--   Reader output-stage entry-frame definition
-- statement:
--   The staging controller entry frame installs the signed-coordinate word on its coordinate tape, clears its output tape, and preserves the supplied contents of all other tapes.
-- source:
--   A shared frame constructor used by the exact staging theorem and its proof.

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Definitions.Def_BitDFT_OperandStage
set_option autoImplicit false
noncomputable section
open IntMul BitDFT.OperandStage
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


