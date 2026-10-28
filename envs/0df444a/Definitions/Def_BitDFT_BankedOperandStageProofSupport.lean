-- Prove2me | Definitions.Def_BitDFT_BankedOperandStageProofSupport
-- name    : BitDFT_BankedOperandStageProofSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T15:10:41.996994+00:00
-- url     : https://prove2.me/theorems/b86b17c3-3834-46e7-ac33-98f4814496a9
-- title:
--   Public configuration frames for operand staging proofs
-- statement:
--   Define the exact initial and intermediate configurations for the finite operand-staging controller. The initial frame places a signed coordinate record on its source tape, leaves the output buffer blank, and preserves every other tape from an arbitrary base configuration. The intermediate frame records the source and buffer heads and the buffer contents after a specified prefix has been written.
-- source:
--   Public support configurations for exact-run theorems about the published operand-stage controller. These equations make theorem interfaces reusable across independent proof submissions.

import Definitions.Def_BitDFT_OperandStage

set_option autoImplicit false
noncomputable section
namespace BitDFT.BankedOperandStageProofSupport
open IntMul BitDFT.OperandStage

def initialStageFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) :
    (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .skipSign
  cells := fun i => if i = coord then N.tapeOf (source.map N.bitSym)
    else if i = out then N.tapeOf [] else base.cells i
  head := fun i => if i = coord ∨ i = out then 1 else base.head i

def coordinateCopyFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) (outBits : List N.Sym) (sourceHead outHead : ℕ) :
    (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .copyCoordinate
  cells := fun i => if i = coord then N.tapeOf (source.map N.bitSym)
    else if i = out then N.tapeOf (N.blank :: outBits) else base.cells i
  head := fun i => if i = coord then sourceHead
    else if i = out then outHead else base.head i

end BitDFT.BankedOperandStageProofSupport
end


