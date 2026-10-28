-- Prove2me | Definitions.Def_BitDFT_VectorReady
-- name    : BitDFT_VectorReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:38:12.02299+00:00
-- url     : https://prove2.me/theorems/bbabc913-695c-4bb3-be38-16ee3547ddf2
-- title:
--   Run the child, prepare precision descriptors, and rewind the output vector
-- statement:
--   Compose the child-and-descriptor setup machine with a rewind controller on the native output tape. The descriptors remain on their work tapes, the output word is preserved, and the final output head is on the first data cell. This prepares sequential coordinate extraction; it does not yet scale coordinates.
-- source:
--   Actual-machine initialization for the exact Fourier output scaler.

import Definitions.Def_BitDFT_ChildDescriptor
import Definitions.Def_BitDFT_RewindTape

noncomputable section
namespace BitDFT.VectorReady
open IntMul MachineSequence
abbrev preparation (M : MultitapeTM) := ChildDescriptor.machine M
abbrev rewind (M : MultitapeTM) := RewindTape.control (preparation M) (preparation M).outTape
abbrev machine (M : MultitapeTM) := (sequence (native (preparation M)) (rewind M)).machine

def final (M : MultitapeTM) (input : List Bool) (c : (NativeChildOutput.program M).Cfg)
    (y : List Bool) : (machine M).Cfg :=
  rightCfg (native (preparation M)) (rewind M)
    (RewindTape.frame (preparation M) (preparation M).outTape
      (ChildDescriptor.final M input c y) true 1)
end BitDFT.VectorReady


