-- Prove2me | Definitions.Def_BitDFT_SerializerEmitContinuation
-- name    : BitDFT_SerializerEmitContinuation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T07:35:59.692684+00:00
-- url     : https://prove2.me/theorems/71bbf092-876b-4c09-81ab-3cc3f337c95c
-- title:
--   Continue the routed serializer from its emit phase
-- statement:
--   A routed counted-block serializer continuation begins at the emit phase, after its product input, output prefix, countdown, and saved template have already been staged.
-- source:
--   This controller reuses the accepted routed serializer transition and its preservation conditions while setting the entry state to the emit phase. It provides the execution interface needed to serialize directly from a prepared multiplier output frame.

import Definitions.Def_BitDFT_SerializerControllerBridge

set_option autoImplicit false
noncomputable section
namespace BitDFT.RoutedCountedBlockFreshTapes
open IntMul BitDFT.MachineSequence

/-- Continue the routed counted-block serializer from its emit phase, when the
    product, output prefix, countdown, and template have already been staged. -/
def serializerEmitContinuation (M : MultitapeTM) : Controller (extension M) :=
  let Q := serializerController M
  { K := (extension M).K
    entry := .emit
    exit := (extension M).qHalt
    distinct := by change CountedStream.State.emit ≠ CountedStream.State.halt; decide
    transition := Q.transition
    marker := Q.marker
    noMarker := Q.noMarker
    frozen := Q.frozen
    readonly := Q.readonly }

end BitDFT.RoutedCountedBlockFreshTapes
end


