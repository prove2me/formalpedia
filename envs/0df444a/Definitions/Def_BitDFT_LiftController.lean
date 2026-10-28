-- Prove2me | Definitions.Def_BitDFT_LiftController
-- name    : BitDFT_LiftController
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T05:51:56.551817+00:00
-- url     : https://prove2.me/theorems/1b7f805d-5e3c-484f-a28b-844327d61fa8
-- title:
--   Lift a controller over a controller machine
-- statement:
--   A finite controller built over the machine of another controller can be lifted to the same underlying multitape alphabet and tape layout. The lifted controller retains the second controller’s finite states, transitions, and halt states. This permits a later controller stage to be composed after a previously sequenced stage while preserving the exact tape configuration.
-- source:
--   Generic finite-state construction used to compose unary positioning and product-suffix positioning controllers in the finite-precision Fourier rescaling machine.

import Definitions.Def_BitDFT_MachineSequence

namespace BitDFT.MachineSequence
open IntMul

/-- A controller over a controller-machine lifts to its unchanged tape model. -/
def liftController {M : MultitapeTM} (P : Controller M)
    (Q : Controller P.machine) : Controller M where
  K := Q.K
  entry := Q.entry
  exit := Q.exit
  distinct := Q.distinct
  transition := Q.transition
  marker := Q.marker
  noMarker := Q.noMarker
  frozen := Q.frozen
  readonly := Q.readonly

end BitDFT.MachineSequence


