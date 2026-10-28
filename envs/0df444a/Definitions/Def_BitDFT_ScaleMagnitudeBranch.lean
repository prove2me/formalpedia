-- Prove2me | Definitions.Def_BitDFT_ScaleMagnitudeBranch
-- name    : BitDFT_ScaleMagnitudeBranch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T22:02:26.317984+00:00
-- url     : https://prove2.me/theorems/0c44bb73-30b9-48e8-9070-947663d21aca
-- title:
--   A finite multiplier-or-shift branch for one magnitude field
-- statement:
--   This controller combines two exact computations over one multitape machine layout. A supplied Boolean test on the scanned magnitude symbol selects the boundary-shift emitter when the high magnitude bit is set; otherwise it runs the native tracked-multiplier machine. Both branches join at a common halt state, preserving the tape frame at selection and join. It is the branch-level construction used to scale one signed coordinate without requiring a regularity assumption on the multiplier runtime.
-- source:
--   Composition of the published finite branch controller and boundary-shift emitter over the IntMul.MultitapeTM semantics.

import Definitions.Def_BitDFT_BranchController
import Definitions.Def_BitDFT_BoundaryShiftEmitter

set_option autoImplicit false
noncomputable section

namespace BitDFT.ScaleMagnitudeBranch
open IntMul BitDFT.MachineSequence

/-- Choose the exact shift emitter when the scanned magnitude bit is one, and
    otherwise run the native tracked-multiplier machine. Both branches use the
    same alphabet and tape layout; the selector and exit join are stationary. -/
noncomputable def controller (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output) :
    Controller N :=
  branchController coordinate isHigh
    (BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo)
    (MachineSequence.native N)

noncomputable abbrev machine (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output) :=
  (controller N coordinate dimension output isHigh hc hd ho hcd hco hdo).machine

end BitDFT.ScaleMagnitudeBranch
end


