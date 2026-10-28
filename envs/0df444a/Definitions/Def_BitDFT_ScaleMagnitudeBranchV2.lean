-- Prove2me | Definitions.Def_BitDFT_ScaleMagnitudeBranchV2
-- name    : BitDFT_ScaleMagnitudeBranchV2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T22:08:36.507258+00:00
-- url     : https://prove2.me/theorems/7999a4eb-22a2-473d-9cbc-ed1e85b03fbf
-- title:
--   A multiplier-or-shift branch with a separate high-bit flag
-- statement:
--   This controller combines the exact boundary-shift emitter with the native tracked-multiplier machine over one tape alphabet and layout. It reads a separately staged high-magnitude-bit flag, so the emitter can simultaneously begin at the sign bit of the coordinate record. A true flag selects the boundary case; a false flag selects multiplication. The disjoint tape hypotheses keep the flag separate from the coordinate, dimension, and output tapes.
-- source:
--   Finite-state conditional composition of the published branch controller and boundary-shift emitter for the integer-multiplication-to-DFT output scaler.

import Definitions.Def_BitDFT_BranchController
import Definitions.Def_BitDFT_BoundaryShiftEmitter

set_option autoImplicit false
noncomputable section

namespace BitDFT.ScaleMagnitudeBranchV2
open IntMul BitDFT.MachineSequence

/-- Select the exact boundary shift or native multiplier by reading a separate
    staged high-bit flag. Keeping the flag tape distinct lets the boundary
    emitter begin at the sign bit of its coordinate record. -/
noncomputable def controller (N : MultitapeTM) (selector coordinate dimension output : Fin N.k)
    (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension) (hso : selector ≠ output) :
    Controller N :=
  branchController selector isHigh
    (BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo)
    (MachineSequence.native N)

noncomputable abbrev machine (N : MultitapeTM) (selector coordinate dimension output : Fin N.k)
    (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension) (hso : selector ≠ output) :=
  (controller N selector coordinate dimension output isHigh hc hd ho hcd hco hdo hsc hsd hso).machine

end BitDFT.ScaleMagnitudeBranchV2
end


