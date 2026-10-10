-- Prove2me | Definitions.Def_IntMul_FlatRecursiveResume
-- name    : IntMul_FlatRecursiveResume
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T02:33:42.181266+00:00
-- url     : https://prove2.me/theorems/fe4d830a-55f3-41bd-974d-d71d5b668ea4
-- title:
--   Exact child-inspection and resumed-parent frames on the single fixed-tape scheduler
-- statement:
--   Complete proof frames for returning from a child invocation and resuming a parent on one depth-independent finite transition table with M.k+3 fixed tapes. The child inspection frame contains the canonical returned shared word, fresh child banks retaining every saved parent and ancestor prefix, and an actual physical stack probe at the final saved-label bit. The resumed frame restores the original parent bank offsets and continuation suffix, updates only the parent result bank and extent, physically parks every work head at its parent marker, and re-enters the same original body control at the recovered finite resume label. All addresses and extents are proof parameters, never delta inputs.
-- source:
--   Original parent-resumption frames for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveCall
import Definitions.Def_IntMul_FlatRecursiveReturn

namespace IntMul.FlatRecursiveResume

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall

/-- Actual continuation-probe frame after complete child cleanup. -/
noncomputable def childInspection (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (machine M n request resume).Cfg :=
  FlatRecursiveReturn.inspectionFrame M n request resume
    (childBase M n request resume base rho sigma offset extent c label)
    (rho+n+1) sigma (TrackedBankReservation.newOffsets M offset extent) w

/-- Complete resumed parent body, with recovered continuation, canonical
result bank, new output extent, all work heads at zero, and restored stack. -/
noncomputable def resumedFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (machine M n request resume).Cfg :=
  bodyFrame M n request resume base rho sigma offset (parentAfterChildExtent M extent w)
    (parentAfterChild M n resume label c w) w

end IntMul.FlatRecursiveResume


