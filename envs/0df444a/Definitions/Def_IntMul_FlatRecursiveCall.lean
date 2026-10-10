-- Prove2me | Definitions.Def_IntMul_FlatRecursiveCall
-- name    : IntMul_FlatRecursiveCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T02:26:41.692671+00:00
-- url     : https://prove2.me/theorems/bc216241-cbcc-4a60-a21a-35be502dfac6
-- title:
--   Saved parent and canonical child frames for one depth-independent recursive scheduler
-- statement:
--   Canonical full configurations for actual recursive calls on one fixed finite transition table with exactly M.k+3 tapes. The parent after argument transfer retains all cells while physically resetting only its output head. The canonical child base retains every saved parent and ancestor prefix, records the finite continuation label physically on the fixed extra tape, retains a fresh stack suffix, empties the shared buffer and parks work heads at the fresh offsets beyond the parent visited extents. The child frame enters the same original body control with canonical child input. The parent after a child return has the recovered resume control, canonical result placement and every logical work head reset physically to its local marker. Every offset, word, extent and depth here is a proof parameter and never input to delta.
-- source:
--   Original complete recursive call frames for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveScheduler

namespace IntMul.FlatRecursiveCall

open IntMul.FlatRecursiveScheduler

/-- Argument transfer physically rewinds the parent's packet/output head
while retaining its entire logical contents and all other head positions. -/
noncomputable def parentAfterInput (M : MultitapeTM) (c : M.Cfg) : M.Cfg where
  state := c.state
  cells := c.cells
  head := fun j => if j=M.outTape then 0 else c.head j

/-- The parent's logical result after a child return, with the recovered
finite resume control and every work head physically parked at its marker. -/
noncomputable def parentAfterChild (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (label : Fin n) (c : M.Cfg) (w : List Bool) : M.Cfg where
  state := resume label
  cells := fun j => if j=M.outTape then M.tapeOf (w.map M.bitSym) else c.cells j
  head := fun _ => 0

noncomputable def parentAfterChildExtent (M : MultitapeTM) (extent : Fin M.k → ℕ)
    (w : List Bool) : Fin M.k → ℕ := fun j => if j=M.outTape then w.length else extent j

/-- Saved parent/ancestor prefixes and a physically appended finite label
record. The child boundary on each work tape is its first fresh cell beyond
the parent's visited extent. The shared argument buffer is physically empty. -/
noncomputable def childBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) : (machine M n request resume).Cfg where
  state := .body M.qStart
  cells := fun i => if i=stackTape M then
    FiniteContinuationStack.recordTape M n (base.cells i) rho label n
    else if i.val=1 then TrackedOutputReturn.bufferTape M (base.cells i) sigma []
    else (bodyFrame M n request resume base rho sigma offset extent c []).cells i
  head := fun i => if i=stackTape M then rho+n+1 else if i.val=1 then sigma+1
    else if h : i.val < M.k+2 then
      if hw : 2 ≤ i.val then TrackedBankReservation.newOffsets M offset extent
        (BankedSimulation.innerTape M ⟨i.val,h⟩ hw) else base.head i
    else base.head i

/-- Complete new invocation of the SAME body control on the SAME fixed
physical tapes, preserving the saved parent and continuation record. -/
noncomputable def childFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (x y : List Bool) :
    (machine M n request resume).Cfg :=
  bodyFrame M n request resume (childBase M n request resume base rho sigma offset extent c label)
    (rho+n+1) sigma (TrackedBankReservation.newOffsets M offset extent)
    (TrackedBankPreparation.initialExtent M x y) (M.initCfg x y) []

end IntMul.FlatRecursiveCall


