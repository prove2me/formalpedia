-- Prove2me | Definitions.Def_IntMul_FlatRecursiveReturn
-- name    : IntMul_FlatRecursiveReturn
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T01:55:34.352573+00:00
-- url     : https://prove2.me/theorems/ff7f0e7b-c09e-42c8-bb6e-fd5a0932f92a
-- title:
--   Complete inspection frame after a physical flat-scheduler return
-- statement:
--   A proof frame for one returned invocation of the fixed-tape recursive scheduler. The shared buffer contains the new result word with its retained local marker, visited payload and fresh suffix; all current work banks are physically fresh beyond their offsets; every earlier work-bank prefix remains exactly as in the base configuration. Work heads are parked at their local offsets, the original input is retained, and the continuation head is positioned one cell left of its former end for physical root-or-parent inspection. The relative cleanup-head distances also record the output head physically restored to zero by result replacement. Addresses, extents and result words in these frames are proof parameters, not inputs to the fixed finite transition table.
-- source:
--   Original complete return frame for the integer-multiplication fixed-tape scheduler. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveScheduler

namespace IntMul.FlatRecursiveReturn

open IntMul.FlatRecursiveScheduler

/-- Relative work-head positions after physical output-buffer replacement. -/
noncomputable def returnedHeads (M : MultitapeTM) (c : M.Cfg) : Fin M.k → ℕ := by
  classical
  exact fun j => if j=M.outTape then 0 else c.head j

/-- The complete configuration after returning and clearing one invocation,
with the physical stack probe positioned one cell left of its former end.
The ancestor prefixes, shared result and fixed extra tape remain literal. -/
noncomputable def inspectionFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset : Fin M.k → ℕ) (w : List Bool) : (machine M n request resume).Cfg where
  state := .inspectStack
  cells := fun i => if h : i.val < M.k+2 then
    if hw : 2 ≤ i.val then TrackedBankCleanup.freshTape M (base.cells i)
      (offset (BankedSimulation.innerTape M ⟨i.val,h⟩ hw))
    else if i.val=1 then TrackedOutputReturn.bufferTape M (base.cells i) sigma w
    else base.cells i
    else FiniteContinuationStack.freshTape M (base.cells i) rho
  head := fun i => if h : i.val < M.k+2 then
    if hw : 2 ≤ i.val then offset (BankedSimulation.innerTape M ⟨i.val,h⟩ hw)
    else if i.val=1 then sigma+w.length+1 else base.head i
    else rho-1

end IntMul.FlatRecursiveReturn


