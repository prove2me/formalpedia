-- Prove2me | Definitions.Def_IntMul_FlatRecursiveEvaluation
-- name    : IntMul_FlatRecursiveEvaluation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T03:04:03.92461+00:00
-- url     : https://prove2.me/theorems/fb5e75c0-55f9-4e47-ad01-d2b3661bb448
-- title:
--   Finite recursive body evaluation with completely charged physical clocks
-- statement:
--   Finite derivation trees for one original body machine and finite request/resume controls. Halt nodes carry literal canonical results and the complete physical return cost. Ordinary nodes execute real body transitions and update visited extents. Call nodes evaluate the same body on canonical native child input, then evaluate the parent with its result bank replaced, all logical work heads physically parked, recovered resume control, and updated output extent. The shared word is tracked solely to charge copying and tail clearing. The indexed clock sums every ordinary transition, argument transfer, physical continuation write, reservation, initialization, buffer rewind, child cleanup, parent restoration, stack pop and result placement. No derivation tree, address, extent, input length or depth appears in the finite transition table.
-- source:
--   Original finite evaluation semantics and exact physical clock bookkeeping for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveResume

namespace IntMul.FlatRecursiveEvaluation

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.FlatRecursiveReturn
open IntMul.FlatRecursiveResume
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- Exact upper bound for the charged physical return and cleanup protocol. -/
noncomputable def returnCost (M : MultitapeTM) (extent : Fin M.k → ℕ)
    (c : M.Cfg) (v w : List Bool) : ℕ :=
  max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+
    span M (returnedHeads M c)+2*span M extent+12

/-- Exact upper bound for real argument transfer, stack push, reservation,
preparation, dispatches and shared-buffer reset. -/
noncomputable def callCost (M : MultitapeTM) (n : ℕ) (extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) : ℕ :=
  max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
    3*(inputWord M x y).length+
    span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+n+16

/-- Exact upper bound for real marker restoration, stack pop and result
placement, including every physical dispatch. -/
noncomputable def resumeCost (M : MultitapeTM) (n : ℕ) (extent : Fin M.k → ℕ) (w : List Bool) : ℕ :=
  span M (fun j => extent j+1)+n+w.length+2*max w.length (extent M.outTape)+12

/-- Finite recursive evaluation of the original body and finite call controls.
Ordinary nodes are actual body transitions. A call evaluates the same body
from native logical child input and then the physically parked parent with
its result bank replaced. The shared word is tracked only to charge costs.
This is a finite proof tree, never data available to the machine's delta. -/
inductive Evaluates (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) :
    (Fin M.k → ℕ) → M.Cfg → List Bool → List Bool → ℕ → Prop
  | halt (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
      (halt : c.state=M.qHalt) (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
      Evaluates M n request resume extent c v w (returnCost M extent c v w)
  | step (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (budget : ℕ)
      (live : c.state≠M.qHalt) (ordinary : request c.state=none)
      (rest : Evaluates M n request resume (nextExtent M c extent) (M.step c) v w budget) :
      Evaluates M n request resume extent c v w (budget+1)
  | call (extent : Fin M.k → ℕ) (c : M.Cfg) (v x y childWord w : List Bool)
      (label : Fin n) (childBudget parentBudget : ℕ)
      (live : c.state≠M.qHalt) (request_label : request c.state=some label)
      (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
      (child : Evaluates M n request resume (initialExtent M x y) (M.initCfg x y) [] childWord childBudget)
      (parent : Evaluates M n request resume (parentAfterChildExtent M extent childWord)
        (parentAfterChild M n resume label c childWord) childWord w parentBudget) :
      Evaluates M n request resume extent c v w
        (callCost M n extent c v x y+childBudget+resumeCost M n extent childWord+parentBudget)

end IntMul.FlatRecursiveEvaluation


