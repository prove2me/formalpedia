-- Prove2me | Definitions.Def_IntMul_EndParkRecursiveTraffic
-- name    : IntMul_EndParkRecursiveTraffic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T04:31:41.105693+00:00
-- url     : https://prove2.me/theorems/923fbb71-a597-4d4a-b25b-512cbe3ad66b
-- title:
--   Exact word and reservation-movement traffic certificates for fixed recursive computation
-- source:
--   Original tight physical word and reservation-distance accounting for same-table arbitrary recursive computation. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution

namespace IntMul.EndParkRecursiveTraffic

open IntMul.EndParkRecursiveEvaluation
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankedSimulation (nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankCleanup (span)

/-- Space and shared-word charge for one invocation's final physical cleanup. -/
def returnTraffic (M : MultitapeTM) (extent : Fin M.k → ℕ) (v w : List Bool) : ℕ :=
  span M extent+v.length+w.length+1

/-- Actual distance to the first fresh bank cells AFTER packet extraction.
Large unchanged banks whose heads are already parked contribute zero. -/
noncomputable def reservationDistance (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg) : ℕ :=
  span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)

/-- Actual parent result-head and fresh-bank reservation traffic, shared
words, child packet/result and a fixed finite-label charge for one call. -/
noncomputable def callTraffic (M : MultitapeTM) (labels : ℕ) (extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y childWord : List Bool) : ℕ :=
  c.head M.outTape+reservationDistance M extent c+v.length+
    (inputWord M x y).length+childWord.length+labels+1

/-- A finite computation certificate counts actual ordinary body transitions
and an additive actual word/movement traffic over its entire recursive tree.
It describes executions of the SAME body; it never enters machine control. -/
inductive HasTraffic (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K) :
    (Fin M.k → ℕ) → M.Cfg → List Bool → List Bool → ℕ → ℕ → Prop
  | halt (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
      (halt : c.state=M.qHalt) (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
      HasTraffic M labels request resume extent c v w 0 (returnTraffic M extent v w)
  | step (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps mass : ℕ)
      (live : c.state≠M.qHalt) (ordinary : request c.state=none)
      (rest : HasTraffic M labels request resume (nextExtent M c extent) (M.step c) v w steps mass) :
      HasTraffic M labels request resume extent c v w (steps+1) mass
  | call (extent : Fin M.k → ℕ) (c : M.Cfg) (v x y childWord w : List Bool)
      (label : Fin labels) (childSteps childMass parentSteps parentMass : ℕ)
      (live : c.state≠M.qHalt) (request_label : request c.state=some label)
      (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
      (child : HasTraffic M labels request resume (initialExtent M x y) (M.initCfg x y) [] childWord childSteps childMass)
      (parent : HasTraffic M labels request resume (parentAfterChildExtent M extent childWord)
        (resumedParent M labels resume label extent c childWord) childWord w parentSteps parentMass) :
      HasTraffic M labels request resume extent c v w (childSteps+parentSteps)
        (childMass+parentMass+callTraffic M labels extent c v x y childWord)

end IntMul.EndParkRecursiveTraffic


