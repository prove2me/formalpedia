-- Prove2me | Definitions.Def_IntMul_EndParkRecursiveWorkload
-- name    : IntMul_EndParkRecursiveWorkload
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T04:14:53.688002+00:00
-- url     : https://prove2.me/theorems/ab669f1b-64f6-4f2d-8b63-8234ac19788e
-- title:
--   Additive ordinary-step and local word-space recursive execution certificates
-- source:
--   Original additive workload certificates for complete same-body finite recursive execution on a fixed tape machine. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution

namespace IntMul.EndParkRecursiveWorkload

open IntMul.EndParkRecursiveEvaluation
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankedSimulation (nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankCleanup (span)

/-- Space and shared-word charge for one invocation's final physical cleanup. -/
def returnMass (M : MultitapeTM) (extent : Fin M.k → ℕ) (v w : List Bool) : ℕ :=
  span M extent+v.length+w.length+1

/-- Space, shared words, packet and finite-label charge for one physical call
and parent resumption. It is local, independent of depth and bank offsets. -/
def callMass (M : MultitapeTM) (labels : ℕ) (extent : Fin M.k → ℕ)
    (v x y childWord : List Bool) : ℕ :=
  span M extent+v.length+(inputWord M x y).length+childWord.length+labels+1

/-- A finite computation certificate counts actual ordinary body transitions
and an additive local word/space workload over its entire recursive tree.
It describes executions of the SAME body; it never enters machine control. -/
inductive HasWorkload (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K) :
    (Fin M.k → ℕ) → M.Cfg → List Bool → List Bool → ℕ → ℕ → Prop
  | halt (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
      (halt : c.state=M.qHalt) (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
      HasWorkload M labels request resume extent c v w 0 (returnMass M extent v w)
  | step (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps mass : ℕ)
      (live : c.state≠M.qHalt) (ordinary : request c.state=none)
      (rest : HasWorkload M labels request resume (nextExtent M c extent) (M.step c) v w steps mass) :
      HasWorkload M labels request resume extent c v w (steps+1) mass
  | call (extent : Fin M.k → ℕ) (c : M.Cfg) (v x y childWord w : List Bool)
      (label : Fin labels) (childSteps childMass parentSteps parentMass : ℕ)
      (live : c.state≠M.qHalt) (request_label : request c.state=some label)
      (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
      (child : HasWorkload M labels request resume (initialExtent M x y) (M.initCfg x y) [] childWord childSteps childMass)
      (parent : HasWorkload M labels request resume (parentAfterChildExtent M extent childWord)
        (resumedParent M labels resume label extent c childWord) childWord w parentSteps parentMass) :
      HasWorkload M labels request resume extent c v w (childSteps+parentSteps)
        (childMass+parentMass+callMass M labels extent v x y childWord)

end IntMul.EndParkRecursiveWorkload


