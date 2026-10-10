-- Prove2me | Definitions.Def_IntMul_EndParkRecursiveClockedCalls
-- name    : IntMul_EndParkRecursiveClockedCalls
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T07:45:09.197198+00:00
-- url     : https://prove2.me/theorems/244c4710-f41e-467c-b35f-dc369e601e45
-- title:
--   Local recursive invocation certificates using actual native child halt clocks
-- source:
--   Original coefficient-one actual child-clock accounting for the fixed-tape recursive integer multiplication scheduler. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveAmortizedWork

namespace IntMul.EndParkRecursiveClockedCalls

open IntMul.EndParkRecursiveEvaluation
open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.EndParkRecursiveAmortizedWork (callWordWork)
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankedSimulation (nextExtent)

/-- A local invocation certificate charges child calls by supplied ACTUAL
native halt clocks, and charges only its own ordinary steps and words.
Children have finite evaluations of the same fixed recursive scheduler;
they are not oracle transitions and their costs are not logical budgets. -/
inductive HasClockedCalls (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K) :
    (Fin M.k → ℕ) → M.Cfg → List Bool → List Bool → ℕ → ℕ → ℕ → Prop
  | halt (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
      (halt : c.state=M.qHalt) (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
      HasClockedCalls M labels request resume extent c v w 0 0 (v.length+w.length+1)
  | step (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps clocks work : ℕ)
      (live : c.state≠M.qHalt) (ordinary : request c.state=none)
      (rest : HasClockedCalls M labels request resume (nextExtent M c extent)
        (M.step c) v w steps clocks work) :
      HasClockedCalls M labels request resume extent c v w (steps+1) clocks work
  | call (extent : Fin M.k → ℕ) (c : M.Cfg) (v x y childWord w : List Bool)
      (label : Fin labels) (childBudget H parentSteps parentClocks parentWork : ℕ)
      (live : c.state≠M.qHalt) (request_label : request c.state=some label)
      (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
      (child : Evaluates M labels request resume (initialExtent M x y)
        (M.initCfg x y) [] childWord childBudget)
      (child_halt : ((machine M labels request resume).step^[H]
        ((machine M labels request resume).initCfg x y)).state=(machine M labels request resume).qHalt)
      (parent : HasClockedCalls M labels request resume (parentAfterChildExtent M extent childWord)
        (resumedParent M labels resume label extent c childWord) childWord w
        parentSteps parentClocks parentWork) :
      HasClockedCalls M labels request resume extent c v w parentSteps
        (H+parentClocks) (parentWork+callWordWork M labels v x y childWord)

end IntMul.EndParkRecursiveClockedCalls


