-- Prove2me | Definitions.Def_IntMul_EndParkRecursiveLocalCalls
-- name    : IntMul_EndParkRecursiveLocalCalls
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T07:51:11.453992+00:00
-- url     : https://prove2.me/theorems/5e4781df-c948-46de-8323-ef2402f38dc9
-- title:
--   Local fixed-width recursive call counts and native caller overhead
-- source:
--   Original concrete local work certificates for a coefficient-one actual multiplication recurrence. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveClockedCalls

namespace IntMul.EndParkRecursiveLocalCalls

open IntMul.EndParkRecursiveEvaluation
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.EndParkRecursiveAmortizedWork (callWordWork)
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankedSimulation (nextExtent)

/-- A concrete local invocation has `calls` same-width child evaluations,
`steps` own ordinary body transitions, and `work` local word charge.
Its children are executions of the same finite scheduler, with no oracle.
No child clock or runtime bound appears in this certificate. -/
inductive HasLocalCalls (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K) (childWidth : ℕ) :
    (Fin M.k → ℕ) → M.Cfg → List Bool → List Bool → ℕ → ℕ → ℕ → Prop
  | halt (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
      (halt : c.state=M.qHalt) (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
      HasLocalCalls M labels request resume childWidth extent c v w 0 0 (v.length+w.length+1)
  | step (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps calls work : ℕ)
      (live : c.state≠M.qHalt) (ordinary : request c.state=none)
      (rest : HasLocalCalls M labels request resume childWidth (nextExtent M c extent)
        (M.step c) v w steps calls work) :
      HasLocalCalls M labels request resume childWidth extent c v w (steps+1) calls work
  | call (extent : Fin M.k → ℕ) (c : M.Cfg) (v x y childWord w : List Bool)
      (label : Fin labels) (childBudget parentSteps parentCalls parentWork : ℕ)
      (live : c.state≠M.qHalt) (request_label : request c.state=some label)
      (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
      (hx : x.length=childWidth) (hy : y.length=childWidth)
      (child : Evaluates M labels request resume (initialExtent M x y)
        (M.initCfg x y) [] childWord childBudget)
      (parent : HasLocalCalls M labels request resume childWidth (parentAfterChildExtent M extent childWord)
        (resumedParent M labels resume label extent c childWord) childWord w
        parentSteps parentCalls parentWork) :
      HasLocalCalls M labels request resume childWidth extent c v w parentSteps
        (parentCalls+1) (parentWork+callWordWork M labels v x y childWord)

/-- Caller overhead from its own steps and words, including physical native
setup and final output placement. Child clocks are excluded. -/
def nativeOverhead (M : MultitapeTM) (x y w : List Bool) (steps work : ℕ) : ℕ :=
  steps+32*(work+(M.k+1)*(inputWord M x y).length+M.k+(2*M.k+3)*steps)+
    5*(inputWord M x y).length+4*w.length+18

end IntMul.EndParkRecursiveLocalCalls


