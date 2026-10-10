-- Prove2me | Definitions.Def_IntMul_EndParkRecursiveAmortizedWork
-- name    : IntMul_EndParkRecursiveAmortizedWork
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T04:42:28.66336+00:00
-- url     : https://prove2.me/theorems/c4aaf1b3-f22a-42e7-83da-b71c10cfee2a
-- title:
--   Word-only computation certificates with amortized retained-space potential
-- source:
--   Original amortized fixed-tape recursive word-work accounting. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveTraffic

namespace IntMul.EndParkRecursiveAmortizedWork

open IntMul.EndParkRecursiveEvaluation
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankedSimulation (nextExtent)

/-- Distance remaining to a fresh bank end, excluding the result tape. -/
def headSlack (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) : ℕ :=
  if j=M.outTape then 0 else extent j+1-c.head j

/-- Proof-only retained-space and head-distance potential. -/
noncomputable def potential (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg) : ℕ :=
  TrackedBankCleanup.span M extent+2*extent M.outTape+∑ j, headSlack M extent c j

/-- Simple word charge; neither head positions nor retained bank extents
occur in this per-call charge. The tape/label counts are fixed constants. -/
def callWordWork (M : MultitapeTM) (labels : ℕ) (v x y childWord : List Bool) : ℕ :=
  v.length+(M.k+2)*(inputWord M x y).length+4*childWord.length+labels+M.k+3

/-- Same fixed-body computation certificates, charging only ordinary body
steps and argument/shared/result words. Space is amortized separately. -/
inductive HasWordWork (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K) :
    (Fin M.k → ℕ) → M.Cfg → List Bool → List Bool → ℕ → ℕ → Prop
  | halt (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
      (halt : c.state=M.qHalt) (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
      HasWordWork M labels request resume extent c v w 0 (v.length+w.length+1)
  | step (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps work : ℕ)
      (live : c.state≠M.qHalt) (ordinary : request c.state=none)
      (rest : HasWordWork M labels request resume (nextExtent M c extent) (M.step c) v w steps work) :
      HasWordWork M labels request resume extent c v w (steps+1) work
  | call (extent : Fin M.k → ℕ) (c : M.Cfg) (v x y childWord w : List Bool)
      (label : Fin labels) (childSteps childWork parentSteps parentWork : ℕ)
      (live : c.state≠M.qHalt) (request_label : request c.state=some label)
      (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
      (child : HasWordWork M labels request resume (initialExtent M x y) (M.initCfg x y) [] childWord childSteps childWork)
      (parent : HasWordWork M labels request resume (parentAfterChildExtent M extent childWord)
        (resumedParent M labels resume label extent c childWord) childWord w parentSteps parentWork) :
      HasWordWork M labels request resume extent c v w (childSteps+parentSteps)
        (childWork+parentWork+callWordWork M labels v x y childWord)

end IntMul.EndParkRecursiveAmortizedWork


