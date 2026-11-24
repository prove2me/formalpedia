-- Prove2me | Definitions.Def_ULHC_Timed_MinPath
-- name    : ULHC_Timed_MinPath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:07:43.386326+00:00
-- url     : https://prove2.me/theorems/9019394d-16ee-4f4e-97b7-c7fc52d9a6b9
-- title:
--   Min Path
-- statement:
--   Definitions and structural lemmas for Min Path, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
set_option autoImplicit true
namespace ULHC.T
variable {α : Type} [DecidableEq α]
def lookT {β : Type} (x : α) : List (α × Option β) → TimeM (Option β)
  | [] => do
    tick 1
    pure none
  | (a, v) :: tf => do
    tick 1
    if a = x then pure v else lookT x tf
def aminT {γ β : Type} (f : γ → TimeM (Option (ℕ × β))) : List γ → TimeM (Option (ℕ × β))
  | [] => do
    tick 1
    pure none
  | y :: ys => do
    let a ← f y
    let b ← aminT f ys
    tick 1
    pure (pick2 a b)
def stepT (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) (x : α) : TimeM (Option (ℕ × List α)) := do
  tick 1
  if tgt x then do
    tick 2
    pure (some (w x, [x]))
  else do
    tick 1
    if mid x then
      aminT (fun y => do
        let e ← edgeT x y
        let tf ← lookT y tbl
        tick 3
        pure (if e then extend x (w x) tf else none)) NL
    else pure none
def nextT (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) : TimeM (List (α × Option (ℕ × List α))) :=
  lmapT (fun x => do
    let r ← stepT NL mid tgt edgeT w tbl x
    pure (x, r)) NL
def layerT (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ) :
    ℕ → TimeM (List (α × Option (ℕ × List α)))
  | 0 => do
    tick 1
    pure []
  | k + 1 => do
    let tf ← layerT NL mid tgt edgeT w k
    nextT NL mid tgt edgeT w tf
def pickSrcT (NL : List α) (srcT : α → TimeM Bool) (tbl : List (α × Option (ℕ × List α))) :
    TimeM (Option (List α)) := do
  let r ← aminT (fun x => do
    let s ← srcT x
    let tf ← lookT x tbl
    tick 1
    pure (if s then tf else none)) NL
  tick 1
  pure (dropW r)
def minPathLT (NL : List α) (srcT : α → TimeM Bool) (mid tgt : α → Bool)
    (edgeT : α → α → TimeM Bool) (w : α → ℕ) : TimeM (Option (List α)) := do
  let n ← lengthT NL
  let tbl ← layerT NL mid tgt edgeT w n
  pickSrcT NL srcT tbl
def minPathT {β : Type} [LinearOrder β] (N : Finset β) (srcT : β → TimeM Bool) (mid tgt : β → Bool)
    (edgeT : β → β → TimeM Bool) (w : β → ℕ) : TimeM (Option (List β)) := do
  let l ← sortT N
  minPathLT l srcT mid tgt edgeT w
section results
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)
end results
section steps
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)
end steps
end ULHC.T


