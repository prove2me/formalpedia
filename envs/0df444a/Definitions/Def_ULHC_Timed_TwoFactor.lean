-- Prove2me | Definitions.Def_ULHC_Timed_TwoFactor
-- name    : ULHC_Timed_TwoFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:09:53.422905+00:00
-- url     : https://prove2.me/theorems/178a1dc9-511a-4469-899c-c4e4ae40f721
-- title:
--   Two Factor
-- statement:
--   Definitions and structural lemmas for Two Factor, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TwoFactor.lean

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostTwoFactor
set_option autoImplicit true
namespace ULHC.T
open Finset TF
def fwdT (V : Finset Pt) (F : Finset Edge) (u : Pt) (e : Edge) : TimeM Bool := do
  let a ← memT e.p V
  let b ← memT e.q V
  let m ← memT e F
  tick 4
  pure (a && b && (if Black u then !m else m))
def nbrT (V : Finset Pt) (F : Finset Edge) (u : Pt) : TimeM (Finset Pt) := do
  let l ← lfilterT (fwdT V F u) (inc4 u)
  let l' ← lmapT (fun e => pure (other e u)) l
  toFinsetT l'
def layerAccT (V : Finset Pt) (F : Finset Edge) : ℕ → TimeM (List (Finset Pt))
  | 0 => do
    let L ← filterT (fun z => do
      let d ← degT F z
      tick 2
      pure ((Black z : Bool) && (d < 2 : Bool))) V
    pure [L]
  | k + 1 => do
    let A ← layerAccT V F k
    match A with
    | [] => do
      tick 1
      pure []
    | L :: Ls => do
      let Bs ← biUnionT (nbrT V F) L
      let L' ← unionT L Bs
      tick 1
      pure (L' :: L :: Ls)
def bwdT (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) (e : Edge) : TimeM Bool := do
  let a ← memT e.p V
  let b ← memT e.q V
  let o ← memT (other e v) L
  let m ← memT e F
  tick 4
  pure (a && b && o && (if Black v then m else !m))
def predT (V : Finset Pt) (F : Finset Edge) (L : Finset Pt) (v : Pt) : TimeM (Option Edge) :=
  lfindT (bwdT V F L v) (inc4 v)
def walkT (V : Finset Pt) (F0 : Finset Edge) :
    List (Finset Pt) → Pt → Finset Edge → TimeM (Finset Edge)
  | [], _, F => do
    tick 1
    pure F
  | L :: Ls, v, F => do
    let b ← memT v L
    tick 1
    if b then walkT V F0 Ls v F
    else do
      let p ← predT V F0 L v
      match p with
      | none => pure F
      | some e => do
        let F' ← if Black v then eraseT e F else insertT e F
        tick 1
        walkT V F0 Ls (other e v) F'
def augStepT (V : Finset Pt) (F : Finset Edge) : TimeM (Option (Finset Edge)) := do
  let n ← cardT V
  let A ← layerAccT V F n
  match A with
  | [] => do
    tick 1
    pure none
  | L :: Ls => do
    let S ← filterT (fun w => do
      let d ← degT F w
      tick 2
      pure (!(Black w : Bool) && (d < 2 : Bool))) L
    let p ← pickT S
    match p with
    | none => pure none
    | some w => do
      let F' ← walkT V F Ls w F
      pure (some F')
def augLoopT (V : Finset Pt) : ℕ → Finset Edge → TimeM (Finset Edge)
  | 0, F => do
    tick 1
    pure F
  | n + 1, F => do
    let r ← augStepT V F
    tick 1
    match r with
    | none => pure F
    | some F' => augLoopT V n F'
def twoFactorT (V : Finset Pt) : TimeM (Option (Finset Edge)) := do
  let n ← cardT V
  let F ← augLoopT V (n + 1) ∅
  let ok ← allT (fun z => do
    let d ← degT F z
    tick 1
    pure (eqN d 2)) V
  tick 1
  pure (if ok then some F else none)
end ULHC.T


