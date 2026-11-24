-- Prove2me | Definitions.Def_ULHC_Timed_Alg
-- name    : ULHC_Timed_Alg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:13:20.656923+00:00
-- url     : https://prove2.me/theorems/fe2678b5-c3a0-4e6a-b997-5de3a3822967
-- title:
--   Alg
-- statement:
--   Definitions and structural lemmas for Alg, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Alg.lean

import Definitions.Def_ULHC_Timed_Strips
import Definitions.Def_ULHC_Timed_MinPath
import Definitions.Def_ULHC_Timed_TwoFactor
import Definitions.Def_ULHC_CostAlg
set_option autoImplicit true
namespace ULHC.T
open Finset
def cellListT (V : Finset Pt) : TimeM (List Pt) := do
  let Cs ← filterT (isCellT V) V
  let Ls ← imageT (fun x => pure (toLex x)) Cs
  let l ← sortT Ls
  lmapT (fun x => pure (ofLex x)) l
def t3BT (V : Finset Pt) (G : Finset Edge) (d : Pt) (tf : Side) : TimeM Bool := do
  let a ← memT (back d tf) G
  let b ← memT (front d tf) G
  let c ← memT (lat1 d tf) G
  let e ← memT (lat2 d tf) G
  let k ← connBT V G (back1 d tf) (front1 d tf)
  tick 4
  pure (a && b && !c && !e && !k)
def findT3T (V : Finset Pt) (G : Finset Edge) : TimeM (Option (Pt × Side)) := do
  let cl ← cellListT V
  let ps ← lflatMapT (fun d => lmapT (fun tf => pure (d, tf)) sidesL) cl
  lfindT (fun p => t3BT V G p.1 p.2) ps
def decodeT : List Node → TimeM (Option (StripSpec × List StripSpec))
  | [] => do
    tick 1
    pure none
  | x :: p => do
    let l ← lmapT (fun y => pure y.σ) p
    tick 1
    pure (some (x.σ, l))
def findPathT (V : Finset Pt) (G : Finset Edge) : TimeM (Option (StripSpec × List StripSpec)) := do
  let N ← candNT V G
  let r ← minPathT N (gsrcT V G) gmid gtgt (gedgeT V G) gw
  match r with
  | none => pure none
  | some q => decodeT q
def flipColT (F : Finset Edge) (c : Pt) (s : Side) : ℕ → TimeM (Finset Edge)
  | 0 => do
    tick 1
    pure F
  | n + 1 => do
    let F' ← flipT F (cellJ c s n)
    flipColT F' c s n
def roundT (V : Finset Pt) (G : Finset Edge) : TimeM (Option (Finset Edge)) := do
  let r ← findT3T V G
  match r with
  | some (d, _) => do
    let G' ← flipT G d
    pure (some G')
  | none => do
    let p ← findPathT V G
    match p with
    | some (a, _) => do
      let G' ← flipColT G a.c a.s a.n
      pure (some G')
    | none => pure none
def runT (V : Finset Pt) : ℕ → Finset Edge → TimeM Bool
  | 0, G => do
    let c ← cncompT V G
    tick 2
    pure (c == 1)
  | k + 1, G => do
    let c ← cncompT V G
    tick 2
    if c == 1 then pure true
    else do
      let r ← roundT V G
      match r with
      | some G' => runT V k G'
      | none => pure false
def fuelN (n : ℕ) : ℕ := (n + 1) * (2 * (3 * (4 * n + n * (4 * n)) * n) + 4) + 2
def ulhcT (V : Finset Pt) : TimeM Bool := do
  let F? ← twoFactorT V
  let n ← cardT V
  tick 9
  match F? with
  | some F => runT V (fuelN n) F
  | none => pure false
end ULHC.T


