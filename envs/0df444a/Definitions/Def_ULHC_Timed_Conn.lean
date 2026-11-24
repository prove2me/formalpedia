-- Prove2me | Definitions.Def_ULHC_Timed_Conn
-- name    : ULHC_Timed_Conn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:06:55.216262+00:00
-- url     : https://prove2.me/theorems/d9776eec-3682-4f80-bbcf-b19638a86362
-- title:
--   Conn
-- statement:
--   Definitions and structural lemmas for Conn, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Conn.lean

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostConn
set_option autoImplicit true
namespace ULHC.T
open Finset
def isCellT (V : Finset Pt) (c : Pt) : TimeM Bool := do
  let a ← memT c V
  let b ← memT (c.1 + 1, c.2) V
  let d ← memT (c.1, c.2 + 1) V
  let e ← memT (c.1 + 1, c.2 + 1) V
  tick 3
  pure (a && b && d && e)
def degT (F : Finset Edge) (p : Pt) : TimeM ℕ := do
  let a ← memT (eR p) F
  let b ← memT (eL p) F
  let c ← memT (eU p) F
  let d ← memT (eD p) F
  tick 4
  pure ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) + (if d then 1 else 0))
def fnbrT (F : Finset Edge) (u : Pt) : TimeM (Finset Pt) := do
  let l ← lfilterT (fun e => memT e F) (TF.inc4 u)
  let l' ← lmapT (fun e => pure (other e u)) l
  toFinsetT l'
def creachT (F : Finset Edge) (x : Pt) : ℕ → TimeM (Finset Pt)
  | 0 => do
    tick 1
    pure {x}
  | k + 1 => do
    let C ← creachT F x k
    let Bs ← biUnionT (fnbrT F) C
    unionT C Bs
def cclsT (V : Finset Pt) (F : Finset Edge) (x : Pt) : TimeM (Finset Pt) := do
  let n ← cardT V
  creachT F x n
def connBT (V : Finset Pt) (F : Finset Edge) (x y : Pt) : TimeM Bool := do
  let C ← cclsT V F x
  memT y C
def cncompT (V : Finset Pt) (F : Finset Edge) : TimeM ℕ := do
  let S ← imageSetsT (cclsT V F) V
  cardT S
end ULHC.T


