-- Prove2me | Definitions.Def_ULHC_CostAlg
-- name    : ULHC_CostAlg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:10:40.202195+00:00
-- url     : https://prove2.me/theorems/9540a1b6-b5cc-4276-9353-cfdd3079d01d
-- title:
--   Cost Alg
-- statement:
--   Definitions and structural lemmas for Cost Alg, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostAlg.lean

import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_CostTwoFactor
import Definitions.Def_ULHC_Timed_TimeM
import Theorems.Thm_ULHC_Good_step

set_option autoImplicit true
namespace ULHC
open Finset
def cellListCost (V : Finset Pt) : ℕ := 10 * V.card + V.card ^ 2
def t3BCost (V : Finset Pt) (G : Finset Edge) (d : Pt) (tf : Side) : ℕ :=
  10 + connBCost V G (back1 d tf)
def findT3Cost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  cellListCost V + 9 * (cellList V).length +
    (((cellList V).flatMap fun d => sidesL.map fun tf => (d, tf)).map
      fun p => t3BCost V G p.1 p.2 + 1).sum
def decodeCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  match findPath V G with
  | some (_, L) => L.length + 2
  | none => 1
def findPathCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  candNCost V G +
    MP.minPathCost (candN V G) gmid gtgt (gedge V G) gw (gedgeCost V G) (gsrcCost V G) +
    decodeCost V G
def applySCost (a : StripSpec) : ℕ := flipCost * a.n + 1
def roundCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  findT3Cost V G +
    match findT3 V G with
    | some _ => flipCost
    | none =>
      findPathCost V G +
        match findPath V G with
        | some (a, _) => applySCost a
        | none => 0
def runCost (V : Finset Pt) : ℕ → Finset Edge → ℕ
  | 0, G => cncompCost V G + 2
  | k + 1, G =>
    cncompCost V G + 2 +
      if cncomp V G == 1 then 0
      else roundCost V G +
        match step V G with
        | some G' => runCost V k G'
        | none => 0
def ulhcCost (V : Finset Pt) : ℕ :=
  twoFactorCost V + V.card + 10 +
    match twoFactor V with
    | some F => runCost V (fuel V) F
    | none => 0
section bounds
variable {V : Finset Pt} {G : Finset Edge}
end bounds
end ULHC


