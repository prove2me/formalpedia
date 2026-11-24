-- Prove2me | Definitions.Def_ULHC_CostConn
-- name    : ULHC_CostConn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:05:24.851928+00:00
-- url     : https://prove2.me/theorems/1b8c05aa-79f3-441f-99f3-5c3098693f6f
-- title:
--   Cost Conn
-- statement:
--   Definitions and structural lemmas for Cost Conn, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostConn.lean

import Definitions.Def_ULHC_Algorithm
set_option autoImplicit true
namespace ULHC
open Finset
def fnbrCost : ℕ := 20
def creachCost (F : Finset Edge) (x : Pt) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
    creachCost F x k + ∑ u ∈ creach F x k, (fnbrCost + (fnbr F u).card) +
      (creach F x k).card + ((creach F x k).biUnion (fnbr F)).card
def cclsCost (V : Finset Pt) (F : Finset Edge) (x : Pt) : ℕ := creachCost F x V.card + V.card + 1
def connBCost (V : Finset Pt) (F : Finset Edge) (x : Pt) : ℕ := cclsCost V F x + 1
def cncompCost (V : Finset Pt) (F : Finset Edge) : ℕ :=
  ∑ x ∈ V, (cclsCost V F x + (ccls V F x).card + 1) + V.card + 1
end ULHC


