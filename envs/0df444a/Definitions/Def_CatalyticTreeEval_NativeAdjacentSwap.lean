-- Prove2me | Definitions.Def_CatalyticTreeEval_NativeAdjacentSwap
-- name    : CatalyticTreeEval_NativeAdjacentSwap
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:23:07.335688+00:00
-- url     : https://prove2.me/theorems/7ca9f962-a01b-4d70-817a-07655c952f43
-- title:
--   Native adjacent catalyst-bit exchange
-- statement:
--   A five-state native binary machine exchanges two adjacent catalyst bits in three transitions, using only its finite control to retain their transient values. This interface specifies the finite code and associated contract data. Exact execution, tape frames and head bounds are proved separately.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section 4.3 and Corollary 4.2, register permutation infrastructure.

import Definitions.Def_CatalyticTreeEval_MachineContracts

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeAdjacentSwap

open CatalyticMatching.General

/-- Exchange the current catalyst bit with its right neighbour in three native steps.
The first and second bits are saved in finite control, never on the work tape. -/
def machine : Main.Machine where
  states := 5
  start := 0
  table q _ work catalyst _ _ _ :=
    if q = 0 then
      { next := some (if catalyst == some true then 2 else 1)
        workWrite := work, catalystWrite := none
        inputMove := .stay, workMove := .stay, catalystMove := .right, emit := none }
    else if q = 1 ∨ q = 2 then
      { next := some (if catalyst == some true then 4 else 3)
        workWrite := work, catalystWrite := some (q == 2)
        inputMove := .stay, workMove := .stay, catalystMove := .left, emit := none }
    else
      { next := none, workWrite := work, catalystWrite := some (q == 4)
        inputMove := .stay, workMove := .stay, catalystMove := .stay, emit := none }

def first (c : Config machine) (a : Bool) : Config machine :=
  { c with
    state := some (if a then (2 : Fin 5) else (1 : Fin 5))
    catalystHead := c.catalystHead + 1 }

def second (c : Config machine) (a b : Bool) : Config machine :=
  { c with
    state := some (if b then (4 : Fin 5) else (3 : Fin 5))
    catalyst := c.catalyst.set (c.catalystHead + 1) a }

def finish (c : Config machine) (a b : Bool) : Config machine :=
  { c with
    state := none
    catalyst := (c.catalyst.set (c.catalystHead + 1) a).set c.catalystHead b }

def envelope (c : Config machine) : Envelope :=
  ⟨c.workHead, c.workHead + 1, c.catalystHead, c.catalystHead + 2⟩

def footprint (c : Config machine) : Footprint :=
  ⟨∅, {c.catalystHead, c.catalystHead + 1}⟩

end CatalyticTreeEval.Contracts.NativeAdjacentSwap


