-- Prove2me | Definitions.Def_CatalyticTreeEval_NatHeaderScan
-- name    : CatalyticTreeEval_NatHeaderScan
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:55:23.354001+00:00
-- url     : https://prove2.me/theorems/fe8c6fed-e8d8-42c9-8d2d-b5fb1ef9127e
-- title:
--   Native binary scanner for a unary field-width header
-- statement:
--   A one-state native binary machine scans a run of true bits followed by a false delimiter. From the input origin it first advances to the first input bit. It writes back the same work bit, does not write the catalyst, and emits nothing. The module also defines proof-level cursor configurations, a head envelope and an empty writable footprint. Execution and resource guarantees are subsequent proof obligations.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section 3 machine model; native parsing infrastructure for the mission natCode serialization.

import Definitions.Def_CatalyticTreeEval_MachineContracts

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NatHeaderScan

open CatalyticMatching.General

/-- Scan the unary width of `natCode`.  At the input origin the same state
first moves onto the input. The first false bit is consumed and causes exit.
Every work bit, the catalyst, and the existing output are preserved. -/
def machine : Main.Machine where
  states := 1
  start := 0
  table _ input work _ origin _ _ :=
    { next := if origin || input == some true then some 0 else none
      workWrite := work
      catalystWrite := none
      inputMove := .right
      workMove := .stay
      catalystMove := .stay
      emit := none }

/-- Only the input cursor and control state change during header scanning. -/
def cursor (c : Config machine) (head : ℕ) (live : Bool) : Config machine :=
  { c with state := if live then some machine.start else none, inputHead := head }

def envelope (c : Config machine) : Envelope :=
  ⟨c.workHead, c.workHead + 1, c.catalystHead, c.catalystHead + 1⟩

def footprint : Footprint := ⟨∅, ∅⟩

end CatalyticTreeEval.Contracts.NatHeaderScan


