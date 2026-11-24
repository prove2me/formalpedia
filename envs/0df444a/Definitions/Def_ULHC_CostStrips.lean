-- Prove2me | Definitions.Def_ULHC_CostStrips
-- name    : ULHC_CostStrips
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:07:39.045667+00:00
-- url     : https://prove2.me/theorems/6cce8530-bd0e-4862-946f-709cd587092f
-- title:
--   Cost Strips
-- statement:
--   Definitions and structural lemmas for Cost Strips, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostStrips.lean

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
namespace ULHC
open Finset
def stripScanCost (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, j =>
    20 + (if IsCell V (cellJ c s j) ∧ LatOK F c s j then
      (if (front (cellJ c s j) s ∈ F ↔ j % 2 = 0) then 0 else stripScanCost V F c s k (j + 1))
      else 0)
def stripLenCost (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) : ℕ :=
  V.card + 3 + stripScanCost V F c s V.card 0
def allStripsCost (V : Finset Pt) (F : Finset Edge) : ℕ :=
  ∑ _c ∈ V, 8 + ∑ c ∈ V.filter (IsCell V), (∑ s ∈ sidesF, (stripLenCost V F c s + 2) + 5)
def flipCost : ℕ := 8
def sideOffBCost (b c : StripSpec) : ℕ := c.n * (20 * b.n + 2) + b.n + 2
def midBCost (b : StripSpec) : ℕ := 10 * b.n + 1
def notEndBCost (c : StripSpec) : ℕ := 5 * c.n + 1
def endOffBCost : ℕ := 30
def cr2BCost (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) : ℕ :=
  13 + 2 * flipCost + allStripsCost V (flip G (endCell b)) + sideOffBCost b c + notEndBCost c +
    endOffBCost + 2 * midBCost b + connBCost V G (back1 c.c c.s) +
    connBCost V (flip G (endCell b)) (back1 c.c c.s)
def chainOKBCost (c : StripSpec) : ℕ := 30 * c.n + 1
def validBCost (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) : ℕ :=
  allStripsCost V F + connBCost V F (back1 σ.c σ.s) + 5
def gedgeCost (V : Finset Pt) (G : Finset Edge) (x y : Node) : ℕ :=
  3 + cr2BCost V G x.σ y.σ + chainOKBCost y.σ
def gsrcCost (V : Finset Pt) (G : Finset Edge) (x : Node) : ℕ := 2 + validBCost V G x.σ
def candCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  allStripsCost V G +
    ∑ u ∈ V.filter (IsCell V), (flipCost + allStripsCost V (flip G u) + (allStrips V (flip G u)).card + 1) +
    9 * V.card + 2 * (cand V G).card
def candNCost (V : Finset Pt) (G : Finset Edge) : ℕ :=
  candCost V G + 10 * (cand V G).card + (candN V G).card
section bounds
variable {V : Finset Pt} {G : Finset Edge}
end bounds
end ULHC


