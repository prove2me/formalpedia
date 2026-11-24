-- Prove2me | Definitions.Def_ULHC_CostMinPath
-- name    : ULHC_CostMinPath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:36:22.791031+00:00
-- url     : https://prove2.me/theorems/7b2af34a-339e-474b-a33d-13455c9c97c6
-- title:
--   Cost Min Path
-- statement:
--   Definitions and structural lemmas for Cost Min Path, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostMinPath.lean

import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
namespace ULHC.MP
variable {α : Type} [DecidableEq α]
def lookCost {β : Type} (tbl : List (α × β)) : ℕ := tbl.length + 1
def stepCost (NL : List α) (mid tgt : α → Bool) (ec : α → α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) (x : α) : ℕ :=
  1 + (if tgt x then 2 else 1 + (if mid x then (NL.map fun y => ec x y + lookCost tbl + 4).sum + 1
    else 0))
def nextCost (NL : List α) (mid tgt : α → Bool) (ec : α → α → ℕ)
    (tbl : List (α × Option (ℕ × List α))) : ℕ :=
  (NL.map fun x => stepCost NL mid tgt ec tbl x + 1).sum
def layerCost (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (ec : α → α → ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => layerCost NL mid tgt edge w ec k + nextCost NL mid tgt ec (layer NL mid tgt edge w k)
def pickSrcCost (NL : List α) (sc : α → ℕ) (tbl : List (α × Option (ℕ × List α))) : ℕ :=
  (NL.map fun x => sc x + lookCost tbl + 2).sum + 2
def minPathLCost (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
    (ec : α → α → ℕ) (sc : α → ℕ) : ℕ :=
  layerCost NL mid tgt edge w ec NL.length + pickSrcCost NL sc (layer NL mid tgt edge w NL.length) +
    NL.length + 1
section bound
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  (ec : α → α → ℕ) (sc : α → ℕ) {E S : ℕ}
  (hE : ∀ x ∈ NL, ∀ y ∈ NL, ec x y ≤ E) (hS : ∀ x ∈ NL, sc x ≤ S)
end bound
section mono
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  {ec ec' : α → α → ℕ} {sc sc' : α → ℕ} (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x)
end mono
def minPathCost {β : Type} [LinearOrder β] (N : Finset β) (mid tgt : β → Bool)
    (edge : β → β → Bool) (w : β → ℕ) (ec : β → β → ℕ) (sc : β → ℕ) : ℕ :=
  N.card ^ 2 + minPathLCost (N.sort (· ≤ ·)) mid tgt edge w ec sc
end ULHC.MP


