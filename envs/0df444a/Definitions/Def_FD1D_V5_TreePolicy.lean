-- Prove2me | Definitions.Def_FD1D_V5_TreePolicy
-- name    : FD1D_V5_TreePolicy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:34:11.9485+00:00
-- url     : https://prove2.me/theorems/ebbbe522-f9be-45c7-81de-909d768047a6
-- title:
--   Tree Policy
-- statement:
--   Definitions and structural lemmas for Tree Policy, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/TreePolicy.lean

import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
namespace FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
def childRate (a p h : ℝ) (x y : ℕ) (side : Fin 2) : ℝ :=
  if side = 0 then rateLeft a p h x y else rateRight a p h x y
def rate (I : AggregatedInventory L m) (a : ℝ) :
    ∀ d, DyadicNode d → ℝ
  | 0, _ => 1 / (m : ℝ)
  | d + 1, w =>
      let z := (childrenEquiv d).symm w
      childRate a (nodeMass d z.1) (rate I a d z.1)
        (I.count (d + 1) (leftChild z.1))
        (I.count (d + 1) (rightChild z.1)) z.2
def inventory (I : AggregatedInventory L m) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  I.count d v
def intervalMass (d : ℕ) (v : DyadicNode d) : ℝ :=
  nodeMass d v
def deletionMass (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  inventory I d v * rate I a d v
def discrepancy (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  (intervalMass d v - deletionMass I a d v) / a
def regularizedMass (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  intervalMass d v / (inventory I d v + a / 2)
def bellmanValue (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  bellman (rate I a d v) (discrepancy I a d v)
    (regularizedMass I a d v)
def imbalance (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  deletionMass I a (d + 1) (leftChild v) -
    deletionMass I a (d + 1) (rightChild v)
def transportEnergy (I : AggregatedInventory L m) (a : ℝ) : ℝ :=
  internalWeightedSum (fun d v => imbalance I a d v ^ 2) L
def restoringDrift (I : AggregatedInventory L m) (a : ℝ) : ℝ :=
  bellmanDrift L (a / 2) (inventory I) (deletionMass I a)
end
end FD1D.V5.TreePolicy


