-- Prove2me | Definitions.Def_FD1D_Potential
-- name    : FD1D_Potential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:54:11.842843+00:00
-- url     : https://prove2.me/theorems/0049edfd-e937-4f74-8454-f6e9ac663485
-- title:
--   Potential
-- statement:
--   Definitions and structural lemmas for Potential, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
set_option autoImplicit true
namespace FD1D
noncomputable section
open scoped BigOperators
def bernoulliMass (r : ℝ) (outcome : Bool) : ℝ :=
  if outcome then r else 1 - r
def updateCount (N : ℕ) (deleted arrived : Bool) : ℕ :=
  if deleted then
    if arrived then N else N - 1
  else
    if arrived then N + 1 else N
def expectedNodePotentialChange
    (a : ℝ) (N : ℕ) (p q : ℝ) : ℝ :=
  ∑ deleted : Bool, ∑ arrived : Bool,
    bernoulliMass q deleted * bernoulliMass p arrived *
      (harmonicPotential a (updateCount N deleted arrived) -
        harmonicPotential a N)
def globalHarmonicPotential
    (L : ℕ) (a : ℝ) (N : ∀ d, DyadicNode d → ℕ) : ℝ :=
  ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
    (nodeMass (d + 1) v) ^ 2 * harmonicPotential a (N (d + 1) v)
def potentialDrift
    (L : ℕ) (a : ℝ) (N : ∀ d, DyadicNode d → ℕ)
    (q : ∀ d, DyadicNode d → ℝ) : ℝ :=
  bellmanDrift L a (fun d v => N d v) q
def potentialRemainder
    (L : ℕ) (a : ℝ) (N : ∀ d, DyadicNode d → ℕ)
    (q : ∀ d, DyadicNode d → ℝ) : ℝ :=
  ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
    (nodeMass (d + 1) v) ^ 3 * (1 - q (d + 1) v) /
      (((N (d + 1) v : ℝ) + a) *
        ((N (d + 1) v : ℝ) + a + 1))
def expectedGlobalPotentialChange
    (L : ℕ) (a : ℝ) (N : ∀ d, DyadicNode d → ℕ)
    (q : ∀ d, DyadicNode d → ℝ) : ℝ :=
  ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
    (nodeMass (d + 1) v) ^ 2 *
      expectedNodePotentialChange a (N (d + 1) v)
        (nodeMass (d + 1) v) (q (d + 1) v)
end
end FD1D


