-- Prove2me | Definitions.Def_LeanPool_PebblingLean_UpperBound
-- name    : LeanPool_PebblingLean_UpperBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:49:56.609889+00:00
-- url     : https://prove2.me/theorems/96a1f5c1-8ccd-4294-bbb5-c5a91091330c
-- title:
--   Upper Bound
-- statement:
--   Definitions and structural lemmas for Upper Bound, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
open Pebbling
def annulus (n rIn rOut : ℕ) (target : HypercubeVertex n) : Finset (HypercubeVertex n) :=
  Finset.univ.filter fun center => rIn ≤ dist center target ∧ dist center target ≤ rOut
def annulusContribution {n : ℕ} (rIn rOut : ℕ) (target center : HypercubeVertex n) : ℕ :=
  if rIn ≤ dist center target ∧ dist center target ≤ rOut then
    2 ^ (rOut - dist center target)
  else
    0
def annulusTotalContribution {n : ℕ} (rIn rOut : ℕ) (target : HypercubeVertex n)
    (centers : List (HypercubeVertex n)) : ℕ :=
  (centers.map (annulusContribution rIn rOut target)).sum
def HasHighDemandDistribution (n T : ℕ) (costBound minPile : ℕ) : Prop :=
  ∃ D : Pebbling (HypercubeVertex n),
    size D ≤ costBound ∧
      SolvableAtLeast (graph n) D T ∧
        MinOccupiedPileSize D minPile
def constantDistribution (n S : ℕ) : Pebbling (HypercubeVertex n) :=
  fun _ => S
end Hypercube
end PebblingLean


