-- Prove2me | Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
-- name    : LeanPool_PebblingLean_UpperBoundDelivery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:50:17.790401+00:00
-- url     : https://prove2.me/theorems/c72eb0b7-21eb-457a-abf5-1e412033bc81
-- title:
--   Upper Bound Delivery
-- statement:
--   Definitions and structural lemmas for Upper Bound Delivery, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundDelivery.lean

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Definitions.Def_LeanPool_PebblingLean_HypercubePath
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
open Pebbling
def stackListDistribution {n : ℕ} (rOut : ℕ) :
    List (HypercubeVertex n) → Pebbling (HypercubeVertex n)
  | [] => fun _ => 0
  | center :: centers =>
      Pebbling.single center (2 ^ rOut) + stackListDistribution rOut centers
def IsGoodCenterList (n rIn rOut T : ℕ) (centers : List (HypercubeVertex n)) : Prop :=
  ∀ target : HypercubeVertex n, T ≤ annulusTotalContribution rIn rOut target centers
end Hypercube
end PebblingLean


