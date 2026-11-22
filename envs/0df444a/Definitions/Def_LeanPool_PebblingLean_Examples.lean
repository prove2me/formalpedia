-- Prove2me | Definitions.Def_LeanPool_PebblingLean_Examples
-- name    : LeanPool_PebblingLean_Examples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:49:58.364904+00:00
-- url     : https://prove2.me/theorems/7e1f1a33-fec0-4a19-843c-90b0fb07110d
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Examples.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Tactic.Bound.Init
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
namespace Hypercube
def zeroVertex (n : ℕ) : HypercubeVertex n :=
  fun _ => false
def oneVertex (n : ℕ) : HypercubeVertex n :=
  fun _ => true
end Hypercube
namespace Examples
def squareThreeAtZero : Pebbling (HypercubeVertex 2) :=
  fun x => if x = Hypercube.zeroVertex 2 then 3 else 0
end Examples
end PebblingLean


