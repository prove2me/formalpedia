-- Prove2me | Definitions.Def_RamanujanNested_PrimeChain
-- name    : RamanujanNested_PrimeChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T05:02:19.241513+00:00
-- url     : https://prove2.me/theorems/c4e19e71-9453-4b8e-a919-cca0bc90d935
-- title:
--   Prime Chain
-- statement:
--   Definitions and structural lemmas for Prime Chain, from Flaman55 (Flaman55/RamanujanNestedRadicals; see pinned Apache-2.0 LICENSE and source headers)'s pinned Convergence and exact values of Ramanujan-type nested radicals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/PrimeChain.lean

module
public import Definitions.Def_RamanujanNested_Bounds
public import Definitions.Def_RamanujanNested_Monotone
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.PrimeCounting
set_option autoImplicit true
@[expose] public section
namespace RamanujanNested
open Filter Topology
@[expose] public noncomputable def primeCoeff (k : ℕ) : ℝ :=
  if k = 0 then 0 else (Nat.nth Nat.Prime (k - 1) : ℝ)
end RamanujanNested


