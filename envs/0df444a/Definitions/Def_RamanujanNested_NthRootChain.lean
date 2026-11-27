-- Prove2me | Definitions.Def_RamanujanNested_NthRootChain
-- name    : RamanujanNested_NthRootChain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T05:05:12.691109+00:00
-- url     : https://prove2.me/theorems/f64d4c74-658c-49aa-8bd5-f239db59518d
-- title:
--   Nth Root Chain
-- statement:
--   Definitions and structural lemmas for Nth Root Chain, from Flaman55 (Flaman55/RamanujanNestedRadicals; see pinned Apache-2.0 LICENSE and source headers)'s pinned Convergence and exact values of Ramanujan-type nested radicals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/NthRootChain.lean

module
public import Definitions.Def_RamanujanNested_Defs
public import Mathlib
set_option autoImplicit true
@[expose] public section
namespace RamanujanNested
@[expose] public noncomputable def rollUpN (n : ℕ) (a : ℕ → ℝ) (T : ℝ) : ℕ → ℝ
  | 0 => T
  | (k + 1) => (1 + a 1 * rollUpN n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ))
open Filter Topology
end RamanujanNested


