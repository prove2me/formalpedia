-- Prove2me | Definitions.Def_RamanujanNested_IdentityChainNthRoot
-- name    : RamanujanNested_IdentityChainNthRoot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T04:58:34.167704+00:00
-- url     : https://prove2.me/theorems/9180e36b-39cb-4071-99c1-be70ecac6268
-- title:
--   Identity Chain Nth Root
-- statement:
--   Definitions and structural lemmas for Identity Chain Nth Root, from Flaman55 (Flaman55/RamanujanNestedRadicals; see pinned Apache-2.0 LICENSE and source headers)'s pinned Convergence and exact values of Ramanujan-type nested radicals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/IdentityChainNthRoot.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
namespace RamanujanNested
open Finset
@[expose] public noncomputable def altSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range n, x ^ i * (-1 : ℝ) ^ (n - 1 - i)
@[expose] public noncomputable def chainClosedFormS (N k : ℕ) : ℝ := (N : ℝ) + (k : ℝ) - 1
@[expose] public noncomputable def altCoeffR (n : ℕ) (N : ℝ) (k : ℕ) : ℝ := altSum n (N + (k : ℝ) - 1)
@[expose] public noncomputable def rollUpNS (n : ℕ) (a : ℕ → ℝ) (T : ℝ) : ℕ → ℝ
  | 0 => T
  | (k + 1) => ((-1 : ℝ) ^ n + a 1 * rollUpNS n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ))
@[expose] public noncomputable def truncRadicalNS (n : ℕ) (N : ℝ) (d : ℕ) : ℝ := rollUpNS n (altCoeffR n N) 1 d
open Filter Topology
@[expose] public noncomputable def limitValNS (n : ℕ) (N : ℝ) : ℝ := ⨆ d, truncRadicalNS n N d
@[expose] public noncomputable def deficitS (n : ℕ) (N : ℝ) : ℝ := N - limitValNS n N
@[expose] public noncomputable def shrinkFactor (n : ℕ) (N : ℝ) : ℝ := 1 - 2 / (N ^ n + 1)
end RamanujanNested


