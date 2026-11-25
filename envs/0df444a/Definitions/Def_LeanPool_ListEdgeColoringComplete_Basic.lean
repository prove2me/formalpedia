-- Prove2me | Definitions.Def_LeanPool_ListEdgeColoringComplete_Basic
-- name    : LeanPool_ListEdgeColoringComplete_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:54:17.27969+00:00
-- url     : https://prove2.me/theorems/0f0c393b-c2ff-58a5-9831-442eb1b88a25
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/haggkvist-janssen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Haggkvist-Janssen bound on the list chromatic index of complete graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Basic.lean

module
public import Mathlib.Data.Fintype.Basic
public import Lean.Elab.Tactic.Omega
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.ListEdgeColoringComplete
def targetDegree (n i j : ℕ) : ℕ :=
  if n - 1 ≤ i + j then n - 1 else n - 2
def blockedRank (n i : ℕ) : ℕ :=
  if i < n / 2 then n - 2 - i else n - 1 - i + n / 2
end LeanPool.ListEdgeColoringComplete


