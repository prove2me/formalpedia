-- Prove2me | Definitions.Def_LeanPool_Vizing_Fan
-- name    : LeanPool_Vizing_Fan
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:54:01.772584+00:00
-- url     : https://prove2.me/theorems/6d697e84-4954-4711-b819-8f3e4da986a3
-- title:
--   Fan
-- statement:
--   Definitions and structural lemmas for Fan, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Fan.lean

module
public import Definitions.Def_LeanPool_Vizing_Kempe
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace LeanPool.Vizing
namespace PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [DecidableEq C]
  {G : SimpleGraph V}
structure IsFan (c : PEC G C) (x y : V) (n : ℕ) (f : ℕ → V) : Prop where
  start : f 0 = y
  uncoloured : c.col x y = none
  adj : ∀ i ≤ n, G.Adj x (f i)
  inj : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i = j
  step : ∀ i < n, ∃ γ, c.col x (f (i + 1)) = some γ ∧ c.IsFree (f i) γ
end PEC
end LeanPool.Vizing


