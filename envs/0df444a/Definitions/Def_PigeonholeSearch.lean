-- Prove2me | Definitions.Def_PigeonholeSearch
-- name    : PigeonholeSearch
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T02:37:06.191578+00:00
-- url     : https://prove2.me/theorems/25db580c-4aee-4e6f-955c-cc2c6b2ba217
-- title:
--   Clause search trees for the unary pigeonhole principle
-- statement:
--   A Boolean variable records whether a given pigeon occupies a given hole. A row clause requires that a pigeon occupies some hole. A collision clause forbids two distinct pigeons from occupying the same hole. A finite binary tree queries one variable at each internal node and names an input clause at each leaf.
-- source:
--   Beyersdorff, Galesi and Lauria, Information Processing Letters 110 (2010), 1074–1077, sections 1, 2 and 4, https://doi.org/10.1016/j.ipl.2010.09.007. The explicit elementary leaf bound here is for the ordinary variable-query search-tree model.

import Mathlib

namespace PigeonholeSearch

inductive Clause (n : ℕ) where
  | row (p : Fin (n+1))
  | collision (p q : Fin (n+1)) (h : Fin n) (distinct : p ≠ q)

abbrev Assignment (n : ℕ) := Fin (n+1) → Fin n → Bool

def Clause.violated {n : ℕ} (x : Assignment n) : Clause n → Prop
  | .row p => ∀ h, x p h = false
  | .collision p q h _ => x p h = true ∧ x q h = true

inductive Tree (n : ℕ) where
  | leaf (c : Clause n)
  | query (p : Fin (n+1)) (h : Fin n) (no yes : Tree n)

def Tree.run {n : ℕ} (x : Assignment n) : Tree n → Clause n
  | .leaf c => c
  | .query p h no yes => if x p h then yes.run x else no.run x

def Tree.leaves {n : ℕ} : Tree n → ℕ
  | .leaf _ => 1
  | .query _ _ no yes => no.leaves + yes.leaves

end PigeonholeSearch


