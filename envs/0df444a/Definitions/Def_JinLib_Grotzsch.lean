-- Prove2me | Definitions.Def_JinLib_Grotzsch
-- name    : JinLib_Grotzsch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:45:04.764163+00:00
-- url     : https://prove2.me/theorems/5abc1dfc-9ac6-4b34-b77c-950a5c3a72c4
-- title:
--   Grotzsch
-- statement:
--   Definitions and structural lemmas for Grotzsch, from Juan Pablo Traverso Gianini (jtraverso/jin-triangle-free; see pinned Apache-2.0 LICENSE and source headers)'s pinned Jin's theorem on dense triangle-free graphs in Lean 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DenseTriangleFree
def grotzschAdjB (i j : Fin 11) : Bool :=
  let a := i.val
  let b := j.val
  (a < 5 && b < 5 && ((a + 1) % 5 == b || (b + 1) % 5 == a)) ||
  (a < 5 && 5 ≤ b && b < 10 && ((b - 5 + 1) % 5 == a || (a + 1) % 5 == b - 5)) ||
  (b < 5 && 5 ≤ a && a < 10 && ((a - 5 + 1) % 5 == b || (b + 1) % 5 == a - 5)) ||
  (a == 10 && 5 ≤ b && b < 10) || (b == 10 && 5 ≤ a && a < 10)
lemma grotzschAdjB_symm : ∀ i j, grotzschAdjB i j = grotzschAdjB j i := by decide
lemma grotzschAdjB_irrefl : ∀ i, grotzschAdjB i i = false := by decide
def grotzsch : SimpleGraph (Fin 11) where
  Adj i j := grotzschAdjB i j = true
  symm := ⟨fun i j h => by rwa [grotzschAdjB_symm]⟩
  loopless := ⟨fun i h => by simp [grotzschAdjB_irrefl i] at h⟩
instance : DecidableRel grotzsch.Adj := fun i j =>
  inferInstanceAs (Decidable (grotzschAdjB i j = true))
def grotzschWt (i : Fin 11) : ℕ := if i.val < 5 then 3 else if i.val < 10 then 2 else 4
def grotzschIndepB (b : Fin 11 → Bool) : Bool :=
  (List.finRange 11).all fun i => (List.finRange 11).all fun j =>
    !(grotzschAdjB i j && b i && b j)
def grotzschWtB (b : Fin 11 → Bool) : ℕ :=
  ((List.finRange 11).map fun i => if b i then grotzschWt i else 0).sum
end DenseTriangleFree


