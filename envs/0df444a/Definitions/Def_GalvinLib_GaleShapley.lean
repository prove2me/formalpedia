-- Prove2me | Definitions.Def_GalvinLib_GaleShapley
-- name    : GalvinLib_GaleShapley
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:11.033106+00:00
-- url     : https://prove2.me/theorems/096508b1-eab4-43ae-b103-68d2e4ef841e
-- title:
--   Gale Shapley
-- statement:
--   Definitions and structural lemmas for Gale Shapley, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinLib/GaleShapley.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose
public import Mathlib.Data.Set.Card
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Galvin
def IsTop {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (m : M) (w : W) : Prop :=
  E m w ∧ ∀ w', E m w' → rm m w ≤ rm m w'
def IsStable {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (rw : W → M → ℕ)
    (μ : M → W → Prop) : Prop :=
  (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m)
end Galvin


