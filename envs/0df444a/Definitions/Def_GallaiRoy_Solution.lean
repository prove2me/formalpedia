-- Prove2me | Definitions.Def_GallaiRoy_Solution
-- name    : GallaiRoy_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:15:25.273237+00:00
-- url     : https://prove2.me/theorems/a6d746f2-1769-4309-8318-0c059dee31d2
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/gallai-roy; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Gallai-Hasse-Roy-Vitaver theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/Solution.lean

module
public import Mathlib
public import Definitions.Def_GallaiRoyLib_GallaiRoy
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace GallaiRoyTheorem
variable {V : Type*}
def IsOrientation (G : SimpleGraph V) (o : V → V → Prop) : Prop :=
  (∀ u v, G.Adj u v → o u v ∨ o v u) ∧ ∀ u v, o u v → G.Adj u v
def IsDirectedPath (o : V → V → Prop) {m : ℕ} (f : Fin m → V) : Prop :=
  Function.Injective f ∧ ∀ (i : ℕ) (h : i + 1 < m), o (f ⟨i, Nat.lt_of_succ_lt h⟩) (f ⟨i + 1, h⟩)
end GallaiRoyTheorem


