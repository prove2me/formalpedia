-- Prove2me | Definitions.Def_GallaiRoyLib_GallaiRoy
-- name    : GallaiRoyLib_GallaiRoy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:12:51.019231+00:00
-- url     : https://prove2.me/theorems/56b50794-f9eb-43bd-974e-362283627df1
-- title:
--   Gallai Roy
-- statement:
--   Definitions and structural lemmas for Gallai Roy, from Juan Pablo Traverso Gianini (jtraverso/gallai-roy; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Gallai-Hasse-Roy-Vitaver theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gallai-roy/blob/e737218bf80c3d3684d670f5f8aa9a8257e1a52f/GallaiRoyLib/GallaiRoy.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace GallaiRoy
variable {V : Type*}
def IsOrientation (G : SimpleGraph V) (o : V → V → Prop) : Prop :=
  (∀ u v, G.Adj u v → o u v ∨ o v u) ∧ ∀ u v, o u v → G.Adj u v
def IsDirectedPath (o : V → V → Prop) {m : ℕ} (f : Fin m → V) : Prop :=
  Function.Injective f ∧ ∀ (i : ℕ) (h : i + 1 < m), o (f ⟨i, by omega⟩) (f ⟨i + 1, h⟩)
end GallaiRoy


