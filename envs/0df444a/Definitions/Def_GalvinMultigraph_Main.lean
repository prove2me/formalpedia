-- Prove2me | Definitions.Def_GalvinMultigraph_Main
-- name    : GalvinMultigraph_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:13:04.989821+00:00
-- url     : https://prove2.me/theorems/f5f0248a-c9be-4774-9497-eaedd2de8aff
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Main.lean

module
public import Definitions.Def_GalvinMultigraph_Gadget
public import Definitions.Def_GalvinLib_Galvin
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GalvinMultigraph
open Finset
variable {A B E Color : Type*}
def Proper (a : E → A) (b : E → B) (c : E → Color) : Prop :=
  ∀ e f, e ≠ f → a e = a f ∨ b e = b f → c e ≠ c f
noncomputable def maxDegree [Fintype A] [Fintype B] (a : E → A) (b : E → B) : ℕ :=
  max (univ.sup fun x => Nat.card {e // a e = x})
      (univ.sup fun y => Nat.card {e // b e = y})
end GalvinMultigraph


