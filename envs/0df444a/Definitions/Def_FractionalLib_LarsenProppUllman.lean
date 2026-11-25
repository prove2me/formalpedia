-- Prove2me | Definitions.Def_FractionalLib_LarsenProppUllman
-- name    : FractionalLib_LarsenProppUllman
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:32:10.328917+00:00
-- url     : https://prove2.me/theorems/8d41d416-a05b-5434-9b5e-dfc64329e6a0
-- title:
--   Larsen Propp Ullman
-- statement:
--   Definitions and structural lemmas for Larsen Propp Ullman, from Juan Pablo Traverso Gianini (jtraverso/erdos-girth-chromatic; see pinned Apache-2.0 LICENSE and source headers)'s pinned Graphs of large girth and large chromatic number: Erdos, Mycielski and Tutte development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/LarsenProppUllman.lean

module
public import Definitions.Def_FractionalLib_Basic
public import Definitions.Def_Mycielski_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset hiding shadow
open Mycielski
namespace FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
def lift (s : Finset V) : Finset (Vertex V) := s.image original ∪ s.image shadow
def liftApex (s : Finset V) : Finset (Vertex V) := insert none (s.image original)
def shadows : Finset (Vertex V) := univ.image shadow
variable {G}
noncomputable def mycielskiColouring (x : Finset V → ℝ) (t : ℝ) : Finset (Vertex V) → ℝ :=
  fun S => ∑ s, ((if S = lift s then x s * ((t - 1) / t) else 0) +
    (if S = liftApex s then x s / t else 0)) + (if S = shadows then 1 / t else 0)
noncomputable def mycielskiClique (g : V → ℝ) (a : ℝ) : Vertex V → ℝ
  | none => 1 / a
  | some (v, b) => if b then g v / a else (1 - 1 / a) * g v
end FractionalColouring


