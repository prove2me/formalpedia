-- Prove2me | Definitions.Def_MurtySimon_Basic
-- name    : MurtySimon_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:50:08.584006+00:00
-- url     : https://prove2.me/theorems/2c24585c-5fe9-5bb7-8557-d8bc1c8590e7
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/murty-simon-conjecture; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Murty-Simon conjecture on diameter-2-critical graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean

module
public import Definitions.Def_MurtySimon_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
def IsMid (x y u : V) : Prop :=
  x ≠ y ∧ ¬ G.Adj x y ∧ G.Adj x u ∧ G.Adj u y ∧ ∀ w, G.Adj x w → G.Adj w y → w = u
def IsCrit (f : Sym2 V) : Prop := ∃ x y u, f = s(x, y) ∧ IsMid G x y u
def OnPath (e f : Sym2 V) : Prop := ∃ x y u, f = s(x, y) ∧ IsMid G x y u ∧ e = s(x, u)
def aux (M : Finset (Sym2 V)) : SimpleGraph (Sym2 V) :=
  SimpleGraph.fromRel fun e f => e ∉ M ∧ OnPath G e f
variable {G}
end MurtySimon


