-- Prove2me | Definitions.Def_FractionalLib_Basic
-- name    : FractionalLib_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:28:52.669363+00:00
-- url     : https://prove2.me/theorems/c0409b8a-fe96-4808-a889-d98f4a55d6d5
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/erdos-girth-chromatic; see pinned Apache-2.0 LICENSE and source headers)'s pinned Graphs of large girth and large chromatic number: Erdos, Mycielski and Tutte development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/Basic.lean

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
def IsFracColouring (x : Finset V → ℝ) : Prop :=
  (∀ s, 0 ≤ x s) ∧ (∀ s : Finset V, ¬ G.IsIndepSet (s : Set V) → x s = 0) ∧
    ∀ v, 1 ≤ ∑ s ∈ univ.filter (fun s => v ∈ s), x s
noncomputable def fracChromaticNumber : ℝ :=
  sInf {t | ∃ x, IsFracColouring G x ∧ t = ∑ s, x s}
def IsFracClique (g : V → ℝ) : Prop :=
  (∀ v, 0 ≤ g v) ∧ ∀ s : Finset V, G.IsIndepSet (s : Set V) → ∑ v ∈ s, g v ≤ 1
variable {G}
noncomputable def singletonColouring : Finset V → ℝ := fun s => if s.card = 1 then 1 else 0
end FractionalColouring


