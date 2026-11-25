-- Prove2me | Definitions.Def_Euler_Orientation
-- name    : Euler_Orientation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:33:43.387671+00:00
-- url     : https://prove2.me/theorems/028cceb6-1865-409f-8833-df7391313cb4
-- title:
--   Orientation
-- statement:
--   Definitions and structural lemmas for Orientation, from Juan Pablo Traverso Gianini (jtraverso/euler-petersen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Euler's theorem on Eulerian circuits and trails, and Petersen's 2-factor theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean

module
public import Definitions.Def_Euler_Trail
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
def EdgeInj (Ds : Finset G.Dart) : Prop :=
  ∀ d ∈ Ds, ∀ d' ∈ Ds, d.edge = d'.edge → d = d'
def Balanced (Ds : Finset G.Dart) : Prop :=
  ∀ v, (Ds.filter fun d => d.fst = v).card = (Ds.filter fun d => d.snd = v).card
end SimpleGraph


