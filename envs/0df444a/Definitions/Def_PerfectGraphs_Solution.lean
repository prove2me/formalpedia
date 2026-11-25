-- Prove2me | Definitions.Def_PerfectGraphs_Solution
-- name    : PerfectGraphs_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:30:35.882795+00:00
-- url     : https://prove2.me/theorems/0b14cdf7-58a4-4952-b320-43c82a1fb090
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/perfect-graphs; see pinned Apache-2.0 LICENSE and source headers)'s pinned Lovasz's perfect graph theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/Solution.lean

module
public import Mathlib
public import Definitions.Def_PerfectLib_Perfect
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace PerfectGraphTheorem
variable {V : Type*}
def IsPerfect (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (G.induce S).chromaticNumber = (G.induce S).cliqueNum
end PerfectGraphTheorem


