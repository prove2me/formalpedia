-- Prove2me | Definitions.Def_PerfectLib_Perfect
-- name    : PerfectLib_Perfect
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T10:27:24.597799+00:00
-- url     : https://prove2.me/theorems/998f2f1b-6057-446c-a39a-1ca82bb82d0a
-- title:
--   Perfect
-- statement:
--   Definitions and structural lemmas for Perfect, from Juan Pablo Traverso Gianini (jtraverso/perfect-graphs; see pinned Apache-2.0 LICENSE and source headers)'s pinned Lovasz's perfect graph theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Perfect.lean

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace PerfectGraph
variable {V : Type*}
def IsPerfect (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, (G.induce S).chromaticNumber = (G.induce S).cliqueNum
end PerfectGraph


