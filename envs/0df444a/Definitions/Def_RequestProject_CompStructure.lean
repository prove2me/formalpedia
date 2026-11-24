-- Prove2me | Definitions.Def_RequestProject_CompStructure
-- name    : RequestProject_CompStructure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:15:29.986318+00:00
-- url     : https://prove2.me/theorems/bae4c3e5-5dfa-427a-8339-713621d1715b
-- title:
--   Comp Structure
-- statement:
--   Definitions and structural lemmas for Comp Structure, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean

import Definitions.Def_RequestProject_PhiFormula
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
section General
variable {V : Type*} [Fintype V]
def compOf (A : Set (Sym2 V)) (v : V) : Finset V :=
  univ.filter fun w => (SimpleGraph.fromEdgeSet A).Reachable v w
end General
section Coeff
end Coeff
end ChromaticReconstruction


