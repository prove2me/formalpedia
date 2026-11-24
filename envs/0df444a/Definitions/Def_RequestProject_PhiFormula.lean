-- Prove2me | Definitions.Def_RequestProject_PhiFormula
-- name    : RequestProject_PhiFormula
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:07:22.23516+00:00
-- url     : https://prove2.me/theorems/f6d3adc2-84b5-4712-b7d5-21981d1777a8
-- title:
--   Phi Formula
-- statement:
--   Definitions and structural lemmas for Phi Formula, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PhiFormula.lean

import Definitions.Def_RequestProject_Components
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
variable {V : Type*} [Fintype V]
def phiTerm (A : Finset (Sym2 V)) (v : V) : MvPolynomial ℕ ℚ :=
  if {v} ∈ compSets (A : Set (Sym2 V)) then
    (-1) ^ A.card * killP1 (∏ D ∈ (compSets (A : Set (Sym2 V))).erase {v}, X D.card)
  else 0
end ChromaticReconstruction
namespace ChromaticReconstruction
variable {V : Type*} [Fintype V]
end ChromaticReconstruction


