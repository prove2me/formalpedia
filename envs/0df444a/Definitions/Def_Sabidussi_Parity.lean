-- Prove2me | Definitions.Def_Sabidussi_Parity
-- name    : Sabidussi_Parity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:07:29.55051+00:00
-- url     : https://prove2.me/theorems/dc257cae-3f0b-523d-b3df-34058be596c9
-- title:
--   Parity
-- statement:
--   Definitions and structural lemmas for Parity, from Upstream contributors (gexahedron/sabidussi-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Sabidussi compatibility conjecture for finite Eulerian loop multigraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Parity.lean

import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
namespace Sabidussi
open scoped BigOperators
def orderedPairBracket {n : ℕ} (f : Fin n → Color) : F₂ :=
  ∑ i, ∑ j, if j < i then bracket (f i) (f j) else 0
def colorFiber {I : Type*} [Fintype I] [DecidableEq I] (f : I → Color) (c : Color) :
    Finset I :=
  Finset.univ.filter fun i ↦ f i = c
def colorFstHom : Color →+ F₂ where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl
def colorSndHom : Color →+ F₂ where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl
end Sabidussi


