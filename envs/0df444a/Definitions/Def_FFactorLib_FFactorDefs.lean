-- Prove2me | Definitions.Def_FFactorLib_FFactorDefs
-- name    : FFactorLib_FFactorDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:50:48.066827+00:00
-- url     : https://prove2.me/theorems/d146e869-2109-425a-acac-49eec2fbf5b3
-- title:
--   FFactor Defs
-- statement:
--   Definitions and structural lemmas for FFactor Defs, from Juan Pablo Traverso Gianini (jtraverso/tutte-f-factor; see pinned Apache-2.0 LICENSE and source headers)'s pinned Tutte f-factor theorem for finite simple graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorDefs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical in
/-- Auxiliary copy of `q(S, T)`. -/
noncomputable def oddCnt (G : SimpleGraph V) (f : V → ℕ) (S T : Finset V) : ℕ :=
  Nat.card {c : (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).ConnectedComponent //
    Odd (∑ w ∈ univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
        (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ T | G.Adj w t}))}
end FFactor


