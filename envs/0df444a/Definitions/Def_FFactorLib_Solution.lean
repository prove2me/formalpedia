-- Prove2me | Definitions.Def_FFactorLib_Solution
-- name    : FFactorLib_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T06:03:04.648844+00:00
-- url     : https://prove2.me/theorems/e6fa2b5b-74a2-412d-a624-6f5e15ba604f
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/tutte-f-factor; see pinned Apache-2.0 LICENSE and source headers)'s pinned Tutte f-factor theorem for finite simple graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/Solution.lean

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactor
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace TutteFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical in
/-- `q(S, T)`: the number of connected components `C` of `G − (S ∪ T)` such that
`∑_{v ∈ C} f v + e(C, T)` is odd, where `e(C, T)` counts the edges between `C` and `T`. -/
noncomputable def oddCount (G : SimpleGraph V) (f : V → ℕ) (S T : Finset V) : ℕ :=
  Nat.card {c : (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).ConnectedComponent //
    Odd (∑ w ∈ univ.filter (fun w : ↥(((S ∪ T : Finset V) : Set V)ᶜ) =>
        (G.induce ((S ∪ T : Finset V) : Set V)ᶜ).connectedComponentMk w = c),
      (f w + #{t ∈ T | G.Adj w t}))}
end TutteFactor


