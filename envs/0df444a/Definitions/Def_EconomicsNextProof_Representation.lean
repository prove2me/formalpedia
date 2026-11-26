-- Prove2me | Definitions.Def_EconomicsNextProof_Representation
-- name    : EconomicsNextProof_Representation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:13:05.357503+00:00
-- url     : https://prove2.me/theorems/895521a7-d45e-4628-acf9-6097bf30c480
-- title:
--   Representation
-- statement:
--   Definitions and structural lemmas for Representation, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Representation.lean

module
public import Definitions.Def_EconomicsNextProof_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
noncomputable def rankingEdge (l : List X) (x : X) (A : Finset X) : ℝ :=
  if x ∈ A ∧ A = lowerContour l x then 1 else 0
noncomputable def lawFlow (w : RankingLaw X) (x : X) (A : Finset X) : ℝ :=
  w.sum (fun l a => a * rankingEdge l x A)
end Falmagne


