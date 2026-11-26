-- Prove2me | Definitions.Def_EconomicsNextProof_PathChoice
-- name    : EconomicsNextProof_PathChoice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:24:48.776932+00:00
-- url     : https://prove2.me/theorems/f297ee53-82fb-50c6-83e0-a934669916b8
-- title:
--   Path Choice
-- statement:
--   Definitions and structural lemmas for Path Choice, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/PathChoice.lean

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Representation
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {x y : X} {A : Finset X}
end Falmagne


