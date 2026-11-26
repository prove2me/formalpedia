-- Prove2me | Definitions.Def_EconomicsNextProof_ChoiceMobius
-- name    : EconomicsNextProof_ChoiceMobius
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:13:34.832519+00:00
-- url     : https://prove2.me/theorems/6da5709d-2a39-5f41-b641-c542d632b3a3
-- title:
--   Choice Mobius
-- statement:
--   Definitions and structural lemmas for Choice Mobius, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/ChoiceMobius.lean

module
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Mobius
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
end Falmagne


