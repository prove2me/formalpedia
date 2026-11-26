-- Prove2me | Definitions.Def_EconomicsNextProof_Conservation
-- name    : EconomicsNextProof_Conservation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:24:09.891656+00:00
-- url     : https://prove2.me/theorems/5fad09ad-dd65-5161-9bbc-2bc16f728852
-- title:
--   Conservation
-- statement:
--   Definitions and structural lemmas for Conservation, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Conservation.lean

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_Path
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
noncomputable def blockMarschak (p : Finset X → X → ℝ) (x : X) (A : Finset X) : ℝ :=
  upperMobius (fun B => p B x) A
end Falmagne


