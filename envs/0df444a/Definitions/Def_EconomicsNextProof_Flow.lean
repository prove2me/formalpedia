-- Prove2me | Definitions.Def_EconomicsNextProof_Flow
-- name    : EconomicsNextProof_Flow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:24:06.614698+00:00
-- url     : https://prove2.me/theorems/73552083-b911-5051-a1be-8f5a7e99609f
-- title:
--   Flow
-- statement:
--   Definitions and structural lemmas for Flow, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Flow.lean

module
public import Definitions.Def_EconomicsNextProof_Path
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}
noncomputable def edgeSupport (q : X → Finset X → ℝ) : Finset (X × Finset X) :=
  Finset.univ.filter fun e => e.1 ∈ e.2 ∧ 0 < q e.1 e.2
end Falmagne


