-- Prove2me | Definitions.Def_EconomicsNextProof_Falmagne
-- name    : EconomicsNextProof_Falmagne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:25:35.098488+00:00
-- url     : https://prove2.me/theorems/44e9c383-8eb0-47b6-9278-72e967f88afc
-- title:
--   Falmagne
-- statement:
--   Definitions and structural lemmas for Falmagne, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz (Arthur742Ramos/falmagne-block-marschak-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Falmagne-Block-Marschak random-utility characterization of stochastic choice rules development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Falmagne.lean

module
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_PathChoice
public import Definitions.Def_EconomicsNextProof_Flow
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
def BlockMarschakNonnegative (p : Finset X → X → ℝ) : Prop :=
  ∀ x A, x ∈ A → 0 ≤ blockMarschak p x A
def RandomUtilityRepresentable (p : Finset X → X → ℝ) : Prop :=
  ∃ w : RankingLaw X, IsRankingLaw w ∧ Represents w p
end Falmagne


