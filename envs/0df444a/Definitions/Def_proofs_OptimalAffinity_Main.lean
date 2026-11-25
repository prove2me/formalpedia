-- Prove2me | Definitions.Def_proofs_OptimalAffinity_Main
-- name    : proofs_OptimalAffinity_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T20:57:51.235364+00:00
-- url     : https://prove2.me/theorems/edab0419-1b86-4864-b4e4-7c4dd314693b
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from mmislan (mmislan/palomar-p004-optimal-affinity-counterexample; see pinned Apache-2.0 LICENSE and README.md)'s pinned A two-reaction counterexample to the gross-amplification affinity bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Main.lean

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OptimalAffinity
def TwoByTwoSeedLowerBound : Prop :=
  ∀ (N : Network) (x y : ℝ),
    SourceValid N → IsUniqueGlobalMaximum N x y →
    seedRatio N ≤ affinityExp N x y
end OptimalAffinity


