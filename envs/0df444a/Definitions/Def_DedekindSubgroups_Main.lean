-- Prove2me | Definitions.Def_DedekindSubgroups_Main
-- name    : DedekindSubgroups_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:05:52.667974+00:00
-- url     : https://prove2.me/theorems/e4558f5a-a59a-4bbc-83eb-bb04b133b15d
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from J. S. Farland (jkfarland-bot/DedekindSubgroups-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned DedekindSubgroups: a congruence modulo 16 for sums of Dedekind sums over subgroups of odd order development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Main.lean

module
public import Definitions.Def_DedekindSubgroups_Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace DedekindSubgroups
variable {k : ℕ} [NeZero k]
noncomputable def subgroupSum (H : Subgroup (ZMod k)ˣ) : ℚ := by
  classical exact ∑ u ∈ univ.filter (· ∈ H), dedekindSum (u : ZMod k).val k
section OddOrder
variable {G : Type*} [Group G]
end OddOrder
end DedekindSubgroups


