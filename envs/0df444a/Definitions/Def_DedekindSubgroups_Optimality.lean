-- Prove2me | Definitions.Def_DedekindSubgroups_Optimality
-- name    : DedekindSubgroups_Optimality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:10:08.691552+00:00
-- url     : https://prove2.me/theorems/6943e320-6a86-5ea4-a681-5370cfb47130
-- title:
--   Optimality
-- statement:
--   Definitions and structural lemmas for Optimality, from J. S. Farland (jkfarland-bot/DedekindSubgroups-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned DedekindSubgroups: a congruence modulo 16 for sums of Dedekind sums over subgroups of odd order development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Optimality.lean

module
public import Definitions.Def_DedekindSubgroups_Prime
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace DedekindSubgroups
def u4 : (ZMod 63)ˣ := ⟨4, 16, by decide, by decide⟩
def u22 : (ZMod 63)ˣ := ⟨22, 43, by decide, by decide⟩
instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
end DedekindSubgroups


