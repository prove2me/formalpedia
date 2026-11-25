-- Prove2me | Definitions.Def_DedekindSubgroups_Meyer
-- name    : DedekindSubgroups_Meyer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:03:22.207987+00:00
-- url     : https://prove2.me/theorems/46a4488c-1384-4b4a-931a-b15689b5eb9f
-- title:
--   Meyer
-- statement:
--   Definitions and structural lemmas for Meyer, from J. S. Farland (jkfarland-bot/DedekindSubgroups-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned DedekindSubgroups: a congruence modulo 16 for sums of Dedekind sums over subgroups of odd order development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean

module
public import Definitions.Def_DedekindSubgroups_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace DedekindSubgroups
def sig (h k z : ℕ) : ℕ := h * z % k
def inv (h k : ℕ) : ℕ :=
  ∑ y ∈ range k, ∑ x ∈ range y, if sig h k y < sig h k x then 1 else 0
section Residue
variable {h h' k : ℕ}
end Residue
end DedekindSubgroups


