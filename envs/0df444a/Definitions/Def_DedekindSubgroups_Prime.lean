-- Prove2me | Definitions.Def_DedekindSubgroups_Prime
-- name    : DedekindSubgroups_Prime
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:08:04.006943+00:00
-- url     : https://prove2.me/theorems/e0a9b436-3a4d-5c68-b312-306b2111b220
-- title:
--   Prime
-- statement:
--   Definitions and structural lemmas for Prime, from J. S. Farland (jkfarland-bot/DedekindSubgroups-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned DedekindSubgroups: a congruence modulo 16 for sums of Dedekind sums over subgroups of odd order development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Prime.lean

module
public import Definitions.Def_DedekindSubgroups_Main
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace DedekindSubgroups
def E (h k : ℕ) : ℤ := ∑ r ∈ range k, (r : ℤ) * sig h k r
section Residue
variable {h h' k : ℕ}
end Residue
section SubgroupSums
variable {p : ℕ} [Fact p.Prime]
end SubgroupSums
end DedekindSubgroups


