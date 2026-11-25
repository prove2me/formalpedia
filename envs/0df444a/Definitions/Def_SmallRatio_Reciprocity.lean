-- Prove2me | Definitions.Def_SmallRatio_Reciprocity
-- name    : SmallRatio_Reciprocity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:14:18.928239+00:00
-- url     : https://prove2.me/theorems/53d52261-c004-5f6d-b9c6-e9ddfebcca17
-- title:
--   Reciprocity
-- statement:
--   Definitions and structural lemmas for Reciprocity, from J. S. Farland (jkfarland-bot/SmallRatios; see pinned Apache-2.0 LICENSE and README.md)'s pinned SmallRatio: Dedekind sums along Euclid's algorithm and the small-ratio theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean

module
public import Definitions.Def_SmallRatio_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SmallRatio
open Finset
def Asum (h k : ℕ) : ℕ := ∑ r ∈ range k, r * (h * r % k)
end SmallRatio


