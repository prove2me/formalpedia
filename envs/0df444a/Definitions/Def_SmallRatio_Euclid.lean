-- Prove2me | Definitions.Def_SmallRatio_Euclid
-- name    : SmallRatio_Euclid
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:16:46.560892+00:00
-- url     : https://prove2.me/theorems/cee4de4d-d894-54b7-8217-9a017f165859
-- title:
--   Euclid
-- statement:
--   Definitions and structural lemmas for Euclid, from J. S. Farland (jkfarland-bot/SmallRatios; see pinned Apache-2.0 LICENSE and README.md)'s pinned SmallRatio: Dedekind sums along Euclid's algorithm and the small-ratio theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean

module
public import Definitions.Def_SmallRatio_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
end SmallRatio


