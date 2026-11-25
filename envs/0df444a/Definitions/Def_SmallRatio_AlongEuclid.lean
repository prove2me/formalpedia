-- Prove2me | Definitions.Def_SmallRatio_AlongEuclid
-- name    : SmallRatio_AlongEuclid
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:18:46.920422+00:00
-- url     : https://prove2.me/theorems/453bd7d1-c1cb-4f1d-8416-af314253a15f
-- title:
--   Along Euclid
-- statement:
--   Definitions and structural lemmas for Along Euclid, from J. S. Farland (jkfarland-bot/SmallRatios; see pinned Apache-2.0 LICENSE and README.md)'s pinned SmallRatio: Dedekind sums along Euclid's algorithm and the small-ratio theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/AlongEuclid.lean

module
public import Definitions.Def_SmallRatio_Reciprocity
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SmallRatio
open Finset
noncomputable def recipTerm (k h : ℕ) (j : ℕ) : ℚ :=
  (rem k h (j - 1) : ℚ) / rem k h j + (rem k h j : ℚ) / rem k h (j - 1)
    + 1 / ((rem k h j : ℚ) * rem k h (j - 1)) - 3
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
end SmallRatio


