-- Prove2me | Definitions.Def_SmallRatio_Main
-- name    : SmallRatio_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:20:15.340872+00:00
-- url     : https://prove2.me/theorems/001b41fc-a114-4a82-a7c4-f3030ba69b2f
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from J. S. Farland (jkfarland-bot/SmallRatios; see pinned Apache-2.0 LICENSE and README.md)'s pinned SmallRatio: Dedekind sums along Euclid's algorithm and the small-ratio theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Main.lean

module
public import Definitions.Def_SmallRatio_AlongEuclid
public import Definitions.Def_SmallRatio_Legendre
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SmallRatio
open Finset
variable {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
include hp hh hhp
end SmallRatio


