-- Prove2me | Definitions.Def_AaronsonAmbainis_TwoSided_AllPairs
-- name    : AaronsonAmbainis_TwoSided_AllPairs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:29:36.074697+00:00
-- url     : https://prove2.me/theorems/7b93e0ba-f0a6-44d3-a1a3-83be0ca7b27c
-- title:
--   All Pairs
-- statement:
--   Definitions and structural lemmas for All Pairs, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairs.lean

import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Theorems.Thm_AaronsonAmbainis_diffSet_flipSet
import Theorems.Thm_AaronsonAmbainis_flipSet_diffSet

set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def flipEquiv (x : Cube ι) : Finset ι ≃ Cube ι where
  toFun F := flipSet x F
  invFun y := diffSet x y
  left_inv F := diffSet_flipSet x F
  right_inv y := flipSet_diffSet x y
end AaronsonAmbainis


