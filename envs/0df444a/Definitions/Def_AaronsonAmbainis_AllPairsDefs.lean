-- Prove2me | Definitions.Def_AaronsonAmbainis_AllPairsDefs
-- name    : AaronsonAmbainis_AllPairsDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:19:02.236282+00:00
-- url     : https://prove2.me/theorems/d67c02f1-c57b-47f6-aa28-e77aafe179cb
-- title:
--   All Pairs Defs
-- statement:
--   Definitions and structural lemmas for All Pairs Defs, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/AllPairsDefs.lean

import Definitions.Def_AaronsonAmbainis_Statements
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
def AllPairsInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (w : ι → ℝ), (∀ j, 0 < w j) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
    2 * ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
          ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
            (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (bdry g j : ℝ) / w j
end AaronsonAmbainis


