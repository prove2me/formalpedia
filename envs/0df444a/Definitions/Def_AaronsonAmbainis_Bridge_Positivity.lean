-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_Positivity
-- name    : AaronsonAmbainis_Bridge_Positivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:03:52.582796+00:00
-- url     : https://prove2.me/theorems/3320cdde-f9c2-46b3-9129-286ac668a786
-- title:
--   Positivity
-- statement:
--   Definitions and structural lemmas for Positivity, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def AntipodalOnZone : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (w : ι → ℝ), (∀ j, 0 < w j) →
  ∀ (lam : Cube ι → ι → ℝ),
    (∀ u ∈ zone g, IsRow g u (lam u) ∧ IsRow g (antipode u) (lam (antipode u))) →
    ∑ u ∈ zone g, 1 / (∑ j, w j * lam u j * lam (antipode u) j) ≤ ∑ j, (bdry g j : ℝ) / w j
noncomputable def extendRows (g : Cube ι → Bool) (lam : Cube ι → ι → ℝ) : Cube ι → ι → ℝ :=
  fun x => if x ∈ zone g ∨ antipode x ∈ zone g then lam x else fun _ => 1
def AllPairsNonconstant : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool), (∃ x y, g x ≠ g y) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) → ∀ (w : ι → ℝ), (∀ j, 0 < w j) →
    ∑ p ∈ (univ.filter fun x : Cube ι => g x = true) ×ˢ
          (univ.filter fun y : Cube ι => g y = false),
        1 / (∑ j ∈ diffSet p.1 p.2, w j * lam p.1 j * lam p.2 j)
      ≤ 2 ^ (Fintype.card ι - 1) * ∑ j, (bdry g j : ℝ) / w j
end AaronsonAmbainis.Bridge


