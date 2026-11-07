-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities
-- name    : AaronsonAmbainis_Bridge_PaperInequalities
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:09:26.969628+00:00
-- url     : https://prove2.me/theorems/1a1f2cfb-574f-4b4f-ad6f-c2fd7c6a31eb
-- title:
--   Paper Inequalities
-- statement:
--   Definitions and structural lemmas for Paper Inequalities, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PaperInequalities.lean

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def TwoSidedPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (g : Cube ι → Bool),
    (∃ x y, g x ≠ g y) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
    4 * ((∑ x : Cube ι, if g x = true then 1 / (∑ j, lam x j) else 0) / 2 ^ Fintype.card ι)
      * ((∑ x : Cube ι, if g x = false then 1 / (∑ j, lam x j) else 0) / 2 ^ Fintype.card ι)
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => infl g j)
def TwoSidedMinCost : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (g : Cube ι → Bool),
    (∃ x y, g x ≠ g y) →
  ∀ (F : Cube ι → ℝ),
    (∀ x, (∃ lam : ι → ℝ, IsRow g x lam ∧ ∑ j, lam j = F x) ∧
      ∀ lam : ι → ℝ, IsRow g x lam → F x ≤ ∑ j, lam j) →
    4 * ((∑ x : Cube ι, if g x = true then 1 / F x else 0) / 2 ^ Fintype.card ι)
      * ((∑ x : Cube ι, if g x = false then 1 / F x else 0) / 2 ^ Fintype.card ι)
      ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => infl g j)
def DetInequalityPrinted : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (ℓ : ι → ℝ), (∀ j, 0 < ℓ j) →
  ∀ (A : Cube ι → Finset ι), (∀ u ∈ zone g, IsWing g u (A u)) →
  ∀ (D : Cube ι → ℝ),
    (∀ u ∈ zone g,
      (∃ G : Finset ι, G ⊆ univ \ A u ∧ g (flipSet (antipode u) G) = true ∧
          D u = ∑ j ∈ G, ℓ j) ∧
      ∀ G : Finset ι, G ⊆ univ \ A u → g (flipSet (antipode u) G) = true →
          D u ≤ ∑ j ∈ G, ℓ j) →
    ∑ u ∈ zone g, D u ≤ ∑ j, ℓ j * (bdry g j : ℝ)
def PackingBoundNonempty : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
  ∀ (x : Cube ι) (κ : Finset ι → ℝ), (∀ S : Finset ι, S.Nonempty → 0 ≤ κ S) →
    (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
    ∑ S ∈ univ.filter (fun S : Finset ι => S.Nonempty), κ S * |f x - f (flipSet x S)|
      ≤ Real.pi ^ 2 * (d : ℝ) ^ 2
end AaronsonAmbainis.Bridge


