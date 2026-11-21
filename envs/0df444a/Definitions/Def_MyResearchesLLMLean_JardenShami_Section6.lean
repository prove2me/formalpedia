-- Prove2me | Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
-- name    : MyResearchesLLMLean_JardenShami_Section6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:41:52.608617+00:00
-- url     : https://prove2.me/theorems/6f83272c-eff9-4ffa-9ad2-e0d1cfe7da34
-- title:
--   Section6
-- statement:
--   Definitions and structural lemmas for Section6, from Adi Jarden and Ziv Shami; formalization by Adi Jarden's pinned Edge colorings, trees and inaccessible cardinals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
namespace JardenShami
open Tree
theorem isTree_subtype {T : Type w} [PartialOrder T] [IsTree T] (S : Set T) : IsTree S := by
  exact isTree_of_strictMono (fun x : S => ht (x : T))
    (fun x y h => ht_lt_ht (show (x : T) < y from h))
    (fun _ x y hx hy => le_total_of_lt (T := T) hx hy)
instance {T : Type w} [PartialOrder T] [IsTree T] (S : Set T) : IsTree S := isTree_subtype S
def Lim (T : Type w) [PartialOrder T] [IsTree T] : Set (Set T) := {b | IsCofinalBranch b}
def treeExp (lam μ : Cardinal.{w}) : Cardinal.{w} :=
  sSup {c | ∃ (T : Type w) (_ : PartialOrder T) (_ : IsTree T),
    height T = μ.ord ∧ #T ≤ lam ∧ c = #(Lim T)}
def IsWeaklyCompact (κ : Cardinal.{w}) : Prop := κ.IsInaccessible ∧ NoAronszajn κ
def Fact_6_3 : Prop :=
  ∀ κ : Cardinal.{w}, ℵ₀ < κ →
    (Arrow (bigSubsets κ) (bigSubsets κ) (allColorings.{w, w} (2 : Cardinal.{w})) ↔
      IsWeaklyCompact κ)
def binRestr {ν : Cardinal.{w}} (f : Kappa ν → Fin 2) (β : Kappa ν) : Set (Kappa ν × Fin 2) :=
  {p | p.1 < β ∧ p.2 = f p.1}
def binTree (ν : Cardinal.{w}) : Set (Set (Kappa ν × Fin 2)) :=
  {g | ∃ (f : Kappa ν → Fin 2) (β : Kappa ν), g = binRestr f β}
section BinTree
variable {ν : Cardinal.{w}}
theorem binRestr_subset_iff {f f' : Kappa ν → Fin 2} {β β' : Kappa ν} :
    binRestr f β ⊆ binRestr f' β' ↔ β ≤ β' ∧ ∀ α < β, f α = f' α := by
  constructor
  · intro h
    have hle : β ≤ β' := by
      by_contra hc
      exact lt_irrefl _ (h (show (β', f β') ∈ binRestr f β from ⟨lt_of_not_ge hc, rfl⟩)).1
    exact ⟨hle, fun α hα => (h (show (α, f α) ∈ binRestr f β from ⟨hα, rfl⟩)).2⟩
  · rintro ⟨hle, hc⟩ ⟨α, d⟩ ⟨hα, hd⟩
    exact ⟨hα.trans_le hle, hd.trans (hc α hα)⟩
theorem binRestr_eq_iff {f f' : Kappa ν → Fin 2} {β β' : Kappa ν} :
    binRestr f β = binRestr f' β' ↔ β = β' ∧ ∀ α < β, f α = f' α := by
  rw [Set.Subset.antisymm_iff, binRestr_subset_iff, binRestr_subset_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, -⟩
    exact ⟨le_antisymm h1 h3, h2⟩
  · rintro ⟨rfl, h⟩
    exact ⟨⟨le_rfl, h⟩, le_rfl, fun α hα => (h α hα).symm⟩
theorem binTree_isTree : IsTree (binTree ν) := by
  classical
  let β : binTree ν → Kappa ν := fun g => Classical.choose (Classical.choose_spec g.2)
  have hβ : ∀ g : binTree ν, g.1 = binRestr g.2.choose (β g) :=
    fun g => Classical.choose_spec (Classical.choose_spec g.2)
  refine isTree_of_strictMono β ?_ ?_
  · intro g g' hlt
    have hss : g.1 ⊂ g'.1 := hlt
    rw [hβ g, hβ g'] at hss
    have hs := binRestr_subset_iff.1 hss.1
    refine lt_of_le_of_ne hs.1 fun heq => hss.2 ?_
    exact (binRestr_eq_iff.2 ⟨heq, hs.2⟩).symm.le
  · intro g x y hx hy
    have sx : x.1 ⊆ g.1 := (show x.1 ⊂ g.1 from hx).1
    have sy : y.1 ⊆ g.1 := (show y.1 ⊂ g.1 from hy).1
    rw [hβ g, hβ x] at sx
    rw [hβ g, hβ y] at sy
    have ax := binRestr_subset_iff.1 sx
    have ay := binRestr_subset_iff.1 sy
    rcases le_total (β x) (β y) with hle | hle
    · left
      change x.1 ⊆ y.1
      rw [hβ x, hβ y]
      exact binRestr_subset_iff.2
        ⟨hle, fun α hα => (ax.2 α hα).trans (ay.2 α (hα.trans_le hle)).symm⟩
    · right
      change y.1 ⊆ x.1
      rw [hβ x, hβ y]
      exact binRestr_subset_iff.2
        ⟨hle, fun α hα => (ay.2 α hα).trans (ax.2 α (hα.trans_le hle)).symm⟩
instance : IsTree (binTree ν) := binTree_isTree
end BinTree
end JardenShami


