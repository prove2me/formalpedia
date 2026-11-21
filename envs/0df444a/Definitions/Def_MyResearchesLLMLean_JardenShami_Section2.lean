-- Prove2me | Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
-- name    : MyResearchesLLMLean_JardenShami_Section2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:40:25.63123+00:00
-- url     : https://prove2.me/theorems/01dcf800-97d7-4831-b23c-69847c8beac7
-- title:
--   Section2
-- statement:
--   Definitions and structural lemmas for Section2, from Adi Jarden and Ziv Shami; formalization by Adi Jarden's pinned Edge colorings, trees and inaccessible cardinals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section2.lean

import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Regular
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
namespace JardenShami
def Pairs (A : Type w) : Type w := {z : Sym2 A // ¬ z.IsDiag}
def Pairs.mk {A : Type w} (a b : A) (h : a ≠ b) : Pairs A :=
  ⟨s(a, b), by simpa [Sym2.mk_isDiag_iff] using h⟩
abbrev Coloring (A : Type w) (D : Type v) : Type (max w v) := Pairs A → D
def Coloring.color {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) (a b : A)
    (h : a < b) : D :=
  C (Pairs.mk a b h.ne)
def IsHomogeneous {A : Type w} {D : Type v} (C : Coloring A D) (B : Set A) : Prop :=
  ∀ p q : Pairs A, (∀ x ∈ p.1, x ∈ B) → (∀ x ∈ q.1, x ∈ B) → C p = C q
section LinearOrder
variable {A : Type w} [LinearOrder A] {D : Type v}
def IsAdditive (C : Coloring A D) : Prop :=
  ∃ s : D × D → D, ∀ (a b c : A) (hab : a < b) (hbc : b < c),
    C.color a c (hab.trans hbc) = s (C.color a b hab, C.color b c hbc)
def IsLocallyAdditive (C : Coloring A D) : Prop :=
  ∀ (a b c d : A) (hab : a < b) (hbc : b < c) (hcd : c < d),
    C.color b c hbc = C.color b d (hbc.trans hcd) →
      C.color a c (hab.trans hbc) = C.color a d ((hab.trans hbc).trans hcd)
def IsStarLocallyAdditive (C : Coloring A D) : Prop :=
  IsLocallyAdditive (A := Aᵒᵈ) C
def Dset (C : Coloring A D) (b : A) : Set D :=
  {t | ∃ (c : A) (h : b < c), C.color b c h = t}
def uMap (C : Coloring A D) (a b : A) (hab : a < b) : Dset C b → D :=
  fun t => C.color a (Classical.choose t.2) (hab.trans (Classical.choose_spec t.2).fst)
end LinearOrder
abbrev Kappa (κ : Cardinal.{w}) : Type w := κ.ord.ToType
def ColoringClass (X : Type w) [LinearOrder X] : Type (max w (v + 1)) :=
  ∀ (S : Set X) (D : Type v), Coloring S D → Prop
section Classes
variable {X : Type w} [LinearOrder X]
def allColorings (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D _ => #D = μ
def add : ColoringClass.{v, w} X := fun _ _ C => IsAdditive C
def addEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsAdditive C ∧ #D = μ
def addLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsAdditive C ∧ #D < μ
def la : ColoringClass.{v, w} X := fun _ _ C => IsLocallyAdditive C
def laEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsLocallyAdditive C ∧ #D = μ
def laLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X := fun _ D C => IsLocallyAdditive C ∧ #D < μ
def IsRegularCardinalOrder (S : Set X) : Prop :=
  ∃ κ : Cardinal.{w}, κ.IsRegular ∧ Nonempty (S ≃o Kappa κ)
def starLa : ColoringClass.{v, w} X :=
  fun S _ C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C
def starLaEq (μ : Cardinal.{v}) : ColoringClass.{v, w} X :=
  fun S D C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C ∧ #D = μ
def starLaLt (μ : Cardinal.{v}) : ColoringClass.{v, w} X :=
  fun S D C => IsRegularCardinalOrder S ∧ IsStarLocallyAdditive C ∧ #D < μ
def Arrow (F₁ F₂ : Set (Set X)) (𝔆 : ColoringClass.{v, w} X) : Prop :=
  ∀ S ∈ F₁, ∀ (D : Type v) (C : Coloring S D), 𝔆 S D C →
    ∃ E : Set S, Subtype.val '' E ∈ F₂ ∧ IsHomogeneous C E
end Classes
def bigSubsets (κ : Cardinal.{w}) : Set (Set (Kappa κ)) := {S | #S = κ}
end JardenShami


