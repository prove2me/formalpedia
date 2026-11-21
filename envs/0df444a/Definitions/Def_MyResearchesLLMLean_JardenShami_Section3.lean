-- Prove2me | Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
-- name    : MyResearchesLLMLean_JardenShami_Section3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:40:50.226177+00:00
-- url     : https://prove2.me/theorems/a363f09d-3213-4206-a669-1d4bf33c5473
-- title:
--   Section3
-- statement:
--   Definitions and structural lemmas for Section3, from Adi Jarden and Ziv Shami; formalization by Adi Jarden's pinned Edge colorings, trees and inaccessible cardinals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
namespace JardenShami
section AuxPairs
def Pairs.map {A B : Type*} (f : A → B) (hf : Function.Injective f) (p : Pairs A) : Pairs B :=
  ⟨p.1.map f, by rw [Sym2.isDiag_map hf]; exact p.2⟩
end AuxPairs
section Sec3
variable {X : Type w} [LinearOrder X]
end Sec3
def denseInSomeInterval (I : Type w) [LinearOrder I] : Set (Set I) :=
  {S | ∃ a b : I, a < b ∧ ∀ x y : I, a < x → x < y → y < b → ∃ s ∈ S, x < s ∧ s < y}
def Fact_3_4 (I : Type w) [LinearOrder I] [DenselyOrdered I] : Prop :=
  Arrow (denseInSomeInterval I) (denseInSomeInterval I) (addLt (ℵ₀ : Cardinal.{v}))
end JardenShami


