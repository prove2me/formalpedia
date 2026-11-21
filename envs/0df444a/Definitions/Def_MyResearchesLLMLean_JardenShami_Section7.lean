-- Prove2me | Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
-- name    : MyResearchesLLMLean_JardenShami_Section7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:42:50.182585+00:00
-- url     : https://prove2.me/theorems/ae347cd9-1e0e-4ac3-9e13-4fec31746669
-- title:
--   Section7
-- statement:
--   Definitions and structural lemmas for Section7, from Adi Jarden and Ziv Shami; formalization by Adi Jarden's pinned Edge colorings, trees and inaccessible cardinals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
namespace JardenShami
open Tree
def Sim {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D) (β γ : A) : Prop :=
  ∃ (α : A) (hβ : β < α) (hγ : γ < α), C.color β α hβ = C.color γ α hγ
def StarLaArrowKappa (κ μ : Cardinal.{w}) : Prop :=
  ∀ C : Coloring (Kappa κ) (Kappa μ), IsStarLocallyAdditive C →
    ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H
section TreeAux
variable {T : Type w} [PartialOrder T] [IsTree T]
end TreeAux
end JardenShami


