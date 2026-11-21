-- Prove2me | Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
-- name    : MyResearchesLLMLean_JardenShami_Section5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:41:31.833817+00:00
-- url     : https://prove2.me/theorems/89a4112a-e820-4ec0-9b78-33c2fa0b67c5
-- title:
--   Section5
-- statement:
--   Definitions and structural lemmas for Section5, from Adi Jarden and Ziv Shami; formalization by Adi Jarden's pinned Edge colorings, trees and inaccessible cardinals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
namespace JardenShami
open Tree
def IsAronszajn (κ : Cardinal.{w}) (T : Type w) [PartialOrder T] [IsTree T] : Prop :=
  IsKappaTree κ T ∧ ¬ ∃ b : Set T, IsCofinalBranch b
def NoAronszajn (κ : Cardinal.{w}) : Prop :=
  ∀ (T : Type w) [PartialOrder T] [IsTree T], ¬ IsAronszajn κ T
def LaArrowKappa (κ μ : Cardinal.{w}) : Prop :=
  ∀ C : Coloring (Kappa κ) (Kappa μ), IsLocallyAdditive C →
    ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H
def Fact_5_1 : Prop :=
  ∀ κ : Cardinal.{w}, κ.IsInaccessible →
    (NoAronszajn κ ↔
      ∀ lam : Cardinal.{w}, lam < κ → ∀ C : Coloring (Kappa κ) (Kappa lam),
        ∃ H : Set (Kappa κ), #H = κ ∧ IsHomogeneous C H)
section Aux
variable {κ : Cardinal.{w}}
end Aux
namespace Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
end Tree
section TreeOfColoringAux
variable {κ : Cardinal.{w}} {D : Type w}
end TreeOfColoringAux
end JardenShami


