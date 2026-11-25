-- Prove2me | Definitions.Def_PretorsionImageClosed_Modules_IndecomposableModule
-- name    : PretorsionImageClosed_Modules_IndecomposableModule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:30:31.520548+00:00
-- url     : https://prove2.me/theorems/7fb2bcfb-922c-437b-88af-b4b31d7230a7
-- title:
--   Indecomposable Module
-- statement:
--   Definitions and structural lemmas for Indecomposable Module, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/IndecomposableModule.lean

module
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Definitions.Def_PretorsionImageClosed_Modules_LocalRingIdempotents
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PretorsionImageClosed
universe u v w
section Semiring
variable (A : Type u) (M : Type v) [Semiring A] [AddCommMonoid M] [Module A M]
def IsIndecomposableModule : Prop :=
  Nontrivial M ∧ ∀ N P : Submodule A M, IsCompl N P → N = ⊥ ∨ P = ⊥
variable {A M}
end Semiring
section Ring
variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]
section Fitting
variable [IsNoetherian A M] [IsArtinian A M]
end Fitting
end Ring
end PretorsionImageClosed


