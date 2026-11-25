-- Prove2me | Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
-- name    : PretorsionImageClosed_Modules_FiniteModules
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:27:07.117445+00:00
-- url     : https://prove2.me/theorems/f55da4e0-4b81-4372-ba88-7be81991fc88
-- title:
--   Finite Modules
-- statement:
--   Definitions and structural lemmas for Finite Modules, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/Modules/FiniteModules.lean

module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open CategoryTheory Limits
namespace FGModuleCat
variable {R : Type*} [Ring R] [IsNoetherianRing R]
end FGModuleCat
end PretorsionImageClosed


