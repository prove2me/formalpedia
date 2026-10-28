-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ModuleLinearMapSquare_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_ModuleLinearMapSquare_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:05:59.965205+00:00
-- url     : https://prove2.me/theorems/b7ddbffc-3ca6-41c3-a2c6-8833e9458f17
-- title:
--   Module Linear Map Square — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for module linear map square used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_ModuleLinearMapSquare.lean, selected declarations in lines 11–20; source SHA-256 c8e8ccbd015c4ccdcf19bda07d11bf072cced48bc26cd3c60dddde0882a4570a; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.Basic

set_option autoImplicit false

namespace LPCA

open CategoryTheory

universe u

theorem moduleLinearMapSquare (R : Type u) [Ring R] (A B C D : ModuleCat.{u} R)
    (f : A →ₗ[R] B) (g : B →ₗ[R] D) (h : A →ₗ[R] C) (i : C →ₗ[R] D)
    (hs : g.comp f = i.comp h) :
    ModuleCat.ofHom f ≫ ModuleCat.ofHom g = ModuleCat.ofHom h ≫ ModuleCat.ofHom i := by
  apply ModuleCat.hom_ext
  exact hs

theorem moduleIsoLinearEquiv_hom (R : Type u) [Ring R] (A B : ModuleCat.{u} R) (e : A ≅ B) :
    ModuleCat.ofHom e.toLinearEquiv.toLinearMap = e.hom := by
  rfl

end LPCA


