-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:03:11.62588+00:00
-- url     : https://prove2.me/theorems/00f2c481-00f5-4a09-af65-4e99438c348f
-- title:
--   Scheme Section Restriction
-- statement:
--   Definitions and structural lemmas for Scheme Section Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeSectionRestriction.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k (schemeRestrictionConstantMap f k c)
def schemeDifferentialRestrictionImageSectionIso (U : Y.Opens) :
    Γ(OmegaY, U) ≅ Γ(OmegaX, f ''ᵁ U) :=
  ((Scheme.Modules.toPresheaf Y).mapIso (schemeDifferentialRestrictionIso f k c)).app (op U) ≪≫
    (OmegaX).restrictAppIso f U
def schemeDifferentialGlobalRestriction : Γ(OmegaX, ⊤) ⟶ Γ(OmegaY, ⊤) :=
  (OmegaX).presheaf.map (homOfLE le_top : f ''ᵁ ⊤ ⟶ ⊤).op ≫
    (schemeDifferentialRestrictionImageSectionIso f k c ⊤).inv
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (h : schemeRestrictionConstantMap f k c = d)
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k d
def schemeDifferentialGlobalRestrictionTo : Γ(OmegaX, ⊤) ⟶ Γ(OmegaY, ⊤) := by
  subst d
  exact schemeDifferentialGlobalRestriction f k c
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (h : schemeRestrictionConstantMap f k c = d)
def schemeDifferentialRestrictionImageSectionIsoTo (U : Y.Opens) :
    Γ(schemeDifferentialSheaf Y k d, U) ≅ Γ(schemeDifferentialSheaf X k c, f ''ᵁ U) := by
  subst d
  exact schemeDifferentialRestrictionImageSectionIso f k c U
end
end QEC.Coding.AlgebraicGeometry


