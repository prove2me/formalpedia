-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:04:05.504423+00:00
-- url     : https://prove2.me/theorems/38b2f62e-78d6-4db7-abc7-083708d29b9c
-- title:
--   Scheme Restriction Coherence
-- statement:
--   Definitions and structural lemmas for Scheme Restriction Coherence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeRestrictionCoherence.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeSectionRestriction
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "cY" => schemeRestrictionConstantMap f k c
local notation "cZ" => schemeRestrictionConstantMap g k cY
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k cY
local notation "OmegaZ" => schemeDifferentialSheaf Z k cZ
def schemeDifferentialRestrictionComparisonTo
    {W V : Scheme.{u}} (i : W ⟶ V) [IsOpenImmersion i]
    (b : CommRingCat.{u}) (a : b ⟶ Γ(V, ⊤)) (d : b ⟶ Γ(W, ⊤))
    (h : schemeRestrictionConstantMap i b a = d) :
    schemeDifferentialSheaf W b d ⟶
      (Scheme.Modules.restrictFunctor i).obj (schemeDifferentialSheaf V b a) := by
  subst d
  exact schemeDifferentialRestrictionComparison i b a
omit [IsOpenImmersion f] [IsOpenImmersion g] in
lemma schemeRestrictionConstantMap_comp :
    schemeRestrictionConstantMap (g ≫ f) k c = cZ :=
  (Category.assoc c f.appTop g.appTop).symm
def schemeDifferentialRestrictionComparisonComposite :
    OmegaZ ⟶ (Scheme.Modules.restrictFunctor (g ≫ f)).obj OmegaX :=
  schemeDifferentialRestrictionComparison g k cY ≫
    (Scheme.Modules.restrictFunctor g).map (schemeDifferentialRestrictionComparison f k c) ≫
    (Scheme.Modules.restrictFunctorComp g f).inv.app OmegaX
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "cY" => schemeRestrictionConstantMap f k c
local notation "cZ" => schemeRestrictionConstantMap g k cY
local notation "OmegaX" => schemeDifferentialSheaf X k c
local notation "OmegaY" => schemeDifferentialSheaf Y k cY
local notation "OmegaZ" => schemeDifferentialSheaf Z k cZ
variable (d : k ⟶ Γ(Y, ⊤)) (e : k ⟶ Γ(Z, ⊤))
variable (hf : schemeRestrictionConstantMap f k c = d)
variable (hg : schemeRestrictionConstantMap g k d = e)
include hf hg in
omit [IsOpenImmersion f] [IsOpenImmersion g] in
lemma schemeRestrictionConstantMap_comp_to :
    schemeRestrictionConstantMap (g ≫ f) k c = e := by
  change c ≫ (f.appTop ≫ g.appTop) = e
  exact (Category.assoc c f.appTop g.appTop).symm.trans
    ((congrArg (fun a : k ⟶ Γ(Y, ⊤) => a ≫ g.appTop) hf).trans hg)
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {Y X : Scheme.{u}} (i j : Y ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j]
variable (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤)) (d : k ⟶ Γ(Y, ⊤))
variable (hi : schemeRestrictionConstantMap i k c = d)
variable (hj : schemeRestrictionConstantMap j k c = d)
local notation "OmegaX" => schemeDifferentialSheaf X k c
lemma schemeOpenImmersionImage_congr (h : i = j) (U : Y.Opens) : i ''ᵁ U = j ''ᵁ U := by
  subst j
  rfl
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
variable [IsOpenImmersion f] [IsOpenImmersion g]
lemma schemeNestedImage_le : (g ≫ f) ''ᵁ ⊤ ≤ f ''ᵁ ⊤ := by
  rw [Scheme.Hom.comp_image]
  exact f.image_mono le_top
end
end QEC.Coding.AlgebraicGeometry


