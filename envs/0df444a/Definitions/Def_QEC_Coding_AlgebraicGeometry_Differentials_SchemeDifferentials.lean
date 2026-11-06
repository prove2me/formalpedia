-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:53:20.727718+00:00
-- url     : https://prove2.me/theorems/69093fa1-ac7c-45b4-ac7c-150361a8d009
-- title:
--   Scheme Differentials
-- statement:
--   Definitions and structural lemmas for Scheme Differentials, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SchemeDifferentials.lean

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (X : Scheme.{u}) (k : CommRingCat.{u})
def schemeConstantPresheafMap (c : k ⟶ Γ(X, ⊤)) :
    (Functor.const X.Opensᵒᵖ).obj k ⟶ X.presheaf where
  app U := c ≫ X.presheaf.map (homOfLE le_top).op
  naturality {U V} f := by
    dsimp
    rw [Category.id_comp, Category.assoc, ← X.presheaf.map_comp]
    congr 1
def schemeDifferentialPresheaf (c : k ⟶ Γ(X, ⊤)) : X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (schemeConstantPresheafMap X k c)
def schemeDifferentialSheaf (c : k ⟶ Γ(X, ⊤)) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (schemeDifferentialPresheaf X k c)
def schemeDifferentialPresheafHomEquiv (c : k ⟶ Γ(X, ⊤))
    (M : X.PresheafOfModules) :
    (schemeDifferentialPresheaf X k c ⟶ M) ≃
      M.Derivation' (schemeConstantPresheafMap X k c) where
  toFun f := (PresheafOfModules.DifferentialsConstruction.derivation'
    (schemeConstantPresheafMap X k c)).postcomp f
  invFun d := (PresheafOfModules.DifferentialsConstruction.isUniversal'
    (schemeConstantPresheafMap X k c)).desc d
  left_inv f := by
    apply (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (schemeConstantPresheafMap X k c)).postcomp_injective
    exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (schemeConstantPresheafMap X k c)).fac _
  right_inv d := by
    exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (schemeConstantPresheafMap X k c)).fac d
def schemeDifferentialSheafHomEquiv (c : k ⟶ Γ(X, ⊤))
    (M : X.Modules) :
    (schemeDifferentialSheaf X k c ⟶ M) ≃
      ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
        (schemeConstantPresheafMap X k c) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    (schemeDifferentialPresheafHomEquiv X k c
      ((Scheme.Modules.toPresheafOfModules X).obj M))
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (X : Scheme.{u}) (k : CommRingCat.{u}) (c : k ⟶ Γ(X, ⊤))
local notation "Omega" => schemeDifferentialSheaf X k c
local notation "constants" => schemeConstantPresheafMap X k c
def schemeDifferentialSheafDerivation :
    ((Scheme.Modules.toPresheafOfModules X).obj Omega).Derivation' constants :=
  schemeDifferentialSheafHomEquiv X k c Omega (𝟙 Omega)
end
end QEC.Coding.AlgebraicGeometry


