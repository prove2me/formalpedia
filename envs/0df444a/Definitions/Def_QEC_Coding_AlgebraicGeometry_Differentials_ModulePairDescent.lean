-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:52:14.98221+00:00
-- url     : https://prove2.me/theorems/a0440b39-60e3-4ddc-9940-9eb6d581d291
-- title:
--   Module Pair Descent
-- statement:
--   Definitions and structural lemmas for Module Pair Descent, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/ModulePairDescent.lean

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
def schemeModuleAbelianSheaf : TopCat.Sheaf AddCommGrpCat X :=
  ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
def schemeModulePairOpens : Bool → X.Opens
  | false => U
  | true => V
def schemeModulePairSections (s : Γ(M, U)) (t : Γ(M, V)) :
    (b : Bool) → M.presheaf.obj (op (schemeModulePairOpens U V b))
  | false => s
  | true => t
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
variable {A B : AddCommGrpCat.{u}} (e : Γ(M, U) ≅ A) (f : Γ(M, V) ≅ B)
def schemeModuleGlobalIsoPair (z : Γ(M, ⊤)) : A × B :=
  (e.hom (M.presheaf.map (homOfLE le_top).op z),
    f.hom (M.presheaf.map (homOfLE le_top).op z))
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
variable {A B : AddCommGrpCat.{u}} (e : Γ(M, U) ≅ A) (f : Γ(M, V) ≅ B)
end
end QEC.Coding.AlgebraicGeometry


