-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_AffineRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:10:10.836484+00:00
-- url     : https://prove2.me/theorems/952ea325-0fa4-4d8e-b512-9c30f1fd4794
-- title:
--   Affine Restriction
-- statement:
--   Definitions and structural lemmas for Affine Restriction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineRestriction.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestrictionCoherence
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialGlobalRestrictionTo_smul

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section
universe u
lemma affineCoefficientRestrictionSquare (C A B : CommRingCat.{u})
    (phi : C ⟶ A) (psi : C ⟶ B) (q : A ⟶ B) (h : phi ≫ q = psi) :
    (phi ≫ (Scheme.ΓSpecIso A).inv) ≫ (Spec.map q).appTop =
      psi ≫ (Scheme.ΓSpecIso B).inv := by
  have hn : (Scheme.ΓSpecIso A).inv ≫ (Spec.map q).appTop =
      q ≫ (Scheme.ΓSpecIso B).inv := (Scheme.ΓSpecIso_inv_naturality q).symm
  have h1 := Category.assoc phi (Scheme.ΓSpecIso A).inv (Spec.map q).appTop
  have h2 := congrArg (fun t : A ⟶ Γ(Spec B, ⊤) => phi ≫ t) hn
  have h3 := (Category.assoc phi q (Scheme.ΓSpecIso B).inv).symm
  have h4 := congrArg (fun t : C ⟶ B => t ≫ (Scheme.ΓSpecIso B).inv) h
  exact h1.trans (h2.trans (h3.trans h4))
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
local notation "f" => Spec.map q
local notation "cA" => affineDifferentialGlobalConstantMap k A
local notation "cB" => affineDifferentialGlobalConstantMap k B
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k) cA
local notation "OmegaB" => schemeDifferentialSheaf (Spec B) (CommRingCat.of k) cB
include hcoeff
lemma affineDifferentialRestrictionConstantMap :
    schemeRestrictionConstantMap (f) (CommRingCat.of k) cA = cB :=
  affineCoefficientRestrictionSquare (CommRingCat.of k) A B
    (CommRingCat.ofHom (algebraMap k A)) (CommRingCat.ofHom (algebraMap k B)) q hcoeff
variable [hopen : IsOpenImmersion (Spec.map q)]
def affineDifferentialGlobalRestriction : Γ(OmegaA, ⊤) ⟶ Γ(OmegaB, ⊤) :=
  schemeDifferentialGlobalRestrictionTo (f) (CommRingCat.of k) cA cB
    (affineDifferentialRestrictionConstantMap k A B q hcoeff)
lemma affineDifferentialGlobalRestriction_smul (a : A) (s : Γ(OmegaA, ⊤)) :
    affineDifferentialGlobalRestriction k A B q hcoeff (a • s) =
      q a • affineDifferentialGlobalRestriction k A B q hcoeff s := by
  have ha : a • s = (Scheme.ΓSpecIso A).inv a • s := by
    rw [Scheme.Modules.smul_Spec_def]
    simp only [show (⊤ : (Spec A).Opens).leTop = 𝟙 _ from rfl,
      op_id]
    exact congrArg (fun t : Γ(Spec A, ⊤) ⟶ Γ(Spec A, ⊤) =>
      t ((Scheme.ΓSpecIso A).inv a) • s) ((Spec A).presheaf.map_id _)
  have hb : q a • affineDifferentialGlobalRestriction k A B q hcoeff s =
      (Scheme.ΓSpecIso B).inv (q a) •
        affineDifferentialGlobalRestriction k A B q hcoeff s := by
    rw [Scheme.Modules.smul_Spec_def]
    simp only [show (⊤ : (Spec B).Opens).leTop = 𝟙 _ from rfl,
      op_id]
    exact congrArg (fun t : Γ(Spec B, ⊤) ⟶ Γ(Spec B, ⊤) =>
      t ((Scheme.ΓSpecIso B).inv (q a)) • affineDifferentialGlobalRestriction k A B q hcoeff s) ((Spec B).presheaf.map_id _)
  have hr := (congrArg (fun t : A ⟶ Γ(Spec B, ⊤) => t a)
    (Scheme.ΓSpecIso_inv_naturality q)).symm
  rw [ha]
  exact (schemeDifferentialGlobalRestrictionTo_smul (f) (CommRingCat.of k) cA cB
    (affineDifferentialRestrictionConstantMap k A B q hcoeff)
    ((Scheme.ΓSpecIso A).inv a) s).trans
      ((congrArg (fun b : Γ(Spec B, ⊤) =>
        b • affineDifferentialGlobalRestriction k A B q hcoeff s) hr).trans hb.symm)
def affineDifferentialGlobalRestrictionKaehler :
    KaehlerDifferential k A →+ KaehlerDifferential k B :=
  (affineDifferentialGlobalSectionsEquiv k B).toAddEquiv.toAddMonoidHom.comp
    ((affineDifferentialGlobalRestriction k A B q hcoeff).hom.comp
      (affineDifferentialGlobalSectionsEquiv k A).symm.toAddEquiv.toAddMonoidHom)
lemma affineDifferentialGlobalRestrictionKaehler_smul
    (a : A) (s : KaehlerDifferential k A) :
    affineDifferentialGlobalRestrictionKaehler k A B q hcoeff (a • s) =
      q a • affineDifferentialGlobalRestrictionKaehler k A B q hcoeff s := by
  change affineDifferentialGlobalSectionsEquiv k B
    (affineDifferentialGlobalRestriction k A B q hcoeff
      ((affineDifferentialGlobalSectionsEquiv k A).symm (a • s))) = _
  rw [LinearEquiv.map_smul]
  have h := affineDifferentialGlobalRestriction_smul k A B q hcoeff a
    ((affineDifferentialGlobalSectionsEquiv k A).symm s)
  exact (congrArg (affineDifferentialGlobalSectionsEquiv k B) h).trans
    ((affineDifferentialGlobalSectionsEquiv k B).map_smul (q a) _)
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
variable [IsOpenImmersion (Spec.map q)]
variable (hq : ∀ a : A, q a = algebraMap A B a)
def affineDifferentialGlobalRestrictionKaehlerLinear :
    KaehlerDifferential k A →ₗ[A] KaehlerDifferential k B where
  __ := affineDifferentialGlobalRestrictionKaehler k A B q hcoeff
  map_smul' a s :=
    (affineDifferentialGlobalRestrictionKaehler_smul k A B q hcoeff a s).trans
      ((congrArg (fun b : B => b • affineDifferentialGlobalRestrictionKaehler k A B q hcoeff s)
        (hq a)).trans (IsScalarTower.algebraMap_smul B a _))
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A B : CommRingCat.{u}) [CommRing k]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable (q : A ⟶ B)
variable (hcoeff : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ A) ≫ q =
  (CommRingCat.ofHom (algebraMap k B) : CommRingCat.of k ⟶ B))
variable [IsOpenImmersion (Spec.map q)]
variable (hq : ∀ a : A, q a = algebraMap A B a)
variable {X : Scheme.{u}} (f : Spec A ⟶ X) [IsOpenImmersion f]
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
local notation "OmegaX" => schemeDifferentialSheaf X (CommRingCat.of k) c
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k A)
local notation "OmegaB" => schemeDifferentialSheaf (Spec B) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k B)
def affineDifferentialChartImageKaehlerIso :
    AddCommGrpCat.of (KaehlerDifferential k A) ≅ Γ(OmegaX, f ''ᵁ ⊤) :=
  (affineDifferentialGlobalSectionsEquiv k A).symm.toAddEquiv.toAddCommGrpIso ≪≫
    schemeDifferentialRestrictionImageSectionIsoTo f (CommRingCat.of k) c
      (affineDifferentialGlobalConstantMap k A) hf ⊤
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) [CommRing k] (X : Scheme.{u})
variable (c : CommRingCat.of k ⟶ Γ(X, ⊤))
local notation "OmegaX" => schemeDifferentialSheaf X (CommRingCat.of k) c
local instance schemeDifferentialGlobalConstantModule : Module k Γ(OmegaX, ⊤) :=
  Module.compHom Γ(OmegaX, ⊤) c.hom
variable (A : CommRingCat.{u}) [Algebra k A] (f : Spec A ⟶ X) [IsOpenImmersion f]
variable (hf : schemeRestrictionConstantMap f (CommRingCat.of k) c =
  affineDifferentialGlobalConstantMap k A)
local notation "OmegaA" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k)
  (affineDifferentialGlobalConstantMap k A)
local notation "psi" => schemeDifferentialGlobalRestrictionTo f (CommRingCat.of k) c
  (affineDifferentialGlobalConstantMap k A) hf
def affineDifferentialGlobalRestrictionToKaehler : Γ(OmegaX, ⊤) →+ KaehlerDifferential k A :=
  (affineDifferentialGlobalSectionsEquiv k A).toAddEquiv.toAddMonoidHom.comp (psi).hom
end
end QEC.Coding.AlgebraicGeometry


