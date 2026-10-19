-- Prove2me | Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018
-- name    : MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T13:01:34.773743+00:00
-- url     : https://prove2.me/theorems/5ad185bf-1b20-4269-9e09-587475bcc8f4
-- title:
--   Original explicit curve-model semilinear function-field lift
-- statement:
--   Preserve twenty-two complete original FLT helper declaration types and four nonproof constructor values for generic-stalk pullback, the function-field isomorphism, the model function-field ring equivalence and the explicit semilinear lift. Complete official Anthropic FLT source is reused at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. The named downstream consumer is the actual geometric Galois semilinear lift and divisor-class naturality.
-- source:
--   MazurTheorem original checked constructors and complete type/value audits; official FLT provenance retained where used.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Complete original helper constructors and proofs from official Anthropic FLT
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a curve-model isomorphism with its coefficient diagram
induces the original explicit semilinear function-field automorphism.
Named downstream consumer: the actual geometric Galois function-field lift
and its complete divisor-class compatibility for the actual nineteen pairing. -/
import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
noncomputable section
universe u v
namespace MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicCurve.CurveModel
namespace FunctionFieldPull

variable {X Y Z : Scheme.{u}}

def pull [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint X)

section

variable [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

theorem pull_germ (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    pull f h (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (h.mem_open U.isOpen hU) (f.app U s) := by
  simp only [pull, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem pull_algebraMap (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y) (x : X)
    (a : Y.presheaf.stalk (f.base x)) :
    pull f h (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  simp only [pull, RingHom.algebraMap_toAlgebra, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply (Y.presheaf)]
  have := Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) x
    ((genericPoint_spec X).specializes trivial) a
  convert this using 2

theorem pull_id : pull (𝟙 X) (specializes_refl _) = 𝟙 _ := by
  simp [pull]

theorem pull_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) ⤳ genericPoint Y)
    (hg : g.base (genericPoint Y) ⤳ genericPoint Z) :
    pull (f ≫ g) ((g.base.hom.map_specializes hf).trans hg) = pull g hg ≫ pull f hf := by
  simp only [pull, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc g (f.base (genericPoint X)) (genericPoint Y) hf]
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

end

variable [IsIntegral X] [IsIntegral Y]

theorem specializes_of_iso (e : X ≅ Y) : e.hom.base (genericPoint X) ⤳ genericPoint Y :=
  (genericPoint_eq_of_isOpenImmersion e.hom).symm ▸ specializes_refl _

theorem specializes_of_iso_inv (e : X ≅ Y) : e.inv.base (genericPoint Y) ⤳ genericPoint X :=
  specializes_of_iso e.symm

def equivOfIso (e : X ≅ Y) : Y.functionField ≃+* X.functionField :=
  (({ hom := pull e.hom (specializes_of_iso e)
      inv := pull e.inv (specializes_of_iso_inv e)
      hom_inv_id := by
        have h := (pull_comp e.inv e.hom (specializes_of_iso_inv e) (specializes_of_iso e)).symm
        rw [h]
        have : ∀ (k : (e.inv ≫ e.hom).base (genericPoint Y) ⤳ genericPoint Y),
            pull (e.inv ≫ e.hom) k = 𝟙 _ := by
          rw [e.inv_hom_id]; intro k; exact pull_id
        exact this _
      inv_hom_id := by
        have h := (pull_comp e.hom e.inv (specializes_of_iso e) (specializes_of_iso_inv e)).symm
        rw [h]
        have : ∀ (k : (e.hom ≫ e.inv).base (genericPoint X) ⤳ genericPoint X),
            pull (e.hom ≫ e.inv) k = 𝟙 _ := by
          rw [e.hom_inv_id]; intro k; exact pull_id
        exact this _ } : Y.functionField ≅ X.functionField)).commRingCatIsoToRingEquiv

theorem equivOfIso_apply (e : X ≅ Y) (a : Y.functionField) :
    equivOfIso e a = pull e.hom (specializes_of_iso e) a := rfl

theorem equivOfIso_symm_apply (e : X ≅ Y) (a : X.functionField) :
    (equivOfIso e).symm a = pull e.inv (specializes_of_iso_inv e) a := rfl

theorem map_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range.map
        (equivOfIso e).toRingHom =
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  haveI : IsIso (e.hom.stalkMap x) := inferInstance
  ext b
  simp only [Subring.mem_map, RingHom.mem_range, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨e.hom.stalkMap x a, (pull_algebraMap e.hom (specializes_of_iso e) x a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', e.hom.stalkMap x a' = a :=
      ⟨inv (e.hom.stalkMap x) a, by
        rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
    exact ⟨_, ⟨a', rfl⟩, pull_algebraMap e.hom (specializes_of_iso e) x a'⟩

theorem image_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e) ''
        ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) =
      ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) := by
  have h := congrArg (fun S : Subring X.functionField => (S : Set X.functionField))
    (map_equivOfIso_range_stalk e x)
  simpa [Subring.coe_map] using h

theorem image_equivOfIso_symm_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e).symm '' ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) =
      ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) := by
  rw [← image_equivOfIso_range_stalk e x, ← Set.image_comp]
  simp

theorem pull_baseToFunctionField {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ cY = cX)
    (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX a := by
  subst hf
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) =
    X.presheaf.germ ⊤ (genericPoint X) trivial _
  erw [pull_germ]
  rfl

theorem equivOfIso_baseToFunctionField {K : Type u} [Field K] (e : X ≅ Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    (hf : e.hom ≫ cY = cX) (a : K) :
    equivOfIso e (baseToFunctionField cY a) = baseToFunctionField cX a :=
  pull_baseToFunctionField e.hom _ cX cY hf a

end FunctionFieldPull

open FunctionFieldPull

section

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] [IsIntegral X] [IsIntegral Y]

theorem pull_baseToFunctionField_twist {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (τ : K ≃+* K)
    (hf : f ≫ cY = cX ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX (τ a) := by
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) =
    X.presheaf.germ ⊤ (genericPoint X) trivial _
  erw [pull_germ]
  have key : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
      cX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (τ a)) := by
    have h1 : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
        cX.appTop.hom ((Spec.map (CommRingCat.ofHom (τ : K →+* K))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) :=
      congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) hf
    rw [h1]
    congr 1
    have h2 := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : K →+* K)))
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h2
    exact h2.symm
  exact congrArg _ key

end

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

def gRingEquiv (M : CurveModel K L) (e : M.C ≅ M.C) : L ≃+* L :=
  (M.ffEquiv.trans (equivOfIso e)).trans M.ffEquiv.symm

theorem gRingEquiv_apply (M : CurveModel K L) (e : M.C ≅ M.C) (a : L) :
    gRingEquiv M e a = M.ffEquiv.symm (equivOfIso e (M.ffEquiv a)) := rfl

theorem gRingEquiv_algebraMap (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) (a : K) :
    gRingEquiv M e (algebraMap K L a) = algebraMap K L (τ a) := by
  rw [gRingEquiv_apply, M.ffEquiv_algebraMap, equivOfIso_apply,
    pull_baseToFunctionField_twist e.hom _ M.toBase M.toBase τ he a, ← M.ffEquiv_algebraMap,
    RingEquiv.symm_apply_apply]

def gSL (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) : SemilinearAut K L :=
  ⟨(gRingEquiv M e, τ), fun a => gRingEquiv_algebraMap M e τ he a⟩

theorem gSL_smul (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) (a : L) :
    gSL M e τ he • a = M.ffEquiv.symm (equivOfIso e (M.ffEquiv a)) := rfl

theorem baseAut_gSL (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) :
    SemilinearAut.baseAut (gSL M e τ he) = τ := rfl


end MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018
#print axioms MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018.gSL


