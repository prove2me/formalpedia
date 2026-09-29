-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4d589a73-11ab-5b28-b8af-ca4587379b4f

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace.AlgebraicCurve"

universe u v

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "baseToFunctionField CurveModel CurveModel.pointEquivPlace_apply Place Place.ext SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.ofAlgAut_smul SemilinearAut.smul_toValuationSubring"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "pointEquivPlace pointEquivPlace_apply toBase C range_stalk_eq ffEquiv ffEquiv_algebraMap smooth"
namespace ModelIndepSol
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

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
  rw [pull_germ]
  rfl

theorem equivOfIso_baseToFunctionField {K : Type u} [Field K] (e : X ≅ Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    (hf : e.hom ≫ cY = cX) (a : K) :
    equivOfIso e (baseToFunctionField cY a) = baseToFunctionField cX a :=
  pull_baseToFunctionField e.hom _ cX cY hf a

end FunctionFieldPull

open FunctionFieldPull

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

def tauRingEquiv (M M' : CurveModel K L) (e : M.C ≅ M'.C) : L ≃+* L :=
  (M.ffEquiv.trans (equivOfIso e).symm).trans M'.ffEquiv.symm

theorem tauRingEquiv_apply (M M' : CurveModel K L) (e : M.C ≅ M'.C) (a : L) :
    tauRingEquiv M M' e a = M'.ffEquiv.symm ((equivOfIso e).symm (M.ffEquiv a)) := rfl

theorem tauRingEquiv_algebraMap (M M' : CurveModel K L) (e : M.C ≅ M'.C)
    (he : e.hom ≫ M'.toBase = M.toBase) (a : K) :
    tauRingEquiv M M' e (algebraMap K L a) = algebraMap K L a := by
  rw [tauRingEquiv_apply, M.ffEquiv_algebraMap,
    ← equivOfIso_baseToFunctionField e M.toBase M'.toBase he a, RingEquiv.symm_apply_apply,
    ← M'.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]

def tau (M M' : CurveModel K L) (e : M.C ≅ M'.C) (he : e.hom ≫ M'.toBase = M.toBase) :
    L ≃ₐ[K] L :=
  AlgEquiv.ofRingEquiv (f := tauRingEquiv M M' e) (tauRingEquiv_algebraMap M M' e he)

theorem tau_apply (M M' : CurveModel K L) (e : M.C ≅ M'.C) (he : e.hom ≫ M'.toBase = M.toBase)
    (a : L) : tau M M' e he a = M'.ffEquiv.symm ((equivOfIso e).symm (M.ffEquiv a)) := rfl

theorem coe_toValuationSubring_pointEquivPlace [IsAlgClosed K] (M : CurveModel K L)
    (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    ((M.pointEquivPlace x).toValuationSubring : Set L) =
      M.ffEquiv.symm '' ((algebraMap (M.C.presheaf.stalk (x.1.base (IsLocalRing.closedPoint K)))
        M.C.functionField).range : Set M.C.functionField) := by
  rw [CurveModel.pointEquivPlace_apply]
  have h := M.range_stalk_eq (pointEquivClosedPoint M.toBase x)
  rw [← RingHom.map_range] at h
  have h' := congrArg (fun S : Subring L => (S : Set L)) h
  simp only [Subring.coe_map] at h'
  exact h'.symm

theorem pointEquivPlace_comp_eq_smul [IsAlgClosed K] (M M' : CurveModel K L) (e : M.C ≅ M'.C)
    (he : e.hom ≫ M'.toBase = M.toBase)
    (x : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    M'.pointEquivPlace ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩ =
      SemilinearAut.ofAlgAut (tau M M' e he) • M.pointEquivPlace x := by
  apply Place.ext
  apply SetLike.coe_injective
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.coe_pointwise_smul, ← Set.image_smul,
    coe_toValuationSubring_pointEquivPlace, coe_toValuationSubring_pointEquivPlace]

  change M'.ffEquiv.symm '' ((algebraMap (M'.C.presheaf.stalk
      (e.hom.base (x.1.base (IsLocalRing.closedPoint K)))) M'.C.functionField).range : Set _) = _
  simp only [SemilinearAut.ofAlgAut_smul]
  rw [← Set.image_comp]
  have hcomp : ((fun m => tau M M' e he m) ∘ (M.ffEquiv.symm : M.C.functionField → L)) =
      (M'.ffEquiv.symm : M'.C.functionField → L) ∘ ((equivOfIso e).symm) := by
    funext a
    simp [Function.comp_apply, tau_apply]
  rw [hcomp, Set.image_comp, image_equivOfIso_symm_range_stalk]

end AlgebraicCurve.CurveModel.ModelIndepSol

end

open AlgebraicCurve.CurveModel.ModelIndepSol in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (L : Type v) [Field L] [Algebra K L]
    (M M' : AlgebraicCurve.CurveModel K L) (e : M.C ≅ M'.C) (he : e.hom ≫ M'.toBase = M.toBase) :
    ∃ τ : L ≃ₐ[K] L,
      ∀ x : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _},
        M'.pointEquivPlace ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩ =
          SemilinearAut.ofAlgAut τ • M.pointEquivPlace x :=
  ⟨tau M M' e he, fun x => pointEquivPlace_comp_eq_smul M M' e he x⟩

end S_AlgebraicCurve_CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace (solution)
