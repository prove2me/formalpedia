-- Prove2me | Definitions.Def_OAIQ031A036
-- name    : OAIQ031A036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:03:40.248732+00:00
-- url     : https://prove2.me/theorems/f0c08b38-a011-449e-910d-a9f819729108
-- title:
--   Definitions bundle OAIQ031A036 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 2 definitions, 2 instances and 10 theorems. The definitions and types are `OAI.ArExplicit.EnvelopingBimodule.leftEquiv`, `OAI.ArExplicit.ResolutionProducts.resolutionEndpointIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Ext_ExtIsoFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtIsoFunctor.lean), [`AuslanderReiten_Modules_BimoduleEnveloping`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/BimoduleEnveloping.lean), [`AuslanderReiten_Resolutions_BinaryKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszul.lean), [`AuslanderReiten_Resolutions_MapResolutionExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/MapResolutionExt.lean), [`AuslanderReiten_Resolutions_MapResolutionExtComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/MapResolutionExtComparison.lean), [`AuslanderReiten_Resolutions_MapResolutionExtMk`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/MapResolutionExtMk.lean), [`AuslanderReiten_Resolutions_ResolutionEndpointIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionEndpointIso.lean), [`AuslanderReiten_Tensor_EnvelopingBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBimodule.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A002`, `OAIQ031A007`, `OAIQ031A011`, `OAIQ031A013`, `OAIQ031A014`, `OAIQ031A015` and `OAIQ031A016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A053`, `OAIQ031A055`, `OAIQ031A056`, `OAIQ031A057` and `OAIQ031A058`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A002
import Definitions.Def_OAIQ031A007
import Definitions.Def_OAIQ031A011
import Definitions.Def_OAIQ031A013
import Definitions.Def_OAIQ031A014
import Definitions.Def_OAIQ031A015
import Definitions.Def_OAIQ031A016

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtIsoFunctor
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit
universe u v w
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable {D : Type w} [Category.{u} D] [Abelian D] [HasExt.{u} D] [Linear k D]
variable {X Y Z : C}

theorem selfExtIso_trans (e : X ≅ Y) (f : Y ≅ Z) (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) f n (selfExtIso (k := k) e n x) =
      selfExtIso (k := k) (e ≪≫ f) n x := by
  simp [selfExtIso_apply]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem selfExtIso_mapExactFunctor (e : X ≅ Y) (n : ℕ) (x : Ext X X n) :
    (selfExtIso (k := k) e n x).mapExactFunctor F =
      selfExtIso (k := k) (F.mapIso e) n (x.mapExactFunctor F) := by
  simp only [selfExtIso_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Functor.mapIso_hom, Functor.mapIso_inv]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBimodule
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

namespace EnvelopingBimodule

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))

def leftEquiv : EnvelopingBimodule k R M ≃ₗ[R]
    ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj M) where
  __ := coordinates M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance instFiniteOfCarrierObjModuleCatTensorProductMulOppositeRestrictScalarsTensorLeftInclusion [Module.Finite R ((ModuleCat.restrictScalars (tensorLeftInclusion k R Rᵐᵒᵖ)).obj M)] :
    Module.Finite R (EnvelopingBimodule k R M) :=
  Module.Finite.equiv (leftEquiv M).symm

end EnvelopingBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_BimoduleEnveloping
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
variable [SMulCommClass k R M] [SMulCommClass k Rᵐᵒᵖ M]
variable [SMulCommClass R Rᵐᵒᵖ M]

instance instIsScalarTowerTensorProductMulOppositeCarrierBimoduleEnvelopingObject : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) (bimoduleEnvelopingObject k R M) :=
  IsScalarTower.of_algebraMap_smul (A := R ⊗[k] Rᵐᵒᵖ) fun a (x : bimoduleEnvelopingObject k R M) => by
    change bimoduleEnvelopingRepresentation k R M (algebraMap k (R ⊗[k] Rᵐᵒᵖ) a) x = a • x
    rw [AlgHom.commutes]
    rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszul
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

theorem mul_commute (n : ℕ) : (mulX k (n + 1)).comp (mulY k n) =
    (mulY k (n + 1)).comp (mulX k n) := by
  apply LinearMap.ext
  intro f
  exact Fin.cons_snoc_eq_snoc_cons 0 f 0

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_MapResolutionExt
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Localization
open CochainComplex CochainComplex.HomComplex HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
  [CategoryTheory.Limits.PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X Y : C} (P : ProjectiveResolution X) {n : ℕ}

theorem map_extOfCocycle
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    (P.extEquivCohomologyClass.symm (CohomologyClass.mk x)).mapExactFunctor F =
      (mapResolution F P).extEquivCohomologyClass.symm
        (CohomologyClass.mk (mappedResolutionCocycle F P x)) := by
  let Φ := F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)
  let eP : (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex ≅
      (mapResolution F P).cochainComplex := (mapResolutionCochainIso F P).symm
  let eX : (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj X) ≅
      (CochainComplex.singleFunctor D 0).obj (F.obj X) := (F.mapCochainComplexSingleFunctor 0).app X
  let eY : (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj Y) ≅
      (CochainComplex.singleFunctor D 0).obj (F.obj Y) := (F.mapCochainComplexSingleFunctor 0).app Y
  have h := congrArg (fun z => Φ.smallShiftedHomMap eP eY z) (precomp_extOfCocycle P x)
  erw [Φ.smallShiftedHomMap_comp eP eX eY,
    Φ.smallShiftedHomMap_mk₀ eP eX, Φ.smallShiftedHomMap_mk eP eY] at h
  have hπ : eP.inv ≫ Φ.functor.map P.π' ≫ eX.hom = (mapResolution F P).π' :=
    mapResolutionCochainIso_π F P
  erw [hπ] at h
  apply (SmallShiftedHom.precompEquiv (mapResolution F P).π'
    (by rw [mem_quasiIso_iff]; infer_instance)).injective
  change (SmallShiftedHom.mk₀ (quasiIso D (.up ℤ)) 0 rfl (mapResolution F P).π').comp
    _ (add_zero (n : ℤ)) =
      (SmallShiftedHom.mk₀ (quasiIso D (.up ℤ)) 0 rfl (mapResolution F P).π').comp
        ((mapResolution F P).extEquivCohomologyClass.symm
          (CohomologyClass.mk (mappedResolutionCocycle F P x))) (add_zero (n : ℤ))
  have hpost := precomp_extOfCocycle (mapResolution F P) (mappedResolutionCocycle F P x)
  refine h.trans (Eq.trans ?_ hpost.symm)
  apply congrArg (SmallShiftedHom.mk (quasiIso D (.up ℤ)))
  rw [mappedResolutionCocycle, AddEquiv.symm_apply_apply]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_MapResolutionExtMk
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X Y : C} (P : ProjectiveResolution X) {n : ℕ}

omit [HasExt.{v} C] [HasExt.{v'} D] in
theorem mappedResolutionCocycle_eq
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    mappedResolutionCocycle F P x =
      ((fullHomCocycleMap F _ _ _ x).precomp (mapResolutionCochainIso F P).hom).postcomp
        ((F.mapCochainComplexSingleFunctor 0).hom.app Y) := by
  apply Cocycle.equivHomShift.symm.injective
  rw [mappedResolutionCocycle, AddEquiv.symm_apply_apply,
    Cocycle.equivHomShift_symm_postcomp, Cocycle.equivHomShift_symm_precomp, cocycle_map_hom]
  exact (Category.assoc _ _ _).symm

omit [HasExt.{v} C] [HasExt.{v'} D] in
theorem mappedResolutionCocycle_v
    (x : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ))
    (i j : ℤ) (hij : i+n=j) :
    (mappedResolutionCocycle F P x).val.v i j hij =
      (mapResolutionCochainIso F P).hom.f i ≫ F.map (x.val.v i j hij) ≫
        ((F.mapCochainComplexSingleFunctor 0).hom.app Y).f j := by
  rw [mappedResolutionCocycle_eq]
  change (((Cochain.ofHom _).comp (x.val.map F) (zero_add (n : ℤ))).comp
    (Cochain.ofHom _) (add_zero (n : ℤ))).v i j hij = _
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Cochain.map_v]
  exact Category.assoc _ _ _

theorem map_extMk (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f = 0) :
    (P.extMk f (n+1) rfl hf).mapExactFunctor F =
      (mapResolution F P).extMk (F.map f) (n+1) rfl
        (by change F.map (P.complex.d (n+1) n) ≫ F.map f = 0
            rw [← F.map_comp, hf, F.map_zero]) := by
  unfold ProjectiveResolution.extMk
  rw [map_extOfCocycle]
  apply congrArg (mapResolution F P).extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  apply (Cochain.toSingleEquiv (p := -(n : ℤ)) (q := 0) (n := (n : ℤ)) (by omega)).injective
  rw [Cocycle.toSingleMk_coe, Cochain.toSingleEquiv_toSingleMk]
  change (mappedResolutionCocycle F P _).val.v (-(n : ℤ)) 0 (by omega) ≫
    (singleObjXSelf (.up ℤ) 0 (F.obj Y)).hom = _
  rw [mappedResolutionCocycle_v, Cocycle.toSingleMk_coe, Cochain.toSingleMk_v]
  change ((mapResolutionCochainIso F P).hom.f (-(n : ℤ)) ≫
    F.map (((P.cochainComplexXIso (-(n : ℤ)) n rfl).hom ≫ f) ≫
      (singleObjXSelf (.up ℤ) 0 Y).inv) ≫
      ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app Y).f 0) ≫
        (singleObjXSelf (.up ℤ) 0 (F.obj Y)).hom = _
  rw [singleMapHomologicalComplex_hom_app_self]
  exact (map_eval_cancel F ((mapResolutionCochainIso F P).hom.f (-(n : ℤ)))
    (P.cochainComplexXIso (-(n : ℤ)) n rfl).hom f
    (singleObjXSelf (.up ℤ) 0 Y) (singleObjXSelf (.up ℤ) 0 (F.obj Y))).trans
      (congrArg (fun g => g ≫ F.map f) (mapResolutionCochainIso_coordinate F P _ n rfl))

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_MapResolutionExtComparison
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X : C} {Y : D} (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)

theorem map_extMk_comparison (e : Y ≅ F.obj X)
    (φ : ProjectiveResolution.Hom Q (mapResolution F P) e.hom)
    {n : ℕ} (f : P.complex.X n ⟶ X) (hf : P.complex.d (n+1) n ≫ f = 0)
    (g : Q.complex.X n ⟶ Y) (hg : Q.complex.d (n+1) n ≫ g = 0)
    (hgf : g = (φ.hom.f n ≫ F.map f) ≫ e.inv) :
    ((Ext.mk₀ e.hom).comp ((P.extMk f (n+1) rfl hf).mapExactFunctor F) (zero_add n)).comp
      (Ext.mk₀ e.inv) (add_zero n) = Q.extMk g (n+1) rfl hg := by
  subst g
  erw [map_extMk, ProjectiveResolution.mk₀_comp_extMk _ _ _ _ φ,
    ProjectiveResolution.extMk_comp_mk₀]

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionEndpointIso
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y Z : C}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)

theorem resolutionEndpointMap_comp (T : ProjectiveResolution Z)
    (f : P.complex ⟶ Q.complex) (g : Q.complex ⟶ T.complex) :
    resolutionEndpointMap P T (f ≫ g) = resolutionEndpointMap P Q f ≫ resolutionEndpointMap Q T g := by
  apply (cancel_epi (P.π.f 0)).1
  exact compose_square (show P.complex.X 0 ⟶ X from P.π.f 0)
    (show Q.complex.X 0 ⟶ Y from Q.π.f 0) (show T.complex.X 0 ⟶ Z from T.π.f 0)
    (f.f 0) (g.f 0) _ _ _ (resolutionEndpointMap_augmentation P Q f)
    (resolutionEndpointMap_augmentation Q T g) (resolutionEndpointMap_augmentation P T (f ≫ g))

def resolutionEndpointIso (e : P.complex ≅ Q.complex) : X ≅ Y where
  hom := resolutionEndpointMap P Q e.hom
  inv := resolutionEndpointMap Q P e.inv
  hom_inv_id := by erw [← resolutionEndpointMap_comp, e.hom_inv_id, resolutionEndpointMap_id]
  inv_hom_id := by erw [← resolutionEndpointMap_comp, e.inv_hom_id, resolutionEndpointMap_id]

@[reassoc] theorem resolutionEndpointIso_augmentation (e : P.complex ≅ Q.complex) :
    P.π.f 0 ≫ (resolutionEndpointIso P Q e).hom = e.hom.f 0 ≫ Q.π.f 0 :=
  resolutionEndpointMap_augmentation P Q e.hom

end ArExplicit.ResolutionProducts

end

end OAI
end


