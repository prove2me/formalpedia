-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/afb3bee4-2b20-5d4f-ba97-8f32ea640be4

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FDStages19

variable (K Kbar : Type) [Field K] [Field Kbar] [Algebra K Kbar]

def Idx : Type := Option {F : IntermediateField K Kbar // FiniteDimensional K F}

variable {K Kbar}

def le : Idx K Kbar → Idx K Kbar → Prop
  | none, _ => True
  | some _, none => False
  | some F, some F' => F.1 ≤ F'.1

scoped instance : Preorder (Idx K Kbar) where
  le := le
  le_refl i := by cases i <;> simp [le]
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp [le] at hab hbc ⊢
    exact le_trans hab hbc

scoped instance : Nonempty (Idx K Kbar) := ⟨none⟩

variable (K Kbar)

def G : Idx K Kbar → Type
  | none => K
  | some F => ↥F.1

scoped instance instCommRingG (i : Idx K Kbar) : CommRing (G K Kbar i) := by
  cases i with
  | none => exact inferInstanceAs (CommRing K)
  | some F => exact inferInstanceAs (CommRing ↥F.1)

def φ : ∀ (i j : Idx K Kbar), i ≤ j → G K Kbar i →+* G K Kbar j
  | none, none, _ => RingHom.id K
  | none, some F, _ => algebraMap K ↥F.1
  | some _, none, h => False.elim h
  | some F, some F', h => (IntermediateField.inclusion h).toRingHom

def g : ∀ (i : Idx K Kbar), G K Kbar i →+* Kbar
  | none => algebraMap K Kbar
  | some F => algebraMap ↥F.1 Kbar

scoped instance directedSystem : DirectedSystem (G K Kbar) (fun i j h => ⇑(φ K Kbar i j h)) where
  map_self i x := by cases i <;> rfl
  map_map {a b c} hab hbc x := by
    cases a <;> cases b <;> cases c <;> first | exact False.elim hab | exact False.elim hbc | rfl

theorem fd_sup (F F' : {F : IntermediateField K Kbar // FiniteDimensional K F}) : FiniteDimensional K ↥(F.1 ⊔ F'.1) := by
  haveI := F.2; haveI := F'.2
  exact IntermediateField.finiteDimensional_sup F.1 F'.1

scoped instance isDirected : IsDirected (Idx K Kbar) (· ≤ ·) where
  directed a b := by
    cases a with
    | none => exact ⟨b, trivial, le_refl b⟩
    | some F =>
      cases b with
      | none => exact ⟨some F, le_refl _, trivial⟩
      | some F' => exact ⟨some ⟨F.1 ⊔ F'.1, fd_sup K Kbar F F'⟩, (le_sup_left : F.1 ≤ F.1 ⊔ F'.1), (le_sup_right : F'.1 ≤ F.1 ⊔ F'.1)⟩

theorem isDirectLimit [Algebra.IsAlgebraic K Kbar] :
    IsDirectLimit (fun i j (h : i ≤ j) => ⇑(φ K Kbar i j h)) (fun i => ⇑(g K Kbar i)) where
  surj x := by
    have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    refine ⟨some ⟨IntermediateField.adjoin K {x}, IntermediateField.adjoin.finiteDimensional hx⟩, ⟨x, ?_⟩, rfl⟩
    exact IntermediateField.mem_adjoin_simple_self K x
  inj i j mi mj h := by
    cases i with
    | none =>
      cases j with
      | none => exact ⟨none, trivial, trivial, (algebraMap K Kbar).injective h⟩
      | some F' => exact ⟨some F', trivial, le_refl _, Subtype.ext h⟩
    | some F =>
      cases j with
      | none => exact ⟨some F, le_refl _, trivial, Subtype.ext h⟩
      | some F' =>
        exact ⟨some ⟨F.1 ⊔ F'.1, fd_sup K Kbar F F'⟩, (le_sup_left : F.1 ≤ F.1 ⊔ F'.1), (le_sup_right : F'.1 ≤ F.1 ⊔ F'.1),
          Subtype.ext h⟩
  compatibility i j hij x := by
    cases i <;> cases j <;> first | exact False.elim hij | rfl

end FDStages19
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic.FDStages19"

theorem solution
    (K Kbar : Type) [Field K] [Field Kbar] [Algebra K Kbar] [Algebra.IsAlgebraic K Kbar]
    {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of K)) [QuasiCompact fX] [QuasiSeparated fX]
    (𝓛 : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K Kbar)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (F : IntermediateField K Kbar) (_ : FiniteDimensional K F)
      (𝓛F : (Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K F)))).Modules),
      Scheme.Modules.IsInvertible 𝓛F ∧
      ∀ cX : Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) ⟶
          Limits.pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K F))),
        cX ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K F))) =
          Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) →
        cX ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K F))) =
          Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap F Kbar)) →
        Nonempty ((Scheme.Modules.pullback cX).obj 𝓛F ≅ 𝓛) := by
  classical
  haveI : @QuasiCompact X (Spec (CommRingCat.of (FDStages19.G K Kbar none))) fX := ‹QuasiCompact fX›
  haveI : @QuasiSeparated X (Spec (CommRingCat.of (FDStages19.G K Kbar none))) fX := ‹QuasiSeparated fX›
  obtain ⟨j, hij, 𝓛j, h𝓛j, hcmp⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
      (FDStages19.φ K Kbar) (FDStages19.g K Kbar) (FDStages19.isDirectLimit K Kbar) (none : FDStages19.Idx K Kbar) fX 𝓛 h𝓛
  cases j with
  | some F => exact ⟨F.1, F.2, 𝓛j, h𝓛j, hcmp⟩
  | none =>

    haveI : FiniteDimensional K ↥(⊥ : IntermediateField K Kbar) := inferInstance
    have w : pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap K ↥(⊥ : IntermediateField K Kbar)))) ≫ fX =
        (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K ↥(⊥ : IntermediateField K Kbar)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K ↥(⊥ : IntermediateField K Kbar)))) ≫
          Spec.map (CommRingCat.ofHom (FDStages19.φ K Kbar none none hij)) := by
      show _ = (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap K ↥(⊥ : IntermediateField K Kbar)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K ↥(⊥ : IntermediateField K Kbar)))) ≫ Spec.map (𝟙 (CommRingCat.of K))
      rw [Spec.map_id, Category.comp_id]; exact pullback.condition
    let q : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap K ↥(⊥ : IntermediateField K Kbar)))) ⟶
        pullback fX (Spec.map (CommRingCat.ofHom (FDStages19.φ K Kbar none none hij))) :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K ↥(⊥ : IntermediateField K Kbar)))) w
    refine ⟨⊥, inferInstance, (Scheme.Modules.pullback q).obj 𝓛j, h𝓛j.pullback q, ?_⟩
    intro cX h1 h2
    have h1' : (cX ≫ q) ≫ pullback.fst _ _ = pullback.fst _ _ := by rw [Category.assoc, pullback.lift_fst, h1]
    have h2' : (cX ≫ q) ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (FDStages19.g K Kbar none)) := by
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, h2, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    obtain ⟨e⟩ := hcmp (cX ≫ q) h1' h2'
    exact ⟨(Scheme.Modules.pullbackComp cX q).app 𝓛j ≪≫ e⟩

end
end S_AlgebraicGeometry_Scheme_Modules_exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_intermediateField_isInvertible_nonempty_pullback_iso_of_isAlgebraic (solution)
