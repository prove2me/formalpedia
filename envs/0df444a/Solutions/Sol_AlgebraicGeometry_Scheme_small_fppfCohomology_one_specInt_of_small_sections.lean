-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.small_fppfCohomology_one_specInt_of_small_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5fcf5cf7-3306-50e6-9184-2ad31771265e

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Theorems.Thm_CategoryTheory_Sheaf_preservesInjectiveObjects_sheafCompose_uliftFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

universe u

open CategoryTheory CategoryTheory.Limits Opposite

universe w'

namespace RSmall

variable {C₀ : Type u} [SmallCategory C₀] (J₀ : GrothendieckTopology C₀)

noncomputable abbrev U : Sheaf J₀ AddCommGrpCat.{u} ⥤ Sheaf J₀ AddCommGrpCat.{u+1} :=
  sheafCompose J₀ AddCommGrpCat.uliftFunctor.{u+1, u}

example : (U J₀).Full := inferInstance
example : (U J₀).Faithful := inferInstance

section S2

variable {J₀}
variable (X : C₀ᵒᵖ ⥤ AddCommGrpCat.{u+1}) [∀ c : C₀ᵒᵖ, Small.{u} (X.obj c)]

noncomputable def shrinkObj (c : C₀ᵒᵖ) : AddCommGrpCat.{u} := AddCommGrpCat.of (Shrink.{u} (X.obj c))

noncomputable def shrinkEquiv (c : C₀ᵒᵖ) : X.obj c ≃+ Shrink.{u} (X.obj c) := Shrink.addEquiv.symm

noncomputable def shrinkPresheaf : C₀ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj c := AddCommGrpCat.of (Shrink.{u} (X.obj c))
  map {c c'} f := AddCommGrpCat.ofHom
    ((shrinkEquiv X c').toAddMonoidHom.comp ((X.map f).hom.comp (shrinkEquiv X c).symm.toAddMonoidHom))
  map_id c := by ext x; simp
  map_comp f g := by ext x; simp

noncomputable def shrinkPresheafIso : shrinkPresheaf X ⋙ AddCommGrpCat.uliftFunctor.{u+1, u} ≅ X :=
  NatIso.ofComponents
    (fun c => AddEquiv.toAddCommGrpIso
      ((AddEquiv.ulift.trans (shrinkEquiv X c).symm) : ULift.{u+1} (Shrink.{u} (X.obj c)) ≃+ X.obj c))
    (by
      intro c c' f
      ext x
      show (shrinkEquiv X c').symm (AddEquiv.ulift.{u, u+1} ((AddEquiv.ulift.{u, u+1}).symm
          (shrinkEquiv X c' ((X.map f) ((shrinkEquiv X c).symm (AddEquiv.ulift.{u, u+1} x))))))
        = (X.map f) ((shrinkEquiv X c).symm (AddEquiv.ulift.{u, u+1} x))
      rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply])

theorem isSheaf_shrinkPresheaf (hX : Presheaf.IsSheaf J₀ X) : Presheaf.IsSheaf J₀ (shrinkPresheaf X) := by
  rw [Presheaf.isSheaf_iff_isSheaf_comp (s := AddCommGrpCat.uliftFunctor.{u+1, u}),
    Presheaf.isSheaf_of_iso_iff (shrinkPresheafIso X)]
  exact hX

end S2

theorem exists_iso_U_obj_of_small_sections (X : Sheaf J₀ AddCommGrpCat.{u+1})
    [∀ c : C₀ᵒᵖ, Small.{u} (X.1.obj c)] :
    ∃ X₀ : Sheaf J₀ AddCommGrpCat.{u}, Nonempty ((U J₀).obj X₀ ≅ X) :=
  ⟨⟨shrinkPresheaf X.1, isSheaf_shrinkPresheaf X.1 X.2⟩,
    ⟨(sheafToPresheaf J₀ _).preimageIso (shrinkPresheafIso X.1)⟩⟩

section S3

variable {D : Type*} [Category D] [Abelian D] [HasExt.{w'} D]
variable (Φ : Sheaf J₀ AddCommGrpCat.{u} ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [Φ.Full] [Φ.Faithful] [Φ.PreservesInjectiveObjects]

example : HasSheafify J₀ AddCommGrpCat.{u} := inferInstance
example : IsGrothendieckAbelian.{u} (Sheaf J₀ AddCommGrpCat.{u}) := inferInstance

theorem small_ext_obj (X₀ Y₀ : Sheaf J₀ AddCommGrpCat.{u}) (n : ℕ) :
    Small.{u} (Abelian.Ext.{w'} (Φ.obj X₀) (Φ.obj Y₀) n) := by
  have hb := Functor.mapExt_bijective_of_preservesInjectiveObjects (F := Φ) X₀ Y₀ n
  exact small_of_surjective hb.2

end S3

section ExtIso

p2m_open "CategoryTheory.Abelian"

variable {D : Type*} [Category D] [Abelian D] [HasExt.{w'} D]

theorem small_ext_of_iso {A A' B B' : D} (eA : A ≅ A') (eB : B ≅ B') (n : ℕ)
    (hs : Small.{u} (Ext.{w'} A B n)) : Small.{u} (Ext.{w'} A' B' n) := by
  haveI := hs
  let φ : Ext.{w'} A B n → Ext.{w'} A' B' n :=
    fun α => (Ext.mk₀ eA.inv).comp (α.comp (Ext.mk₀ eB.hom) (add_zero n)) (zero_add n)
  refine small_of_surjective (f := φ) ?_
  intro β
  refine ⟨(Ext.mk₀ eA.hom).comp (β.comp (Ext.mk₀ eB.inv) (add_zero n)) (zero_add n), ?_⟩
  simp only [φ]
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    eB.inv_hom_id, Ext.comp_mk₀_id, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    eA.inv_hom_id, Ext.mk₀_id_comp]

end ExtIso

section Const

variable [HasWeakSheafify J₀ AddCommGrpCat.{u+1}]
  [J₀.PreservesSheafification AddCommGrpCat.uliftFunctor.{u+1, u}]

def uliftULiftIntIso :
    AddCommGrpCat.uliftFunctor.{u+1, u}.obj (AddCommGrpCat.of (ULift.{u} ℤ)) ≅ AddCommGrpCat.of (ULift.{u+1} ℤ) :=
  AddEquiv.toAddCommGrpIso
    ((AddEquiv.ulift.trans (AddEquiv.ulift.trans AddEquiv.ulift.symm))
      : ULift.{u+1} (ULift.{u} ℤ) ≃+ ULift.{u+1} ℤ)

noncomputable def U_constantSheaf_iso :
    (U J₀).obj ((constantSheaf J₀ AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf J₀ AddCommGrpCat.{u+1}).obj (AddCommGrpCat.of (ULift.{u+1} ℤ)) :=
  (constantCommuteCompose J₀ AddCommGrpCat.uliftFunctor.{u+1, u}).app (AddCommGrpCat.of (ULift.{u} ℤ)) ≪≫
    (constantSheaf J₀ AddCommGrpCat.{u+1}).mapIso uliftULiftIntIso

end Const

section Exact

variable [HasWeakSheafify J₀ AddCommGrpCat.{u+1}]
  [J₀.PreservesSheafification AddCommGrpCat.uliftFunctor.{u+1, u}]

noncomputable def U_comp_sheafToPresheaf_iso :
    U J₀ ⋙ sheafToPresheaf J₀ AddCommGrpCat.{u+1} ≅
      sheafToPresheaf J₀ AddCommGrpCat.{u} ⋙
        (Functor.whiskeringRight C₀ᵒᵖ _ _).obj AddCommGrpCat.uliftFunctor.{u+1, u} :=
  NatIso.ofComponents (fun _ => Iso.refl _)

scoped instance U_preservesLimitsOfShape (K : Type u) [SmallCategory K] : PreservesLimitsOfShape K (U J₀) := by
  haveI : PreservesLimitsOfShape K (U J₀ ⋙ sheafToPresheaf J₀ AddCommGrpCat.{u+1}) :=
    preservesLimitsOfShape_of_natIso (U_comp_sheafToPresheaf_iso J₀).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves (U J₀) (sheafToPresheaf J₀ AddCommGrpCat.{u+1})

noncomputable scoped instance U_preservesFiniteLimits : PreservesFiniteLimits (U J₀) where
  preservesFiniteLimits K _ _ := by
    haveI : PreservesLimitsOfShape (ULiftHom.{u} (ULift.{u} K)) (U J₀) := inferInstance
    exact preservesLimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv.{u, u} K).symm (U J₀)

scoped instance U_preservesColimitsOfShape (K : Type u) [SmallCategory K] : PreservesColimitsOfShape K (U J₀) := by
  rw [(sheafificationAdjunction J₀ AddCommGrpCat.{u}).preservesColimitsOfShape_iff]
  exact preservesColimitsOfShape_of_natIso
    (sheafComposeNatIso J₀ AddCommGrpCat.uliftFunctor.{u+1, u}
      (sheafificationAdjunction J₀ AddCommGrpCat.{u}) (sheafificationAdjunction J₀ AddCommGrpCat.{u+1}))

noncomputable scoped instance U_preservesFiniteColimits : PreservesFiniteColimits (U J₀) where
  preservesFiniteColimits K _ _ := by
    haveI : PreservesColimitsOfShape (ULiftHom.{u} (ULift.{u} K)) (U J₀) := inferInstance
    exact preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv.{u, u} K).symm (U J₀)

scoped instance U_additive : (U J₀).Additive where
  map_add := by intros; rfl

end Exact

section Composite

variable [HasSheafify J₀ AddCommGrpCat.{u+1}]
  [J₀.PreservesSheafification AddCommGrpCat.uliftFunctor.{u+1, u}]
  {D : Type*} [Category D] [Abelian D] (E : Sheaf J₀ AddCommGrpCat.{u+1} ≌ D)

noncomputable abbrev Φ : Sheaf J₀ AddCommGrpCat.{u} ⥤ D := U J₀ ⋙ E.functor

scoped instance Φ_full : (Φ J₀ E).Full := Functor.Full.comp _ _
scoped instance Φ_faithful : (Φ J₀ E).Faithful := Functor.Faithful.comp _ _

scoped instance E_functor_additive : E.functor.Additive := Functor.additive_of_preserves_binary_products _

scoped instance Φ_additive : (Φ J₀ E).Additive := inferInstance

noncomputable scoped instance Φ_preservesFiniteLimits : PreservesFiniteLimits (Φ J₀ E) := comp_preservesFiniteLimits _ _
noncomputable scoped instance Φ_preservesFiniteColimits : PreservesFiniteColimits (Φ J₀ E) := comp_preservesFiniteColimits _ _

scoped instance Φ_preservesInjectiveObjects
    [(sheafCompose J₀ (AddCommGrpCat.uliftFunctor.{u+1,u})).PreservesInjectiveObjects] :
    (Φ J₀ E).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_comp _ _

theorem small_ext_Φ [HasExt.{w'} D]
    [(sheafCompose J₀ (AddCommGrpCat.uliftFunctor.{u+1,u})).PreservesInjectiveObjects]
    (X₀ Y₀ : Sheaf J₀ AddCommGrpCat.{u}) (n : ℕ) :
    Small.{u} (Abelian.Ext.{w'} ((Φ J₀ E).obj X₀) ((Φ J₀ E).obj Y₀) n) :=
  small_ext_obj J₀ (Φ J₀ E) X₀ Y₀ n

theorem small_ext_const_of_small_sections [HasExt.{w'} D]
    [(sheafCompose J₀ (AddCommGrpCat.uliftFunctor.{u+1,u})).PreservesInjectiveObjects]
    (X : Sheaf J₀ AddCommGrpCat.{u+1}) [∀ c : C₀ᵒᵖ, Small.{u} (X.1.obj c)] (n : ℕ) :
    Small.{u} (Abelian.Ext.{w'}
      (E.functor.obj ((constantSheaf J₀ AddCommGrpCat.{u+1}).obj (AddCommGrpCat.of (ULift.{u+1} ℤ))))
      (E.functor.obj X) n) := by
  obtain ⟨X₀, ⟨i⟩⟩ := exists_iso_U_obj_of_small_sections J₀ X
  exact small_ext_of_iso (E.functor.mapIso (U_constantSheaf_iso J₀)) (E.functor.mapIso i) n
    (small_ext_Φ J₀ E ((constantSheaf J₀ AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) X₀ n)

end Composite

section Dense

variable {C₁ : Type*} [Category C₁] {D₁ : Type*} [Category D₁]
  (J₁ : GrothendieckTopology C₁) (K₁ : GrothendieckTopology D₁) (G : C₁ ⥤ D₁)
  [G.IsDenseSubsite J₁ K₁]
  [∀ X : D₁ᵒᵖ, HasLimitsOfShape (StructuredArrow X G.op) AddCommGrpCat.{u+1}]

scoped instance small_sections_sheafEquiv_inverse (F : Sheaf K₁ AddCommGrpCat.{u+1}) (c : C₁ᵒᵖ)
    [Small.{u} (F.1.obj (G.op.obj c))] :
    Small.{u} (((Functor.IsDenseSubsite.sheafEquiv J₁ K₁ G AddCommGrpCat.{u+1}).inverse.obj F).1.obj c) :=
  inferInstanceAs (Small.{u} (F.1.obj (G.op.obj c)))

variable [HasWeakSheafify J₁ AddCommGrpCat.{u+1}] [HasWeakSheafify K₁ AddCommGrpCat.{u+1}]

noncomputable def sheafEquiv_functor_constantSheaf_iso {T : C₁} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T))
    (M : AddCommGrpCat.{u+1}) :
    (Functor.IsDenseSubsite.sheafEquiv J₁ K₁ G AddCommGrpCat.{u+1}).functor.obj
        ((constantSheaf J₁ AddCommGrpCat.{u+1}).obj M) ≅
      (constantSheaf K₁ AddCommGrpCat.{u+1}).obj M :=
  (equivCommuteConstant J₁ AddCommGrpCat.{u+1} K₁ G hT hT').app M

end Dense

section Engine

variable [HasSheafify J₀ AddCommGrpCat.{u+1}]
  [J₀.PreservesSheafification AddCommGrpCat.uliftFunctor.{u+1, u}]
  {D : Type*} [Category D] [Abelian D] (E : Sheaf J₀ AddCommGrpCat.{u+1} ≌ D)

theorem small_ext_of_small_sections' [HasExt.{w'} D]
    [(sheafCompose J₀ (AddCommGrpCat.uliftFunctor.{u+1,u})).PreservesInjectiveObjects]
    (X : Sheaf J₀ AddCommGrpCat.{u+1}) [∀ c : C₀ᵒᵖ, Small.{u} (X.1.obj c)]
    {Z' X' : D}
    (eZ : E.functor.obj ((constantSheaf J₀ AddCommGrpCat.{u+1}).obj (AddCommGrpCat.of (ULift.{u+1} ℤ))) ≅ Z')
    (eX : E.functor.obj X ≅ X') (n : ℕ) :
    Small.{u} (Abelian.Ext.{w'} Z' X' n) :=
  small_ext_of_iso eZ eX n (small_ext_const_of_small_sections J₀ E X n)

end Engine

end RSmall
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall"

p2m_open "CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.MorphismProperty"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Spec Spec.map Scheme essentiallySmall_costructuredArrow_Spec IsOpenImmersion Spec.map_injective Flat Spec.preimage Scheme.Spec LocallyOfFinitePresentation Scheme.AffineEtale"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget Hom overGrothendieckTopology precoverage affineCover mem_overGrothendieckTopology isCoverDense_toOver_Spec Hom.ext affineOverMk AffineEtale Cover Cover.Over fppfProperty Fppf smallFppfTopology fppfTerminalIsTerminal fppfCohomology specInt"
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {S : Scheme.{u}}

theorem fppfProperty_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : fppfProperty f) (hg : fppfProperty g) : fppfProperty (f ≫ g) := by
  obtain ⟨hf1, hf2⟩ := hf; obtain ⟨hg1, hg2⟩ := hg
  haveI : Flat f := hf1; haveI : Flat g := hg1
  haveI : LocallyOfFinitePresentation f := hf2; haveI : LocallyOfFinitePresentation g := hg2
  exact ⟨inferInstance, inferInstance⟩

theorem fppfProperty_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    fppfProperty f :=
  ⟨inferInstance, inferInstance⟩

private def _root_.AlgebraicGeometry.Scheme.AffineFppf (S : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.CostructuredArrow fppfProperty.{u} ⊤ Scheme.Spec.{u} S

p2m_export "AlgebraicGeometry.Scheme" "AffineFppf"
noncomputable scoped instance : Category S.AffineFppf :=
  inferInstanceAs <| Category (MorphismProperty.CostructuredArrow fppfProperty.{u} ⊤ Scheme.Spec.{u} S)

namespace AffineFppf

@[simps! obj_left obj_hom map_left]
private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.Spec (S : Scheme.{u}) : S.AffineFppf ⥤ S.Fppf :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

scoped instance : (AffineFppf.Spec S).Faithful :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

scoped instance : (AffineFppf.Spec S).Full :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Full

scoped instance : (AffineFppf.Spec S).IsCoverDense (smallFppfTopology S) where
  is_cover U := by
    refine (Functor.mem_restrictedTopology_iff (G := MorphismProperty.Over.forget fppfProperty ⊤ S)
      (K := S.overGrothendieckTopology fppfProperty)).mpr ?_
    rw [mem_overGrothendieckTopology]
    let 𝒰 : Cover.{u} (precoverage fppfProperty) U.left :=
      U.left.affineCover.changeProp (fun j ↦ fppfProperty_of_isOpenImmersion _)
    letI (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ U.hom⟩
    letI h𝒰 : Cover.Over S 𝒰 := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰, h𝒰, ?_⟩
    rintro - - ⟨i⟩

    let a : S.AffineFppf := affineOverMk (𝒰.f i ≫ U.hom) (fppfProperty_comp _ _ (𝒰.map_prop i) U.prop)
    let g : (AffineFppf.Spec S).obj a ⟶ U := MorphismProperty.Over.homMk (𝒰.f i) (by simp [a]; rfl) trivial
    have hg : Sieve.coverByImage (AffineFppf.Spec S) U g :=
      ⟨⟨a, 𝟙 _, g, by simp⟩⟩
    refine ⟨(AffineFppf.Spec S).obj a, g, 𝟙 _, hg, ?_⟩
    ext : 1
    simp [g]
    exact (Category.id_comp _).symm

variable (S) in

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.topology : GrothendieckTopology S.AffineFppf :=
  (AffineFppf.Spec S).inducedTopology (smallFppfTopology S)

p2m_export "AlgebraicGeometry.Scheme.AffineFppf" "topology"
scoped instance : Functor.IsDenseSubsite (topology S) (smallFppfTopology S) (AffineFppf.Spec S) := by
  dsimp [topology]
  infer_instance

scoped instance : EssentiallySmall.{u} S.AffineFppf :=
  essentiallySmall_costructuredArrow_Spec _ (fun _ _ f hf ↦ by
    haveI : LocallyOfFinitePresentation f := hf.2
    infer_instance)

end AffineFppf
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf"

namespace AffineFppf

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.sheafEquiv (S : Scheme.{u}) :
    Sheaf (AffineFppf.topology S) Ab.{u + 1} ≌ Sheaf (smallFppfTopology S) Ab.{u + 1} :=
  (AffineFppf.Spec S).sheafInducedTopologyEquivOfIsCoverDense (smallFppfTopology S) Ab.{u + 1}

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.sheafEquiv"
namespace AffineFppf

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.smallSite (S : Scheme.{u}) : Type u := SmallModel.{u} S.AffineFppf

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.smallSite"
noncomputable scoped instance (S : Scheme.{u}) : SmallCategory (AffineFppf.smallSite S) :=
  inferInstanceAs <| SmallCategory (SmallModel.{u} S.AffineFppf)

namespace AffineFppf

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.smallSiteEquiv (S : Scheme.{u}) : S.AffineFppf ≌ AffineFppf.smallSite S :=
  equivSmallModel.{u} S.AffineFppf

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.smallSiteEquiv"
namespace AffineFppf

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.smallTopology (S : Scheme.{u}) : GrothendieckTopology (AffineFppf.smallSite S) :=
  (AffineFppf.smallSiteEquiv S).inverse.inducedTopology (AffineFppf.topology S)

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.smallTopology"
namespace AffineFppf

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.smallSheafEquiv (S : Scheme.{u}) :
    Sheaf (AffineFppf.smallTopology S) Ab.{u + 1} ≌ Sheaf (AffineFppf.topology S) Ab.{u + 1} :=
  (AffineFppf.smallSiteEquiv S).inverse.sheafInducedTopologyEquivOfIsCoverDense (AffineFppf.topology S) Ab.{u + 1}

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.smallSheafEquiv"

noncomputable def smallFppfSheafEquiv (S : Scheme.{u}) :
    Sheaf (AffineFppf.smallTopology S) Ab.{u + 1} ≌ Sheaf (smallFppfTopology S) Ab.{u + 1} :=
  (AffineFppf.smallSheafEquiv S).trans (AffineFppf.sheafEquiv S)

example (S : Scheme.{u}) : IsGrothendieckAbelian.{u} (Sheaf (AffineFppf.smallTopology S) Ab.{u}) :=
  inferInstance

end AlgebraicGeometry.Scheme
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Spec Spec.map Scheme essentiallySmall_costructuredArrow_Spec IsOpenImmersion Spec.map_injective Flat Spec.preimage Scheme.Spec LocallyOfFinitePresentation Scheme.AffineEtale"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget Hom overGrothendieckTopology precoverage affineCover mem_overGrothendieckTopology isCoverDense_toOver_Spec Hom.ext affineOverMk AffineEtale Cover Cover.Over fppfProperty Fppf smallFppfTopology fppfTerminalIsTerminal fppfCohomology specInt"
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"
variable (S : Scheme.{u})

namespace AffineFppf
private noncomputable scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.hasSheafify_ab : HasSheafify (AffineFppf.topology S) Ab.{u + 1} := inferInstance

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.hasSheafify_ab"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.isDenseSubsite_symm_inverse :
    (AffineFppf.smallSiteEquiv S).symm.inverse.IsDenseSubsite (AffineFppf.topology S) (AffineFppf.smallTopology S) :=
  inferInstanceAs <| (AffineFppf.smallSiteEquiv S).functor.IsDenseSubsite (AffineFppf.topology S)
    ((AffineFppf.smallSiteEquiv S).inverse.inducedTopology (AffineFppf.topology S))

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.isDenseSubsite_symm_inverse"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.isDenseSubsite_functor :
    (AffineFppf.smallSiteEquiv S).functor.IsDenseSubsite (AffineFppf.topology S) (AffineFppf.smallTopology S) :=
  inferInstanceAs <| (AffineFppf.smallSiteEquiv S).functor.IsDenseSubsite (AffineFppf.topology S)
    ((AffineFppf.smallSiteEquiv S).inverse.inducedTopology (AffineFppf.topology S))

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.isDenseSubsite_functor"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.isContinuous_functor :
    (AffineFppf.smallSiteEquiv S).functor.IsContinuous (AffineFppf.topology S) (AffineFppf.smallTopology S) :=
  inferInstance

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.isContinuous_functor"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.isCocontinuous_functor :
    (AffineFppf.smallSiteEquiv S).functor.IsCocontinuous (AffineFppf.topology S) (AffineFppf.smallTopology S) :=
  inferInstance

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.isCocontinuous_functor"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
namespace AffineFppf
private noncomputable scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.hasSheafify_small_ab : HasSheafify (AffineFppf.smallTopology S) Ab.{u + 1} :=
  Equivalence.hasSheafify (AffineFppf.smallTopology S) (AffineFppf.topology S) (AffineFppf.smallSiteEquiv S).symm Ab.{u + 1}

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.hasSheafify_small_ab"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
noncomputable example : Abelian (Sheaf (AffineFppf.smallTopology S) Ab.{u + 1}) := inferInstance

namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.wEqualsLocallyBijective_ab :
    (AffineFppf.topology S).WEqualsLocallyBijective Ab.{u + 1} := inferInstance

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.wEqualsLocallyBijective_ab"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.wEqualsLocallyBijective_small_ab0 :
    (AffineFppf.smallTopology S).WEqualsLocallyBijective Ab.{u} := inferInstance

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.wEqualsLocallyBijective_small_ab0"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.wEqualsLocallyBijective_small_ab :
    (AffineFppf.smallTopology S).WEqualsLocallyBijective Ab.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.transport (A := Ab.{u + 1})
    (AffineFppf.smallTopology S) (AffineFppf.topology S) (AffineFppf.smallSiteEquiv S).functor
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.wEqualsLocallyBijective_small_ab"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
end AlgebraicGeometry.Scheme
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Spec Spec.map Scheme essentiallySmall_costructuredArrow_Spec IsOpenImmersion Spec.map_injective Flat Spec.preimage Scheme.Spec LocallyOfFinitePresentation Scheme.AffineEtale"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget Hom overGrothendieckTopology precoverage affineCover mem_overGrothendieckTopology isCoverDense_toOver_Spec Hom.ext affineOverMk AffineEtale Cover Cover.Over fppfProperty Fppf smallFppfTopology fppfTerminalIsTerminal fppfCohomology specInt"
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"
variable (S : Scheme.{u})
p2m_open "CategoryTheory CategoryTheory.Presheaf CategoryTheory.GrothendieckTopology"

section
variable {C₀ : Type u} [SmallCategory C₀] (J₀ : GrothendieckTopology C₀)

theorem isLocallyInjective_whiskerRight_ulift {P Q : C₀ᵒᵖ ⥤ Ab.{u}} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J₀ f] :
    Presheaf.IsLocallyInjective J₀ (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1, u}) where
  equalizerSieve_mem {X} x y h := by
    have h' : f.app X x.down = f.app X y.down := by
      have := congrArg ULift.down h
      exact this
    have hm := Presheaf.equalizerSieve_mem J₀ f x.down y.down h'
    refine J₀.superset_covering ?_ hm
    intro Y g hg

    change (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map g.op x = (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map g.op y
    apply ULift.ext
    exact hg

theorem isLocallySurjective_whiskerRight_ulift {P Q : C₀ᵒᵖ ⥤ Ab.{u}} (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J₀ f] :
    Presheaf.IsLocallySurjective J₀ (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1, u}) where
  imageSieve_mem {X} y := by
    have hm := Presheaf.imageSieve_mem J₀ f y.down
    refine J₀.superset_covering ?_ hm
    intro Y g hg
    obtain ⟨x, hx⟩ := hg
    exact ⟨ULift.up x, by apply ULift.ext; exact hx⟩

theorem preservesSheafification_ulift [J₀.WEqualsLocallyBijective Ab.{u}] [J₀.WEqualsLocallyBijective Ab.{u + 1}] :
    J₀.PreservesSheafification AddCommGrpCat.uliftFunctor.{u + 1, u} where
  le P Q f hf := by
    rw [MorphismProperty.inverseImage_iff]
    change J₀.W (Functor.whiskerRight f _)
    rw [J₀.W_iff_isLocallyBijective] at hf ⊢
    obtain ⟨h1, h2⟩ := hf
    exact ⟨isLocallyInjective_whiskerRight_ulift J₀ f, isLocallySurjective_whiskerRight_ulift J₀ f⟩

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"

namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.preservesSheafification_small_ulift :
    (AffineFppf.smallTopology S).PreservesSheafification AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  preservesSheafification_ulift _

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.preservesSheafification_small_ulift"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
end AlgebraicGeometry.Scheme
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Spec Spec.map Scheme essentiallySmall_costructuredArrow_Spec IsOpenImmersion Spec.map_injective Flat Spec.preimage Scheme.Spec LocallyOfFinitePresentation Scheme.AffineEtale"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget Hom overGrothendieckTopology precoverage affineCover mem_overGrothendieckTopology isCoverDense_toOver_Spec Hom.ext affineOverMk AffineEtale Cover Cover.Over fppfProperty Fppf smallFppfTopology fppfTerminalIsTerminal fppfCohomology specInt"
namespace AffineFppf
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.MorphismProperty"

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.idObj (R : CommRingCat.{u}) : (Spec R).AffineFppf :=
  affineOverMk (P := fppfProperty) (𝟙 (Spec R)) (fppfProperty.id_mem _)

p2m_export "AlgebraicGeometry.Scheme.AffineFppf" "idObj"

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.idObjIsTerminal (R : CommRingCat.{u}) : IsTerminal (idObj R) :=
  IsTerminal.ofUniqueHom
    (fun Y => CostructuredArrow.homMk (Scheme.Spec.preimage Y.hom) trivial
      (by rw [Functor.map_preimage]; exact Category.comp_id _))
    (fun Y g => by
      apply MorphismProperty.CostructuredArrow.Hom.ext
      show g.left = Scheme.Spec.preimage Y.hom
      apply Scheme.Spec.map_injective
      have h : Scheme.Spec.map g.left ≫ 𝟙 (Spec R) = Y.hom := CostructuredArrow.w g.hom
      exact ((Category.comp_id _).symm.trans h).trans (Scheme.Spec.map_preimage Y.hom).symm)

p2m_export "AlgebraicGeometry.Scheme.AffineFppf" "idObjIsTerminal"

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.specIdObjIsTerminal (R : CommRingCat.{u}) :
    IsTerminal ((AffineFppf.Spec (Spec R)).obj (idObj R)) :=
  fppfTerminalIsTerminal (Spec R)

p2m_export "AlgebraicGeometry.Scheme.AffineFppf" "specIdObjIsTerminal"

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.isTerminal_functor_obj {C : Type*} [Category C] {C' : Type*} [Category C'] (e : C ≌ C')
    {T : C} (hT : IsTerminal T) : IsTerminal (e.functor.obj T) :=
  hT.isTerminalObj e.functor

p2m_export "AlgebraicGeometry.Scheme.AffineFppf" "isTerminal_functor_obj"

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.isTerminal_inverse_functor_obj {C : Type*} [Category C] {C' : Type*} [Category C']
    (e : C ≌ C') {T : C} (hT : IsTerminal T) : IsTerminal (e.inverse.obj (e.functor.obj T)) :=
  hT.ofIso (e.unitIso.app T)

p2m_export "AlgebraicGeometry.Scheme.AffineFppf" "isTerminal_inverse_functor_obj"

private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.smallIdObjIsTerminal (R : CommRingCat.{u}) :
    IsTerminal ((AffineFppf.smallSiteEquiv (Spec R)).functor.obj (idObj R)) :=
  isTerminal_functor_obj _ (idObjIsTerminal R)

p2m_export "AlgebraicGeometry.Scheme.AffineFppf" "smallIdObjIsTerminal"
private noncomputable def _root_.AlgebraicGeometry.Scheme.AffineFppf.inverseSmallIdObjIsTerminal (R : CommRingCat.{u}) :
    IsTerminal ((AffineFppf.smallSiteEquiv (Spec R)).inverse.obj
      ((AffineFppf.smallSiteEquiv (Spec R)).functor.obj (idObj R))) :=
  isTerminal_inverse_functor_obj _ (idObjIsTerminal R)

p2m_export "AlgebraicGeometry.Scheme.AffineFppf" "inverseSmallIdObjIsTerminal"
end AlgebraicGeometry.Scheme.AffineFppf
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Spec Spec.map Scheme essentiallySmall_costructuredArrow_Spec IsOpenImmersion Spec.map_injective Flat Spec.preimage Scheme.Spec LocallyOfFinitePresentation Scheme.AffineEtale"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget Hom overGrothendieckTopology precoverage affineCover mem_overGrothendieckTopology isCoverDense_toOver_Spec Hom.ext affineOverMk AffineEtale Cover Cover.Over fppfProperty Fppf smallFppfTopology fppfTerminalIsTerminal fppfCohomology specInt"
p2m_open "AlgebraicGeometry.Scheme AlgebraicGeometry"
open RSmall

namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.isDenseSubsite_inverse (S : Scheme.{u}) :
    (AffineFppf.smallSiteEquiv S).inverse.IsDenseSubsite (AffineFppf.smallTopology S) (AffineFppf.topology S) := by
  dsimp only [AffineFppf.smallTopology]
  infer_instance

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.isDenseSubsite_inverse"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
namespace AffineFppf
private scoped instance _root_.AlgebraicGeometry.Scheme.AffineFppf.isDenseSubsite_Spec (S : Scheme.{u}) :
    (AffineFppf.Spec S).IsDenseSubsite (AffineFppf.topology S) (smallFppfTopology S) := by
  dsimp only [AffineFppf.topology]
  infer_instance

end AffineFppf
p2m_export "AlgebraicGeometry.Scheme" "AffineFppf.isDenseSubsite_Spec"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
end AlgebraicGeometry.Scheme
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme.AffineFppf P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme"

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections.RSmall"

theorem solution (F : Sheaf (smallFppfTopology specInt) Ab.{1})
    [∀ U : specInt.Fppf, Small.{0} (F.1.obj (op U))] :
    Small.{0} (fppfCohomology specInt F 1) := by

  let G₂ := AffineFppf.Spec specInt
  let e := AffineFppf.smallSiteEquiv specInt
  let G₁ := e.inverse
  let J₀ := AffineFppf.smallTopology specInt
  let E₁ := AffineFppf.smallSheafEquiv specInt
  let E₂ := AffineFppf.sheafEquiv specInt
  let E := E₁.trans E₂
  haveI : G₁.IsDenseSubsite J₀ (AffineFppf.topology specInt) :=
    inferInstanceAs ((AffineFppf.smallSiteEquiv specInt).inverse.IsDenseSubsite (AffineFppf.smallTopology specInt) (AffineFppf.topology specInt))
  haveI : G₂.IsDenseSubsite (AffineFppf.topology specInt) (smallFppfTopology specInt) :=
    inferInstanceAs ((AffineFppf.Spec specInt).IsDenseSubsite (AffineFppf.topology specInt) (smallFppfTopology specInt))

  haveI : ∀ c : (specInt.AffineFppf)ᵒᵖ, Small.{0} ((E₂.inverse.obj F).1.obj c) := fun c =>
    RSmall.small_sections_sheafEquiv_inverse (AffineFppf.topology specInt) (smallFppfTopology specInt) G₂ F c
  haveI : ∀ c : (AffineFppf.smallSite specInt)ᵒᵖ, Small.{0} ((E₁.inverse.obj (E₂.inverse.obj F)).1.obj c) := fun c =>
    RSmall.small_sections_sheafEquiv_inverse J₀ (AffineFppf.topology specInt) G₁ (E₂.inverse.obj F) c

  let T : specInt.AffineFppf := AffineFppf.idObj (CommRingCat.of ℤ)
  have hT : IsTerminal T := AffineFppf.idObjIsTerminal (CommRingCat.of ℤ)
  have hT' : IsTerminal ((AffineFppf.Spec specInt).obj T) := AffineFppf.specIdObjIsTerminal (CommRingCat.of ℤ)
  have hT₁ : IsTerminal (e.functor.obj T) := hT.isTerminalObj e.functor
  have hT₁' : IsTerminal (G₁.obj (e.functor.obj T)) := (hT.ofIso (e.unitIso.app T))

  let M : Ab.{1} := AddCommGrpCat.of (ULift.{1} ℤ)
  let eZ₁ := RSmall.sheafEquiv_functor_constantSheaf_iso J₀ (AffineFppf.topology specInt) G₁ hT₁ hT₁' M
  let eZ₂ := RSmall.sheafEquiv_functor_constantSheaf_iso (AffineFppf.topology specInt) (smallFppfTopology specInt) G₂ hT hT' M
  let eZ : E.functor.obj ((constantSheaf J₀ Ab.{1}).obj M) ≅ (constantSheaf (smallFppfTopology specInt) Ab.{1}).obj M :=
    (E₂.functor.mapIso eZ₁).trans eZ₂
  haveI := CategoryTheory.Sheaf.preservesInjectiveObjects_sheafCompose_uliftFunctor J₀
  have h := RSmall.small_ext_of_small_sections' J₀ E (E₁.inverse.obj (E₂.inverse.obj F)) eZ
    (E.counitIso.app F) 1
  exact h

end S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections (solution)
