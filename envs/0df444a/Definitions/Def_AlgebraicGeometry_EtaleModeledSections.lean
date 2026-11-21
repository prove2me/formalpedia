-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleModeledSections
-- name    : AlgebraicGeometry_EtaleModeledSections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T03:05:35.585928+00:00
-- url     : https://prove2.me/theorems/315ab1f8-aa79-4eaf-bfb7-0dab59dfccc7
-- title:
--   Sections on étale charts over affine inverse limits
-- statement:
--   Descent of étale charts, finite coverings, and restriction maps to finite stages of an affine inverse limit.

import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSites

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)


namespace PhilipponEtaleLimitPresheaf

universe u

variable {Y Q Z : Scheme.{u}} (p : Q ⟶ Y) (t : Z ⟶ Q) [Etale t]

private abbrev T : Q.Etale := Scheme.Etale.mk t

private abbrev Comma := CostructuredArrow (baseChange p).op (op (T t))

private def sectionOfMap {V : Y.Etale} (a : Z ⟶ V.left) (ha : a ≫ V.hom = t ≫ p) :
    T t ⟶ (baseChange p).obj V :=
  MorphismProperty.Over.homMk
    (pullback.lift a t ha)
    (pullback.lift_snd ..) trivial

private theorem section_ext {V : Y.Etale} {a b : T t ⟶ (baseChange p).obj V}
    (h : a.left ≫ pullback.fst V.hom p = b.left ≫ pullback.fst V.hom p) : a = b :=
  MorphismProperty.Over.Hom.ext (pullback.hom_ext h
    ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm))

private theorem sectionOfMap_comp {U V : Y.Etale} (a : Z ⟶ U.left) (ha : a ≫ U.hom = t ≫ p)
    (g : U ⟶ V) :
    sectionOfMap p t a ha ≫ (baseChange p).map g =
      sectionOfMap p t (a ≫ g.left) (by rw [Category.assoc, MorphismProperty.Over.w g, ha]) := by
  apply section_ext p t
  change (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ =
    pullback.lift _ _ _ ≫ pullback.fst _ _
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]

variable {I : Type u} [Category.{u} I] (E : I ⥤ Y.Etale)

private abbrev underlying := E ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y

private def structuralMaps : underlying E ⟶ (Functor.const I).obj Y where
  app i := (E.obj i).hom
  naturality _ _ k :=
    (MorphismProperty.Over.w (E.map k)).trans (Category.comp_id _).symm

variable (c : Cone (underlying E)) (t : c.pt ⟶ Q) [Etale t]
  (hp : ∀ i, c.π.app i ≫ (E.obj i).hom = t ≫ p)

private abbrev stageSection (i : I) := sectionOfMap p t (c.π.app i) (hp i)

private theorem stageSection_w {i j : I} (k : i ⟶ j) :
    stageSection p E c t hp i ≫ (baseChange p).map (E.map k) = stageSection p E c t hp j := by
  rw [sectionOfMap_comp]
  have h : c.π.app i ≫ (E.map k).left = c.π.app j := c.w k
  simp only [h, stageSection]

/-- The functor from the inverse system to the indexing category for
presheaf inverse image at the étale object of the limit scheme. -/
def neighborhoodIndex : Iᵒᵖ ⥤ Comma p t where
  obj i := CostructuredArrow.mk (stageSection p E c t hp i.unop).op
  map k := CostructuredArrow.homMk (E.map k.unop).op
    (Quiver.Hom.unop_inj (stageSection_w p E c t hp k.unop))
  map_id i := by
    apply CostructuredArrow.hom_ext
    change (E.map (𝟙 i.unop)).op = 𝟙 _
    exact congrArg (fun a : E.obj i.unop ⟶ E.obj i.unop => a.op) (E.map_id i.unop)
  map_comp k l := by
    apply CostructuredArrow.hom_ext
    change (E.map (l.unop ≫ k.unop)).op = (E.map k.unop).op ≫ (E.map l.unop).op
    rw [Functor.map_comp, op_comp]

private theorem from_stage_comm {d : Comma p t} {i : Iᵒᵖ}
    (a : d ⟶ (neighborhoodIndex p E c t hp).obj i) :
    c.π.app i.unop ≫ a.left.unop.left = d.hom.unop.left ≫ pullback.fst d.left.unop.hom p := by
  let g : E.obj i.unop ⟶ d.left.unop := a.left.unop
  have h : stageSection p E c t hp i.unop ≫ (baseChange p).map g = d.hom.unop :=
    congrArg Quiver.Hom.unop (CostructuredArrow.w a)
  rw [sectionOfMap_comp] at h
  have h' := congrArg (fun m => m.left ≫ pullback.fst d.left.unop.hom p) h
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _ at h'
  rw [pullback.lift_fst] at h'
  exact h'

variable [IsCofiltered I] (hc : IsLimit c)
  [∀ i, CompactSpace ((underlying E).obj i)] [∀ i, QuasiSeparatedSpace ((underlying E).obj i)]
  [∀ {i j : I} (k : i ⟶ j), IsAffineHom ((underlying E).map k)]

include hc in
/-- Every map over the base from the inverse limit to an étale scheme
descends to some stage, and any two descents eventually agree. Consequently
the stages are final in the indexing category for presheaf inverse image. -/
theorem neighborhoodIndex_final : (neighborhoodIndex p E c t hp).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro d
    let V := d.left.unop
    let a : c.pt ⟶ V.left := d.hom.unop.left ≫ pullback.fst V.hom p
    have ha : a ≫ V.hom = t ≫ p := by
      dsimp only [a]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have h : d.hom.unop.left ≫ pullback.snd V.hom p = t :=
        MorphismProperty.Over.w d.hom.unop
      rw [h]
    have ht : c.π ≫ structuralMaps E = (Functor.const I).map (a ≫ V.hom) := by
      ext i
      exact (hp i).trans ha.symm
    obtain ⟨i, g, hg, hw⟩ :=
      Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (underlying E)
        (structuralMaps E) V.hom c hc a ht
    let b : E.obj i ⟶ V := MorphismProperty.Over.homMk g hw trivial
    refine ⟨op i, ⟨CostructuredArrow.homMk b.op ?_⟩⟩
    apply Quiver.Hom.unop_inj
    change stageSection p E c t hp i ≫ (baseChange p).map b = d.hom.unop
    rw [sectionOfMap_comp]
    apply section_ext p t
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = a
    rw [pullback.lift_fst]
    exact hg
  · intro d i a b
    let V := d.left.unop
    let i₀ := i.unop
    let h₁ : (underlying E).obj i₀ ⟶ V.left := a.left.unop.left
    let h₂ : (underlying E).obj i₀ ⟶ V.left := b.left.unop.left
    have hlim₁ : c.π.app i₀ ≫ h₁ = d.hom.unop.left ≫ pullback.fst V.hom p :=
      from_stage_comm p E c t hp a
    have hlim₂ : c.π.app i₀ ≫ h₂ = d.hom.unop.left ≫ pullback.fst V.hom p :=
      from_stage_comm p E c t hp b
    obtain ⟨j, k, h⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (underlying E)
      (structuralMaps E) V.hom c hc h₁ h₂
      (MorphismProperty.Over.w a.left.unop).symm (MorphismProperty.Over.w b.left.unop).symm
      (hlim₁.trans hlim₂.symm)
    refine ⟨op j, k.op, ?_⟩
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    exact h

include hc in
/-- A colimit of stage evaluations computes the pointwise inverse image
at an étale object presented as a limit of stage objects. -/
def pointwisePullbackCocone {B : Type*} [Category* B] (P : Y.Etaleᵒᵖ ⥤ B)
    (d : ColimitCocone (E.op ⋙ P)) :
    ColimitCocone (CostructuredArrow.proj (baseChange p).op (op (T t)) ⋙ P) := by
  let H := neighborhoodIndex p E c t hp
  let : H.Final := neighborhoodIndex_final p E c t hp hc
  exact Functor.Final.colimitCoconeOfComp H d

include hc in
/-- The comparison sends sections representing a colimit element to the
same section indexed by its pullback map from the limit chart. -/
theorem pointwisePullbackCocone_ι {B : Type*} [Category* B] (P : Y.Etaleᵒᵖ ⥤ B)
    (d : ColimitCocone (E.op ⋙ P)) (j : Iᵒᵖ) :
    (pointwisePullbackCocone p E c t hp hc P d).cocone.ι.app
      ((neighborhoodIndex p E c t hp).obj j) = d.cocone.ι.app j := by
  let H := neighborhoodIndex p E c t hp
  let : H.Final := neighborhoodIndex_final p E c t hp hc
  let G := CostructuredArrow.proj (baseChange p).op (op (T t)) ⋙ P
  let d' : Cocone (H ⋙ G) := d.cocone
  exact Functor.Final.colimit_cocone_comp_aux (F := H) d' j

include hc in
/-- Compare an arbitrary pointwise colimit cocone with the colimit over
the stages of an étale chart. -/
def stageColimitIso {B : Type*} [Category* B] (P : Y.Etaleᵒᵖ ⥤ B)
    [HasColimit (E.op ⋙ P)]
    (d : ColimitCocone (CostructuredArrow.proj (baseChange p).op (op (T t)) ⋙ P)) :
    colimit (E.op ⋙ P) ≅ d.cocone.pt := by
  let H := neighborhoodIndex p E c t hp
  let : H.Final := neighborhoodIndex_final p E c t hp hc
  exact (colimit.isColimit (E.op ⋙ P)).coconePointUniqueUpToIso
    ((Functor.Final.isColimitWhiskerEquiv H d.cocone).symm d.isColimit)

include hc in
@[reassoc]
theorem stageColimitIso_ι {B : Type*} [Category* B] (P : Y.Etaleᵒᵖ ⥤ B)
    [HasColimit (E.op ⋙ P)]
    (d : ColimitCocone (CostructuredArrow.proj (baseChange p).op (op (T t)) ⋙ P)) (j : Iᵒᵖ) :
    colimit.ι (E.op ⋙ P) j ≫ (stageColimitIso p E c t hp hc P d).hom =
      d.cocone.ι.app ((neighborhoodIndex p E c t hp).obj j) := by
  let H := neighborhoodIndex p E c t hp
  let : H.Final := neighborhoodIndex_final p E c t hp hc
  exact (colimit.isColimit (E.op ⋙ P)).comp_coconePointUniqueUpToIso_hom
    ((Functor.Final.isColimitWhiskerEquiv H d.cocone).symm d.isColimit) j

include hc in
/-- The pointwise presheaf inverse image at the specified étale object
of the limit scheme is the colimit of sections over the stages. -/
def colimitIsoOfPointwiseExtension {B : Type*} [Category* B]
    (P : Y.Etaleᵒᵖ ⥤ B) (P' : Q.Etaleᵒᵖ ⥤ B)
    [HasColimit (E.op ⋙ P)] (η : P ⟶ (baseChange p).op ⋙ P')
    (h : (Functor.LeftExtension.mk P' η).IsPointwiseLeftKanExtensionAt (op (T t))) :
    colimit (E.op ⋙ P) ≅ P'.obj (op (T t)) := by
  let H := neighborhoodIndex p E c t hp
  let : H.Final := neighborhoodIndex_final p E c t hp hc
  let hc' := (Functor.Final.isColimitWhiskerEquiv H _).symm h
  exact (colimit.isColimit (E.op ⋙ P)).coconePointUniqueUpToIso hc'

include hc in
@[reassoc]
theorem colimitIsoOfPointwiseExtension_ι {B : Type*} [Category* B]
    (P : Y.Etaleᵒᵖ ⥤ B) (P' : Q.Etaleᵒᵖ ⥤ B)
    [HasColimit (E.op ⋙ P)] (η : P ⟶ (baseChange p).op ⋙ P')
    (h : (Functor.LeftExtension.mk P' η).IsPointwiseLeftKanExtensionAt (op (T t))) (j : Iᵒᵖ) :
    colimit.ι (E.op ⋙ P) j ≫
        (colimitIsoOfPointwiseExtension p E c t hp hc P P' η h).hom =
      η.app (op (E.obj j.unop)) ≫ P'.map (stageSection p E c t hp j.unop).op := by
  let H := neighborhoodIndex p E c t hp
  let : H.Final := neighborhoodIndex_final p E c t hp hc
  let hc' := (Functor.Final.isColimitWhiskerEquiv H _).symm h
  exact (colimit.isColimit (E.op ⋙ P)).comp_coconePointUniqueUpToIso_hom hc' j

section Restriction

variable (E' : I ⥤ Y.Etale) (c' : Cone (underlying E')) (t' : c'.pt ⟶ Q) [Etale t']
  (hp' : ∀ i, c'.π.app i ≫ (E'.obj i).hom = t' ≫ p)
  (hc' : IsLimit c') [∀ i, CompactSpace ((underlying E').obj i)]
  [∀ i, QuasiSeparatedSpace ((underlying E').obj i)]
  [∀ {i j : I} (k : i ⟶ j), IsAffineHom ((underlying E').map k)]

include hc hc' in
/-- The stage colimit comparison respects the maps represented by stage
restrictions, using the colimit cocones on the two comma categories. -/
theorem stageColimitIso_naturality {B : Type*} [Category* B]
    (P : Y.Etaleᵒᵖ ⥤ B) [HasColimit (E.op ⋙ P)] [HasColimit (E'.op ⋙ P)]
    (μ : E ⟶ E') (a : T t ⟶ T t')
    (ha : ∀ j, c.π.app j ≫ (μ.app j).left = a.left ≫ c'.π.app j)
    (d : ColimitCocone (CostructuredArrow.proj (baseChange p).op (op (T t)) ⋙ P))
    (d' : ColimitCocone (CostructuredArrow.proj (baseChange p).op (op (T t')) ⋙ P))
    (r : d'.cocone.pt ⟶ d.cocone.pt)
    (hr : ∀ j, d'.cocone.ι.app j ≫ r = d.cocone.ι.app ((CostructuredArrow.map a.op).obj j)) :
    colimMap (Functor.whiskerRight (NatTrans.op μ) P) ≫
        (stageColimitIso p E c t hp hc P d).hom =
      (stageColimitIso p E' c' t' hp' hc' P d').hom ≫ r := by
  apply colimit.hom_ext
  intro j
  rw [ι_colimMap_assoc, stageColimitIso_ι, stageColimitIso_ι_assoc, hr]
  have hw : stageSection p E c t hp j.unop ≫ (baseChange p).map (μ.app j.unop) =
      a ≫ stageSection p E' c' t' hp' j.unop := by
    rw [sectionOfMap_comp]
    apply section_ext p t
    change pullback.lift _ _ _ ≫ pullback.fst _ _ =
      (a.left ≫ pullback.lift _ _ _) ≫ pullback.fst _ _
    simpa only [Category.assoc, pullback.lift_fst] using ha j.unop
  let l : (CostructuredArrow.map a.op).obj ((neighborhoodIndex p E' c' t' hp').obj j) ⟶
      ((neighborhoodIndex p E c t hp).obj j) := CostructuredArrow.homMk (μ.app j.unop).op (by
    apply Quiver.Hom.unop_inj
    exact hw)
  exact d.cocone.w l

include hc hc' in
/-- The comparison of sections with stage colimits respects restrictions
along morphisms that are represented by compatible maps at the stages. -/
theorem colimitIsoOfPointwiseExtension_naturality {B : Type*} [Category* B]
    (P : Y.Etaleᵒᵖ ⥤ B) (P' : Q.Etaleᵒᵖ ⥤ B)
    [HasColimit (E.op ⋙ P)] [HasColimit (E'.op ⋙ P)]
    (η : P ⟶ (baseChange p).op ⋙ P')
    (h : (Functor.LeftExtension.mk P' η).IsPointwiseLeftKanExtensionAt (op (T t)))
    (h' : (Functor.LeftExtension.mk P' η).IsPointwiseLeftKanExtensionAt (op (T t')))
    (μ : E ⟶ E') (a : T t ⟶ T t')
    (ha : ∀ j, c.π.app j ≫ (μ.app j).left = a.left ≫ c'.π.app j) :
    colimMap (Functor.whiskerRight (NatTrans.op μ) P) ≫
        (colimitIsoOfPointwiseExtension p E c t hp hc P P' η h).hom =
      (colimitIsoOfPointwiseExtension p E' c' t' hp' hc' P P' η h').hom ≫ P'.map a.op := by
  apply colimit.hom_ext
  intro j
  rw [ι_colimMap_assoc, colimitIsoOfPointwiseExtension_ι,
    colimitIsoOfPointwiseExtension_ι_assoc]
  have hw : stageSection p E c t hp j.unop ≫ (baseChange p).map (μ.app j.unop) =
      a ≫ stageSection p E' c' t' hp' j.unop := by
    rw [sectionOfMap_comp]
    apply section_ext p t
    change pullback.lift _ _ _ ≫ pullback.fst _ _ =
      (a.left ≫ pullback.lift _ _ _) ≫ pullback.fst _ _
    simpa only [Category.assoc, pullback.lift_fst] using ha j.unop
  have hn := η.naturality (μ.app j.unop).op
  change P.map (μ.app j.unop).op ≫ η.app (op (E.obj j.unop)) =
    η.app (op (E'.obj j.unop)) ≫ P'.map ((baseChange p).map (μ.app j.unop)).op at hn
  change P.map (μ.app j.unop).op ≫
      η.app (op (E.obj j.unop)) ≫ P'.map (stageSection p E c t hp j.unop).op =
    η.app (op (E'.obj j.unop)) ≫ P'.map (stageSection p E' c' t' hp' j.unop).op ≫ P'.map a.op
  rw [← Category.assoc, hn, Category.assoc]
  simp only [← P'.map_comp, ← op_comp, hw]

end Restriction

end PhilipponEtaleLimitPresheaf

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct


namespace PhilipponEtaleFilteredDescent

universe u v w

variable {J : Type w} [Category.{v} J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) {c : Cocone F} (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat.{u})]

include hc in
/-- Every étale algebra over a filtered colimit of rings is the base change
of an étale algebra over one of its stages. -/
theorem exists_etale_model (B : Type u) [CommRing B] [Algebra c.pt B] [Algebra.Etale c.pt B] :
    ∃ (i : J) (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (F.obj i) Bᵢ),
      Algebra.Etale (F.obj i) Bᵢ ∧
        letI : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
        Nonempty (c.pt ⊗[F.obj i] Bᵢ ≃ₐ[c.pt] B) := by
  let : Algebra (ULift.{u} ℤ) c.pt := ULift.algebra' ℤ c.pt
  obtain ⟨A₀, B₀, _, _, hfg, he, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg (ULift.{u} ℤ) c.pt B
  let Z := CommRingCat.of (ULift.{u} ℤ)
  let A := CommRingCat.of A₀
  let z : Z ⟶ A := CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A₀)
  let hZ : IsInitial Z := CommRingCat.isInitial
  let α : (Functor.const J).obj Z ⟶ F :=
    { app := fun i => hZ.to (F.obj i)
      naturality := fun _ _ _ => hZ.hom_ext _ _ }
  let k : A ⟶ c.pt := CommRingCat.ofHom A₀.val.toRingHom
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : Algebra.FiniteType (ULift.{u} ℤ) A₀ := A₀.fg_iff_finiteType.mp hfg
  have hz : z.hom.FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp inferInstance)
  obtain ⟨i, kᵢ, _, hi⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    Z F α z c hc hz k (fun i => hZ.hom_ext _ _)
  let : Algebra A₀ (F.obj i) := kᵢ.hom.toAlgebra
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  let : IsScalarTower A₀ (F.obj i) c.pt :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hi)
  let : Algebra.Etale A₀ B₀ := he
  refine ⟨i, (F.obj i) ⊗[A₀] B₀, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨(Algebra.TensorProduct.cancelBaseChange A₀ (F.obj i) c.pt c.pt B₀).trans e.symm⟩

include hc in
/-- An étale ring map with source the colimit is a pushout of an étale
ring map at a stage of the diagram. -/
theorem exists_etale_pushout {B : CommRingCat.{u}} (p : c.pt ⟶ B) (hp : p.hom.Etale) :
    ∃ (i : J) (Bᵢ : CommRingCat.{u}) (g : F.obj i ⟶ Bᵢ) (q : Bᵢ ⟶ B),
      g.hom.Etale ∧ IsPushout (c.ι.app i) g p q := by
  let : Algebra c.pt B := p.hom.toAlgebra
  let : Algebra.Etale c.pt B := RingHom.etale_algebraMap.mp hp
  obtain ⟨i, T, _, _, hT, h⟩ := exists_etale_model F hc B
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  obtain ⟨e⟩ := h
  let T' := CommRingCat.of T
  let g : F.obj i ⟶ T' := CommRingCat.ofHom (algebraMap (F.obj i) T)
  let e' := e.toRingEquiv.toCommRingCatIso
  let q : T' ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e'.hom
  have hleft : CommRingCat.ofHom (algebraMap c.pt (c.pt ⊗[F.obj i] T)) ≫ e'.hom = p := by
    apply ConcreteCategory.hom_ext
    intro x
    exact e.commutes x
  refine ⟨i, T', g, q, RingHom.etale_algebraMap.mpr hT, ?_⟩
  exact (CommRingCat.isPushout_tensorProduct (F.obj i) c.pt T).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e'
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
    (by rw [Iso.refl_hom, Category.id_comp]; exact hleft)
    (by rw [Iso.refl_hom, Category.id_comp])

end PhilipponEtaleFilteredDescent

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponEtaleAffineLimitDescent

universe u v w

variable {J : Type w} [Category.{v} J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) {c : Cocone F} (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat.{u})]

include hc in
/-- An affine étale scheme over the spectrum of a filtered colimit
descends, with its structure morphism, to an affine étale scheme at a stage. -/
theorem exists_affine_etale_model {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec c.pt) [Etale f] :
    ∃ (i : J) (Yᵢ : Scheme.{u}) (fᵢ : Yᵢ ⟶ Spec (F.obj i)) (g : Y ⟶ Yᵢ),
      IsAffine Yᵢ ∧ Etale fᵢ ∧ IsPullback f g (Spec.map (c.ι.app i)) fᵢ := by
  obtain ⟨p, hp⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ f)
  have hpEt : Etale (Spec.map p) := hp.symm ▸ (inferInstance : Etale (Y.isoSpec.inv ≫ f))
  obtain ⟨i, T, d, q, hd, h⟩ := PhilipponEtaleFilteredDescent.exists_etale_pushout F hc p
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hpEt)
  have hSpec : IsPullback (Spec.map p) (Spec.map q) (Spec.map (c.ι.app i)) (Spec.map d) :=
    h.op.flip.map Scheme.Spec
  refine ⟨i, Spec T, Spec.map d, Y.isoSpec.hom ≫ Spec.map q, inferInstance,
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hd, ?_⟩
  apply hSpec.of_iso Y.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa using hp
  · simp
  · simp
  · simp

end PhilipponEtaleAffineLimitDescent

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponEtaleCoverLimitDescent

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

include hc in
/-- A family of open maps whose pullbacks cover the inverse limit covers
after pulling back to some stage. -/
theorem exists_covering_stage [∀ i, CompactSpace (D.obj i)]
    [∀ {i j} (k : i ⟶ j), IsAffineHom (D.map k)]
    {i : I} {α : Type*} {V : α → Scheme.{u}} (g : ∀ a, V a ⟶ D.obj i)
    (hOpen : ∀ a, IsOpenMap (g a))
    (hCover : ∀ x : c.pt, ∃ a, x ∈ Set.range (pullback.fst (c.π.app i) (g a))) :
    ∃ (j : I) (k : j ⟶ i), ∀ x : D.obj j,
      ∃ a, x ∈ Set.range (pullback.fst (D.map k) (g a)) := by
  let U : (D.obj i).Opens :=
    ⟨⋃ a, Set.range (g a), isOpen_iUnion fun a => (hOpen a).isOpen_range⟩
  have hU : c.π.app i ⁻¹ᵁ U = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, ha⟩ := hCover x
    rw [Scheme.Pullback.range_fst] at ha
    exact Set.mem_iUnion.mpr ⟨a, ha⟩
  obtain ⟨j, k, hk⟩ := AlgebraicGeometry.exists_map_eq_top D c hc U hU
  refine ⟨j, k, fun x => ?_⟩
  have hx : x ∈ D.map k ⁻¹ᵁ U := hk.symm ▸ trivial
  change D.map k x ∈ ⋃ a, Set.range (g a) at hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  exact ⟨a, by rwa [Scheme.Pullback.range_fst]⟩

include hc in
/-- Affine étale schemes descend along an inverse limit of affine schemes. -/
theorem exists_affine_model [∀ i, IsAffine (D.obj i)]
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ c.pt) [Etale f] :
    ∃ (i : I) (Yᵢ : Scheme.{u}) (fᵢ : Yᵢ ⟶ D.obj i) (g : Y ⟶ Yᵢ),
      IsAffine Yᵢ ∧ Etale fᵢ ∧ IsPullback f g (c.π.app i) fᵢ := by
  let : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let (i : I) : QuasiSeparatedSpace (D.obj i) := inferInstance
  let {i j : I} (k : i ⟶ j) : IsAffineHom (D.map k) := inferInstance
  let Γ := Scheme.Γ.mapCocone c.op
  let hΓ : IsColimit Γ := (AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone D c hc).some
  let f' : Y ⟶ Spec Γ.pt := f ≫ c.pt.isoSpec.hom
  let : Etale f' := inferInstanceAs (Etale (f ≫ c.pt.isoSpec.hom))
  obtain ⟨i, P, v, g, hP, hv, h⟩ :=
    PhilipponEtaleAffineLimitDescent.exists_affine_etale_model (D.op ⋙ Scheme.Γ) hΓ f'
  let e := (D.obj i.unop).isoSpec
  let : Etale v := hv
  refine ⟨i.unop, P, v ≫ e.inv, g, hP, inferInstance, ?_⟩
  apply h.of_iso (Iso.refl _) c.pt.isoSpec.symm (Iso.refl _) e.symm
  · simp [f']
  · simp
  · change Spec.map ((c.π.app i.unop).appTop) ≫ e.inv =
      c.pt.isoSpec.inv ≫ c.π.app i.unop
    exact @Scheme.isoSpec_inv_naturality c.pt (D.obj i.unop) inferInstance inferInstance
      (c.π.app i.unop)
  · simp

omit [IsCofiltered I] in
private theorem exists_model_at_refinement {i j : I} (k : i ⟶ j)
    {Y V : Scheme.{u}} {f : Y ⟶ c.pt} {g : Y ⟶ V} {v : V ⟶ D.obj j}
    (h : IsPullback f g (c.π.app j) v) :
    ∃ t : Y ⟶ pullback (D.map k) v,
      IsPullback f t (c.π.app i) (pullback.fst (D.map k) v) := by
  have hw : (f ≫ c.π.app i) ≫ D.map k = g ≫ v := by
    rw [Category.assoc, c.w, h.w]
  let t := pullback.lift (f ≫ c.π.app i) g hw
  have ht : t ≫ pullback.snd (D.map k) v = g := pullback.lift_snd ..
  refine ⟨t, IsPullback.of_bot ?_ (pullback.lift_fst _ _ hw).symm (IsPullback.of_hasPullback _ _)⟩
  rw [ht, c.w]
  exact h

include hc in
/-- Near any point of an étale scheme over an inverse limit, an affine
open neighborhood descends to an étale scheme over one stage. -/
theorem exists_affine_refinement_model_at_point
    [∀ {i j} (k : i ⟶ j), IsAffineHom (D.map k)]
    {Y : Scheme.{u}} (f : Y ⟶ c.pt) [Etale f] (y : Y) :
    ∃ (i : I) (A W : Scheme.{u}) (a : A ⟶ Y) (v : W ⟶ D.obj i) (g : A ⟶ W),
      IsAffine A ∧ IsOpenImmersion a ∧ y ∈ Set.range a ∧
      IsAffine W ∧ Etale v ∧ IsPullback (a ≫ f) g (c.π.app i) v := by
  let i := Classical.choice (IsCofiltered.nonempty (C := I))
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := c.π.app i (f y)) (U := ⊤) trivial
  let G := AlgebraicGeometry.opensDiagram D i U
  let d := AlgebraicGeometry.opensCone D c i U
  let U₀ := c.π.app i ⁻¹ᵁ U
  let Y₀ := f ⁻¹ᵁ U₀
  let y₀ : Y₀ := ⟨y, hy⟩
  obtain ⟨R, a, ha, hy₀, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Y₀.toScheme) (x := y₀) (U := ⊤) trivial
  let : IsOpenImmersion a := ha
  let b : Spec R ⟶ Y := a ≫ Y₀.ι
  let p : Spec R ⟶ d.pt := a ≫ (f ∣_ U₀)
  let : Etale p := inferInstanceAs (Etale (a ≫ (f ∣_ U₀)))
  let (j : Over i) : IsAffine (G.obj j) :=
    hU.preimage (D.map j.hom)
  obtain ⟨j, W, v, g, hW, hv, h⟩ :=
    exists_affine_model G d (AlgebraicGeometry.isLimitOpensCone D c hc i U) p
  let V := D.map j.hom ⁻¹ᵁ U
  have hOpen : IsPullback (d.π.app j) U₀.ι V.ι (c.π.app j.left) := by
    apply IsOpenImmersion.isPullback _ _ _ _
    · simp [d, U₀, V]
    · simp [U₀, V, ← Scheme.Hom.comp_preimage]
  let : Etale v := hv
  refine ⟨j.left, Spec R, W, b, v ≫ V.ι, g, inferInstance, inferInstance,
    ?_, hW, inferInstance, ?_⟩
  · obtain ⟨z, hz⟩ := hy₀
    exact ⟨z, congrArg (fun z : Y₀ => Y₀.ι z) hz⟩
  · have hp : p ≫ U₀.ι = b ≫ f := by
      simp [p, b, Y₀, Category.assoc]
    rw [← hp]
    exact h.paste_horiz hOpen.flip

include hc in
private theorem assemble_cover_model [∀ i, CompactSpace (D.obj i)]
    [∀ {i j} (k : i ⟶ j), IsAffineHom (D.map k)]
    {α : Type u} [Finite α] {V : α → Scheme.{u}} (f : ∀ a, V a ⟶ c.pt)
    (hCover : ∀ x : c.pt, ∃ a, x ∈ Set.range (f a))
    (hModels : ∀ a, ∃ (i : I) (W : Scheme.{u}) (v : W ⟶ D.obj i) (g : V a ⟶ W),
      IsAffine W ∧ Etale v ∧ IsPullback (f a) g (c.π.app i) v) :
    ∃ (j : I) (W : α → Scheme.{u}) (v : ∀ a, W a ⟶ D.obj j) (g : ∀ a, V a ⟶ W a),
      (∀ a, IsAffine (W a)) ∧ (∀ a, Etale (v a)) ∧
      (∀ a, IsPullback (f a) (g a) (c.π.app j) (v a)) ∧
      (∀ x : D.obj j, ∃ a, x ∈ Set.range (v a)) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  choose j W v g hW hv hp using hModels
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let k (a : α) : i ⟶ j a := (hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).some
  let V₀ (a : α) := pullback (D.map (k a)) (v a)
  let v₀ (a : α) : V₀ a ⟶ D.obj i := pullback.fst _ _
  have hV₀ (a : α) : IsAffine (V₀ a) := by
    let : IsAffine (W a) := hW a
    dsimp [V₀]
    infer_instance
  have hv₀ (a : α) : Etale (v₀ a) := by
    let : Etale (v a) := hv a
    dsimp [v₀]
    infer_instance
  choose g₀ hg₀ using fun a => exists_model_at_refinement D c (k a) (hp a)
  have h₀ (x : c.pt) : ∃ a, x ∈ Set.range (pullback.fst (c.π.app i) (v₀ a)) := by
    obtain ⟨a, y, rfl⟩ := hCover x
    refine ⟨a, (hg₀ a).isoPullback.hom y, ?_⟩
    exact congrArg (fun h : V a ⟶ c.pt => h y) (hg₀ a).isoPullback_hom_fst
  obtain ⟨l, m, hsurj⟩ := exists_covering_stage D c hc v₀
    (fun a => by
      let : Etale (v₀ a) := hv₀ a
      exact (v₀ a).isOpenMap) h₀
  let V₁ (a : α) := pullback (D.map m) (v₀ a)
  let v₁ (a : α) : V₁ a ⟶ D.obj l := pullback.fst _ _
  choose g₁ hg₁ using fun a => exists_model_at_refinement D c m (hg₀ a)
  refine ⟨l, V₁, v₁, g₁, ?_, ?_, hg₁, hsurj⟩
  · intro a
    let : IsAffine (V₀ a) := hV₀ a
    dsimp [V₁]
    infer_instance
  · intro a
    let : Etale (v₀ a) := hv₀ a
    dsimp [v₁]
    infer_instance

include hc in
/-- A finite affine étale cover of a limit of affine schemes has a
jointly surjective affine étale model at a common stage. -/
theorem exists_finite_affine_cover_model [∀ i, IsAffine (D.obj i)]
    {α : Type u} [Finite α] {V : α → Scheme.{u}} [∀ a, IsAffine (V a)]
    (f : ∀ a, V a ⟶ c.pt) [∀ a, Etale (f a)]
    (hCover : ∀ x : c.pt, ∃ a, x ∈ Set.range (f a)) :
    ∃ (j : I) (W : α → Scheme.{u}) (v : ∀ a, W a ⟶ D.obj j) (g : ∀ a, V a ⟶ W a),
      (∀ a, IsAffine (W a)) ∧ (∀ a, Etale (v a)) ∧
      (∀ a, IsPullback (f a) (g a) (c.π.app j) (v a)) ∧
      (∀ x : D.obj j, ∃ a, x ∈ Set.range (v a)) := by
  let {i j : I} (k : i ⟶ j) : IsAffineHom (D.map k) := inferInstance
  exact assemble_cover_model D c hc f hCover (fun a => exists_affine_model D c hc (f a))

include hc in
/-- An étale cover of the limit of a cofiltered diagram of compact schemes
with affine transition maps admits a finite affine refinement obtained
by pulling back an étale cover from one stage. -/
theorem exists_refined_cover_model [∀ i, CompactSpace (D.obj i)]
    [∀ {i j} (k : i ⟶ j), IsAffineHom (D.map k)]
    {α : Type*} {V : α → Scheme.{u}} (f : ∀ a, V a ⟶ c.pt) [∀ a, Etale (f a)]
    (hCover : ∀ x : c.pt, ∃ a, x ∈ Set.range (f a)) :
    ∃ (j : I) (β : Type u) (_ : Fintype β) (a : β → α)
      (U W : β → Scheme.{u}) (r : ∀ b, U b ⟶ V (a b))
      (v : ∀ b, W b ⟶ D.obj j) (g : ∀ b, U b ⟶ W b),
      (∀ b, IsAffine (U b) ∧ IsOpenImmersion (r b) ∧ IsAffine (W b) ∧ Etale (v b) ∧
        IsPullback (r b ≫ f (a b)) (g b) (c.π.app j) (v b)) ∧
      (∀ x : c.pt, ∃ b, x ∈ Set.range (r b ≫ f (a b))) ∧
      (∀ x : D.obj j, ∃ b, x ∈ Set.range (v b)) := by
  classical
  choose a y hy using hCover
  choose i U W r v g hU hr hmem hW hv hp using fun x =>
    exists_affine_refinement_model_at_point D c hc (f (a x)) (y x)
  let q (x : c.pt) := r x ≫ f (a x)
  have hqx (x : c.pt) : x ∈ Set.range (q x) := by
    obtain ⟨z, hz⟩ := hmem x
    exact ⟨z, (congrArg (f (a x)) hz).trans (hy x)⟩
  have hOpen (x : c.pt) : IsOpen (Set.range (q x)) := by
    let : IsOpenImmersion (r x) := hr x
    let : Etale (q x) := inferInstanceAs (Etale (r x ≫ f (a x)))
    exact (q x).isOpenMap.isOpen_range
  let : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have hc' : (Set.univ : Set c.pt) ⊆ ⋃ x, Set.range (q x) :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hqx x⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover _ hOpen hc'
  have hSub (x : c.pt) : ∃ b : S, x ∈ Set.range (q b.val) := by
    obtain ⟨b, hb, H⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ x))
    exact ⟨⟨b, hb⟩, H⟩
  obtain ⟨j, W', v', g', hW', hv', hp', hcov⟩ :=
    assemble_cover_model D c hc (fun b : S => q b.val) hSub
      (fun b => ⟨i b.val, W b.val, v b.val, g b.val, hW b.val, hv b.val, hp b.val⟩)
  exact ⟨j, S, inferInstance, fun b => a b.val, fun b => U b.val, W',
    fun b => r b.val, v', g', fun b => ⟨hU b.val, hr b.val, hW' b, hv' b, hp' b⟩, hSub, hcov⟩

end PhilipponEtaleCoverLimitDescent

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleStrictHenselization
  (Neighborhood IsAffineNeighborhood affineInclusion pullbackNeighborhoods
    pullbackNeighborhoodLimitCone affinePullbackTransition toBase)


namespace PhilipponStrictLocalEtaleCoverDescent

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X) (f : Y ⟶ X)

private abbrev AffineNeighborhood := (IsAffineNeighborhood s).FullSubcategory

private abbrev strictPullback : Scheme.{u} := pullback (toBase s) f

private abbrev neighborhoodPullback (N : AffineNeighborhood s) : Scheme.{u} :=
  pullback N.obj.1.hom f

private instance affineNeighborhood_initiallySmall : InitiallySmall.{u} (AffineNeighborhood s) := by
  let : InitiallySmall.{u} (Neighborhood s) := (Scheme.pointSmallEtale s).initiallySmall
  let F := affineInclusion s
  let H := fromInitialModel.{u} (Neighborhood s)
  let r (j : InitialModel.{u} (Neighborhood s)) := Functor.Initial.lift F (H.obj j)
  apply initiallySmall_of_small_weakly_initial_set (Set.range r)
  intro W
  let j := Functor.Initial.lift H (F.obj W)
  let h := Functor.Initial.homToLift F (H.obj j) ≫ Functor.Initial.homToLift H (F.obj W)
  exact ⟨r j, Set.mem_range_self _, ⟨F.preimage h⟩⟩

/-- Every étale cover of the pullback to the strict localization of the base
has a finite affine refinement pulled back from a cover over a single
pointed affine étale neighborhood. -/
theorem exists_refined_cover_over_neighborhood [IsProper f]
    {α : Type*} {V : α → Scheme.{u}} (p : ∀ a, V a ⟶ strictPullback s f)
    [∀ a, Etale (p a)] (hCover : ∀ x : strictPullback s f, ∃ a, x ∈ Set.range (p a)) :
    ∃ (N : AffineNeighborhood s) (β : Type u) (_ : Fintype β) (a : β → α)
      (U W : β → Scheme.{u}) (r : ∀ b, U b ⟶ V (a b))
      (v : ∀ b, W b ⟶ neighborhoodPullback s f N) (g : ∀ b, U b ⟶ W b),
      (∀ b, IsAffine (U b) ∧ IsOpenImmersion (r b) ∧ IsAffine (W b) ∧ Etale (v b) ∧
        IsPullback (r b ≫ p (a b)) (g b) ((pullbackNeighborhoodLimitCone s f).cone.π.app N.obj) (v b)) ∧
      (∀ x : strictPullback s f, ∃ b, x ∈ Set.range (r b ≫ p (a b))) ∧
      (∀ x : neighborhoodPullback s f N, ∃ b, x ∈ Set.range (v b)) := by
  let H := InitiallySmall.fromCofilteredInitialModel.{u} (AffineNeighborhood s)
  let F := H ⋙ affineInclusion s
  let D := F ⋙ pullbackNeighborhoods s f
  let M := pullbackNeighborhoodLimitCone s f
  let c : Cone D := M.cone.whisker F
  let hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv F _).symm M.isLimit
  let (i : InitiallySmall.CofilteredInitialModel.{u} (AffineNeighborhood s)) :
      CompactSpace (D.obj i) := by
    let N := H.obj i
    let : IsAffine N.obj.1.left := N.property
    change CompactSpace (neighborhoodPullback s f N)
    let q : neighborhoodPullback s f N ⟶ N.obj.1.left := pullback.fst N.obj.1.hom f
    exact (quasiCompact_iff_compactSpace q).mp (inferInstanceAs (QuasiCompact (pullback.fst N.obj.1.hom f)))
  let {i j : InitiallySmall.CofilteredInitialModel.{u} (AffineNeighborhood s)} (k : i ⟶ j) :
      IsAffineHom (D.map k) := affinePullbackTransition s f (H.map k)
  obtain ⟨j, β, hβ, a, U, W, r, v, g, hmodels, hlim, hstage⟩ :=
    PhilipponEtaleCoverLimitDescent.exists_refined_cover_model D c hc p hCover
  exact ⟨H.obj j, β, hβ, a, U, W, r, v, g, hmodels, hlim, hstage⟩

end PhilipponStrictLocalEtaleCoverDescent

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleNeighborhoodRestriction

universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- Regard an étale scheme over an étale neighborhood as étale over the base. -/
abbrev along : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (show Etale f from inferInstance)

private def liftObj {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) : Y.Etale :=
  Scheme.Etale.mk (a.left ≫ U.hom)

private def liftIso {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) :
    (along f).obj (liftObj f a) ≅ V :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans ((MorphismProperty.Over.w a).symm.trans
      (Category.assoc a.left U.hom f).symm))

private theorem coverPreserving : CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (along f) := by
  constructor
  intro W S hS
  rw [← Sieve.ofArrows_category S, Scheme.ofArrows_mem_smallEtaleTopology_iff] at hS
  rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows,
    Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact hS

private theorem compatiblePreserving :
    CompatiblePreserving X.smallEtaleTopology (along f) := by
  constructor
  intro F T S z hz U₁ U₂ V a₁ a₂ g₁ g₂ h₁ h₂ h
  let V' := liftObj f a₁
  have hleft := congrArg (fun a => a.left) h
  change a₁.left ≫ g₁.left = a₂.left ≫ g₂.left at hleft
  let b₁ : V' ⟶ U₁ := MorphismProperty.Over.homMk a₁.left rfl trivial
  let b₂ : V' ⟶ U₂ := MorphismProperty.Over.homMk a₂.left (by
    change a₂.left ≫ U₂.hom = a₁.left ≫ U₁.hom
    rw [← MorphismProperty.Over.w g₂, ← MorphismProperty.Over.w g₁,
      ← Category.assoc, ← Category.assoc, hleft]) trivial
  have he : b₁ ≫ g₁ = b₂ ≫ g₂ := MorphismProperty.Over.Hom.ext hleft
  let e := liftIso f a₁
  have hₐ₁ : (along f).map b₁ = e.hom ≫ a₁ :=
    MorphismProperty.Over.Hom.ext (Category.id_comp a₁.left).symm
  have hₐ₂ : (along f).map b₂ = e.hom ≫ a₂ :=
    MorphismProperty.Over.Hom.ext (Category.id_comp a₂.left).symm
  have hz' : F.obj.map ((along f).map b₁).op (z g₁ h₁) =
      F.obj.map ((along f).map b₂).op (z g₂ h₂) := hz b₁ b₂ h₁ h₂ he
  apply (F.obj.mapIso e.op).toEquiv.injective
  simpa only [Iso.op_hom, Iso.toEquiv_fun, F.obj.mapIso_hom, ← Functor.map_comp_apply,
    ← op_comp, ← hₐ₁, ← hₐ₂] using hz'

instance along_isContinuous : (along f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving f) (coverPreserving f)

/-- Restriction to the small étale site of an étale neighborhood. -/
abbrev restrict : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (along f).sheafPushforwardContinuous AddCommGrpCat Y.smallEtaleTopology X.smallEtaleTopology

private def restrictAdjunction : restrict f ⊣ pushforward f := by
  let adj : along f ⊣ baseChange f :=
    MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ f inferInstance trivial
  exact adj.sheafPushforwardContinuous Y.smallEtaleTopology X.smallEtaleTopology

/-- Restriction to an étale neighborhood agrees with the ordinary inverse image. -/
def restrictionIso : restrict f ≅ pullbackSheaves f :=
  (restrictAdjunction f).leftAdjointUniq (pullbackAdjunction f)

section Fibers

variable (W : X.Etale)

private abbrev Lifts := {p : W.left ⟶ Y // p ≫ f = W.hom}
private abbrev Comma := CostructuredArrow (along f).op (op W)

private def liftObject (p : Lifts f W) : Y.Etale := by
  let : Etale (p.val ≫ f) := by rw [p.property]; infer_instance
  let : Etale p.val := Etale.of_comp p.val f
  exact Scheme.Etale.mk p.val

private def liftObjectIso (p : Lifts f W) : (along f).obj (liftObject f W p) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl W.left) ((Category.id_comp _).trans p.property.symm)

private def representative (p : Lifts f W) : Comma f W :=
  CostructuredArrow.mk ((liftObjectIso f W p).inv.op)

private def representatives : Discrete (Lifts f W) ⥤ Comma f W :=
  Discrete.functor (representative f W)

private def liftOfArrow (j : Comma f W) : Lifts f W :=
  ⟨j.hom.unop.left ≫ j.left.unop.hom,
    (Category.assoc _ _ _).trans (MorphismProperty.Over.w j.hom.unop)⟩

private theorem arrow_left_eq {j : Comma f W} {p : Lifts f W}
    (h : j ⟶ representative f W p) : h.left.unop.left = j.hom.unop.left := by
  have he := congrArg (fun a => a.unop.left) (CostructuredArrow.w h)
  change 𝟙 W.left ≫ h.left.unop.left = j.hom.unop.left at he
  exact (Category.id_comp _).symm.trans he

private theorem liftOfArrow_eq {j : Comma f W} {p : Lifts f W}
    (h : j ⟶ representative f W p) : liftOfArrow f W j = p := by
  apply Subtype.ext
  change j.hom.unop.left ≫ j.left.unop.hom = p.val
  rw [← arrow_left_eq f W h]
  exact MorphismProperty.Over.w h.left.unop

private def arrowToRepresentative (j : Comma f W) :
    j ⟶ representative f W (liftOfArrow f W j) := by
  let k : liftObject f W (liftOfArrow f W j) ⟶ j.left.unop :=
    MorphismProperty.Over.homMk j.hom.unop.left rfl trivial
  refine CostructuredArrow.homMk k.op ?_
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

private theorem uniqueArrowToRepresentative {j : Comma f W} {p : Lifts f W}
    (a b : j ⟶ representative f W p) : a = b := by
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  exact (arrow_left_eq f W a).trans (arrow_left_eq f W b).symm

private instance representatives_final : (representatives f W).Final where
  out j := by
    let a : StructuredArrow j (representatives f W) :=
      StructuredArrow.mk (arrowToRepresentative f W j)
    apply isConnected_of_isInitial _ (x := a)
    refine IsInitial.ofUniqueHom (fun b => ?_) (fun b h => ?_)
    · let e : a.right = b.right := Discrete.ext (liftOfArrow_eq f W b.hom)
      exact StructuredArrow.homMk (eqToHom e) (uniqueArrowToRepresentative f W _ _)
    · apply StructuredArrow.hom_ext
      exact Subsingleton.elim _ _

end Fibers

instance along_hasPointwiseLeftKanExtension (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (along f).op.HasPointwiseLeftKanExtension P := by
  intro V
  let W := V.unop
  change HasColimit (CostructuredArrow.proj (along f).op (op W) ⋙ P)
  exact Functor.Final.hasColimit_of_comp (representatives f W)

private abbrev leftKan :
    (Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (along f).op.lan

set_option maxHeartbeats 600000 in
private instance leftKan_preservesMonomorphisms : (leftKan f).PreservesMonomorphisms where
  preserves {P Q} α hα := by
    rw [NatTrans.mono_iff_mono_app] at hα ⊢
    intro V
    let W := V.unop
    let L := (along f).op
    let R := representatives f W
    let D := R ⋙ CostructuredArrow.proj L (op W)
    let c (B : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) : Cocone (D ⋙ B) :=
      ((Functor.LeftExtension.mk _ (L.leftKanExtensionUnit B)).coconeAt (op W)).whisker R
    let hc (B : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) : IsColimit (c B) :=
      (Functor.Final.isColimitWhiskerEquiv R _).symm
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit B (op W))
    let e (B : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) : ((leftKan f).obj B).obj (op W) ≅ colimit (D ⋙ B) :=
      (hc B).coconePointUniqueUpToIso (colimit.isColimit _)
    have he (B : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) (j : Discrete (Lifts f W)) :
        (c B).ι.app j ≫ (e B).hom = colimit.ι (D ⋙ B) j :=
      (hc B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) j
    let β := Functor.whiskerLeft D α
    have hAt (j : Discrete (Lifts f W)) :
        (c P).ι.app j ≫ ((leftKan f).map α).app (op W) = β.app j ≫ (c Q).ι.app j := by
      let t := R.obj j
      change ((L.lanUnit.app P).app t.left ≫ (L.lan.obj P).map t.hom) ≫
        (L.lan.map α).app (op W) = α.app t.left ≫ ((L.lanUnit.app Q).app t.left ≫
          (L.lan.obj Q).map t.hom)
      rw [Category.assoc, (L.lan.map α).naturality t.hom, ← Category.assoc]
      have hn := NatTrans.congr_app (L.lanUnit.naturality α) t.left
      change α.app t.left ≫ (L.lanUnit.app Q).app t.left =
        (L.lanUnit.app P).app t.left ≫ (L.lan.map α).app (L.obj t.left) at hn
      rw [← hn, Category.assoc]
    have hcomp : ((leftKan f).map α).app (op W) ≫ (e Q).hom =
        (e P).hom ≫ colim.map β := by
      apply (hc P).hom_ext
      intro j
      rw [← Category.assoc, hAt, Category.assoc, he Q, ← Category.assoc, he P]
      exact (colimit.ι_map β j).symm
    let : Mono β := (NatTrans.mono_iff_mono_app _).mpr (fun j => hα (D.obj j))
    let : PreservesFiniteLimits (colim (J := Discrete (Lifts f W)) (C := AddCommGrpCat.{u})) :=
      HasExactColimitsOfShape.preservesFiniteLimits
    exact mono_of_mono_fac hcomp

/-- Restriction along an étale map preserves injectives because extension
by zero is the sheafification of an objectwise coproduct over the lifts. -/
instance restrict_preservesInjectiveObjects : (restrict f).PreservesInjectiveObjects := by
  let L := Functor.sheafPullbackConstruction.sheafPullback (along f) AddCommGrpCat
    Y.smallEtaleTopology X.smallEtaleTopology
  have : L.PreservesMonomorphisms := by
    unfold L Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (along f) AddCommGrpCat
      Y.smallEtaleTopology X.smallEtaleTopology)

instance pullback_preservesInjectiveObjects : (pullbackSheaves f).PreservesInjectiveObjects where
  injective_obj h := Injective.of_iso ((restrictionIso f).app _)
    ((restrict f).injective_obj_of_injective h)

end PhilipponEtaleNeighborhoodRestriction

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleNeighborhoodRestriction (along)


namespace PhilipponEtaleModeledSections

universe u

variable {I : Type u} [Category.{u} I] {Y : Scheme.{u}} (E : I ⥤ Y.Etale)

private abbrev D := E ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y

variable {i : I} {V : Scheme.{u}} (v : V ⟶ (D E).obj i) [Etale v]

private abbrev baseChangeAtStage := Over.pullback v ⋙ Over.forget V

private abbrev modelSchemes := Over.post (D E) ⋙ baseChangeAtStage E v

/-- The diagram of the base changes of a stage's étale object to subsequent
stages, regarded as étale objects of the original base. -/
def chartStages : Over i ⥤ Y.Etale where
  obj j := Scheme.Etale.mk (pullback.fst ((D E).map j.hom) v ≫ (E.obj j.left).hom)
  map {j k} a := MorphismProperty.Over.homMk ((modelSchemes E v).map a) (by
    have h : ((modelSchemes E v).map a) ≫ pullback.fst ((D E).map k.hom) v =
        pullback.fst ((D E).map j.hom) v ≫ (D E).map a.left :=
      pullback.lift_fst ..
    change (_ : (modelSchemes E v).obj j ⟶ (modelSchemes E v).obj k) ≫
      pullback.fst ((D E).map k.hom) v ≫ (E.obj k.left).hom =
      pullback.fst ((D E).map j.hom) v ≫ (E.obj j.left).hom
    rw [← Category.assoc, h, Category.assoc]
    exact congrArg (pullback.fst ((D E).map j.hom) v ≫ ·) (MorphismProperty.Over.w (E.map a.left))
    ) trivial
  map_id j := MorphismProperty.Over.Hom.ext ((modelSchemes E v).map_id j)
  map_comp a b := MorphismProperty.Over.Hom.ext ((modelSchemes E v).map_comp a b)

private def overChartMap {S X' V' W' : Scheme.{u}} (r : X' ⟶ S)
    (v' : V' ⟶ S) (w' : W' ⟶ S) (a : V' ⟶ W') (ha : a ≫ w' = v') :
    pullback r v' ⟶ pullback r w' :=
  pullback.lift (pullback.fst r v') (pullback.snd r v' ≫ a)
    (by rw [Category.assoc, ha, pullback.condition])

private theorem overChartMap_comm {S X₀ X₁ V' W' : Scheme.{u}}
    {r₀ : X₀ ⟶ S} {r₁ : X₁ ⟶ S} (v' : V' ⟶ S) (w' : W' ⟶ S)
    (a : V' ⟶ W') (ha : a ≫ w' = v') (d : X₀ ⟶ X₁)
    (mV : pullback r₀ v' ⟶ pullback r₁ v') (mW : pullback r₀ w' ⟶ pullback r₁ w')
    (hv₁ : mV ≫ pullback.fst r₁ v' = pullback.fst r₀ v' ≫ d)
    (hv₂ : mV ≫ pullback.snd r₁ v' = pullback.snd r₀ v')
    (hw₁ : mW ≫ pullback.fst r₁ w' = pullback.fst r₀ w' ≫ d)
    (hw₂ : mW ≫ pullback.snd r₁ w' = pullback.snd r₀ w') :
    mV ≫ overChartMap r₁ v' w' a ha = overChartMap r₀ v' w' a ha ≫ mW := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, hw₁, overChartMap, overChartMap,
      pullback.lift_fst, pullback.lift_fst_assoc, hv₁]
  · rw [Category.assoc, Category.assoc, hw₂, overChartMap, overChartMap,
      pullback.lift_snd, pullback.lift_snd, ← Category.assoc, hv₂]

private theorem overChartMap_id {S X' V' : Scheme.{u}} (r : X' ⟶ S) (v' : V' ⟶ S) :
    overChartMap r v' v' (𝟙 _) (Category.id_comp _) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [overChartMap]

private theorem overChartMap_comp {S X' U' V' W' : Scheme.{u}} (r : X' ⟶ S)
    (u' : U' ⟶ S) (v' : V' ⟶ S) (w' : W' ⟶ S)
    (a : U' ⟶ V') (b : V' ⟶ W') (ha : a ≫ v' = u') (hb : b ≫ w' = v') :
    overChartMap r u' w' (a ≫ b) (by rw [Category.assoc, hb, ha]) =
      overChartMap r u' v' a ha ≫ overChartMap r v' w' b hb := by
  apply pullback.hom_ext <;> simp [overChartMap, Category.assoc]

private theorem overChartMap_paste {Q S A B T W : Scheme.{u}}
    {m : Q ⟶ S} {b : B ⟶ Q} {t : B ⟶ T} {v : T ⟶ S}
    {a : A ⟶ B} {g : A ⟶ W} {w : W ⟶ T}
    (h : IsPullback a g t w) (k : IsPullback b t m v) :
    (h.paste_horiz k).isoPullback.hom ≫ overChartMap m (w ≫ v) v w rfl =
      a ≫ k.isoPullback.hom := by
  let e := (h.paste_horiz k).isoPullback
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, k.isoPullback_hom_fst]
    change e.hom ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst]
    exact (h.paste_horiz k).isoPullback_hom_fst
  · rw [Category.assoc, Category.assoc, k.isoPullback_hom_snd]
    change e.hom ≫ pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd, ← Category.assoc, (h.paste_horiz k).isoPullback_hom_snd]
    exact h.w.symm

variable {W : Scheme.{u}} (w : W ⟶ (D E).obj i) [Etale w]
  (a : V ⟶ W) (ha : a ≫ w = v)

/-- A map of étale charts at one stage induces maps on their pullbacks at
every subsequent stage. -/
def chartStagesMap : chartStages E v ⟶ chartStages E w where
  app j := MorphismProperty.Over.homMk (overChartMap ((D E).map j.hom) v w a ha)
    (by
      let r := (D E).map j.hom
      change overChartMap r v w a ha ≫ pullback.fst r w ≫ (E.obj j.left).hom =
        pullback.fst r v ≫ (E.obj j.left).hom
      exact pullback.lift_fst_assoc ..) trivial
  naturality {j k} b := by
    apply MorphismProperty.Over.Hom.ext
    exact overChartMap_comm v w a ha ((D E).map b.left)
      ((modelSchemes E v).map b) ((modelSchemes E w).map b)
      (pullback.lift_fst ..) (pullback.lift_snd ..) (pullback.lift_fst ..) (pullback.lift_snd ..)

/-- Pullback of a chart at a fixed stage, functorial in the chart and in all
subsequent stages. -/
def chartStagesFunctor (i : I) : ((D E).obj i).Etale ⥤ Over i ⥤ Y.Etale where
  obj U := chartStages E U.hom
  map b := chartStagesMap E _ _ b.left (MorphismProperty.Over.w b)
  map_id U := by
    ext j : 2
    exact MorphismProperty.Over.Hom.ext (overChartMap_id ((D E).map j.hom) U.hom)
  map_comp {U V W} a b := by
    ext j : 2
    exact MorphismProperty.Over.Hom.ext (overChartMap_comp ((D E).map j.hom)
      U.hom V.hom W.hom a.left b.left (MorphismProperty.Over.w a) (MorphismProperty.Over.w b))

/-- The restriction diagrams underlying the stage section colimits. -/
def chartStageSections (i : I) (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((D E).obj i).Etaleᵒᵖ ⥤ (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := ((chartStagesFunctor E i).obj U.unop).op ⋙ P
  map b := Functor.whiskerRight (NatTrans.op ((chartStagesFunctor E i).map b.unop)) P
  map_id U := by
    ext j : 2
    change P.map (((chartStagesFunctor E i).map (𝟙 U.unop)).app j.unop).op = 𝟙 _
    rw [(chartStagesFunctor E i).map_id U.unop]
    exact P.map_id _
  map_comp a b := by
    ext j : 2
    change P.map (((chartStagesFunctor E i).map (b.unop ≫ a.unop)).app j.unop).op = _
    rw [Functor.map_comp]
    exact P.map_comp _ _

private def reversedBaseChange {X X' : Scheme.{u}} (r : X' ⟶ X) : X.Etale ⥤ X'.Etale where
  obj U := Scheme.Etale.mk (pullback.fst r U.hom)
  map b := MorphismProperty.Over.homMk (overChartMap r _ _ b.left (MorphismProperty.Over.w b))
    (pullback.lift_fst ..) trivial
  map_id U := MorphismProperty.Over.Hom.ext (overChartMap_id r U.hom)
  map_comp {U V W} a b := MorphismProperty.Over.Hom.ext (overChartMap_comp r
    U.hom V.hom W.hom a.left b.left (MorphismProperty.Over.w a) (MorphismProperty.Over.w b))

private def reversedBaseChangeIso {X X' : Scheme.{u}} (r : X' ⟶ X) :
    reversedBaseChange r ≅ baseChange r := by
  refine NatIso.ofComponents (fun U => MorphismProperty.Over.isoMk
    (pullbackSymmetry r U.hom) (pullbackSymmetry_hom_comp_snd ..)) ?_
  intro U V b
  apply MorphismProperty.Over.Hom.ext
  let a := overChartMap r U.hom V.hom b.left (MorphismProperty.Over.w b)
  let d := ((baseChange r).map b).left
  change a ≫ (pullbackSymmetry r V.hom).hom = (pullbackSymmetry r U.hom).hom ≫ d
  have h₁ : d ≫ pullback.fst V.hom r = pullback.fst U.hom r ≫ b.left := pullback.lift_fst ..
  have h₂ : d ≫ pullback.snd V.hom r = pullback.snd U.hom r := pullback.lift_snd ..
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst, h₁,
      pullbackSymmetry_hom_comp_fst_assoc]
    exact pullback.lift_snd ..
  · rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_snd, h₂,
      pullbackSymmetry_hom_comp_snd]
    exact pullback.lift_fst ..

/-- Evaluation at a stage pulls the chart back along the transition and
regards the result as a chart over the original base. -/
def chartAtStageIso {i : I} (j : Over i) :
    chartStagesFunctor E i ⋙ (evaluation (Over i) Y.Etale).obj j ≅
      baseChange ((D E).map j.hom) ⋙ along (E.obj j.left).hom :=
  Functor.isoWhiskerRight (reversedBaseChangeIso ((D E).map j.hom)) (along (E.obj j.left).hom)

/-- At each stage the section diagram evaluates to a sheaf, by restriction
along the étale neighborhood and then precomposition by base change. -/
theorem chartStageSections_isSheaf {i : I} (j : (Over i)ᵒᵖ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    Presheaf.IsSheaf ((D E).obj i).smallEtaleTopology
      (chartStageSections E i F.obj ⋙ (evaluation _ _).obj j) := by
  let r := (D E).map j.unop.hom
  let f := (E.obj j.unop.left).hom
  let K := baseChange r ⋙ along f
  let K' := chartStagesFunctor E i ⋙ (evaluation (Over i) Y.Etale).obj j.unop
  let e' : K'.op ⋙ F.obj ≅ K.op ⋙ F.obj :=
    Functor.isoWhiskerRight (NatIso.op (chartAtStageIso E j.unop).symm) F.obj
  apply (Presheaf.isSheaf_of_iso_iff e').mpr
  let : (baseChange r).IsContinuous ((D E).obj i).smallEtaleTopology
      (E.obj j.unop.left).left.smallEtaleTopology :=
    PhilipponEtaleBaseChangeComparison.baseChange_isContinuous r
  let : (along f).IsContinuous (E.obj j.unop.left).left.smallEtaleTopology Y.smallEtaleTopology :=
    PhilipponEtaleNeighborhoodRestriction.along_isContinuous f
  let : K.IsContinuous ((D E).obj i).smallEtaleTopology Y.smallEtaleTopology :=
    Functor.isContinuous_comp (baseChange r) (along f) _ (E.obj j.unop.left).left.smallEtaleTopology _
  exact K.op_comp_isSheaf_of_isSheaf _ _ _ F.property

omit [Etale v] in
private theorem model_transition_affine [∀ {j k : I} (a : j ⟶ k), IsAffineHom ((D E).map a)]
    {j k : Over i} (a : j ⟶ k) : IsAffineHom ((modelSchemes E v).map a) := by
  let d₁ := (D E).map j.hom
  let d₂ := (D E).map k.hom
  let d := (D E).map a.left
  let h : pullback d₁ v ⟶ pullback d₂ v := (modelSchemes E v).map a
  have hw : d ≫ d₂ = d₁ := by
    change (D E).map a.left ≫ (D E).map k.hom = (D E).map j.hom
    rw [← Functor.map_comp, Over.w]
  have h₁ : h ≫ pullback.fst d₂ v = pullback.fst d₁ v ≫ d := pullback.lift_fst ..
  have h₂ : h ≫ pullback.snd d₂ v = pullback.snd d₁ v := pullback.lift_snd ..
  have hpb : IsPullback (pullback.fst d₁ v) (h ≫ pullback.snd d₂ v) (d ≫ d₂) v := by
    rw [h₂, hw]
    exact IsPullback.of_hasPullback d₁ v
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_bot hpb h₁.symm (IsPullback.of_hasPullback d₂ v)) (inferInstance : IsAffineHom d)

variable (c : Cone (D E))

private abbrev modelCone : Cone (modelSchemes E v) :=
  (baseChangeAtStage E v).mapCone ((Over.conePost (D E) i).obj c)

omit [Etale v] in
private theorem modelCone_isPullback (j : Over i) :
    IsPullback (pullback.fst (c.π.app i) v) ((modelCone E v c).π.app j)
      (c.π.app j.left) (pullback.fst ((D E).map j.hom) v) := by
  let d := (D E).map j.hom
  let t := (modelCone E v c).π.app j
  have h₁ : t ≫ pullback.fst d v = pullback.fst (c.π.app i) v ≫ c.π.app j.left :=
    pullback.lift_fst ..
  have h₂ : t ≫ pullback.snd d v = pullback.snd (c.π.app i) v := pullback.lift_snd ..
  apply IsPullback.of_bot _ h₁.symm (IsPullback.of_hasPullback d v)
  rw [h₂, c.w]
  exact IsPullback.of_hasPullback _ _

/-- The map of stage charts gives the corresponding map on the limit. -/
def chartLimitMap :
    Scheme.Etale.mk (pullback.fst (c.π.app i) v) ⟶ Scheme.Etale.mk (pullback.fst (c.π.app i) w) :=
  MorphismProperty.Over.homMk (overChartMap (c.π.app i) v w a ha) (pullback.lift_fst ..) trivial

theorem chartLimitMap_projection (j : Over i) :
    (modelCone E v c).π.app j ≫ ((chartStagesMap E v w a ha).app j).left =
      (chartLimitMap E v w a ha c).left ≫ (modelCone E w c).π.app j :=
  overChartMap_comm v w a ha (c.π.app j.left)
    ((modelCone E v c).π.app j) ((modelCone E w c).π.app j)
    (pullback.lift_fst ..) (pullback.lift_snd ..) (pullback.lift_fst ..) (pullback.lift_snd ..)

/-- Pull back a chart at the chosen stage to the limit scheme. -/
def chartLimitFunctor (i : I) : ((D E).obj i).Etale ⥤ c.pt.Etale :=
  reversedBaseChange (c.π.app i)

instance chartLimitFunctor_preservesFiniteLimits (i : I) :
    PreservesFiniteLimits (chartLimitFunctor E c i) := by
  let : PreservesFiniteLimits (baseChange (c.π.app i)) := inferInstanceAs
    (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ (c.π.app i)))
  exact preservesFiniteLimits_of_natIso (reversedBaseChangeIso (c.π.app i)).symm

variable [IsCofiltered I] (hc : IsLimit c)
  [∀ {j k : I} (a : j ⟶ k), IsAffineHom ((D E).map a)]
  [CompactSpace V] [QuasiSeparatedSpace V]

omit [Etale v] [CompactSpace V] [QuasiSeparatedSpace V] in
include hc in
private def modelCone_isLimit : IsLimit (modelCone E v c) := by
  let : IsConnected (Over i) := IsCofiltered.isConnected (Over i)
  exact isLimitOfPreserves (baseChangeAtStage E v) (Over.isLimitConePost _ hc)

omit [IsCofiltered I] in
private theorem modelCompact (j : Over i) : CompactSpace ((D (chartStages E v)).obj j) := by
  let r : (modelSchemes E v).obj j ⟶ V := pullback.snd ((D E).map j.hom) v
  exact (quasiCompact_iff_compactSpace r).mp
    (inferInstanceAs (QuasiCompact (pullback.snd ((D E).map j.hom) v)))

omit [IsCofiltered I] [CompactSpace V] in
private theorem modelQuasiSeparated (j : Over i) :
    QuasiSeparatedSpace ((D (chartStages E v)).obj j) := by
  let r : (modelSchemes E v).obj j ⟶ V := pullback.snd ((D E).map j.hom) v
  let : QuasiSeparated r := inferInstanceAs (QuasiSeparated (pullback.snd ((D E).map j.hom) v))
  exact quasiSeparatedSpace_of_quasiSeparated r

omit [IsCofiltered I] [∀ {j k : I} (a : j ⟶ k), IsAffineHom ((D E).map a)]
  [CompactSpace V] [QuasiSeparatedSpace V] in
private theorem modelCone_comm (p : c.pt ⟶ Y)
    (hp : ∀ j, c.π.app j ≫ (E.obj j).hom = p) (j : Over i) :
    (modelCone E v c).π.app j ≫ ((chartStages E v).obj j).hom =
      pullback.fst (c.π.app i) v ≫ p := by
  change pullback.lift _ _ _ ≫ pullback.fst ((D E).map j.hom) v ≫ (E.obj j.left).hom =
    pullback.fst (c.π.app i) v ≫ p
  rw [pullback.lift_fst_assoc, Category.assoc]
  change pullback.fst (c.π.app i) v ≫ c.π.app j.left ≫ (E.obj j.left).hom =
    pullback.fst (c.π.app i) v ≫ p
  rw [hp]

include hc in
/-- Every covering sieve of a pulled-back quasi-compact, quasi-separated chart
contains a finite covering family obtained from an affine étale cover at a stage. -/
theorem exists_modeled_cover_refinement {U : ((D E).obj i).Etale}
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (S : Sieve ((chartLimitFunctor E c i).obj U))
    (hS : S ∈ c.pt.smallEtaleTopology ((chartLimitFunctor E c i).obj U)) :
    ∃ (j : I) (T : ((D E).obj j).Etale)
      (e : (chartLimitFunctor E c i).obj U ≅ (chartLimitFunctor E c j).obj T)
      (β : Type u) (_ : Fintype β) (W : β → ((D E).obj j).Etale) (a : ∀ b, W b ⟶ T),
      CompactSpace T.left ∧ QuasiSeparatedSpace T.left ∧ (∀ b, IsAffine (W b).left) ∧
      Sieve.ofArrows W a ∈ ((D E).obj j).smallEtaleTopology T ∧
      (∀ b, S ((chartLimitFunctor E c j).map (a b) ≫ e.inv)) ∧
      Sieve.ofArrows ((chartLimitFunctor E c j).obj ∘ W)
        (fun b => (chartLimitFunctor E c j).map (a b) ≫ e.inv) ∈ c.pt.smallEtaleTopology _ := by
  classical
  let V' := (chartLimitFunctor E c i).obj U
  let G := modelSchemes E U.hom
  let C := modelCone E U.hom c
  let : CompactSpace ((𝟭 Scheme.{u}).obj U.left) := ‹CompactSpace U.left›
  let : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj U.left) := ‹QuasiSeparatedSpace U.left›
  let (j : Over i) : CompactSpace (G.obj j) := modelCompact E U.hom j
  let {j k : Over i} (b : j ⟶ k) : IsAffineHom (G.map b) := model_transition_affine E U.hom b
  let f (a : S.arrows.category) : a.obj.left.left ⟶ C.pt := a.obj.hom.left
  let (a : S.arrows.category) : Etale (f a) := inferInstanceAs (Etale a.obj.hom.left)
  have hcov : ∀ x : C.pt, ∃ a, x ∈ Set.range (f a) := by
    rw [← Sieve.ofArrows_category S, Scheme.ofArrows_mem_smallEtaleTopology_iff] at hS
    simp only [Set.eq_univ_iff_forall, Set.mem_iUnion] at hS
    exact fun x => hS x
  obtain ⟨j, β, hβ, b, R, M, r, m, g, hr, hh, hm⟩ :=
    PhilipponEtaleCoverLimitDescent.exists_refined_cover_model G C
      (modelCone_isLimit E U.hom c hc) f hcov
  let T : ((D E).obj j.left).Etale := Scheme.Etale.mk (pullback.fst ((D E).map j.hom) U.hom)
  let K := chartLimitFunctor E c j.left
  let m' := c.π.app j.left
  let k : IsPullback V'.hom (C.π.app j) m' T.hom := modelCone_isPullback E U.hom c j
  let e : V' ≅ K.obj T := MorphismProperty.Over.isoMk k.isoPullback k.isoPullback_hom_fst
  let (l : β) : Etale (m l) := (hr l).2.2.2.1
  let W (l : β) : ((D E).obj j.left).Etale := Scheme.Etale.mk (m l ≫ T.hom)
  let a (l : β) : W l ⟶ T := MorphismProperty.Over.homMk (m l) rfl trivial
  let q (l : β) : R l ⟶ V'.left := r l ≫ f (b l)
  let h (l : β) : IsPullback (q l) (g l) (C.π.app j) (m l) := (hr l).2.2.2.2
  let (l : β) : IsOpenImmersion (r l) := (hr l).2.1
  let A (l : β) : c.pt.Etale := Scheme.Etale.mk (q l ≫ V'.hom)
  let z (l : β) : A l ⟶ V' := MorphismProperty.Over.homMk (q l) rfl trivial
  let ρ (l : β) : A l ≅ K.obj (W l) := MorphismProperty.Over.isoMk
    ((h l).paste_horiz k).isoPullback ((h l).paste_horiz k).isoPullback_hom_fst
  have he (l : β) : (ρ l).hom ≫ K.map (a l) = z l ≫ e.hom := by
    apply MorphismProperty.Over.Hom.ext
    exact overChartMap_paste (h l) k
  have hz (l : β) : (ρ l).hom ≫ (K.map (a l) ≫ e.inv) = z l := by
    rw [← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨j.left, T, e, β, hβ, W, a, modelCompact E U.hom j, modelQuasiSeparated E U.hom j,
    fun l => (hr l).2.2.1, ?_, ?_, ?_⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr
    simp only [Set.eq_univ_iff_forall, Set.mem_iUnion]
    exact fun x => hm x
  · intro l
    let s : A l ⟶ (b l).obj.left := MorphismProperty.Over.homMk (r l) (by
      change r l ≫ (b l).obj.left.hom = (r l ≫ (b l).obj.hom.left) ≫ V'.hom
      rw [Category.assoc, MorphismProperty.Over.w]) trivial
    have hl : z l = s ≫ (b l).obj.hom := MorphismProperty.Over.Hom.ext rfl
    rw [← Category.id_comp (K.map (a l) ≫ e.inv), ← (ρ l).inv_hom_id, Category.assoc, hz, hl]
    exact S.downward_closed (S.downward_closed (b l).property s) (ρ l).inv
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun l => K.map (a l) ≫ e.inv)).mpr
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨l, y, hy⟩ := hh x
    exact Set.mem_iUnion.mpr ⟨l, (ρ l).hom.left y,
      (congrArg (fun d : A l ⟶ V' => d.left y) (hz l)).trans hy⟩

include hc in
/-- At the pullback of an étale chart from one stage, the sections of the
presheaf inverse image are a filtered colimit of the sections on its stage
pullbacks. This includes quasi-compact quasi-separated overlap charts. -/
def modeledPresheafColimitCocone (p : c.pt ⟶ Y)
    (hp : ∀ j, c.π.app j ≫ (E.obj j).hom = p) (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ColimitCocone (CostructuredArrow.proj (baseChange p).op
      (op (Scheme.Etale.mk (pullback.fst (c.π.app i) v))) ⋙ P) := by
  let (j : Over i) : CompactSpace ((D (chartStages E v)).obj j) := modelCompact E v j
  let (j : Over i) : QuasiSeparatedSpace ((D (chartStages E v)).obj j) := modelQuasiSeparated E v j
  let {j k : Over i} (a : j ⟶ k) : IsAffineHom ((D (chartStages E v)).map a) :=
    model_transition_affine E v a
  exact PhilipponEtaleLimitPresheaf.pointwisePullbackCocone p (chartStages E v) (modelCone E v c)
    (pullback.fst (c.π.app i) v) (modelCone_comm E v c p hp) (modelCone_isLimit E v c hc)
    P (getColimitCocone ((chartStages E v).op ⋙ P))

section PointwiseExtension

variable (p : c.pt ⟶ Y) (hp : ∀ j, c.π.app j ≫ (E.obj j).hom = p)
  (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u})

private abbrev chartCocone (U : ((D E).obj i).Etale) :=
  ColimitCocone (CostructuredArrow.proj (baseChange p).op
    (op ((chartLimitFunctor E c i).obj U)) ⋙ P)

/-- The section colimit at a chart is independent of the choice of the
pointwise colimit cocone representing the inverse image. -/
def modeledStageColimitIso (U : ((D E).obj i).Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (d : chartCocone E c p P U) : (chartStageSections E i P ⋙ colim).obj (op U) ≅ d.cocone.pt := by
  let : CompactSpace ((𝟭 Scheme.{u}).obj U.left) := ‹CompactSpace U.left›
  let : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj U.left) := ‹QuasiSeparatedSpace U.left›
  let (j : Over i) : CompactSpace ((D (chartStages E U.hom)).obj j) := modelCompact E U.hom j
  let (j : Over i) : QuasiSeparatedSpace ((D (chartStages E U.hom)).obj j) :=
    modelQuasiSeparated E U.hom j
  let {j k : Over i} (a : j ⟶ k) : IsAffineHom ((D (chartStages E U.hom)).map a) :=
    model_transition_affine E U.hom a
  exact PhilipponEtaleLimitPresheaf.stageColimitIso p (chartStages E U.hom)
    (modelCone E U.hom c) (pullback.fst (c.π.app i) U.hom) (modelCone_comm E U.hom c p hp)
    (modelCone_isLimit E U.hom c hc) P d

omit [Etale v] [CompactSpace V] [QuasiSeparatedSpace V] in
theorem modeledStageColimitIso_naturality {U U' : ((D E).obj i).Etale} (b : U ⟶ U')
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    [CompactSpace U'.left] [QuasiSeparatedSpace U'.left]
    (d : chartCocone E c p P U) (d' : chartCocone E c p P U') (r : d'.cocone.pt ⟶ d.cocone.pt)
    (hr : ∀ j, d'.cocone.ι.app j ≫ r = d.cocone.ι.app
      ((CostructuredArrow.map ((chartLimitFunctor E c i).map b).op).obj j)) :
    (chartStageSections E i P ⋙ colim).map b.op ≫ (modeledStageColimitIso E c hc p hp P U d).hom =
      (modeledStageColimitIso E c hc p hp P U' d').hom ≫ r := by
  let : CompactSpace ((𝟭 Scheme.{u}).obj U.left) := ‹CompactSpace U.left›
  let : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj U.left) := ‹QuasiSeparatedSpace U.left›
  let : CompactSpace ((𝟭 Scheme.{u}).obj U'.left) := ‹CompactSpace U'.left›
  let : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj U'.left) := ‹QuasiSeparatedSpace U'.left›
  let (j : Over i) : CompactSpace ((D (chartStages E U.hom)).obj j) := modelCompact E U.hom j
  let (j : Over i) : QuasiSeparatedSpace ((D (chartStages E U.hom)).obj j) :=
    modelQuasiSeparated E U.hom j
  let {j k : Over i} (a : j ⟶ k) : IsAffineHom ((D (chartStages E U.hom)).map a) :=
    model_transition_affine E U.hom a
  let (j : Over i) : CompactSpace ((D (chartStages E U'.hom)).obj j) := modelCompact E U'.hom j
  let (j : Over i) : QuasiSeparatedSpace ((D (chartStages E U'.hom)).obj j) :=
    modelQuasiSeparated E U'.hom j
  let {j k : Over i} (a : j ⟶ k) : IsAffineHom ((D (chartStages E U'.hom)).map a) :=
    model_transition_affine E U'.hom a
  exact PhilipponEtaleLimitPresheaf.stageColimitIso_naturality
    p (chartStages E U.hom) (modelCone E U.hom c) (pullback.fst (c.π.app i) U.hom)
    (modelCone_comm E U.hom c p hp) (modelCone_isLimit E U.hom c hc)
    (chartStages E U'.hom) (modelCone E U'.hom c) (pullback.fst (c.π.app i) U'.hom)
    (modelCone_comm E U'.hom c p hp) (modelCone_isLimit E U'.hom c hc) P
    ((chartStagesFunctor E i).map b) ((chartLimitFunctor E c i).map b)
    (chartLimitMap_projection E U.hom U'.hom b.left (MorphismProperty.Over.w b) c) d d' r hr

variable (P' : c.pt.Etaleᵒᵖ ⥤ AddCommGrpCat.{u})
  (η : P ⟶ (baseChange p).op ⋙ P')

/-- A pointwise extension at a modeled chart computes the section colimit. -/
def modeledPresheafColimitIso (U : ((D E).obj i).Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (h : (Functor.LeftExtension.mk P' η).IsPointwiseLeftKanExtensionAt
      (op ((chartLimitFunctor E c i).obj U))) :
    (chartStageSections E i P ⋙ colim).obj (op U) ≅
      P'.obj (op ((chartLimitFunctor E c i).obj U)) :=
  modeledStageColimitIso E c hc p hp P U ⟨_, h⟩

omit [Etale v] [CompactSpace V] [QuasiSeparatedSpace V] in
theorem modeledPresheafColimitIso_naturality {U U' : ((D E).obj i).Etale} (b : U ⟶ U')
    [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    [CompactSpace U'.left] [QuasiSeparatedSpace U'.left]
    (h : (Functor.LeftExtension.mk P' η).IsPointwiseLeftKanExtensionAt
      (op ((chartLimitFunctor E c i).obj U)))
    (h' : (Functor.LeftExtension.mk P' η).IsPointwiseLeftKanExtensionAt
      (op ((chartLimitFunctor E c i).obj U'))) :
    (chartStageSections E i P ⋙ colim).map b.op ≫
        (modeledPresheafColimitIso E c hc p hp P P' η U h).hom =
      (modeledPresheafColimitIso E c hc p hp P P' η U' h').hom ≫
        P'.map ((chartLimitFunctor E c i).map b).op := by
  apply modeledStageColimitIso_naturality E c hc p hp P b ⟨_, h⟩ ⟨_, h'⟩
  intro j
  change (η.app j.left ≫ P'.map j.hom) ≫ P'.map ((chartLimitFunctor E c i).map b).op =
    η.app j.left ≫ P'.map (j.hom ≫ ((chartLimitFunctor E c i).map b).op)
  rw [P'.map_comp, Category.assoc]

end PointwiseExtension

end PhilipponEtaleModeledSections

end

end


