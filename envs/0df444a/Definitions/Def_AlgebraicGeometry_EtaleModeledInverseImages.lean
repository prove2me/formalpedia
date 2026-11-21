-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleModeledInverseImages
-- name    : AlgebraicGeometry_EtaleModeledInverseImages
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T03:07:43.577175+00:00
-- url     : https://prove2.me/theorems/b44e414f-d9d8-4315-9b8b-49be631f57a3
-- title:
--   Étale inverse image over affine inverse limits
-- statement:
--   Gluing for finite-stage étale charts and the comparison of their filtered sections with inverse image of an abelian sheaf.

import Definitions.Def_AlgebraicGeometry_EtaleModeledSections

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

open CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponFilteredSheafGluing

universe u

variable {C : Type*} [Category* C] {X : C} (E : PreOneHypercover.{u} X)

private def multicospanComp {A B : Type*} [Category* A] [Category* B]
    (P : Cᵒᵖ ⥤ A) (F : A ⥤ B) :
    (E.multicospanIndex (P ⋙ F)).multicospan ≅ (E.multicospanIndex P).multicospan ⋙ F :=
  NatIso.ofComponents (fun j => match j with
    | .left _ => Iso.refl _
    | .right _ => Iso.refl _) (by
    rintro _ _ (j | j | j)
    · rename_i j
      cases j <;> simp
    · change F.map (P.map (E.p₁ j.2).op) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (P.map (E.p₁ j.2).op)
      simp only [Category.comp_id, Category.id_comp]
    · change F.map (P.map (E.p₂ j.2).op) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (P.map (E.p₂ j.2).op)
      simp only [Category.comp_id, Category.id_comp])

private def multiforkComp {A B : Type*} [Category* A] [Category* B]
    (P : Cᵒᵖ ⥤ A) (F : A ⥤ B) :
    F.mapCone (E.multifork P) ≅
      (Cone.postcompose (multicospanComp E P F).hom).obj (E.multifork (P ⋙ F)) :=
  Cone.ext (Iso.refl _) (by
    rintro (j | j)
    · change F.map (P.map (E.f j).op) = 𝟙 _ ≫ F.map (P.map (E.f j).op) ≫ 𝟙 _
      rw [Category.comp_id, Category.id_comp]
    · change F.map (P.map (E.f j.1.1).op ≫ P.map (E.p₁ j.2).op) =
        𝟙 _ ≫ (F.map (P.map (E.f j.1.1).op) ≫ F.map (P.map (E.p₁ j.2).op)) ≫ 𝟙 _
      rw [Category.comp_id, Category.id_comp, F.map_comp])

/-- Section diagrams identified by a natural isomorphism have the same
gluing condition on a fixed hypercover. -/
def isLimitMultiforkOfIso {A : Type*} [Category* A] {P Q : Cᵒᵖ ⥤ A}
    (e : P ≅ Q) (h : IsLimit (E.multifork P)) : IsLimit (E.multifork Q) := by
  let T := 𝟭 (Cᵒᵖ)
  let hP := ((IsLimit.postcomposeHomEquiv (multicospanComp E T P) _).symm h).ofIsoLimit
    (multiforkComp E T P).symm
  let hQ := IsLimit.mapConeEquiv e hP
  exact IsLimit.postcomposeHomEquiv (multicospanComp E T Q) _
    (hQ.ofIsoLimit (multiforkComp E T Q))

/-- A filtered colimit of section diagrams preserves the gluing condition for
a fixed finite family and its finite family of overlaps. -/
def isLimitMultiforkColim {J : Type u} [Category.{u} J] [IsFiltered J]
    [Fintype E.I₀] [Fintype E.I₁']
    (P : Cᵒᵖ ⥤ J ⥤ AddCommGrpCat.{u})
    (h : ∀ j, IsLimit (E.multifork (P ⋙ (evaluation _ _).obj j))) :
    IsLimit (E.multifork (P ⋙ colim)) := by
  classical
  letI : Fintype E.multicospanShape.L := ‹Fintype E.I₀›
  letI : Fintype E.multicospanShape.R := ‹Fintype E.I₁'›
  letI : DecidableEq E.multicospanShape.L := Classical.decEq _
  letI : DecidableEq E.multicospanShape.R := Classical.decEq _
  let t : IsLimit (E.multifork P) :=
    evaluationJointlyReflectsLimits _ fun j =>
      ((IsLimit.postcomposeHomEquiv (multicospanComp E P ((evaluation _ _).obj j)) _).symm
        (h j)).ofIsoLimit (multiforkComp E P ((evaluation _ _).obj j)).symm
  exact IsLimit.postcomposeHomEquiv (multicospanComp E P colim) _
    ((isLimitOfPreserves colim t).ofIsoLimit (multiforkComp E P colim))

end PhilipponFilteredSheafGluing

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleModeledSections
open PhilipponEtaleBaseChangeComparison (baseChange)


namespace PhilipponEtaleModeledGluing

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {Y : Scheme.{u}} (E : I ⥤ Y.Etale)

private abbrev D := E ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y

/-- The section colimits over the stages satisfy gluing on every finite
étale hypercover of a chart at the chosen stage. -/
def isLimitStageSectionMultifork {i : I} {U : ((D E).obj i).Etale}
    (H : ((D E).obj i).smallEtaleTopology.OneHypercover.{u} U)
    [Fintype H.I₀] [Fintype H.I₁']
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    IsLimit (H.multifork (chartStageSections E i F.obj ⋙ colim)) :=
  PhilipponFilteredSheafGluing.isLimitMultiforkColim H.toPreOneHypercover _ fun j =>
    H.isLimitMultifork ⟨_, chartStageSections_isSheaf E j F⟩

/-- The quasi-compact, quasi-separated charts in the small étale site. -/
def qcqsCharts (X : Scheme.{u}) : ObjectProperty X.Etale :=
  fun U => CompactSpace U.left ∧ QuasiSeparatedSpace U.left

/-- A hypercover whose objects are in a full subcategory can be viewed as a
pre-hypercover in that subcategory. -/
def fullSubcategoryHypercover {C : Type*} [Category* C] (V : ObjectProperty C)
    {U : C} (hU : V U) (H : PreOneHypercover.{u} U) (hX : ∀ j, V (H.X j))
    (hY : ∀ ⦃j k⦄ (b : H.I₁ j k), V (H.Y b)) :
    PreOneHypercover.{u} (⟨U, hU⟩ : V.FullSubcategory) where
  I₀ := H.I₀
  X j := ⟨H.X j, hX j⟩
  f j := ObjectProperty.homMk (H.f j)
  I₁ := H.I₁
  Y _ _ b := ⟨H.Y b, hY b⟩
  p₁ _ _ b := ObjectProperty.homMk (H.p₁ b)
  p₂ _ _ b := ObjectProperty.homMk (H.p₂ b)
  w _ _ b := ObjectProperty.hom_ext V (H.w b)

section Limit

variable (c : Cone (D E)) (hc : IsLimit c)
  [∀ {j k : I} (b : j ⟶ k), IsAffineHom ((D E).map b)]
  (p : c.pt ⟶ Y) (hp : ∀ j, c.π.app j ≫ (E.obj j).hom = p)
  (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) (P' : c.pt.Etaleᵒᵖ ⥤ AddCommGrpCat.{u})
  (η : P ⟶ (baseChange p).op ⋙ P')

private abbrev incl (i : I) := (qcqsCharts ((D E).obj i)).ι

variable {i : I}
  (h : ∀ U : (qcqsCharts ((D E).obj i)).FullSubcategory,
    (Functor.LeftExtension.mk P' η).IsPointwiseLeftKanExtensionAt
      (op ((chartLimitFunctor E c i).obj U.obj)))

/-- On the quasi-compact, quasi-separated charts from a fixed stage the
pointwise extension and the stage section colimits are naturally isomorphic. -/
def stageSectionIso : (incl E i).op ⋙ (chartStageSections E i P ⋙ colim) ≅
    (incl E i ⋙ chartLimitFunctor E c i).op ⋙ P' := by
  refine NatIso.ofComponents (fun U => ?_) ?_
  · letI : CompactSpace U.unop.obj.left := U.unop.property.1
    letI : QuasiSeparatedSpace U.unop.obj.left := U.unop.property.2
    exact modeledPresheafColimitIso E c hc p hp P P' η U.unop.obj (h U.unop)
  · intro U V b
    let : CompactSpace U.unop.obj.left := U.unop.property.1
    let : QuasiSeparatedSpace U.unop.obj.left := U.unop.property.2
    let : CompactSpace V.unop.obj.left := V.unop.property.1
    let : QuasiSeparatedSpace V.unop.obj.left := V.unop.property.2
    exact modeledPresheafColimitIso_naturality E c hc p hp P P' η
      (U := V.unop.obj) (U' := U.unop.obj) b.unop.hom (h V.unop) (h U.unop)

private def isLimitModeledSectionMultiforkAux {U : (qcqsCharts ((D E).obj i)).FullSubcategory}
    (H : PreOneHypercover.{u} U) [Fintype H.I₀] [Fintype H.I₁']
    (H₀ : ((D E).obj i).smallEtaleTopology.OneHypercover.{u} U.obj)
    (hH : H.map (incl E i) = H₀.toPreOneHypercover)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (ηF : F.obj ⟶ (baseChange p).op ⋙ P')
    (hF : ∀ V : (qcqsCharts ((D E).obj i)).FullSubcategory,
      (Functor.LeftExtension.mk P' ηF).IsPointwiseLeftKanExtensionAt
        (op ((chartLimitFunctor E c i).obj V.obj))) :
    IsLimit ((H.map (incl E i ⋙ chartLimitFunctor E c i)).multifork P') := by
  letI : Fintype H₀.I₀ := by
    rw [← hH]
    exact ‹Fintype H.I₀›
  letI : Fintype H₀.I₁' := by
    rw [← hH]
    exact ‹Fintype H.I₁'›
  let R := chartStageSections E i F.obj ⋙ colim
  have t : IsLimit ((H.map (incl E i)).multifork R) := by
    rw [hH]
    exact isLimitStageSectionMultifork E H₀ F
  let t' := (H.isLimitMapMultiforkEquiv (incl E i) R) t
  let e := stageSectionIso E c hc p hp F.obj P' ηF hF
  exact (H.isLimitMapMultiforkEquiv (incl E i ⋙ chartLimitFunctor E c i) P').symm
    (PhilipponFilteredSheafGluing.isLimitMultiforkOfIso H e t')

/-- Gluing for the pointwise extension on the pullback of a finite stage
hypercover whose charts and overlaps are quasi-compact and quasi-separated. -/
def isLimitModeledSectionMultifork {U : ((D E).obj i).Etale}
    (H : ((D E).obj i).smallEtaleTopology.OneHypercover.{u} U) [Fintype H.I₀] [Fintype H.I₁']
    (hU : qcqsCharts ((D E).obj i) U) (hX : ∀ j, qcqsCharts ((D E).obj i) (H.X j))
    (hY : ∀ ⦃j k⦄ (b : H.I₁ j k), qcqsCharts ((D E).obj i) (H.Y b))
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (ηF : F.obj ⟶ (baseChange p).op ⋙ P')
    (hF : ∀ V : (qcqsCharts ((D E).obj i)).FullSubcategory,
      (Functor.LeftExtension.mk P' ηF).IsPointwiseLeftKanExtensionAt
        (op ((chartLimitFunctor E c i).obj V.obj))) :
    IsLimit ((H.toPreOneHypercover.map (chartLimitFunctor E c i)).multifork P') := by
  let H' := fullSubcategoryHypercover _ hU H.toPreOneHypercover hX hY
  letI : Fintype H'.I₀ := ‹Fintype H.I₀›
  letI : Fintype H'.I₁' := ‹Fintype H.I₁'›
  exact isLimitModeledSectionMultiforkAux E c hc p hp P' H' H rfl F ηF hF

end Limit

end PhilipponEtaleModeledGluing

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial


namespace PhilipponCech

section WidePullbackProperties

variable {C : Type*} [Category* C] [HasFiniteLimits C]
  (P : ObjectProperty C) {V U : C} (f : V ⟶ U)

private abbrev family (n : ℕ) : Fin n → (V ⟶ U) := fun _ => f

/-- A property closed under isomorphisms and pullbacks over objects with
the property holds on all finite powers in the slice over such an object. -/
theorem widePullback_prop_of_pullbacks [P.IsClosedUnderIsomorphisms]
    (hp : ∀ ⦃X Y Z : C⦄ (g : X ⟶ Z) (h : Y ⟶ Z), P X → P Y → P Z → P (pullback g h))
    (hU : P U) (hV : P V) (n : ℕ) : P (widePullback U (fun _ : Fin n => V) (family f n)) := by
  induction n with
  | zero =>
    let c : WidePullbackCone (family f 0) := WidePullbackCone.mk (𝟙 U)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    let h : IsLimit c := WidePullbackCone.IsLimit.mk c (fun d => d.base)
      (fun d => Category.comp_id _) (fun _ i => Fin.elim0 i)
      (fun _ m hm _ => (Category.comp_id m).symm.trans hm)
    exact P.prop_of_iso (h.conePointUniqueUpToIso (limit.isLimit _)) hU
  | succ n ih =>
    let b := WidePullback.base (family f n)
    let u := pullback.fst b f
    let v := pullback.snd b f
    let p (i : Fin (n + 1)) : pullback b f ⟶ V :=
      Fin.cases v (fun j => u ≫ WidePullback.π (family f n) j) i
    let c : WidePullbackCone (family f (n + 1)) := WidePullbackCone.mk (v ≫ f) p (by
      intro i
      refine Fin.cases rfl (fun j => ?_) i
      change (u ≫ WidePullback.π (family f n) j) ≫ f = v ≫ f
      rw [Category.assoc, WidePullback.π_arrow (family f n) j]
      exact pullback.condition)
    let restrict (d : WidePullbackCone (family f (n + 1))) :=
      WidePullback.lift (arrows := family f n) d.base (fun i => d.π i.succ)
        (fun i => d.condition i.succ)
    have hr (d : WidePullbackCone (family f (n + 1))) : restrict d ≫ b = d.base :=
      WidePullback.lift_base ..
    let lift (d : WidePullbackCone (family f (n + 1))) :=
      pullback.lift (restrict d) (d.π 0) ((hr d).trans (d.condition 0).symm)
    let h : IsLimit c := WidePullbackCone.IsLimit.mk c lift (by
      intro d
      change lift d ≫ v ≫ f = _
      rw [pullback.lift_snd_assoc]
      exact d.condition 0) (by
      intro d i
      refine Fin.cases ?_ (fun j => ?_) i
      · change lift d ≫ v = _
        exact pullback.lift_snd ..
      · change lift d ≫ u ≫ WidePullback.π (family f n) j = d.π j.succ
        rw [pullback.lift_fst_assoc]
        exact WidePullback.lift_π ..) (by
      intro d m hb hp'
      have h₁ : lift d ≫ u = restrict d := pullback.lift_fst ..
      have h₂ : lift d ≫ v = d.π 0 := pullback.lift_snd ..
      apply pullback.hom_ext
      · rw [h₁]
        apply WidePullback.hom_ext
        · intro j
          rw [Category.assoc, WidePullback.lift_π]
          exact hp' j.succ
        · rw [hr, Category.assoc, pullback.condition]
          exact hb
      · rw [h₂]
        exact hp' 0)
    exact P.prop_of_iso (h.conePointUniqueUpToIso (limit.isLimit _)) (hp b f ih hV hU)

end WidePullbackProperties

variable {C D : Type*} [Category* C] [Category* D] [HasFiniteLimits C] [HasFiniteLimits D]
  (G : C ⥤ D) [PreservesFiniteLimits G] {V U : C} (f : V ⟶ U)

private abbrev arrows (n : ℕ) : Fin n → (V ⟶ U) := fun _ => f

private def mappedCone (n : ℕ) : WidePullbackCone (fun _ : Fin n => G.map f) :=
  WidePullbackCone.mk (G.map (WidePullback.base (arrows f n)))
    (fun i => G.map (WidePullback.π (arrows f n) i)) (by
      intro i
      rw [← G.map_comp, WidePullback.π_arrow])

private def mappedConeIsLimit (n : ℕ) : IsLimit (mappedCone G f n) := by
  let K := WidePullbackShape.wideCospan U (fun _ : Fin n => V) (arrows f n)
  let c := G.mapCone (limit.cone K)
  let e := WidePullbackShape.diagramIsoWideCospan (K ⋙ G)
  let hc : IsLimit c := isLimitOfPreserves G (limit.isLimit K)
  let h := (IsLimit.postcomposeHomEquiv e c).symm hc
  exact h.ofIsoLimit (Cone.ext (Iso.refl _) (by
    rintro (_ | _) <;> simp [mappedCone, c, e, WidePullbackShape.diagramIsoWideCospan] <;> rfl))

private def wideIso (n : ℕ) :
    G.obj (widePullback U (fun _ : Fin n => V) (arrows f n)) ≅
      widePullback (G.obj U) (fun _ : Fin n => G.obj V) (fun _ => G.map f) :=
  (mappedConeIsLimit G f n).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc]
private theorem wideIso_π (n : ℕ) (i : Fin n) :
    (wideIso G f n).hom ≫ WidePullback.π (fun _ : Fin n => G.map f) i =
      G.map (WidePullback.π (arrows f n) i) :=
  (mappedConeIsLimit G f n).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some i)

@[reassoc]
private theorem wideIso_base (n : ℕ) :
    (wideIso G f n).hom ≫ WidePullback.base (fun _ : Fin n => G.map f) =
      G.map (WidePullback.base (arrows f n)) :=
  (mappedConeIsLimit G f n).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none

/-- A finite-limit-preserving functor carries the Čech nerve to the Čech
nerve of the image arrow, with all faces and degeneracies. -/
def cechNerveMapIso : (Arrow.mk f).cechNerve ⋙ G ≅ (Arrow.mk (G.map f)).cechNerve :=
  NatIso.ofComponents (fun n => wideIso G f (n.unop.len + 1)) (by
    intro n m a
    apply WidePullback.hom_ext
    · intro i
      change (G.map ((Arrow.mk f).cechNerve.map a) ≫ (wideIso G f _).hom) ≫
        WidePullback.π _ i = ((wideIso G f _).hom ≫ (Arrow.mk (G.map f)).cechNerve.map a) ≫
          WidePullback.π _ i
      rw [Category.assoc, wideIso_π, ← G.map_comp, Category.assoc]
      have h₁ : (Arrow.mk f).cechNerve.map a ≫ WidePullback.π (arrows f _) i =
          WidePullback.π (arrows f _) (a.unop.toOrderHom i) := WidePullback.lift_π ..
      have h₂ : (Arrow.mk (G.map f)).cechNerve.map a ≫ WidePullback.π (arrows (G.map f) _) i =
          WidePullback.π (arrows (G.map f) _) (a.unop.toOrderHom i) := WidePullback.lift_π ..
      rw [h₁]
      change _ = (wideIso G f _).hom ≫ (Arrow.mk (G.map f)).cechNerve.map a ≫
        WidePullback.π (arrows (G.map f) _) i
      rw [h₂, wideIso_π]
    · change (G.map ((Arrow.mk f).cechNerve.map a) ≫ (wideIso G f _).hom) ≫
        WidePullback.base _ = ((wideIso G f _).hom ≫ (Arrow.mk (G.map f)).cechNerve.map a) ≫
          WidePullback.base _
      rw [Category.assoc, wideIso_base, ← G.map_comp, Category.assoc]
      have h₁ : (Arrow.mk f).cechNerve.map a ≫ WidePullback.base (arrows f (m.unop.len + 1)) =
          WidePullback.base (arrows f (n.unop.len + 1)) := WidePullback.lift_base ..
      have h₂ : (Arrow.mk (G.map f)).cechNerve.map a ≫ WidePullback.base (arrows (G.map f) (m.unop.len + 1)) =
          WidePullback.base (arrows (G.map f) (n.unop.len + 1)) := WidePullback.lift_base ..
      rw [h₁]
      change _ = (wideIso G f _).hom ≫ (Arrow.mk (G.map f)).cechNerve.map a ≫
        WidePullback.base (arrows (G.map f) (m.unop.len + 1))
      rw [h₂, wideIso_base])

end PhilipponCech

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleModeledSections PhilipponEtaleModeledGluing
open PhilipponEtaleBaseChangeComparison (baseChange)


namespace PhilipponEtaleRefinementGluing

universe u

private theorem qcqs_overlap {X : Scheme.{u}} {T V W : X.Etale}
    [QuasiSeparatedSpace T.left] [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] (f : V ⟶ T) (g : W ⟶ T) :
    qcqsCharts X (pullback f g) := by
  let K := Scheme.Etale.forget X ⋙ Over.forget X
  let : PreservesLimitsOfShape WalkingCospan K := by dsimp [K]; infer_instance
  have h : IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
    (IsPullback.of_hasPullback f g).map K
  let : QuasiCompact g.left := quasiCompact_of_compactSpace g.left
  let : QuasiSeparated g.left := QuasiSeparated.of_quasiSeparatedSpace g.left
  let e := h.isoPullback
  let : CompactSpace ↥(pullback f.left g.left) := inferInstance
  let : QuasiSeparatedSpace ↥(pullback f.left g.left) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst f.left g.left)
  exact ⟨QuasiCompact.compactSpace_of_compactSpace e.hom,
    quasiSeparatedSpace_of_quasiSeparated e.hom⟩

instance qcqsCharts_closedUnderIsomorphisms (X : Scheme.{u}) :
    (qcqsCharts X).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let K := Scheme.Etale.forget X ⋙ Over.forget X
    let e' := K.mapIso e
    let : CompactSpace ↥(K.obj _) := h.1
    let : QuasiSeparatedSpace ↥(K.obj _) := h.2
    exact ⟨QuasiCompact.compactSpace_of_compactSpace e'.inv,
      quasiSeparatedSpace_of_quasiSeparated e'.inv⟩

/-- Every term of the Čech nerve of a map of qcqs charts is again qcqs. -/
theorem qcqsCharts_cechNerve {X : Scheme.{u}} {U V : X.Etale}
    (f : V ⟶ U) (hU : qcqsCharts X U) (hV : qcqsCharts X V) (n : SimplexCategoryᵒᵖ) :
    qcqsCharts X ((Arrow.mk f).cechNerve.obj n) := by
  apply PhilipponCech.widePullback_prop_of_pullbacks (qcqsCharts X) f _ hU hV (n.unop.len + 1)
  intro A B T a b hA hB hT
  let : CompactSpace A.left := hA.1
  let : QuasiSeparatedSpace A.left := hA.2
  let : CompactSpace B.left := hB.1
  let : QuasiSeparatedSpace B.left := hB.2
  let : QuasiSeparatedSpace T.left := hT.2
  exact qcqs_overlap a b

private theorem isSheafFor_of_multifork {C A : Type*} [Category* C] [Category* A]
    {V U : C} (H : PreOneHypercover.{u} V) (e : U ≅ V) (P : Cᵒᵖ ⥤ A)
    (h : IsLimit (H.multifork P)) (B : Aᵒᵖ) :
    (Presieve.ofArrows H.X (fun i => H.f i ≫ e.inv)).IsSheafFor (P ⋙ coyoneda.obj B) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let N : Multifork (H.multicospanIndex P) := Multifork.ofι _ B.unop x (by
    rintro ⟨⟨i, j⟩, k⟩
    exact hx i j (H.Y k) (H.p₁ k) (H.p₂ k) (by
      simpa only [Category.assoc] using congrArg (· ≫ e.inv) (H.w k)))
  have hι (i : H.I₀) : h.lift N ≫ P.map (H.f i).op = x i :=
    h.fac N (.left i)
  refine ⟨h.lift N ≫ P.map e.hom.op, ?_, ?_⟩
  · intro i
    change (h.lift N ≫ P.map e.hom.op) ≫ P.map (H.f i ≫ e.inv).op = x i
    rw [op_comp, P.map_comp, Category.assoc, ← P.map_comp_assoc, ← op_comp,
      e.inv_hom_id, op_id, P.map_id, Category.id_comp, hι]
  · intro t ht
    apply (cancel_mono (P.map e.inv.op)).mp
    have he : (h.lift N ≫ P.map e.hom.op) ≫ P.map e.inv.op = h.lift N := by
      rw [Category.assoc, ← P.map_comp, ← op_comp, e.inv_hom_id, op_id, P.map_id]
      exact Category.comp_id (h.lift N)
    rw [he]
    apply Multifork.IsLimit.hom_ext h
    intro i
    change (t ≫ P.map e.inv.op) ≫ P.map (H.f i).op = h.lift N ≫ P.map (H.f i).op
    rw [Category.assoc, ← P.map_comp, ← op_comp, hι]
    exact ht i

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {Y : Scheme.{u}} (E : I ⥤ Y.Etale)

private abbrev D := E ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y

/-- Charts isomorphic to the pullback of a quasi-compact, quasi-separated
chart at a stage. -/
def modeledCharts (c : Cone (D E)) : ObjectProperty c.pt.Etale := fun U =>
  ∃ (i : I) (V : ((D E).obj i).Etale),
    qcqsCharts ((D E).obj i) V ∧ Nonempty (U ≅ (chartLimitFunctor E c i).obj V)

variable (c : Cone (D E)) (hc : IsLimit c)
  [∀ {j k : I} (b : j ⟶ k), IsAffineHom ((D E).map b)]

include hc in
/-- Every étale chart of the limit is covered by affine open charts having
affine models at stages. -/
theorem modeledCharts_hasCover (U : c.pt.Etale) :
    ∃ (ι : Type u) (V : ι → (modeledCharts E c).FullSubcategory)
      (f : ∀ x, ((modeledCharts E c).ι.obj (V x)) ⟶ U),
      Sieve.ofArrows _ f ∈ c.pt.smallEtaleTopology U := by
  choose i A W a v g hA ha hmem hW hv hpb using fun x : U.left =>
    PhilipponEtaleCoverLimitDescent.exists_affine_refinement_model_at_point (D E) c hc U.hom x
  let (x : U.left) : IsOpenImmersion (a x) := ha x
  let (x : U.left) : Etale (v x) := hv x
  let V (x : U.left) := Scheme.Etale.mk (a x ≫ U.hom)
  let f (x : U.left) : V x ⟶ U := MorphismProperty.Over.homMk (a x) rfl trivial
  let P (x : U.left) := Scheme.Etale.mk (v x)
  have hV (x : U.left) : modeledCharts E c (V x) := by
    let : IsAffine (W x) := hW x
    let e : V x ≅ (chartLimitFunctor E c (i x)).obj (P x) :=
      MorphismProperty.Over.isoMk (hpb x).isoPullback (hpb x).isoPullback_hom_fst
    exact ⟨i x, P x, ⟨inferInstanceAs (CompactSpace (W x)),
      inferInstanceAs (QuasiSeparatedSpace (W x))⟩, ⟨e⟩⟩
  refine ⟨U.left, fun x => ⟨V x, hV x⟩, f, ?_⟩
  exact (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr <|
    Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨x, hmem x⟩

include hc in
theorem modeledCharts_coverDense : (modeledCharts E c).ι.IsCoverDense c.pt.smallEtaleTopology where
  is_cover U := by
    obtain ⟨β, V, f, hf⟩ := modeledCharts_hasCover E c hc U
    apply c.pt.smallEtaleTopology.superset_covering _ hf
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    exact Presieve.in_coverByImage (modeledCharts E c).ι (f x)

include hc in
/-- Restrict a sheaf to the modeled charts with the induced topology. -/
def modeledChartsRestriction : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf ((modeledCharts E c).ι.inducedTopology c.pt.smallEtaleTopology) AddCommGrpCat.{u} := by
  let G := (modeledCharts E c).ι
  let J := c.pt.smallEtaleTopology
  let : G.IsCoverDense J := modeledCharts_coverDense E c hc
  exact G.sheafPushforwardContinuous _ _ _

/-- Restriction to the modeled charts is an equivalence on abelian sheaves. -/
theorem modeledCharts_restrictionEquivalence : (modeledChartsRestriction E c hc).IsEquivalence := by
  let G := (modeledCharts E c).ι
  let J := c.pt.smallEtaleTopology
  let J₀ := G.inducedTopology J
  let : G.IsCoverDense J := modeledCharts_coverDense E c hc
  let : G.IsDenseSubsite J₀ J := inferInstance
  let : G.IsOneHypercoverDense.{u} J₀ J := Functor.IsOneHypercoverDense.of_hasPullbacks
    (modeledCharts_hasCover E c hc)
  exact Functor.isEquivalence_of_isOneHypercoverDense G J₀ J AddCommGrpCat.{u}

private abbrev incl := (modeledCharts E c).ι

private abbrev topology := (incl E c).inducedTopology c.pt.smallEtaleTopology

/-- The pullback from a stage, as a functor into the modeled subsite. -/
def stageToModeled (i : I) : (qcqsCharts ((D E).obj i)).FullSubcategory ⥤
    (modeledCharts E c).FullSubcategory :=
  (modeledCharts E c).lift ((qcqsCharts ((D E).obj i)).ι ⋙ chartLimitFunctor E c i)
    (fun U => ⟨i, U.obj, U.property, ⟨Iso.refl _⟩⟩)

variable (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
  (P : (modeledCharts E c).FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u})
  (stageIso : ∀ i, (qcqsCharts ((D E).obj i)).ι.op ⋙ (chartStageSections E i F.obj ⋙ colim) ≅
    (stageToModeled E c i).op ⋙ P)

include hc stageIso in
/-- A cover in the modeled subsite has a covering refinement on which
the presheaf given by the stage section colimits satisfies the sheaf condition. -/
theorem exists_covering_gluing_subsieve {U : (modeledCharts E c).FullSubcategory}
    (S : Sieve U) (hS : S ∈ topology E c U) :
    ∃ R : Sieve U, R ≤ S ∧ R ∈ topology E c U ∧
      ∀ B : AddCommGrpCat.{u}ᵒᵖ, R.arrows.IsSheafFor (P ⋙ coyoneda.obj B) := by
  let G := incl E c
  let : G.IsCoverDense c.pt.smallEtaleTopology := modeledCharts_coverDense E c hc
  have hS' := (G.mem_inducedTopology_iff_of_isCoverDense _ S).mp hS
  obtain ⟨i, U₀, hU₀, ⟨z⟩⟩ := U.property
  let : CompactSpace U₀.left := hU₀.1
  let : QuasiSeparatedSpace U₀.left := hU₀.2
  obtain ⟨j, T, e, β, hβ, W, a, hT, hT', hW, hstage, hmem, hcover⟩ :=
    exists_modeled_cover_refinement E c hc ((S.functorPushforward G).pullback z.inv)
      (c.pt.smallEtaleTopology.pullback_stable z.inv hS')
  let : Fintype β := hβ
  let H₀ : PreZeroHypercover.{u} T := ⟨β, W, a⟩
  let H : ((D E).obj j).smallEtaleTopology.OneHypercover.{u} T :=
    GrothendieckTopology.OneHypercover.mk' H₀.toPreOneHypercover hstage (by simp)
  let : Fintype H.I₀ := hβ
  let : Finite H.I₁' := by
    change Finite (Sigma fun _ : β × β => PUnit)
    infer_instance
  let : Fintype H.I₁' := Fintype.ofFinite _
  let : QuasiSeparatedSpace T.left := hT'
  have h₀ (l : H.I₀) : qcqsCharts ((D E).obj j) (H.X l) := by
    let : IsAffine (W l).left := hW l
    exact ⟨inferInstanceAs (CompactSpace (W l).left),
      inferInstanceAs (QuasiSeparatedSpace (W l).left)⟩
  have h₁ ⦃l l' : H.I₀⦄ (b : H.I₁ l l') : qcqsCharts ((D E).obj j) (H.Y b) := by
    let : CompactSpace (W l).left := (h₀ l).1
    let : QuasiSeparatedSpace (W l).left := (h₀ l).2
    let : CompactSpace (W l').left := (h₀ l').1
    let : QuasiSeparatedSpace (W l').left := (h₀ l').2
    exact qcqs_overlap (a l) (a l')
  let V₀ : (qcqsCharts ((D E).obj j)).FullSubcategory := ⟨T, ⟨hT, hT'⟩⟩
  let H₁ : PreOneHypercover V₀ := fullSubcategoryHypercover _ V₀.property H.toPreOneHypercover h₀ h₁
  let G₀ := (qcqsCharts ((D E).obj j)).ι
  let R := chartStageSections E j F.obj ⋙ colim
  have t : IsLimit ((H₁.map G₀).multifork R) := isLimitStageSectionMultifork E H F
  let t₁ := (H₁.isLimitMapMultiforkEquiv G₀ R) t
  let t₂ := PhilipponFilteredSheafGluing.isLimitMultiforkOfIso H₁ (stageIso j) t₁
  let K := chartLimitFunctor E c j
  let K' := stageToModeled E c j
  let H' := H₁.map K'
  let e' : U ≅ K'.obj V₀ := ObjectProperty.isoMk (modeledCharts E c) (z ≪≫ e)
  let a' (l : β) := H'.f l ≫ e'.inv
  refine ⟨Sieve.ofArrows H'.X a', ?_, ?_, fun B => ?_⟩
  · apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨l⟩
    rw [← Sieve.functorPullback_functorPushforward_eq G (S := S)]
    exact hmem l
  · apply (G.mem_inducedTopology_iff_of_isCoverDense _ _).mpr
    rw [Sieve.functorPushforward_ofArrows]
    apply c.pt.smallEtaleTopology.superset_covering _
      (c.pt.smallEtaleTopology.pullback_stable z.hom hcover)
    rintro B f ⟨V, g, _, ⟨l⟩, hf⟩
    refine ⟨_, g, _, ⟨l⟩, ?_⟩
    have he := congrArg (· ≫ z.inv) hf
    change (g ≫ K.map (a l) ≫ e.inv) ≫ z.inv = (f ≫ z.hom) ≫ z.inv at he
    change g ≫ K.map (a l) ≫ e.inv ≫ z.inv = f
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he
  · apply (Presieve.isSheafFor_iff_generate _).mp
    exact isSheafFor_of_multifork H' e' P ((H₁.isLimitMapMultiforkEquiv K' P).symm t₂) B

include hc stageIso in
/-- On the dense subsite of modeled quasi-compact, quasi-separated charts,
the presheaf identified with the stage section colimits is a sheaf. -/
theorem isSheaf_on_modeledCharts : Presheaf.IsSheaf (topology E c) P := by
  intro B U S hS
  obtain ⟨R, hRS, hRcov, hR⟩ := exists_covering_gluing_subsieve E c hc F P stageIso S hS
  apply Presieve.isSheafFor_subsieve_aux _ hRS (hR (op B))
  intro W f _
  obtain ⟨T, hT, _, hTglue⟩ := exists_covering_gluing_subsieve E c hc F P stageIso
    (R.pullback f) ((topology E c).pullback_stable f hRcov)
  intro x y₁ y₂ hy₁ hy₂
  exact (hTglue (op B)).isSeparatedFor _ _ _ (Presieve.isAmalgamation_restrict hT x _ hy₁)
    (Presieve.isAmalgamation_restrict hT x _ hy₂)

end PhilipponEtaleRefinementGluing

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponRestrictedKan

variable {A B C W : Type*} [Category* A] [Category* B] [Category* C] [Category* W]
  (L : A ⥤ B) (F : A ⥤ W) (G : C ⥤ B)
  (d : ∀ c : C, ColimitCocone (CostructuredArrow.proj L (G.obj c) ⋙ F))

private def postcomposeCocone {x y : C} (f : x ⟶ y) :
    Cocone (CostructuredArrow.proj L (G.obj x) ⋙ F) :=
  (d y).cocone.whisker (CostructuredArrow.map (G.map f))

/-- The pointwise left Kan colimits at objects in the image of `G` form a
functor on the domain of `G`. -/
def restrictedColimit : C ⥤ W where
  obj x := (d x).cocone.pt
  map {x y} f := (d x).isColimit.desc (postcomposeCocone L F G d f)
  map_id x := (d x).isColimit.hom_ext fun j => by
    rw [(d x).isColimit.fac]
    change (d x).cocone.ι.app ((CostructuredArrow.map (G.map (𝟙 x))).obj j) = _
    rw [G.map_id, Category.comp_id]
    congr 1
    exact CostructuredArrow.map_id
  map_comp {x y z} f g := (d x).isColimit.hom_ext fun j => by
    rw [(d x).isColimit.fac, ← Category.assoc, (d x).isColimit.fac]
    change (d z).cocone.ι.app ((CostructuredArrow.map (G.map (f ≫ g))).obj j) =
      (d y).cocone.ι.app ((CostructuredArrow.map (G.map f)).obj j) ≫ _
    rw [(d y).isColimit.fac]
    change _ = (d z).cocone.ι.app
      ((CostructuredArrow.map (G.map g)).obj ((CostructuredArrow.map (G.map f)).obj j))
    rw [G.map_comp]
    congr 1
    exact CostructuredArrow.map_comp

@[reassoc]
theorem ι_map {x y : C} (f : x ⟶ y) (j : CostructuredArrow L (G.obj x)) :
    (d x).cocone.ι.app j ≫ (restrictedColimit L F G d).map f =
      (d y).cocone.ι.app ((CostructuredArrow.map (G.map f)).obj j) :=
  (d x).isColimit.fac (postcomposeCocone L F G d f) j

variable {P : B ⥤ W}

/-- A natural family from `F` into `P` over `L` induces a map out of the
restricted colimit. -/
def descend (η : F ⟶ L ⋙ P) : restrictedColimit L F G d ⟶ G ⋙ P where
  app x := (d x).isColimit.desc (Functor.costructuredArrowMapCocone L F P η (G.obj x))
  naturality {x y} f := (d x).isColimit.hom_ext fun j => by
    rw [ι_map_assoc, (d y).isColimit.fac, ← Category.assoc, (d x).isColimit.fac]
    change η.app j.left ≫ P.map (j.hom ≫ G.map f) =
      (η.app j.left ≫ P.map j.hom) ≫ P.map (G.map f)
    rw [P.map_comp, Category.assoc]

@[reassoc]
theorem ι_descend (η : F ⟶ L ⋙ P) (x : C) (j : CostructuredArrow L (G.obj x)) :
    (d x).cocone.ι.app j ≫ (descend L F G d η).app x = η.app j.left ≫ P.map j.hom :=
  (d x).isColimit.fac (Functor.costructuredArrowMapCocone L F P η (G.obj x)) j

theorem descend_postcompose {P' : B ⥤ W} (ν : P ⟶ P') (η : F ⟶ L ⋙ P) :
    descend L F G d (η ≫ Functor.whiskerLeft L ν) =
      descend L F G d η ≫ Functor.whiskerLeft G ν := by
  ext x
  apply (d x).isColimit.hom_ext
  intro j
  simp only [NatTrans.comp_app, ι_descend, ι_descend_assoc]
  change (η.app j.left ≫ ν.app (L.obj j.left)) ≫ P'.map j.hom =
    η.app j.left ≫ P.map j.hom ≫ ν.app (G.obj x)
  rw [Category.assoc, ν.naturality]

private abbrev rightExtension (P : B ⥤ W) : Functor.RightExtension G (G ⋙ P) :=
  Functor.RightExtension.mk P (𝟙 (G ⋙ P))

private theorem coneAt_π {b : B} (j : StructuredArrow b G) :
    ((rightExtension G P).coneAt b).π.app j = P.map j.hom := Category.comp_id _

private def testCone (θ : restrictedColimit L F G d ⟶ G ⋙ P) (x : A) :
    Cone (StructuredArrow.proj (L.obj x) G ⋙ G ⋙ P) where
  pt := F.obj x
  π :=
    { app := fun j => (d j.right).cocone.ι.app (CostructuredArrow.mk j.hom) ≫ θ.app j.right
      naturality := by
        intro j k f
        symm
        change ((d j.right).cocone.ι.app (CostructuredArrow.mk j.hom) ≫ θ.app j.right) ≫
          (G ⋙ P).map f.right = 𝟙 _ ≫ (d k.right).cocone.ι.app (CostructuredArrow.mk k.hom) ≫ θ.app k.right
        rw [Category.id_comp, Category.assoc, ← θ.naturality, ι_map_assoc]
        congr 2
        rw [CostructuredArrow.map_mk, StructuredArrow.w] }

/-- When the test functor is a pointwise right Kan extension from `G`, a
map out of the restricted colimit determines a natural family over `L`. -/
def ascend (h : (rightExtension G P).IsPointwiseRightKanExtension)
    (θ : restrictedColimit L F G d ⟶ G ⋙ P) : F ⟶ L ⋙ P where
  app x := (h (L.obj x)).lift (testCone L F G d θ x)
  naturality {x y} f := (h (L.obj y)).hom_ext fun j => by
    let k : StructuredArrow (L.obj x) G := StructuredArrow.mk (L.map f ≫ j.hom)
    have hw : (h (L.obj x)).lift (testCone L F G d θ x) ≫ P.map (L.map f ≫ j.hom) =
        (d j.right).cocone.ι.app (CostructuredArrow.mk (L.map f ≫ j.hom)) ≫ θ.app j.right := by
      have w := (h (L.obj x)).fac (testCone L F G d θ x) k
      rw [coneAt_π] at w
      exact w
    rw [coneAt_π]
    change (F.map f ≫ (h (L.obj y)).lift (testCone L F G d θ y)) ≫ P.map j.hom =
      ((h (L.obj x)).lift (testCone L F G d θ x) ≫ P.map (L.map f)) ≫ P.map j.hom
    have hz : (h (L.obj y)).lift (testCone L F G d θ y) ≫ P.map j.hom =
        (d j.right).cocone.ι.app (CostructuredArrow.mk j.hom) ≫ θ.app j.right := by
      have w := (h (L.obj y)).fac (testCone L F G d θ y) j
      rw [coneAt_π] at w
      exact w
    rw [Category.assoc, hz, Category.assoc, ← P.map_comp, hw]
    rw [← Category.assoc]
    exact congrArg (· ≫ θ.app j.right)
      ((d j.right).cocone.w (CostructuredArrow.mkPrecomp j.hom f))

@[reassoc]
theorem ascend_map (h : (rightExtension G P).IsPointwiseRightKanExtension)
    (θ : restrictedColimit L F G d ⟶ G ⋙ P) (x : A) (j : StructuredArrow (L.obj x) G) :
    (ascend L F G d h θ).app x ≫ P.map j.hom =
      (d j.right).cocone.ι.app (CostructuredArrow.mk j.hom) ≫ θ.app j.right := by
  have w := (h (L.obj x)).fac (testCone L F G d θ x) j
  rw [coneAt_π] at w
  exact w

/-- The natural maps out of the restricted colimit are exactly the natural
families over `L` when the test functor is determined pointwise by `G`. -/
def homEquiv (h : (rightExtension G P).IsPointwiseRightKanExtension) :
    (restrictedColimit L F G d ⟶ G ⋙ P) ≃ (F ⟶ L ⋙ P) where
  toFun := ascend L F G d h
  invFun := descend L F G d
  left_inv θ := by
    ext x
    apply (d x).isColimit.hom_ext
    intro j
    rw [ι_descend]
    exact ascend_map L F G d h θ j.left (StructuredArrow.mk j.hom)
  right_inv η := by
    ext x
    apply (h (L.obj x)).hom_ext
    intro j
    rw [coneAt_π]
    rw [ascend_map, ι_descend]
    rfl

end PhilipponRestrictedKan

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponDenseSheafKan

universe v u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {A : Type u₃}
  [Category.{v} C] [Category.{v} D] [Category.{v} A]
  (G : C ⥤ D) (J : GrothendieckTopology D) [G.IsCoverDense J] [G.IsLocallyFull J]
  (F : Sheaf J A)

private abbrev extension := Functor.RightExtension.mk F.obj (𝟙 (G.op ⋙ F.obj))

private def testFamily {U : D}
    (d : Cone (StructuredArrow.proj (op U) G.op ⋙ G.op ⋙ F.obj)) :
    G.op ⋙ yoneda.obj U ⟶ G.op ⋙ (F.obj ⋙ coyoneda.obj (op d.pt)) where
  app V := TypeCat.ofHom (fun (a : G.obj V.unop ⟶ U) =>
    d.π.app (StructuredArrow.mk (T := G.op) (Y := V) a.op))
  naturality {V W} f := by
    ext a
    let g := StructuredArrow.mkPostcomp (T := G.op) a.op f
    change d.π.app (StructuredArrow.mk ((G.map f.unop ≫ a).op)) =
      d.π.app (StructuredArrow.mk a.op) ≫ F.obj.map ((G.map f.unop).op)
    exact (d.w g).symm

private def testSheaf {U : D}
    (d : Cone (StructuredArrow.proj (op U) G.op ⋙ G.op ⋙ F.obj)) : Sheaf J (Type v) :=
  ⟨_, Presheaf.isSheaf_comp_of_isSheaf J F.obj (coyoneda.obj (op d.pt)) F.property⟩

private def extendFamily {U : D}
    (d : Cone (StructuredArrow.proj (op U) G.op ⋙ G.op ⋙ F.obj)) :
    yoneda.obj U ⟶ (testSheaf G J F d).obj :=
  Functor.IsCoverDense.sheafHom (testFamily G J F d)

private theorem extendFamily_app {U : D}
    (d : Cone (StructuredArrow.proj (op U) G.op ⋙ G.op ⋙ F.obj))
    (j : StructuredArrow (op U) G.op) :
    (extendFamily G J F d).app ((G.op).obj j.right) j.hom.unop = d.π.app j := by
  have h := Functor.IsCoverDense.sheafHom_restrict_eq (K := J) (ℱ' := testSheaf G J F d)
    (testFamily G J F d)
  have w := ConcreteCategory.congr_hom (NatTrans.congr_app h j.right) j.hom.unop
  change (extendFamily G J F d).app (G.op.obj j.right) j.hom.unop =
    d.π.app (StructuredArrow.mk j.hom) at w
  refine w.trans ?_
  congr 1

/-- A sheaf is the pointwise right Kan extension of its restriction to a
cover-dense, locally full subsite. -/
def isPointwiseRightKanExtension : (extension G J F).IsPointwiseRightKanExtension := by
  intro X
  let U := X.unop
  refine {
    lift := fun d => (extendFamily G J F d).app X (𝟙 U)
    fac := ?_
    uniq := ?_ }
  · intro d j
    have hw := ConcreteCategory.congr_hom ((extendFamily G J F d).naturality j.hom) (𝟙 U)
    change (extendFamily G J F d).app (G.op.obj j.right) (j.hom.unop ≫ 𝟙 U) =
      (extendFamily G J F d).app X (𝟙 U) ≫ F.obj.map j.hom at hw
    rw [Category.comp_id, extendFamily_app G J F d j] at hw
    change (extendFamily G J F d).app X (𝟙 U) ≫ (F.obj.map j.hom ≫ 𝟙 _) = d.π.app j
    rw [Category.comp_id]
    exact hw.symm
  · intro d m hm
    let φ : yoneda.obj U ⟶ (testSheaf G J F d).obj := yonedaEquiv.symm m
    have hφ : Functor.whiskerLeft G.op φ = testFamily G J F d := by
      ext V a
      have h := hm (StructuredArrow.mk (Y := V) a.op)
      change m ≫ (F.obj.map a.op ≫ 𝟙 _) = _ at h
      rw [Category.comp_id] at h
      exact h
    have hEq : φ = extendFamily G J F d := by
      rw [← Functor.IsCoverDense.sheafHom_eq G (K := J) (ℱ' := testSheaf G J F d) φ, hφ]
      rfl
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hEq X) (𝟙 U)
    let e := yonedaEquiv (X := U) (F := (testSheaf G J F d).obj)
    exact (e.apply_symm_apply m).symm.trans hh

end PhilipponDenseSheafKan

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleModeledGluing (qcqsCharts)
open PhilipponEtaleModeledSections PhilipponEtaleRefinementGluing


namespace PhilipponEtaleModeledInverseImage

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {Y : Scheme.{u}} (E : I ⥤ Y.Etale)

private abbrev D := E ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y

variable (c : Cone (D E)) (hc : IsLimit c)
  [∀ {i j : I} (a : i ⟶ j), IsAffineHom ((D E).map a)]
  (p : c.pt ⟶ Y) (hp : ∀ i, c.π.app i ≫ (E.obj i).hom = p)
  (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

private abbrev G := (modeledCharts E c).ι
private abbrev L {Z X : Scheme.{u}} (f : Z ⟶ X) := (baseChange f).op
private abbrev J₀ := (G E c).inducedTopology c.pt.smallEtaleTopology

include hc hp in
theorem hasColimitOnModeledChart (U : (modeledCharts E c).FullSubcategory) :
    HasColimit (CostructuredArrow.proj (L p) (op U.obj) ⋙ F.obj) := by
  obtain ⟨i, V, hV, ⟨e⟩⟩ := U.property
  let : CompactSpace ((𝟭 Scheme.{u}).obj V.left) := hV.1
  let : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj V.left) := hV.2
  let d := modeledPresheafColimitCocone E V.hom c hc p hp F.obj
  apply (Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso (L p) F.obj (Iso.op e)).mp
  exact ⟨⟨d⟩⟩

private def cocone (U : (modeledCharts E c).FullSubcategoryᵒᵖ) :
    ColimitCocone (CostructuredArrow.proj (L p) ((G E c).op.obj U) ⋙ F.obj) := by
  let : HasColimit (CostructuredArrow.proj (L p) ((G E c).op.obj U) ⋙ F.obj) :=
    hasColimitOnModeledChart E c hc p hp F U.unop
  exact getColimitCocone _

/-- Construct the inverse image's pointwise section colimits on the modeled
charts, using the small filtered diagrams over stages. -/
def presheaf : (modeledCharts E c).FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u} :=
  PhilipponRestrictedKan.restrictedColimit (L p) F.obj (G E c).op (cocone E c hc p hp F)

private def stageIso (i : I) :
    (qcqsCharts ((D E).obj i)).ι.op ⋙ (chartStageSections E i F.obj ⋙ colim) ≅
      (stageToModeled E c i).op ⋙ presheaf E c hc p hp F := by
  let K := stageToModeled E c i
  let d := cocone E c hc p hp F
  refine NatIso.ofComponents (fun U => ?_) ?_
  · let : CompactSpace U.unop.obj.left := U.unop.property.1
    let : QuasiSeparatedSpace U.unop.obj.left := U.unop.property.2
    exact modeledStageColimitIso E c hc p hp F.obj U.unop.obj (d (op (K.obj U.unop)))
  · intro U V b
    let : CompactSpace U.unop.obj.left := U.unop.property.1
    let : QuasiSeparatedSpace U.unop.obj.left := U.unop.property.2
    let : CompactSpace V.unop.obj.left := V.unop.property.1
    let : QuasiSeparatedSpace V.unop.obj.left := V.unop.property.2
    exact modeledStageColimitIso_naturality E c hc p hp F.obj
      (U := V.unop.obj) (U' := U.unop.obj) b.unop.hom
      (d (op (K.obj V.unop))) (d (op (K.obj U.unop))) _
      (PhilipponRestrictedKan.ι_map (L p) F.obj (G E c).op d (K.op.map b))

/-- The section colimits on modeled charts, with their restriction maps,
form a sheaf on the induced site. -/
def sectionsSheaf : Sheaf (J₀ E c) AddCommGrpCat.{u} :=
  ⟨presheaf E c hc p hp F, isSheaf_on_modeledCharts E c hc F _ (stageIso E c hc p hp F)⟩

private def sectionsComparison : sectionsSheaf E c hc p hp F ⟶
    (modeledChartsRestriction E c hc).obj ((pullbackSheaves p).obj F) :=
  ⟨PhilipponRestrictedKan.descend (L p) F.obj (G E c).op (cocone E c hc p hp F)
    ((pullbackAdjunction p).unit.app F).hom⟩

private theorem isIso_of_equivalence_tests {C B : Type*} [Category* C] [Category* B]
    (e : C ≌ B) {A : C} {S : B} (k : S ⟶ e.functor.obj A)
    (h : ∀ H : C, Function.Bijective (fun q : A ⟶ H => k ≫ e.functor.map q)) : IsIso k := by
  apply isIso_of_coyoneda_map_bijective k
  intro T
  let H := e.inverse.obj T
  let eH : e.functor.obj H ≅ T := e.counitIso.app T
  let e₁ : (A ⟶ H) ≃ (e.functor.obj A ⟶ T) :=
    e.fullyFaithfulFunctor.homEquiv.trans ((Iso.refl _).homCongr eH)
  let e₂ : (S ⟶ e.functor.obj H) ≃ (S ⟶ T) := (Iso.refl _).homCongr eH
  apply (Function.Bijective.of_comp_iff _ e₁.bijective).mp
  simpa [e₁, e₂, Function.comp_def, Category.assoc] using e₂.bijective.comp (h H)

private theorem sectionsComparison_isIso : IsIso (sectionsComparison E c hc p hp F) := by
  let B := modeledChartsRestriction E c hc
  let : B.IsEquivalence := modeledCharts_restrictionEquivalence E c hc
  let : (G E c).IsCoverDense c.pt.smallEtaleTopology := modeledCharts_coverDense E c hc
  let d := cocone E c hc p hp F
  let R := sectionsSheaf E c hc p hp F
  let A := (pullbackSheaves p).obj F
  let k : R ⟶ B.obj A := sectionsComparison E c hc p hp F
  apply isIso_of_equivalence_tests B.asEquivalence k
  intro H
  let adj := pullbackAdjunction p
  let φ := PhilipponDenseSheafKan.isPointwiseRightKanExtension (G E c) c.pt.smallEtaleTopology H
  let e : (A ⟶ H) ≃ (R ⟶ B.obj H) :=
    (adj.homEquiv F H).trans ((fullyFaithfulSheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).homEquiv.trans
      ((PhilipponRestrictedKan.homEquiv (L p) F.obj (G E c).op d φ).symm.trans
        ((fullyFaithfulSheafToPresheaf (J₀ E c) AddCommGrpCat.{u}).homEquiv (X := R) (Y := B.obj H)).symm))
  suffices (fun q : A ⟶ H => k ≫ B.map q) = e from this ▸ e.bijective
  funext q
  apply (sheafToPresheaf (J₀ E c) AddCommGrpCat.{u}).map_injective
  change (PhilipponRestrictedKan.descend (L p) F.obj (G E c).op d (adj.unit.app F).hom) ≫
      Functor.whiskerLeft (G E c).op q.hom =
    PhilipponRestrictedKan.descend (L p) F.obj (G E c).op d ((adj.homEquiv F H) q).hom
  rw [adj.homEquiv_unit]
  exact (PhilipponRestrictedKan.descend_postcompose (L p) F.obj (G E c).op d q.hom
    (adj.unit.app F).hom).symm

/-- On the modeled charts the genuine sheaf inverse image is computed by
the pointwise presheaf colimit, via the inverse image adjunction unit. -/
def sectionsInverseImageIso : sectionsSheaf E c hc p hp F ≅
    (modeledChartsRestriction E c hc).obj ((pullbackSheaves p).obj F) :=
  letI := sectionsComparison_isIso E c hc p hp F
  asIso (sectionsComparison E c hc p hp F)

/-- The genuine sheaf inverse image has the pointwise colimit property at
each modeled chart. -/
def inverseImageIsPointwiseOnModeledChart (U : (modeledCharts E c).FullSubcategory) :
    (Functor.LeftExtension.mk ((pullbackSheaves p).obj F).obj
      ((pullbackAdjunction p).unit.app F).hom).IsPointwiseLeftKanExtensionAt (op U.obj) := by
  let d := cocone E c hc p hp F
  let V := sheafToPresheaf (J₀ E c) AddCommGrpCat.{u} ⋙ (evaluation _ _).obj (op U)
  let e := V.mapIso (sectionsInverseImageIso E c hc p hp F)
  refine (d (op U)).isColimit.ofIsoColimit (Cocone.ext e ?_)
  intro j
  exact PhilipponRestrictedKan.ι_descend (L p) F.obj (G E c).op d
    ((pullbackAdjunction p).unit.app F).hom (op U) j

end PhilipponEtaleModeledInverseImage

end

end


