-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
-- name    : AlgebraicGeometry_EtaleFiniteSectionLifts
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T21:35:18.770279+00:00
-- url     : https://prove2.me/theorems/690b9bca-7bef-4f72-942e-29d4171615f8
-- title:
--   Finite refinements for lifting étale sections
-- statement:
--   Comparison on stalks and finite refinements of étale charts carrying lifts of sections.

import Definitions.Def_AlgebraicGeometry_EtaleClosedImmersionSections

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)


namespace PhilipponEtaleStalkPullback

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ Y)

private def skyscraperIso :
    (Scheme.pointSmallEtale s).skyscraperSheafFunctor ⋙ pushforward f ≅
      (Scheme.pointSmallEtale (s ≫ f)).skyscraperSheafFunctor := by
  let e := (flipFunctor _ _ _).mapIso
    (Functor.isoWhiskerRight (NatIso.op (pointFiberIso f s).symm) (piFunctor.{u}.flip :
      (Type u)ᵒᵖ ⥤ AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
  let ff := fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}
  refine NatIso.ofComponents (fun M => ff.preimageIso (e.app M)) ?_
  intro M N a
  apply ff.map_injective
  exact e.hom.naturality a

private theorem skyscraperIso_hom_app_π (W : X.Etale)
    (t : (Scheme.pointSmallEtale s).fiber.obj ((baseChange f).obj W)) (M : AddCommGrpCat.{u}) :
    ((skyscraperIso f s).hom.app M).hom.app (op W) ≫
        Pi.π (fun _ : (Scheme.pointSmallEtale (s ≫ f)).fiber.obj W => M)
          ((pointFiberIso f s).hom.app W t) =
      Pi.π (fun _ : (Scheme.pointSmallEtale s).fiber.obj ((baseChange f).obj W) => M) t := by
  let e := pointFiberIso f s
  change Pi.map'
    (f := fun _ : (Scheme.pointSmallEtale s).fiber.obj ((baseChange f).obj W) => M)
    (g := fun _ : (Scheme.pointSmallEtale (s ≫ f)).fiber.obj W => M)
    (e.inv.app W) (fun _ => 𝟙 M) ≫ Pi.π _ (e.hom.app W t) = _
  let A := (Scheme.pointSmallEtale s).fiber.obj ((baseChange f).obj W)
  have he : e.hom.app W ≫ e.inv.app W = 𝟙 A := Iso.hom_inv_id_app e W
  have h : e.inv.app W (e.hom.app W t) = t := congrArg (fun k : A ⟶ A => k t) he
  rw [Pi.map'_comp_π, Category.comp_id, h]

set_option maxRecDepth 4096 in
/-- A germ represented by an étale chart pulls back to the germ represented
by its base-changed chart. -/
theorem stalkPullbackIso_germ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (W : X.Etale) (t : (Scheme.pointSmallEtale s).fiber.obj ((baseChange f).obj W)) :
    ((pullbackAdjunction f).unit.app F).hom.app (op W) ≫
      (Scheme.pointSmallEtale s).toPresheafFiber ((baseChange f).obj W) t
        ((pullbackSheaves f).obj F).obj ≫ (stalkPullbackIso f s).hom.app F =
    (Scheme.pointSmallEtale (s ≫ f)).toPresheafFiber W ((pointFiberIso f s).hom.app W t) F.obj := by
  let P := Scheme.pointSmallEtale (s ≫ f)
  let Q := Scheme.pointSmallEtale s
  let L := pullbackSheaves f
  let R := pushforward f
  let a := pullbackAdjunction f
  let b := Q.skyscraperSheafAdjunction (A := AddCommGrpCat.{u})
  let d := P.skyscraperSheafAdjunction (A := AddCommGrpCat.{u})
  let D := (skyscraperIso f s).hom
  let M := (P.sheafFiber (A := AddCommGrpCat.{u})).obj F
  let e := (stalkPullbackIso f s).hom.app F
  let α := (b.homEquiv (L.obj F) M) e
  let β := (d.homEquiv F M) (𝟙 M)
  have hβ : β = d.unit.app F := d.homEquiv_id F
  have h : a.unit.app F ≫ R.map α ≫ D.app M = β := by
    have he := Adjunction.homEquiv_leftAdjointUniq_hom_app
      ((a.comp b).ofNatIsoRight (skyscraperIso f s)) d F
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at he
    change a.homEquiv F _ α ≫ D.app M = _ at he
    rw [Adjunction.homEquiv_unit a] at he
    rw [hβ]
    simpa only [Category.assoc] using he
  let v := (pointFiberIso f s).hom.app W t
  have hv := congrArg (fun γ : F ⟶ P.skyscraperSheaf M =>
    γ.hom.app (op W) ≫ Pi.π (fun _ : P.fiber.obj W => M) v) h
  let η : F.obj.obj (op W) ⟶ (L.obj F).obj.obj (op ((baseChange f).obj W)) :=
    (a.unit.app F).hom.app (op W)
  change (η ≫ α.hom.app (op ((baseChange f).obj W)) ≫
    (D.app M).hom.app (op W)) ≫ Pi.π _ v = β.hom.app (op W) ≫ Pi.π _ v at hv
  simp only [Category.assoc] at hv
  have hπ : (D.app M).hom.app (op W) ≫ Pi.π (fun _ : P.fiber.obj W => M) v =
      Pi.π (fun _ : Q.fiber.obj ((baseChange f).obj W) => M) t :=
    skyscraperIso_hom_app_π f s W t M
  have hαπ : α.hom.app (op ((baseChange f).obj W)) ≫ Pi.π _ t =
      Q.toPresheafFiber ((baseChange f).obj W) t (L.obj F).obj ≫ e := by
    rw [show α.hom = Q.skyscraperPresheafHomEquiv e from Q.skyscraperSheafAdjunction_homEquiv_apply_hom e]
    exact Q.skyscraperPresheafHomEquiv_app_π e _ t
  have hβπ : β.hom.app (op W) ≫ Pi.π _ v = P.toPresheafFiber W v F.obj := by
    rw [show β.hom = P.skyscraperPresheafHomEquiv (𝟙 M) from
      P.skyscraperSheafAdjunction_homEquiv_apply_hom (𝟙 M)]
    exact (P.skyscraperPresheafHomEquiv_app_π (𝟙 (P.presheafFiber.obj F.obj)) W v).trans
      (Category.comp_id _)
  have h₁ := congrArg (fun m => η ≫ α.hom.app (op ((baseChange f).obj W)) ≫ m) hπ
  have h₂ := congrArg (fun m => η ≫ m) hαπ
  exact h₂.symm.trans (h₁.symm.trans (hv.trans hβπ))

/-- The unit of inverse image is injective on the stalk at any geometric
point that lifts along the morphism. -/
theorem stalk_unit_injective (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Injective
      ((Scheme.pointSmallEtale (s ≫ f)).sheafFiber.map ((pullbackAdjunction f).unit.app F)) := by
  let P := Scheme.pointSmallEtale (s ≫ f)
  let Q := Scheme.pointSmallEtale s
  let M := P.sheafFiber.obj F
  let B := Q.skyscraperSheafFunctor.obj M
  let adj := pullbackAdjunction f
  let pointAdj := P.skyscraperSheafAdjunction (A := AddCommGrpCat.{u})
  let e := skyscraperIso f s
  let a : (pullbackSheaves f).obj F ⟶ B :=
    (adj.homEquiv F B).symm (pointAdj.unit.app F ≫ e.inv.app M)
  let b := (pushforward f).map a ≫ e.hom.app M
  have hu : adj.unit.app F ≫ b = pointAdj.unit.app F := calc
    _ = adj.homEquiv F B a ≫ e.hom.app M := by
      rw [Adjunction.homEquiv_unit]
      simp only [b, Category.assoc]
    _ = _ := by
      simp only [a, Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id_app]
      exact Category.comp_id _
  let r : P.sheafFiber.obj ((pushforward f).obj ((pullbackSheaves f).obj F)) ⟶ M :=
    P.sheafFiber.map b ≫ pointAdj.counit.app M
  have hr : P.sheafFiber.map (adj.unit.app F) ≫ r = 𝟙 M := by
    dsimp only [r]
    rw [← Category.assoc, ← Functor.map_comp, hu]
    exact pointAdj.left_triangle_components F
  have hright (x : M) : r (P.sheafFiber.map (adj.unit.app F) x) = x :=
    ConcreteCategory.congr_hom hr x
  exact Function.LeftInverse.injective hright

/-- Inverse image along a surjective scheme morphism has monomorphic unit
on abelian étale sheaves. -/
theorem unit_mono_of_surjective [Surjective f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Mono ((pullbackAdjunction f).unit.app F) := by
  let t (y : Y) := geometricMap y ≫ f
  have hCover : ⋃ y, Set.range (t y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := f.surjective x
    exact Set.mem_iUnion.mpr ⟨y, default, by simpa [t, Scheme.Hom.comp_apply] using hy⟩
  let P : ObjectProperty (X.smallEtaleTopology.Point.{u}) :=
    ObjectProperty.ofObj (fun y : Y => Scheme.pointSmallEtale (t y))
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservative_pointSmallEtale t hCover
  let η := (pullbackAdjunction f).unit.app F
  let : ∀ Φ : P.FullSubcategory, Mono (Φ.obj.sheafFiber.map η) := by
    intro Φ
    have h := Φ.property
    change ObjectProperty.ofObj (fun y : Y => Scheme.pointSmallEtale (t y)) Φ.obj at h
    obtain ⟨y, hy⟩ := (ObjectProperty.ofObj_iff _ _).mp h
    rw [← hy]
    exact (AddCommGrpCat.mono_iff_injective _).2 (stalk_unit_injective f (geometricMap y) F)
  exact (hP.jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono η

omit [IsSepClosed K] in
/-- A field-valued point in the image of a closed immersion factors
through the closed subscheme over the same field. -/
theorem exists_point_lift_of_mem_range [IsClosedImmersion f] (t : Spec (CommRingCat.of K) ⟶ X)
    (ht : t default ∈ Set.range f) : ∃ s' : Spec (CommRingCat.of K) ⟶ Y, s' ≫ f = t := by
  let p := pullback.fst t f
  have hp : (default : Spec (CommRingCat.of K)) ∈ Set.range p := by
    rw [show Set.range p = t ⁻¹' Set.range f from Scheme.Pullback.range_fst t f]
    exact ht
  have : Surjective p :=
    ⟨fun x => (Subsingleton.elim (default : Spec (CommRingCat.of K)) x) ▸ hp⟩
  have : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.fst t f))
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  refine ⟨inv p ≫ pullback.snd t f, ?_⟩
  rw [Category.assoc, ← pullback.condition]
  exact IsIso.inv_hom_id_assoc p t

/-- The inverse image unit induces an isomorphism on a stalk at a
geometric point that factors through the closed immersion. -/
theorem stalk_unit_isIso [IsClosedImmersion f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((Scheme.pointSmallEtale (s ≫ f)).sheafFiber.map ((pullbackAdjunction f).unit.app F)) := by
  let L := pullbackSheaves f
  let adj := pullbackAdjunction f
  let ff := PhilipponEtaleClosedPushforward.fullyFaithfulPushforward f
  have := ff.full
  have := ff.faithful
  have : IsIso (adj.counit.app (L.obj F)) := inferInstance
  have : IsIso (L.map (adj.unit.app F)) := by
    rw [IsIso.eq_inv_of_inv_hom_id (adj.left_triangle_components F)]
    infer_instance
  exact (NatIso.isIso_map_iff (stalkPullbackIso f s) (adj.unit.app F)).mp
    (Functor.map_isIso (Scheme.pointSmallEtale s).sheafFiber _)

/-- A section over an étale chart of a closed subscheme lifts locally to
sections on the ambient scheme. -/
theorem unit_epi_of_isClosedImmersion [IsClosedImmersion f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Epi ((pullbackAdjunction f).unit.app F) := by
  let η := (pullbackAdjunction f).unit.app F
  let P : ObjectProperty (X.smallEtaleTopology.Point.{u}) :=
    ObjectProperty.ofObj (fun x : X => geometricPoint x)
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let : ∀ Φ : P.FullSubcategory, Epi (Φ.obj.sheafFiber.map η) := by
    intro Φ
    have h := Φ.property
    change ObjectProperty.ofObj (fun x : X => geometricPoint x) Φ.obj at h
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp h
    rw [← hx]
    by_cases hs : geometricMap x default ∈ Set.range f
    · obtain ⟨t, ht⟩ := exists_point_lift_of_mem_range f (geometricMap x) hs
      change Epi ((Scheme.pointSmallEtale (geometricMap x)).sheafFiber.map η)
      rw [← ht]
      have : IsIso ((Scheme.pointSmallEtale (t ≫ f)).sheafFiber.map η) :=
        stalk_unit_isIso f t F
      exact IsIso.epi_of_iso ((Scheme.pointSmallEtale (t ≫ f)).sheafFiber.map η)
    · exact (PhilipponEtaleClosedPushforward.isZero_stalk_pushforward_of_not_mem_range
        f (geometricMap x) hs ((pullbackSheaves f).obj F)).epi _
  exact (hP.jointlyReflectEpimorphisms AddCommGrpCat.{u}).epi η

/-- On a quasi-compact étale chart, a section of the inverse image on a
closed subscheme admits lifts on a finite affine étale covering. -/
theorem exists_finite_affine_lifts [IsClosedImmersion f] {U : X.Etale} [CompactSpace U.left]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ↥(((pushforward f).obj ((pullbackSheaves f).obj F)).obj.obj (op U))) :
    ∃ (ι : Type u) (_ : Fintype ι) (V : ι → X.Etale) (g : ∀ i, V i ⟶ U)
      (b : ∀ i, ↥(F.obj.obj (op (V i)))),
      (∀ i, IsAffine (V i).left) ∧ Sieve.ofArrows V g ∈ X.smallEtaleTopology U ∧
        ∀ i, ((pullbackAdjunction f).unit.app F).hom.app (op (V i)) (b i) =
          ((pushforward f).obj ((pullbackSheaves f).obj F)).obj.map (g i).op a := by
  classical
  let η := (pullbackAdjunction f).unit.app F
  have : Epi η := unit_epi_of_isClosedImmersion f F
  have : Sheaf.IsLocallySurjective η :=
    (Sheaf.isLocallySurjective_iff_epi' (J := X.smallEtaleTopology) AddCommGrpCat.{u} η).mpr
      inferInstance
  have hS := Presheaf.imageSieve_mem X.smallEtaleTopology η.hom (U := op U) a
  obtain ⟨ι, hι, V, g, hLift, hAffine, hCover⟩ :=
    Scheme.exists_finite_affine_refinement (Presheaf.imageSieve η.hom a) hS
  choose b hb using hLift
  exact ⟨ι, hι, V, g, b, hAffine, hCover, hb⟩

end PhilipponEtaleStalkPullback

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso globalSectionsIso_hom_app_eq_map)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (unit_mono_of_surjective)


namespace PhilipponEtalePullbackComposition

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)

/-- Inverse image along a composite agrees with the composite inverse image. -/
def pullbackCompIso : pullbackSheaves f ⋙ pullbackSheaves g ≅ pullbackSheaves (g ≫ f) :=
  Adjunction.leftAdjointUniq
    (((pullbackAdjunction f).comp (pullbackAdjunction g)).ofNatIsoRight (pushforwardCompIso f g))
    (pullbackAdjunction (g ≫ f))

/-- The composition comparison over a specified composite is the unique
left-adjoint comparison associated with the direct-image comparison. -/
theorem pullbackCompIso_over_hom (ρ : Z ⟶ X) (h : g ≫ f = ρ) (F : Ab X) :
    ((((pullbackAdjunction f).comp (pullbackAdjunction g)).ofNatIsoRight
      (pushforwardCompIso f g ≪≫ eqToIso (congrArg pushforward h))).leftAdjointUniq
      (pullbackAdjunction ρ)).hom.app F =
    ((pullbackCompIso f g ≪≫ eqToIso (congrArg pullbackSheaves h)).hom.app F) := by
  subst ρ
  simp only [congrArg, eqToIso_refl, Iso.trans_refl, pullbackCompIso]

/-- The inverse-image unit of a composite is the composite unit under the
direct- and inverse-image comparisons. -/
theorem unit_comp (F : Ab X) :
    (pullbackAdjunction f).unit.app F ≫
      (pushforward f).map ((pullbackAdjunction g).unit.app ((pullbackSheaves f).obj F)) ≫
      (pushforwardCompIso f g).hom.app ((pullbackSheaves g).obj ((pullbackSheaves f).obj F)) ≫
      (pushforward (g ≫ f)).map ((pullbackCompIso f g).hom.app F) =
    (pullbackAdjunction (g ≫ f)).unit.app F := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((pullbackAdjunction f).comp (pullbackAdjunction g)).ofNatIsoRight (pushforwardCompIso f g))
    (pullbackAdjunction (g ≫ f)) F
  simpa only [pullbackCompIso, Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc] using h

/-- Restriction on direct images along a map over the base. -/
def restrictDirectImage (ρ : Z ⟶ X) (h : g ≫ f = ρ) (F : Ab X) :
    (pushforward f).obj ((pullbackSheaves f).obj F) ⟶
      (pushforward ρ).obj ((pullbackSheaves ρ).obj F) :=
  let G := (pullbackSheaves g).obj ((pullbackSheaves f).obj F)
  let e := pushforwardCompIso f g ≪≫ eqToIso (congrArg pushforward h)
  let e' := pullbackCompIso f g ≪≫ eqToIso (congrArg pullbackSheaves h)
  (pushforward f).map ((pullbackAdjunction g).unit.app ((pullbackSheaves f).obj F)) ≫
    e.hom.app G ≫ (pushforward ρ).map (e'.hom.app F)

/-- Direct-image restriction carries the unit for the source to the
unit for the composite. -/
theorem unit_restrictDirectImage (ρ : Z ⟶ X) (h : g ≫ f = ρ) (F : Ab X) :
    (pullbackAdjunction f).unit.app F ≫ restrictDirectImage f g ρ h F =
      (pullbackAdjunction ρ).unit.app F := by
  subst ρ
  simp only [restrictDirectImage, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  exact unit_comp f g F

private abbrev terminal (P : Scheme.{u}) := Scheme.Etale.mk (𝟙 P)

private def isTerminal (P : Scheme.{u}) : IsTerminal (terminal P) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget P) _ Over.mkIdTerminal

private def terminalArrow {P Q : Scheme.{u}} (p : Q ⟶ P) :
    terminal Q ⟶ (baseChange p).obj (terminal P) :=
  MorphismProperty.Over.homMk
    (pullback.lift p (𝟙 Q) ((Category.comp_id p).trans (Category.id_comp p).symm))
    (pullback.lift_snd ..) trivial

/-- Direct-image comparisons on global sections commute with composition. -/
theorem globalSectionsIso_comp (F : Ab Z) :
    (globalSections X).map ((pushforwardCompIso f g).hom.app F) ≫
      (globalSectionsIso (g ≫ f)).hom.app F =
    (globalSectionsIso f).hom.app ((pushforward g).obj F) ≫ (globalSectionsIso g).hom.app F := by
  let e := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).hom.app (terminal X)
  have hT : IsTerminal ((baseChange f ⋙ baseChange g).obj (terminal X)) := by
    have : PreservesFiniteLimits (baseChange f) :=
      inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ f))
    have : PreservesFiniteLimits (baseChange g) :=
      inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ g))
    exact IsTerminal.isTerminalObj (baseChange f ⋙ baseChange g) _ (isTerminal X)
  have he : terminalArrow (g ≫ f) ≫ e = terminalArrow g ≫ (baseChange g).map (terminalArrow f) :=
    hT.hom_ext _ _
  rw [globalSectionsIso_hom_app_eq_map (g ≫ f) F (terminalArrow (g ≫ f)),
    globalSectionsIso_hom_app_eq_map f ((pushforward g).obj F) (terminalArrow f),
    globalSectionsIso_hom_app_eq_map g F (terminalArrow g)]
  change (𝟙 _ ≫ F.obj.map e.op) ≫ F.obj.map (terminalArrow (g ≫ f)).op =
    F.obj.map ((baseChange g).map (terminalArrow f)).op ≫ F.obj.map (terminalArrow g).op
  rw [Category.id_comp, ← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp, he]

/-- Restriction on global sections is evaluation of the unit, followed by
the global-section isomorphism for direct image. -/
theorem restrictGlobalSections_app_eq {P Q : Scheme.{u}} (p : Q ⟶ P) (F : Ab P) :
    (restrictGlobalSections p).app F =
      (globalSections P).map ((pullbackAdjunction p).unit.app F) ≫
        (globalSectionsIso p).hom.app ((pullbackSheaves p).obj F) := by
  simp only [restrictGlobalSections, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp]

set_option maxRecDepth 4096 in
/-- Restriction of a direct image over the base is ordinary restriction
of global sections after the direct-image identifications. -/
theorem globalSectionsIso_restrictDirectImage (ρ : Z ⟶ X) (h : g ≫ f = ρ) (F : Ab X) :
    (globalSections X).map (restrictDirectImage f g ρ h F) ≫
      (globalSectionsIso ρ).hom.app ((pullbackSheaves ρ).obj F) =
    (globalSectionsIso f).hom.app ((pullbackSheaves f).obj F) ≫
      (restrictGlobalSections g).app ((pullbackSheaves f).obj F) ≫
      (globalSections Z).map
        ((pullbackCompIso f g ≪≫ eqToIso (congrArg pullbackSheaves h)).hom.app F) := by
  subst ρ
  let H := (pullbackSheaves f).obj F
  let J := (pullbackSheaves g).obj H
  let A := (pullbackSheaves (g ≫ f)).obj F
  let b : H ⟶ (pushforward g).obj J := (pullbackAdjunction g).unit.app H
  let c : J ⟶ A := (pullbackCompIso f g).hom.app F
  have h₁ : (globalSections X).map ((pushforward f).map b) ≫
      (globalSectionsIso f).hom.app ((pushforward g).obj J) =
      (globalSectionsIso f).hom.app H ≫ (globalSections Y).map b :=
    (globalSectionsIso f).hom.naturality b
  have h₂ : (globalSections X).map ((pushforward (g ≫ f)).map c) ≫
      (globalSectionsIso (g ≫ f)).hom.app A =
      (globalSectionsIso (g ≫ f)).hom.app J ≫ (globalSections Z).map c :=
    (globalSectionsIso (g ≫ f)).hom.naturality c
  simp only [restrictDirectImage, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id,
    Functor.map_comp, Category.assoc, restrictGlobalSections_app_eq]
  change (globalSections X).map ((pushforward f).map b) ≫
    (globalSections X).map ((pushforwardCompIso f g).hom.app J) ≫
    (globalSections X).map ((pushforward (g ≫ f)).map c) ≫
    (globalSectionsIso (g ≫ f)).hom.app A = _
  rw [h₂, ← Category.assoc ((globalSections X).map ((pushforwardCompIso f g).hom.app J)),
    globalSectionsIso_comp, Category.assoc, ← Category.assoc ((globalSections X).map ((pushforward f).map b)),
    h₁, Category.assoc]

/-- Injectivity of ordinary restriction also gives injectivity on the
global sections of the corresponding direct-image restriction. -/
theorem restrictDirectImage_sections_injective (ρ : Z ⟶ X) (h : g ≫ f = ρ) (F : Ab X)
    (hg : Function.Injective ((restrictGlobalSections g).app ((pullbackSheaves f).obj F))) :
    Function.Injective ((globalSections X).map (restrictDirectImage f g ρ h F)) := by
  let e := (globalSectionsIso f).app ((pullbackSheaves f).obj F)
  let d := (globalSectionsIso ρ).app ((pullbackSheaves ρ).obj F)
  let c := (pullbackCompIso f g ≪≫ eqToIso (congrArg pullbackSheaves h)).app F
  let k := (globalSections Z).map c.hom
  have hComparison := globalSectionsIso_restrictDirectImage f g ρ h F
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  apply hg
  apply (ConcreteCategory.bijective_of_isIso k).1
  exact (ConcreteCategory.congr_hom hComparison a).symm.trans
    ((congrArg d.hom hab).trans (ConcreteCategory.congr_hom hComparison b))

/-- Global sections of an étale sheaf inject into their inverse image
along a surjective scheme morphism. -/
theorem restrictGlobalSections_injective_of_surjective {P Q : Scheme.{u}} (p : Q ⟶ P)
    [Surjective p] (F : Ab P) : Function.Injective ((restrictGlobalSections p).app F) := by
  let Γ := globalSections P
  let : PreservesFiniteLimits Γ := by
    change PreservesFiniteLimits
      (sheafToPresheaf P.smallEtaleTopology AddCommGrpCat.{u} ⋙
        (CategoryTheory.evaluation _ _).obj (op (terminal P)))
    infer_instance
  let : Mono ((pullbackAdjunction p).unit.app F) := unit_mono_of_surjective p F
  have h : Mono ((restrictGlobalSections p).app F) := by
    rw [restrictGlobalSections_app_eq]
    change Mono (Γ.map ((pullbackAdjunction p).unit.app F) ≫
      (globalSectionsIso p).hom.app ((pullbackSheaves p).obj F))
    infer_instance
  exact (AddCommGrpCat.mono_iff_injective _).1 h

set_option maxRecDepth 4096 in
/-- Successive restrictions of a global section agree with restriction
along the composite. -/
theorem restrictGlobalSections_comp (F : Ab X) :
    (restrictGlobalSections f).app F ≫
      (restrictGlobalSections g).app ((pullbackSheaves f).obj F) ≫
      (globalSections Z).map ((pullbackCompIso f g).hom.app F) =
    (restrictGlobalSections (g ≫ f)).app F := by
  let H := (pullbackSheaves f).obj F
  let J := (pullbackSheaves g).obj H
  let a : F ⟶ (pushforward f).obj H := (pullbackAdjunction f).unit.app F
  let b : H ⟶ (pushforward g).obj J := (pullbackAdjunction g).unit.app H
  let A := (pullbackSheaves (g ≫ f)).obj F
  let c : J ⟶ A := (pullbackCompIso f g).hom.app F
  have h₁ : (globalSections X).map ((pushforward f).map b) ≫
      (globalSectionsIso f).hom.app ((pushforward g).obj J) =
      (globalSectionsIso f).hom.app H ≫ (globalSections Y).map b :=
    (globalSectionsIso f).hom.naturality b
  have h₂ : (globalSections X).map ((pushforward (g ≫ f)).map c) ≫
      (globalSectionsIso (g ≫ f)).hom.app A =
      (globalSectionsIso (g ≫ f)).hom.app J ≫ (globalSections Z).map c :=
    (globalSectionsIso (g ≫ f)).hom.naturality c
  have hu : a ≫ (pushforward f).map b ≫ (pushforwardCompIso f g).hom.app J ≫
      (pushforward (g ≫ f)).map c = (pullbackAdjunction (g ≫ f)).unit.app F := unit_comp f g F
  simp only [restrictGlobalSections_app_eq, Category.assoc]
  change (globalSections X).map a ≫ (globalSectionsIso f).hom.app H ≫
    (globalSections Y).map b ≫ (globalSectionsIso g).hom.app J ≫ (globalSections Z).map c = _
  rw [← reassoc_of% h₁, ← reassoc_of% (globalSectionsIso_comp f g J), ← h₂]
  repeat rw [← CategoryTheory.Functor.map_comp_assoc]
  simp only [Category.assoc, hu]
  rfl

end PhilipponEtalePullbackComposition

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackComposition (pullbackCompIso pullbackCompIso_over_hom restrictDirectImage)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtalePullbackSquareUnits

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

section Adjunctions

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {L : A ⥤ B} {R : B ⥤ A} {M : A ⥤ C} {S : C ⥤ A}
  {N : C ⥤ D} {T : D ⥤ C} {Q : B ⥤ D} {V : D ⥤ B}
  (a : M ⊣ S) (b : N ⊣ T) (c : L ⊣ R) (d : Q ⊣ V)
  (e : V ⋙ R ≅ T ⋙ S)

private theorem unit_square_aux (F : A) (g : M.obj (R.obj (L.obj F)) ⟶ T.obj (Q.obj (L.obj F)))
    (hg : a.homEquiv _ _ g = R.map (d.unit.app (L.obj F)) ≫ e.hom.app (Q.obj (L.obj F))) :
    b.unit.app (M.obj F) ≫ T.map (((a.comp b).leftAdjointUniq
      ((c.comp d).ofNatIsoRight e)).hom.app F) = M.map (c.unit.app F) ≫ g := by
  apply (a.homEquiv F (T.obj (Q.obj (L.obj F)))).injective
  rw [Adjunction.homEquiv_naturality_left]
  change _ = c.unit.app F ≫ (a.homEquiv (R.obj (L.obj F)) (T.obj (Q.obj (L.obj F)))) g
  rw [hg, Adjunction.homEquiv_unit]
  have h := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) ((c.comp d).ofNatIsoRight e) F
  rw [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Adjunction.comp_unit_app] at h
  simpa only [Functor.whiskerLeft_app, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.assoc] using h

end Adjunctions

section Comparison

variable {A B : Type*} [Category A] [Category B]
  {L M N : A ⥤ B} {R S T : B ⥤ A}
  (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T)
  (e : R ≅ T) (f : S ≅ T)

private theorem compare_via_common_right (x : A) :
    (a.leftAdjointUniq (b.ofNatIsoRight (f ≪≫ e.symm))).hom.app x ≫
      ((b.ofNatIsoRight f).leftAdjointUniq c).hom.app x =
    ((a.ofNatIsoRight e).leftAdjointUniq c).hom.app x := by
  let α := (a.leftAdjointUniq (b.ofNatIsoRight (f ≪≫ e.symm))).hom.app x
  let β := ((b.ofNatIsoRight f).leftAdjointUniq c).hom.app x
  let γ := ((a.ofNatIsoRight e).leftAdjointUniq c).hom.app x
  have hα : a.unit.app x ≫ R.map α = b.unit.app x ≫ f.hom.app (M.obj x) ≫ e.inv.app (M.obj x) := by
    simpa only [α, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Iso.trans_hom, Iso.symm_hom, Category.assoc] using
      Adjunction.unit_leftAdjointUniq_hom_app a (b.ofNatIsoRight (f ≪≫ e.symm)) x
  have hβ : b.unit.app x ≫ f.hom.app (M.obj x) ≫ T.map β = c.unit.app x := by
    simpa only [β, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc] using Adjunction.unit_leftAdjointUniq_hom_app (b.ofNatIsoRight f) c x
  have hγ : a.unit.app x ≫ e.hom.app (L.obj x) ≫ T.map γ = c.unit.app x := by
    simpa only [γ, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Category.assoc] using Adjunction.unit_leftAdjointUniq_hom_app (a.ofNatIsoRight e) c x
  change α ≫ β = γ
  apply ((a.ofNatIsoRight e).homEquiv x (N.obj x)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (a.unit.app x ≫ e.hom.app (L.obj x)) ≫ T.map (α ≫ β) =
    (a.unit.app x ≫ e.hom.app (L.obj x)) ≫ T.map γ
  rw [Functor.map_comp, Category.assoc, ← reassoc_of% (e.hom.naturality α),
    ← Category.assoc (a.unit.app x) (R.map α), hα]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, hβ, hγ]

end Comparison

section OverComposite

variable {X P Z W : Scheme.{u}} (p : P ⟶ X) (i : Z ⟶ X) (j : W ⟶ P) (r : W ⟶ Z)
    (ρ : W ⟶ X) (hp : j ≫ p = ρ) (hi : r ≫ i = ρ)

private def pushforwardSquareIsoOver :
    pushforward r ⋙ pushforward i ≅ pushforward j ⋙ pushforward p :=
  (pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)) ≪≫
    (pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)).symm

/-- Comparison of the two inverse images around a commutative square. -/
def pullbackSquareIsoOver :
    pullbackSheaves p ⋙ pullbackSheaves j ≅ pullbackSheaves i ⋙ pullbackSheaves r :=
  ((pullbackAdjunction p).comp (pullbackAdjunction j)).leftAdjointUniq
    (((pullbackAdjunction i).comp (pullbackAdjunction r)).ofNatIsoRight
      (pushforwardSquareIsoOver p i j r ρ hp hi))

/-- The square comparison commutes with inverse image along the common map. -/
theorem pullbackSquareIsoOver_comp (F : Ab X) :
    (pullbackSquareIsoOver p i j r ρ hp hi).hom.app F ≫
      ((pullbackCompIso i r ≪≫ eqToIso (congrArg pullbackSheaves hi)).hom.app F) =
    ((pullbackCompIso p j ≪≫ eqToIso (congrArg pullbackSheaves hp)).hom.app F) := by
  let e := pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)
  let f := pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)
  rw [← pullbackCompIso_over_hom i r ρ hi, ← pullbackCompIso_over_hom p j ρ hp]
  exact compare_via_common_right ((pullbackAdjunction p).comp (pullbackAdjunction j))
    ((pullbackAdjunction i).comp (pullbackAdjunction r)) (pullbackAdjunction ρ) e f F

/-- The adjunction map from the pulled-back direct image to the direct
image of the sheaf pulled back around the other side of the square. -/
def restrictionBaseChangeOver (B : Ab Z) :
    (pullbackSheaves p).obj ((pushforward i).obj B) ⟶
      (pushforward j).obj ((pullbackSheaves r).obj B) :=
  ((pullbackAdjunction p).homEquiv _ _).symm
    ((pushforward i).map ((pullbackAdjunction r).unit.app B) ≫
      (pushforwardSquareIsoOver p i j r ρ hp hi).hom.app ((pullbackSheaves r).obj B))

/-- The base-change map with the coefficient comparison to the inverse
image around the side through the new base. -/
def pulledImageComparisonOver (F : Ab X) :
    (pullbackSheaves p).obj ((pushforward i).obj ((pullbackSheaves i).obj F)) ⟶
      (pushforward j).obj ((pullbackSheaves j).obj ((pullbackSheaves p).obj F)) :=
  restrictionBaseChangeOver p i j r ρ hp hi ((pullbackSheaves i).obj F) ≫
    (pushforward j).map ((pullbackSquareIsoOver p i j r ρ hp hi).inv.app F)

/-- The comparison sends the pulled-back restriction unit to the
restriction unit on the new base. -/
theorem pulledImageComparison_unit (F : Ab X) :
    (pullbackSheaves p).map ((pullbackAdjunction i).unit.app F) ≫
      pulledImageComparisonOver p i j r ρ hp hi F =
    (pullbackAdjunction j).unit.app ((pullbackSheaves p).obj F) := by
  let e := pullbackSquareIsoOver p i j r ρ hp hi
  let c := restrictionBaseChangeOver p i j r ρ hp hi ((pullbackSheaves i).obj F)
  let η := (pullbackAdjunction j).unit.app ((pullbackSheaves p).obj F)
  have h : η ≫ (pushforward j).map (e.hom.app F) =
      (pullbackSheaves p).map ((pullbackAdjunction i).unit.app F) ≫ c :=
    unit_square_aux (pullbackAdjunction p) (pullbackAdjunction j) (pullbackAdjunction i)
      (pullbackAdjunction r) (pushforwardSquareIsoOver p i j r ρ hp hi) F c
      (Equiv.apply_symm_apply _ _)
  change (pullbackSheaves p).map ((pullbackAdjunction i).unit.app F) ≫
    c ≫ (pushforward j).map (e.inv.app F) = η
  rw [← Category.assoc, ← h, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  exact (congrArg (η ≫ ·) ((pushforward j).map_id
    ((pullbackSheaves p ⋙ pullbackSheaves j).obj F))).trans (Category.comp_id η)

set_option maxRecDepth 4096 in
/-- Pulling back the section of the closed image gives the restriction to
the common composite after the direct-image comparison. -/
theorem unit_pulledImageComparison (F : Ab X) :
    (pullbackAdjunction p).unit.app ((pushforward i).obj ((pullbackSheaves i).obj F)) ≫
      (pushforward p).map (pulledImageComparisonOver p i j r ρ hp hi F) ≫
      ((pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)).hom.app
        ((pullbackSheaves j).obj ((pullbackSheaves p).obj F))) ≫
      (pushforward ρ).map
        ((pullbackCompIso p j ≪≫ eqToIso (congrArg pullbackSheaves hp)).hom.app F) =
    restrictDirectImage i r ρ hi F := by
  let B := (pullbackSheaves i).obj F
  let P := (pullbackSheaves j).obj ((pullbackSheaves p).obj F)
  let Z := (pullbackSheaves r).obj B
  let e := pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)
  let f := pushforwardCompIso i r ≪≫ eqToIso (congrArg pushforward hi)
  let α := (pullbackSquareIsoOver p i j r ρ hp hi).app F
  let β := ((pullbackCompIso p j ≪≫ eqToIso (congrArg pullbackSheaves hp)).hom.app F)
  let γ := ((pullbackCompIso i r ≪≫ eqToIso (congrArg pullbackSheaves hi)).hom.app F)
  let g := restrictionBaseChangeOver p i j r ρ hp hi B
  have hα : α.hom ≫ γ = β := pullbackSquareIsoOver_comp p i j r ρ hp hi F
  have hInv : α.inv ≫ β = γ := by rw [← hα, α.inv_hom_id_assoc]
  have hg : (pullbackAdjunction p).homEquiv _ _ g =
      (pushforward i).map ((pullbackAdjunction r).unit.app B) ≫ f.hom.app Z ≫ e.inv.app Z :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at hg
  have hn : (pushforward p).map ((pushforward j).map α.inv) ≫ e.hom.app P =
      e.hom.app Z ≫ (pushforward ρ).map α.inv := e.hom.naturality α.inv
  unfold pulledImageComparisonOver
  simp only [Functor.map_comp, Category.assoc]
  change _ ≫ (pushforward p).map g ≫ (pushforward p).map ((pushforward j).map α.inv) ≫
    e.hom.app P ≫ (pushforward ρ).map β = _
  rw [← Category.assoc _ ((pushforward p).map g), hg, Category.assoc,
    reassoc_of% hn]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, hInv,
    restrictDirectImage, f, B, Z, γ]

end OverComposite

variable {X Z P : Scheme.{u}} (i : Z ⟶ X) (p : P ⟶ X)

private abbrev r := pullback.snd p i
private abbrev j := pullback.fst p i

private def pushforwardSquareIso :
    pushforward (r i p) ⋙ pushforward i ≅ pushforward (j i p) ⋙ pushforward p :=
  pushforwardSquareIsoOver p i (j i p) (r i p) (j i p ≫ p) rfl pullback.condition.symm

/-- The two inverse-image composites in the pullback square agree. -/
def pullbackSquareIso :
    pullbackSheaves p ⋙ pullbackSheaves (j i p) ≅
      pullbackSheaves i ⋙ pullbackSheaves (r i p) :=
  ((pullbackAdjunction p).comp (pullbackAdjunction (j i p))).leftAdjointUniq
    (((pullbackAdjunction i).comp (pullbackAdjunction (r i p))).ofNatIsoRight
      (pushforwardSquareIso i p))

/-- The ordinary base-change map on a sheaf, expressed via adjunction. -/
def restrictionBaseChange (B : Ab Z) :
    (pullbackSheaves p).obj ((pushforward i).obj B) ⟶
      (pushforward (j i p)).obj ((pullbackSheaves (r i p)).obj B) :=
  restrictionBaseChangeOver p i (j i p) (r i p) (j i p ≫ p) rfl pullback.condition.symm B

/-- The base-change map carries the pulled-back unit of restriction to
the restriction unit on the new base. -/
theorem unit_square (F : Ab X) :
    ((pullbackAdjunction (j i p)).unit.app ((pullbackSheaves p).obj F)) ≫
      (pushforward (j i p)).map ((pullbackSquareIso i p).hom.app F) =
    (pullbackSheaves p).map ((pullbackAdjunction i).unit.app F) ≫
      restrictionBaseChange i p ((pullbackSheaves i).obj F) := by
  exact unit_square_aux (pullbackAdjunction p) (pullbackAdjunction (j i p)) (pullbackAdjunction i)
    (pullbackAdjunction (r i p)) (pushforwardSquareIso i p) F _ (Equiv.apply_symm_apply _ _)

end PhilipponEtalePullbackSquareUnits

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackComposition (pullbackCompIso restrictDirectImage restrictGlobalSections_app_eq)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtalePullbackSquareUnits (pulledImageComparisonOver unit_pulledImageComparison)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleSectionComparison

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X P Z W : Scheme.{u}} (p : P ⟶ X) (i : Z ⟶ X) (j : W ⟶ P) (r : W ⟶ Z)
    (ρ : W ⟶ X) (hp : j ≫ p = ρ) (hi : r ≫ i = ρ)

private theorem compare_directImage_sections {G : Ab X} {H J : Ab P}
    (d : H ⟶ J) (c : (pullbackSheaves p).obj G ⟶ J)
    (a : (globalSections X).obj G) (b : (globalSections P).obj H)
    (hb : (globalSections P).map d b =
      (globalSections P).map c ((restrictGlobalSections p).app G a)) :
    (globalSections X).map ((pushforward p).map d) ((globalSectionsIso p).inv.app H b) =
      (globalSections X).map ((pullbackAdjunction p).unit.app G ≫ (pushforward p).map c) a := by
  let e := globalSectionsIso p
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app J)).1
  have hD : (globalSections X).map ((pushforward p).map d) ≫ e.hom.app J =
      e.hom.app H ≫ (globalSections P).map d := e.hom.naturality d
  have hn : (globalSections X).map ((pushforward p).map c) ≫ e.hom.app J =
      e.hom.app ((pullbackSheaves p).obj G) ≫ (globalSections P).map c := e.hom.naturality c
  have hC : (globalSections X).map ((pullbackAdjunction p).unit.app G ≫ (pushforward p).map c) ≫
      e.hom.app J = (restrictGlobalSections p).app G ≫ (globalSections P).map c := by
    rw [Functor.map_comp, Category.assoc, hn, restrictGlobalSections_app_eq, Category.assoc]
  calc
    _ = (globalSections P).map d (e.hom.app H (e.inv.app H b)) :=
      ConcreteCategory.congr_hom hD (e.inv.app H b)
    _ = (globalSections P).map d b :=
      congrArg ((globalSections P).map d) (ConcreteCategory.congr_hom (e.inv_hom_id_app H) b)
    _ = _ := hb.trans (ConcreteCategory.congr_hom hC a).symm

set_option maxRecDepth 4096 in
/-- The section equation after pullback to a commutative square gives
agreement after restriction of the two direct images to the common composite. -/
theorem restrictDirectImage_eq_of_lift (F : Ab X)
    (a : (globalSections X).obj ((pushforward i).obj ((pullbackSheaves i).obj F)))
    (b : (globalSections P).obj ((pullbackSheaves p).obj F))
    (hb : (globalSections P).map ((pullbackAdjunction j).unit.app ((pullbackSheaves p).obj F)) b =
      (globalSections P).map (pulledImageComparisonOver p i j r ρ hp hi F)
        ((restrictGlobalSections p).app ((pushforward i).obj ((pullbackSheaves i).obj F)) a)) :
    (globalSections X).map (restrictDirectImage p j ρ hp F)
        ((globalSectionsIso p).inv.app ((pullbackSheaves p).obj F) b) =
      (globalSections X).map (restrictDirectImage i r ρ hi F) a := by
  let H := (pullbackSheaves p).obj F
  let G := (pushforward i).obj ((pullbackSheaves i).obj F)
  let d := (pullbackAdjunction j).unit.app H
  let c := pulledImageComparisonOver p i j r ρ hp hi F
  let E := (pullbackSheaves j).obj H
  let θ := ((pushforwardCompIso p j ≪≫ eqToIso (congrArg pushforward hp)).hom.app E) ≫
    (pushforward ρ).map ((pullbackCompIso p j ≪≫ eqToIso (congrArg pullbackSheaves hp)).hom.app F)
  have h := compare_directImage_sections p d c a b hb
  have hδ : ((pullbackAdjunction p).unit.app G ≫ (pushforward p).map c) ≫ θ =
      restrictDirectImage i r ρ hi F :=
    (Category.assoc _ _ _).trans (unit_pulledImageComparison p i j r ρ hp hi F)
  change (globalSections X).map ((pushforward p).map d ≫ θ)
    ((globalSectionsIso p).inv.app H b) = _
  rw [← hδ, Functor.map_comp, Functor.map_comp]
  exact congrArg ((globalSections X).map θ) h

end PhilipponEtaleSectionComparison

end

section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSectionsIso globalSectionsIso_hom_app_eq_map)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (pointFiberIso stalkPullbackIso stalkPullbackIso_germ)


namespace PhilipponEtaleSectionFiniteRefinement

universe u

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

section PullSection

variable {P : Scheme.{u}} (p : P ⟶ X)
variable {U V : X.Etale} {A B : P.Etale}

private def chartLift (l : A.left ⟶ U.left) (hl : l ≫ U.hom = A.hom ≫ p) :
    A ⟶ (baseChange p).obj U :=
  MorphismProperty.Over.homMk (pullback.lift l A.hom hl) (pullback.lift_snd _ _ _) trivial

private theorem chartLift_comp (g : V ⟶ U) (l : A.left ⟶ V.left)
    (hl : l ≫ V.hom = A.hom ≫ p) :
    chartLift p l hl ≫ (baseChange p).map g =
      chartLift p (l ≫ g.left) (by rw [Category.assoc, MorphismProperty.Over.w, hl]) := by
  have hfst : ((baseChange p).map g).left ≫ pullback.fst U.hom p =
      pullback.fst V.hom p ≫ g.left := pullback.lift_fst _ _ _
  have hsnd : ((baseChange p).map g).left ≫ pullback.snd U.hom p =
      pullback.snd V.hom p := pullback.lift_snd _ _ _
  apply MorphismProperty.Over.Hom.ext
  change pullback.lift l A.hom hl ≫ ((baseChange p).map g).left = pullback.lift _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, hfst, pullback.lift_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, hsnd, pullback.lift_snd, pullback.lift_snd]

private theorem comp_chartLift (k : B ⟶ A) (l : A.left ⟶ U.left)
    (hl : l ≫ U.hom = A.hom ≫ p) :
    k ≫ chartLift p l hl =
      chartLift p (k.left ≫ l) (by rw [Category.assoc, hl, ← Category.assoc,
        MorphismProperty.Over.w]) := by
  apply MorphismProperty.Over.Hom.ext
  change k.left ≫ pullback.lift l A.hom hl = pullback.lift _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, MorphismProperty.Over.w]

/-- Pull sections from a chart of the base to a chart of the changed
scheme along a diagram that commutes over the base. -/
def pullSectionAlongChart (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (l : A.left ⟶ U.left) (hl : l ≫ U.hom = A.hom ≫ p) :
    F.obj.obj (op U) ⟶ ((pullbackSheaves p).obj F).obj.obj (op A) :=
  ((pullbackAdjunction p).unit.app F).hom.app (op U) ≫
    ((pullbackSheaves p).obj F).obj.map (chartLift p l hl).op

theorem pullSectionAlongChart_congr (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {l m : A.left ⟶ U.left} (he : l = m)
    (hl : l ≫ U.hom = A.hom ≫ p) (hm : m ≫ U.hom = A.hom ≫ p) :
    pullSectionAlongChart p F l hl = pullSectionAlongChart p F m hm := by
  subst m
  rfl

theorem pullSectionAlongChart_comp (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (g : V ⟶ U) (l : A.left ⟶ V.left) (hl : l ≫ V.hom = A.hom ≫ p) :
    F.obj.map g.op ≫ pullSectionAlongChart p F l hl =
      pullSectionAlongChart p F (l ≫ g.left) (by rw [Category.assoc, MorphismProperty.Over.w, hl]) := by
  let η := (pullbackAdjunction p).unit.app F
  have h := η.hom.naturality g.op
  change F.obj.map g.op ≫ η.hom.app (op V) = η.hom.app (op U) ≫
    ((pullbackSheaves p).obj F).obj.map ((baseChange p).map g).op at h
  unfold pullSectionAlongChart
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp, ← op_comp, chartLift_comp]

theorem pullSectionAlongChart_restrict (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (k : B ⟶ A) (l : A.left ⟶ U.left) (hl : l ≫ U.hom = A.hom ≫ p) :
    pullSectionAlongChart p F l hl ≫ ((pullbackSheaves p).obj F).obj.map k.op =
      pullSectionAlongChart p F (k.left ≫ l) (by rw [Category.assoc, hl, ← Category.assoc,
        MorphismProperty.Over.w]) := by
  unfold pullSectionAlongChart
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, comp_chartLift]

theorem pullSectionAlongChart_naturality {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) (l : A.left ⟶ U.left) (hl : l ≫ U.hom = A.hom ≫ p) :
    η.hom.app (op U) ≫ pullSectionAlongChart p G l hl =
      pullSectionAlongChart p F l hl ≫ ((pullbackSheaves p).map η).hom.app (op A) := by
  let L := pullbackSheaves p
  let u := (pullbackAdjunction p).unit
  let v := chartLift p l hl
  have h := congrArg (fun m : F ⟶ (pushforward p).obj (L.obj G) => m.hom.app (op U)) (u.naturality η)
  change η.hom.app (op U) ≫ (u.app G).hom.app (op U) =
    (u.app F).hom.app (op U) ≫ (L.map η).hom.app (op ((baseChange p).obj U)) at h
  change η.hom.app (op U) ≫ ((u.app G).hom.app (op U) ≫ (L.obj G).obj.map v.op) =
    ((u.app F).hom.app (op U) ≫ (L.obj F).obj.map v.op) ≫ (L.map η).hom.app (op A)
  rw [← Category.assoc, h, Category.assoc, ← (L.map η).hom.naturality v.op, Category.assoc]

end PullSection

/-- A map over the base from a scheme to an étale chart pulls sections on
that chart to global sections of the inverse-image sheaf. -/
def pullSectionAlong {W : Scheme.{u}} (k : W ⟶ X) {V : X.Etale}
    (l : W ⟶ V.left) (hl : l ≫ V.hom = k)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    F.obj.obj (op V) ⟶ ((pullbackSheaves k).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 W))) :=
  pullSectionAlongChart (A := Scheme.Etale.mk (𝟙 W)) k F l (hl.trans (Category.id_comp k).symm)

/-- Pulling a section from the terminal chart agrees with global
restriction along the same morphism. -/
theorem pullSectionAlong_terminal {P : Scheme.{u}} (p : P ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    pullSectionAlong p (V := Scheme.Etale.mk (𝟙 X)) p (Category.comp_id p) F =
      (restrictGlobalSections p).app F := by
  let h : p ≫ 𝟙 X = 𝟙 P ≫ p := (Category.comp_id p).trans (Category.id_comp p).symm
  let k := chartLift (A := Scheme.Etale.mk (𝟙 P)) (U := Scheme.Etale.mk (𝟙 X)) p p h
  change ((pullbackAdjunction p).unit.app F).hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
    ((pullbackSheaves p).obj F).obj.map k.op = _
  rw [← globalSectionsIso_hom_app_eq_map p _ k]
  simp only [restrictGlobalSections, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp]
  rfl

/-- Pulling a section from an étale chart commutes with taking its germ
at the corresponding geometric point of that chart. -/
theorem pullSectionAlong_germ {P : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (p : P ⟶ X) (s : Spec (.of K) ⟶ P) {V : X.Etale}
    (l : P ⟶ V.left) (hl : l ≫ V.hom = p)
    (w : (Scheme.pointSmallEtale (s ≫ p)).fiber.obj V) (hw : w.left = s ≫ l)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    pullSectionAlong p l hl F ≫
      (Scheme.pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk (𝟙 P))
        (Over.homMk s (Category.comp_id s)) ((pullbackSheaves p).obj F).obj ≫
      (stalkPullbackIso p s).hom.app F =
    (Scheme.pointSmallEtale (s ≫ p)).toPresheafFiber V w F.obj := by
  let A := Scheme.Etale.mk (𝟙 P)
  let Q := Scheme.pointSmallEtale s
  let L := pullbackSheaves p
  let h : l ≫ V.hom = 𝟙 P ≫ p := hl.trans (Category.id_comp p).symm
  let k := chartLift (A := A) (U := V) p l h
  let v : Q.fiber.obj A := Over.homMk s (Category.comp_id s)
  let t := Q.fiber.map k v
  have ht : (pointFiberIso p s).hom.app V t = w := by
    apply Over.OverMorphism.ext
    change (s ≫ pullback.lift l (𝟙 P) h) ≫ pullback.fst V.hom p = w.left
    rw [Category.assoc, pullback.lift_fst, hw]
  change (((pullbackAdjunction p).unit.app F).hom.app (op V) ≫ (L.obj F).obj.map k.op) ≫
      Q.toPresheafFiber A v (L.obj F).obj ≫ (stalkPullbackIso p s).hom.app F = _
  rw [Category.assoc, ← Category.assoc ((L.obj F).obj.map k.op), Q.toPresheafFiber_w,
    stalkPullbackIso_germ, ht]

/-- Restriction of a global section along a scheme morphism commutes with
its germ at a geometric point. -/
theorem restrictGlobalSections_germ {P : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (p : P ⟶ X) (s : Spec (.of K) ⟶ P) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (restrictGlobalSections p).app F ≫
      (Scheme.pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk (𝟙 P))
        (Over.homMk s (Category.comp_id s)) ((pullbackSheaves p).obj F).obj ≫
      (stalkPullbackIso p s).hom.app F =
    (Scheme.pointSmallEtale (s ≫ p)).toPresheafFiber (Scheme.Etale.mk (𝟙 X))
      (Over.homMk (s ≫ p) (Category.comp_id _)) F.obj := by
  rw [← pullSectionAlong_terminal]
  exact pullSectionAlong_germ p s (V := Scheme.Etale.mk (𝟙 X)) p (Category.comp_id p)
    (Over.homMk (s ≫ p) (Category.comp_id _)) rfl F

/-- A section on a closed subscheme admits lifts on étale charts such
that a finite surjective cover of the original chart factors through
these lifting charts locally for the Zariski topology. -/
theorem exists_finite_refinement_of_lifts {U : X.Etale} [SpectralSpace U.left]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ↥(((pushforward i).obj ((pullbackSheaves i).obj F)).obj.obj (op U))) :
    ∃ (I : Type u) (_ : Fintype I) (V : I → X.Etale) (g : ∀ j, V j ⟶ U)
      (b : ∀ j, ↥(F.obj.obj (op (V j)))) (P : Scheme.{u}) (p : P ⟶ U.left),
      IsFinite p ∧ Surjective p ∧
      (∀ j, ((pullbackAdjunction i).unit.app F).hom.app (op (V j)) (b j) =
        ((pushforward i).obj ((pullbackSheaves i).obj F)).obj.map (g j).op a) ∧
      ∀ x : P, ∃ (j : I) (W : Scheme.{u}) (k : W ⟶ P), IsOpenImmersion k ∧ x ∈ Set.range k ∧
        ∃ l : W ⟶ (V j).left, l ≫ (g j).left = k ≫ p := by
  obtain ⟨I, hI, V, g, b, _, hCover, hLift⟩ :=
    PhilipponEtaleStalkPullback.exists_finite_affine_lifts i F a
  let S (j : I) := (V j).left
  let α := Sigma.desc (fun j => (g j).left)
  have : Etale α := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ => inferInstance)
  have : Surjective α :=
    Surjective.sigmaDesc_of_union_range_eq_univ ((Scheme.ofArrows_mem_smallEtaleTopology_iff g).mp hCover)
  obtain ⟨P, p, hp, hs, hl⟩ :=
    AlgebraicGeometry.Scheme.exists_finite_zariski_refinement_of_surjective_etale α
  refine ⟨I, hI, V, g, b, P, p, hp, hs, hLift, fun x => ?_⟩
  obtain ⟨W, k, hk, ⟨w, hw⟩, d, hd⟩ := hl x
  obtain ⟨⟨j, z⟩, hz⟩ := (sigmaMk S).surjective (d w)
  let s := Sigma.ι S j
  have hr : w ∈ Set.range (pullback.fst d s) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨z, ?_⟩
    simpa only [s, sigmaMk_mk] using hz
  obtain ⟨w', hw'⟩ := hr
  let v := pullback.fst d s
  let l := pullback.snd d s
  have : IsOpenImmersion v := inferInstanceAs (IsOpenImmersion (pullback.fst d s))
  refine ⟨j, pullback d s, v ≫ k, inferInstance, ⟨w', ?_⟩, l, ?_⟩
  · exact (congrArg k hw').trans hw
  · calc
      l ≫ (g j).left = l ≫ s ≫ α := by
        rw [show s ≫ α = (g j).left from Sigma.ι_desc _ _]
      _ = v ≫ d ≫ α := by rw [← pullback.condition_assoc]
      _ = (v ≫ k) ≫ p := by rw [hd, Category.assoc]

end PhilipponEtaleSectionFiniteRefinement

end

end


