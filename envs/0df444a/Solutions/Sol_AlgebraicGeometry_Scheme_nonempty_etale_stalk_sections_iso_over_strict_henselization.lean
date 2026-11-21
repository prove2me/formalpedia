-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_stalk_sections_iso_over_strict_henselization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T04:25:01.516306+00:00
-- url     : https://prove2.me/submissions/8498e18b-0644-4f5d-989f-3d86a1d755c1

import Definitions.Def_AlgebraicGeometry_EtaleModeledInverseImages

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleStrictHenselization
  (IsAffineNeighborhood affineInclusion pullbackNeighborhoodLimitCone affinePullbackTransition toBase)


namespace PhilipponStrictLocalPresheaf

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X) (f : Y ⟶ X)

private abbrev Local : Scheme.{u} := pullback (toBase s) f
private abbrev π : Local s f ⟶ Y := pullback.snd (toBase s) f
private abbrev T : (Local s f).Etale := Scheme.Etale.mk (𝟙 _)

private abbrev PullbackPointwise (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :=
  (Functor.LeftExtension.mk ((pullbackSheaves (π s f)).obj F).obj
    ((pullbackAdjunction (π s f)).unit.app F).hom).IsPointwiseLeftKanExtensionAt (op (T s f))

private abbrev Φ := Scheme.pointSmallEtale s
private abbrev C := (IsAffineNeighborhood s).FullSubcategory
private abbrev Index := InitiallySmall.CofilteredInitialModel.{u} (C s)
private abbrev H := InitiallySmall.fromCofilteredInitialModel.{u} (C s)
private abbrev J := H s ⋙ affineInclusion s
private abbrev E := J s ⋙ CategoryOfElements.π (Φ s).fiber ⋙ baseChange f
private abbrev D := E s f ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y
private abbrev limitCone : Cone (D s f) := (pullbackNeighborhoodLimitCone s f).cone.whisker (J s)
private abbrev t : (limitCone s f).pt ⟶ Local s f := 𝟙 _

private theorem stageComm (i : Index s) :
    (limitCone s f).π.app i ≫ ((E s f).obj i).hom = t s f ≫ π s f := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _ ≫ pullback.snd _ _
  exact (pullback.lift_snd ..).trans (Category.id_comp _).symm

private def limitWitness : IsLimit (limitCone s f) :=
  (Functor.Initial.isLimitWhiskerEquiv (J s) _).symm (pullbackNeighborhoodLimitCone s f).isLimit

private abbrev q (i : Index s) : (D s f).obj i ⟶ ((H s).obj i).obj.1.left :=
  pullback.fst ((H s).obj i).obj.1.hom f

local instance stageCompact [IsProper f] (i : Index s) : CompactSpace ((D s f).obj i) := by
  let : IsAffine ((H s).obj i).obj.1.left := ((H s).obj i).property
  let : IsProper (q s f i) := inferInstanceAs (IsProper (pullback.fst ((H s).obj i).obj.1.hom f))
  exact (quasiCompact_iff_compactSpace (q s f i)).mp inferInstance

local instance stageQuasiSeparated [IsProper f] (i : Index s) :
    QuasiSeparatedSpace ((D s f).obj i) := by
  let : IsAffine ((H s).obj i).obj.1.left := ((H s).obj i).property
  let : IsProper (q s f i) := inferInstanceAs (IsProper (pullback.fst ((H s).obj i).obj.1.hom f))
  exact quasiSeparatedSpace_of_quasiSeparated (q s f i)

local instance stageAffine {i j : Index s} (b : i ⟶ j) : IsAffineHom ((D s f).map b) :=
  affinePullbackTransition s f ((H s).map b)

private def stageCocone (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ColimitCocone ((E s f).op ⋙ F.obj) :=
  ⟨((Φ s).presheafFiberCocone ((pushforward f).obj F).obj).whisker (J s).op,
    (Functor.Final.isColimitWhiskerEquiv (J s).op _).symm
      ((Φ s).isColimitPresheafFiberCocone ((pushforward f).obj F).obj)⟩

private theorem modeledTerminal [IsProper f] :
    PhilipponEtaleRefinementGluing.modeledCharts (E s f) (limitCone s f) (T s f) := by
  let c := limitCone s f
  let i := Classical.choice (IsCofiltered.nonempty (C := Index s))
  let V := Scheme.Etale.mk (𝟙 ((D s f).obj i))
  let g := pullback.fst (c.π.app i) (𝟙 ((D s f).obj i))
  let e : T s f ≅ (PhilipponEtaleModeledSections.chartLimitFunctor (E s f) c i).obj V :=
    MorphismProperty.Over.isoMk (asIso g).symm (IsIso.inv_hom_id g)
  exact ⟨i, V, ⟨stageCompact s f i, stageQuasiSeparated s f i⟩, ⟨e⟩⟩

private def strictLocalCocones [IsProper f] (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ColimitCocone (CostructuredArrow.proj (baseChange (π s f)).op (op (T s f)) ⋙ F.obj) ×
      PullbackPointwise s f F := by
  let c := limitCone s f
  let hc := limitWitness s f
  refine ⟨PhilipponEtaleLimitPresheaf.pointwisePullbackCocone (π s f) (E s f) c (t s f)
    (stageComm s f) hc F.obj (stageCocone s f F), ?_⟩
  let U : (PhilipponEtaleRefinementGluing.modeledCharts (E s f) c).FullSubcategory :=
    ⟨T s f, modeledTerminal s f⟩
  exact PhilipponEtaleModeledInverseImage.inverseImageIsPointwiseOnModeledChart (E s f) c hc
    (π s f) (fun j => (stageComm s f j).trans (Category.id_comp _)) F U

/-- For proper (f), the geometric stalk of (f_*F) computes the value
at the terminal étale object of the presheaf inverse image of (F) to
the pullback over the strict henselization. -/
def stalkPresheafPullbackCocone [IsProper f] (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ColimitCocone (CostructuredArrow.proj (baseChange (π s f)).op (op (T s f)) ⋙ F.obj) :=
  (strictLocalCocones s f F).1

@[simp] theorem stalkPresheafPullbackCocone_pt [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (stalkPresheafPullbackCocone s f F).cocone.pt =
      (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward f).obj F) := rfl

/-- Degree-zero comparison for a proper morphism at a geometric point.
The geometric direct-image stalk is the sections of the sheaf inverse
image over the strict henselization pullback. -/
def stalkDirectImageIsoStrictLocalSections [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward f).obj F) ≅
      ((pullbackSheaves (π s f)).obj F).obj.obj (op (T s f)) :=
  (stalkPresheafPullbackCocone s f F).isColimit.coconePointUniqueUpToIso
    (strictLocalCocones s f F).2

@[reassoc]
theorem stalkDirectImageIsoStrictLocalSections_ι [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (j : CostructuredArrow (baseChange (π s f)).op (op (T s f))) :
    (stalkPresheafPullbackCocone s f F).cocone.ι.app j ≫
        (stalkDirectImageIsoStrictLocalSections s f F).hom =
      ((pullbackAdjunction (π s f)).unit.app F).hom.app j.left ≫
        ((pullbackSheaves (π s f)).obj F).obj.map j.hom :=
  (stalkPresheafPullbackCocone s f F).isColimit.comp_coconePointUniqueUpToIso_hom
    (strictLocalCocones s f F).2 j

private abbrev comparisonIndex := PhilipponEtaleLimitPresheaf.neighborhoodIndex
  (π s f) (E s f) (limitCone s f) (t s f) (stageComm s f)

private theorem stalkPresheafPullbackCocone_ι_stage [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (i : (Index s)ᵒᵖ) :
    (stalkPresheafPullbackCocone s f F).cocone.ι.app ((comparisonIndex s f).obj i) =
      (stageCocone s f F).cocone.ι.app i :=
  PhilipponEtaleLimitPresheaf.pointwisePullbackCocone_ι (π s f) (E s f) (limitCone s f)
    (t s f) (stageComm s f) (limitWitness s f) F.obj (stageCocone s f F) i

private theorem stageCocone_naturality [IsProper f]
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G) (i : (Index s)ᵒᵖ) :
    (stalkPresheafPullbackCocone s f F).cocone.ι.app ((comparisonIndex s f).obj i) ≫
      (pushforward f ⋙ (Φ s).sheafFiber).map a =
    a.hom.app ((comparisonIndex s f).obj i).left ≫
      (stalkPresheafPullbackCocone s f G).cocone.ι.app ((comparisonIndex s f).obj i) := by
  rw [stalkPresheafPullbackCocone_ι_stage, stalkPresheafPullbackCocone_ι_stage]
  let U := (J s).obj i.unop
  exact (Φ s).toPresheafFiber_naturality ((pushforward f).map a).hom U.1 U.2

/-- The degree-zero strict-local comparison is natural in the sheaf. -/
def stalkDirectImageNatIsoStrictLocalSections [IsProper f] :
    pushforward f ⋙ (Φ s).sheafFiber ≅ pullbackSheaves (π s f) ⋙ globalSections (Local s f) :=
  NatIso.ofComponents (stalkDirectImageIsoStrictLocalSections s f) (fun {F G} a => by
    let B := comparisonIndex s f
    let : B.Final := PhilipponEtaleLimitPresheaf.neighborhoodIndex_final (π s f) (E s f)
      (limitCone s f) (t s f) (stageComm s f) (limitWitness s f)
    let dF := stalkPresheafPullbackCocone s f F
    apply ((Functor.Final.isColimitWhiskerEquiv B dF.cocone).symm dF.isColimit).hom_ext
    intro i
    let j := B.obj i
    change dF.cocone.ι.app j ≫ (pushforward f ⋙ (Φ s).sheafFiber).map a ≫
        (stalkDirectImageIsoStrictLocalSections s f G).hom =
      dF.cocone.ι.app j ≫ (stalkDirectImageIsoStrictLocalSections s f F).hom ≫
        ((pullbackSheaves (π s f)).map a).hom.app (op (T s f))
    rw [← Category.assoc, stageCocone_naturality, Category.assoc,
      stalkDirectImageIsoStrictLocalSections_ι, stalkDirectImageIsoStrictLocalSections_ι_assoc]
    let L := pullbackSheaves (π s f)
    let η := (pullbackAdjunction (π s f)).unit
    have hη := congrArg (fun h : F ⟶ (pushforward (π s f)).obj (L.obj G) => h.hom.app j.left)
      (η.naturality a)
    change a.hom.app j.left ≫ (η.app G).hom.app j.left =
      (η.app F).hom.app j.left ≫ (L.map a).hom.app ((baseChange (π s f)).op.obj j.left) at hη
    change a.hom.app j.left ≫ (η.app G).hom.app j.left ≫ (L.obj G).obj.map j.hom =
      (η.app F).hom.app j.left ≫ (L.obj F).obj.map j.hom ≫ (L.map a).hom.app (op (T s f))
    rw [← Category.assoc, hη, Category.assoc, ← (L.map a).hom.naturality j.hom]
    rfl)

end PhilipponStrictLocalPresheaf

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) :
    Nonempty (PhilipponEtaleClosedPushforward.pushforward f ⋙ (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u}) ≅
      PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f) ⋙ PhilipponEtaleAcyclicCohomology.globalSections (pullback (PhilipponEtaleStrictHenselization.toBase s) f)) := by
  exact ⟨PhilipponStrictLocalPresheaf.stalkDirectImageNatIsoStrictLocalSections s f⟩


end
