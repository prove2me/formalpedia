-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms
-- name    : AlgebraicGeometry_EtaleStrictLocalSectionGerms
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T00:41:32.934349+00:00
-- url     : https://prove2.me/theorems/cbc0a301-65fa-485e-b053-a7542d38cb19
-- title:
--   Section germs on finite schemes over strict localizations
-- statement:
--   Identification of strict-local sections with the germs of an étale direct image.

import Definitions.Def_AlgebraicGeometry_EtaleDirectImageSectionGerms
import Definitions.Def_AlgebraicGeometry_EtaleHenselianComponentGerms

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver evalAtLift_germ_of_eq)
open PhilipponEtaleLocalRing (evaluateGerm)
open PhilipponEtaleSectionFiniteRefinement (pullSectionAlong pullSectionAlong_germ)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponEtaleStrictHenselization
  (IsAffineNeighborhood affineInclusion pullbackNeighborhoodLimitCone affinePullbackTransition toBase)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)
open PhilipponStrictLocalFinitePoints (comp_neighborhoodProjection)


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

/-- A representative of a direct-image germ pulls back to the strict-local
section along the projection to its étale chart. -/
@[reassoc]
theorem stalkDirectImageIsoStrictLocalSections_stage [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (i : Index s) :
    let W := (J s).obj i
    (Φ s).toPresheafFiber W.fst W.snd ((pushforward f).obj F).obj ≫
      (stalkDirectImageIsoStrictLocalSections s f F).hom =
    pullSectionAlong (π s f) (V := (E s f).obj i) ((limitCone s f).π.app i)
      ((stageComm s f i).trans (Category.id_comp _)) F := by
  change (stageCocone s f F).cocone.ι.app (op i) ≫
    (stalkDirectImageIsoStrictLocalSections s f F).hom = _
  rw [← stalkPresheafPullbackCocone_ι_stage, stalkDirectImageIsoStrictLocalSections_ι]
  rfl

set_option maxRecDepth 4096 in
/-- The germ of a strict-local section at a point over the strict-local
center is the evaluation of the direct-image stalk at the induced lift. -/
theorem germ_of_stalkDirectImageIsoStrictLocalSections [IsProper f]
    (r : Spec (.of K) ⟶ Local s f)
    (hr : r ≫ pullback.fst (toBase s) f = Spec.map (evaluateGerm s))
    (h : (r ≫ π s f) ≫ f = s) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (stalkDirectImageIsoStrictLocalSections s f F).hom ≫
        (terminalGerm r).app ((pullbackSheaves (π s f)).obj F) ≫
        (stalkPullbackIso (π s f) r).hom.app F =
      evalAtLiftOver f (r ≫ π s f) s h F := by
  apply (stageCocone s f F).isColimit.hom_ext
  intro i
  let W := (J s).obj i.unop
  let k := (pullbackNeighborhoodLimitCone s f).cone.π.app W
  obtain ⟨hfst, hsnd⟩ := comp_neighborhoodProjection s f r hr W
  let v : (Scheme.pointSmallEtale (r ≫ π s f)).fiber.obj ((baseChange f).obj W.fst) :=
    Over.homMk (r ≫ k) hsnd
  have hStage : k ≫ ((baseChange f).obj W.fst).hom = π s f :=
    (stageComm s f i.unop).trans (Category.id_comp _)
  let e := (terminalGerm r).app ((pullbackSheaves (π s f)).obj F) ≫
    (stalkPullbackIso (π s f) r).hom.app F
  calc
    _ = pullSectionAlong (π s f) (V := (baseChange f).obj W.fst) k hStage F ≫ e :=
      stalkDirectImageIsoStrictLocalSections_stage_assoc s f F i.unop e
    _ = (Scheme.pointSmallEtale (r ≫ π s f)).toPresheafFiber
        ((baseChange f).obj W.fst) v F.obj :=
      pullSectionAlong_germ (π s f) r (V := (baseChange f).obj W.fst) k hStage v rfl F
    _ = _ := (evalAtLift_germ_of_eq f (r ≫ π s f) h F W.fst W.snd v hfst).symm

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

end


