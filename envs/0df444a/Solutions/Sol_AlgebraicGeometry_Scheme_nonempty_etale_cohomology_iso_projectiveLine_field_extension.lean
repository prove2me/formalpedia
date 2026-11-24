-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_field_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T04:04:41.327403+00:00
-- url     : https://prove2.me/submissions/796e9794-88a0-40eb-b6f9-5a2ddeae4565
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleDirectImageSectionGerms
import Definitions.Def_AlgebraicGeometry_EtaleHenselianComponentGerms
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Polynomial.Subring
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_projectiveLine_field_extension_of_isAlgClosed
import Theorems.Thm_HenselianLocalRing_of_moduleFinite_of_isLocalRing

set_option maxHeartbeats 1300000

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

local instance stageCompact [QuasiCompact f] (i : Index s) : CompactSpace ((D s f).obj i) := by
  let : IsAffine ((H s).obj i).obj.1.left := ((H s).obj i).property
  let : QuasiCompact (q s f i) := inferInstanceAs (QuasiCompact (pullback.fst ((H s).obj i).obj.1.hom f))
  exact (quasiCompact_iff_compactSpace (q s f i)).mp inferInstance

local instance stageQuasiSeparated [QuasiSeparated f] (i : Index s) :
    QuasiSeparatedSpace ((D s f).obj i) := by
  let : IsAffine ((H s).obj i).obj.1.left := ((H s).obj i).property
  let : QuasiSeparated (q s f i) := inferInstanceAs (QuasiSeparated (pullback.fst ((H s).obj i).obj.1.hom f))
  exact quasiSeparatedSpace_of_quasiSeparated (q s f i)

local instance stageAffine {i j : Index s} (b : i ⟶ j) : IsAffineHom ((D s f).map b) :=
  affinePullbackTransition s f ((H s).map b)

private def stageCocone (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ColimitCocone ((E s f).op ⋙ F.obj) :=
  ⟨((Φ s).presheafFiberCocone ((pushforward f).obj F).obj).whisker (J s).op,
    (Functor.Final.isColimitWhiskerEquiv (J s).op _).symm
      ((Φ s).isColimitPresheafFiberCocone ((pushforward f).obj F).obj)⟩

private theorem modeledTerminal [QuasiCompact f] [QuasiSeparated f] :
    PhilipponEtaleRefinementGluing.modeledCharts (E s f) (limitCone s f) (T s f) := by
  let c := limitCone s f
  let i := Classical.choice (IsCofiltered.nonempty (C := Index s))
  let V := Scheme.Etale.mk (𝟙 ((D s f).obj i))
  let g := pullback.fst (c.π.app i) (𝟙 ((D s f).obj i))
  let e : T s f ≅ (PhilipponEtaleModeledSections.chartLimitFunctor (E s f) c i).obj V :=
    MorphismProperty.Over.isoMk (asIso g).symm (IsIso.inv_hom_id g)
  exact ⟨i, V, ⟨stageCompact s f i, stageQuasiSeparated s f i⟩, ⟨e⟩⟩

private def strictLocalCocones [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
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

/-- For a quasi-compact quasi-separated `f`, the geometric stalk of `f_*F` computes the value
at the terminal étale object of the presheaf inverse image of (F) to
the pullback over the strict henselization. -/
def stalkPresheafPullbackCocone [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    ColimitCocone (CostructuredArrow.proj (baseChange (π s f)).op (op (T s f)) ⋙ F.obj) :=
  (strictLocalCocones s f F).1

@[simp] theorem stalkPresheafPullbackCocone_pt [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (stalkPresheafPullbackCocone s f F).cocone.pt =
      (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward f).obj F) := rfl

/-- Degree-zero comparison for a quasi-compact quasi-separated morphism at a geometric point.
The geometric direct-image stalk is the sections of the sheaf inverse
image over the strict henselization pullback. -/
def stalkDirectImageIsoStrictLocalSections [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward f).obj F) ≅
      ((pullbackSheaves (π s f)).obj F).obj.obj (op (T s f)) :=
  (stalkPresheafPullbackCocone s f F).isColimit.coconePointUniqueUpToIso
    (strictLocalCocones s f F).2

@[reassoc]
theorem stalkDirectImageIsoStrictLocalSections_ι [QuasiCompact f] [QuasiSeparated f]
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

private theorem stalkPresheafPullbackCocone_ι_stage [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (i : (Index s)ᵒᵖ) :
    (stalkPresheafPullbackCocone s f F).cocone.ι.app ((comparisonIndex s f).obj i) =
      (stageCocone s f F).cocone.ι.app i :=
  PhilipponEtaleLimitPresheaf.pointwisePullbackCocone_ι (π s f) (E s f) (limitCone s f)
    (t s f) (stageComm s f) (limitWitness s f) F.obj (stageCocone s f F) i

/-- A representative of a direct-image germ pulls back to the strict-local
section along the projection to its étale chart. -/
@[reassoc]
theorem stalkDirectImageIsoStrictLocalSections_stage [QuasiCompact f] [QuasiSeparated f]
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
theorem germ_of_stalkDirectImageIsoStrictLocalSections [QuasiCompact f] [QuasiSeparated f]
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

end PhilipponStrictLocalPresheaf

end

section

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false


namespace PhilipponStrictHenselianIntegral

open Polynomial IsLocalRing

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- An integral map that is injective on spectra has a local source over a local target. -/
theorem isLocalRing_of_integral_injective_comap [IsLocalRing A] [Nontrivial B]
    [Algebra.IsIntegral A B] (hInj : Function.Injective (PrimeSpectrum.comap (algebraMap A B))) :
    IsLocalRing B := by
  have hcomap (y : MaximalSpectrum B) : y.asIdeal.comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) y.asIdeal)
  let : Subsingleton (MaximalSpectrum B) := ⟨fun i j => by
    apply MaximalSpectrum.ext
    let i' : PrimeSpectrum B := ⟨i.asIdeal, i.isMaximal.isPrime⟩
    let j' : PrimeSpectrum B := ⟨j.asIdeal, j.isMaximal.isPrime⟩
    have h : PrimeSpectrum.comap (algebraMap A B) i' = PrimeSpectrum.comap (algebraMap A B) j' :=
      PrimeSpectrum.ext ((hcomap i).trans (hcomap j).symm)
    exact congrArg PrimeSpectrum.asIdeal (hInj h)⟩
  exact IsLocalRing.of_singleton_maximalSpectrum

/-- A subalgebra with integral local overring is local. -/
private theorem subalgebra_local (C : Subalgebra A B) [IsLocalRing B] [Algebra.IsIntegral A B] :
    IsLocalRing C := by
  let : Algebra.IsIntegral C B := Algebra.IsIntegral.tower_top (R := A)
  let : Nontrivial C := ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x : C => (x : B)) h)⟩⟩
  have he (M : MaximalSpectrum C) : M.asIdeal = (maximalIdeal B).comap C.val.toRingHom := by
    let : M.asIdeal.IsMaximal := M.isMaximal
    have hc : RingHom.ker (algebraMap C B) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective
    obtain ⟨Q, hQ, hM⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) M.asIdeal
      (by rw [hc]; exact bot_le)
    exact hM.symm.trans (congrArg (Ideal.comap C.val.toRingHom) (eq_maximalIdeal hQ))
  let : Subsingleton (MaximalSpectrum C) := ⟨fun i j => MaximalSpectrum.ext ((he i).trans (he j).symm)⟩
  exact IsLocalRing.of_singleton_maximalSpectrum

/-- A local integral algebra over a henselian local ring is henselian.
For Hensel's lemma the polynomial and the approximate root lie in a finite subalgebra. -/
theorem henselianLocalRing_of_integral [HenselianLocalRing A] [IsLocalRing B]
    [Algebra.IsIntegral A B] : HenselianLocalRing B := by
  constructor
  intro f hf a₀ hzero hunit
  classical
  let S : Finset B := insert a₀ f.coeffs
  let C := Algebra.adjoin A (↑S : Set B)
  let : Module.Finite A C := Module.Finite.of_fg
    (fg_adjoin_of_finite S.finite_toSet (fun b _ => Algebra.IsIntegral.isIntegral b))
  let : IsLocalRing C := subalgebra_local C
  let : HenselianLocalRing C := HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := A)
  let : Algebra.IsIntegral C B := Algebra.IsIntegral.tower_top (R := A)
  have hMax : (maximalIdeal B).comap C.val.toRingHom = maximalIdeal C :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := C) (maximalIdeal B))
  let b₀ : C := ⟨a₀, Algebra.subset_adjoin (Finset.mem_insert_self _ _)⟩
  have hcoeff : (↑f.coeffs : Set B) ⊆ C.toSubring := fun _ h =>
    Algebra.subset_adjoin (Finset.mem_insert_of_mem h)
  let p : C[X] := f.toSubring C.toSubring hcoeff
  let i : C →+* B := C.toSubring.subtype
  let : IsLocalHom i := ((local_hom_TFAE i).out 4 0).mp hMax
  have hp : p.map i = f := map_toSubring _ _ _
  have hmonic : p.Monic := Polynomial.monic_of_injective (f := i) Subtype.val_injective (hp.symm ▸ hf)
  have hz : p.eval b₀ ∈ maximalIdeal C := by
    rw [← hMax]
    change i (p.eval b₀) ∈ maximalIdeal B
    rw [← eval_map_apply, hp]
    exact hzero
  have hu : IsUnit (p.derivative.eval b₀) := by
    apply (isUnit_map_iff i _).mp
    rw [← eval_map_apply, ← derivative_map, hp]
    exact hunit
  obtain ⟨b, hb, hc⟩ := HenselianLocalRing.is_henselian p hmonic b₀ hz hu
  refine ⟨(b : B), ?_, ?_⟩
  · change f.eval (i b) = 0
    rw [← hp, eval_map_apply, show p.eval b = 0 from hb, map_zero]
  · rw [← hMax] at hc
    exact hc

/-- The residue field of an integral local algebra over a strictly
henselian ring is separably closed. -/
theorem sepClosed_residue_of_integral [IsLocalRing A] [IsLocalRing B]
    [IsSepClosed (ResidueField A)] [Algebra.IsIntegral A B] : IsSepClosed (ResidueField B) := by
  let L := ResidueField B
  have : Algebra.IsIntegral A L := Algebra.IsIntegral.trans B
  let : Algebra (ResidueField A) L := ResidueField.algebraOfIsIntegral
  let : IsScalarTower A (ResidueField A) L := ResidueField.isScalarTowerOfIsIntegral
  let : Algebra.IsIntegral (ResidueField A) L := Algebra.IsIntegral.tower_top (R := A)
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField A)

end PhilipponStrictHenselianIntegral

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory


namespace PhilipponFiniteLocalGeometricPoint

universe u

/-- A geometric point obtained from the residue field of the base local
ring lifts to the closed point of an integral local scheme over it. -/
theorem exists_closed_lift_of_integral {R B K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing B] [IsLocalRing B] [Field K] [IsAlgClosed K]
    (p : Spec (.of B) ⟶ Spec (.of R)) [IsIntegralHom p]
    (ι : IsLocalRing.ResidueField R →+* K) :
    ∃ t : Spec (.of K) ⟶ Spec (.of B),
      t ≫ p = Spec.map (CommRingCat.ofHom (ι.comp (IsLocalRing.residue R))) ∧
        t default = IsLocalRing.closedPoint B := by
  let r := Spec.preimage p
  let _ : Algebra R B := r.hom.toAlgebra
  have hr : IsIntegralHom (Spec.map r) := by
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.IsIntegral R B := algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hr)
  have hMax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (IsLocalRing.maximalIdeal B)
  have : IsLocalHom (algebraMap R B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 4 0).mp (IsLocalRing.eq_maximalIdeal hMax)
  have : Algebra.IsIntegral R (IsLocalRing.ResidueField B) := Algebra.IsIntegral.trans B
  let : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B) :=
    IsLocalRing.ResidueField.algebraOfIsIntegral
  let : IsScalarTower R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B) :=
    IsLocalRing.ResidueField.isScalarTowerOfIsIntegral
  let : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B) :=
    Algebra.IsIntegral.tower_top (R := R)
  let _ : Algebra (IsLocalRing.ResidueField R) K := ι.toAlgebra
  let ψ : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField R] K := IsAlgClosed.lift
  let t := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
  refine ⟨t, ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) ≫ p = _
    rw [← Spec.map_preimage p, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact ψ.commutes (IsLocalRing.residue R x)
  · change (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))) default = _
    rw [Scheme.Hom.comp_apply]
    exact IsLocalRing.PrimeSpectrum.comap_residue B _

end PhilipponFiniteLocalGeometricPoint

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward
  (pushforward fullyFaithfulPushforward isZero_stalk_pushforward_of_not_mem_range)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback
  (exists_point_lift_of_mem_range stalk_unit_isIso stalkPullbackIso)


namespace PhilipponEtaleClosedImmersionBaseChange

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- A sheaf with zero stalks off a closed subscheme is recovered by
restricting to the closed subscheme and taking the direct image. -/
theorem isIso_unit_of_support {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (F : Ab X)
    (hF : ∀ x : X, geometricMap x default ∉ Set.range f →
      IsZero ((geometricPoint x).sheafFiber.obj F)) :
    IsIso ((pullbackAdjunction f).unit.app F) := by
  let P := ObjectProperty.ofObj fun x : X => geometricPoint x
  have hP : P.IsConservativeFamilyOfPoints :=
    Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let η := (pullbackAdjunction f).unit.app F
  apply ((hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff η).mpr
  intro Φ
  have h := Φ.property
  change ObjectProperty.ofObj (fun x : X => geometricPoint x) Φ.obj at h
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp h
  rw [← hx]
  by_cases hs : geometricMap x default ∈ Set.range f
  · obtain ⟨t, ht⟩ := exists_point_lift_of_mem_range f (geometricMap x) hs
    change IsIso ((Scheme.pointSmallEtale (geometricMap x)).sheafFiber.map η)
    rw [← ht]
    exact stalk_unit_isIso f t F
  · exact (hF x hs).isIso
      (isZero_stalk_pushforward_of_not_mem_range f (geometricMap x) hs
        ((pullbackSheaves f).obj F)) _

end PhilipponEtaleClosedImmersionBaseChange

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleClosedImmersionBaseChange (isIso_unit_of_support)
open PhilipponEtalePullbackComposition (pullbackCompIso restrictGlobalSections_app_eq)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleIteratedFiberSections

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- Pulling sections back along a scheme isomorphism gives an isomorphism. -/
theorem isIso_restrictGlobalSections_of_isIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f]
    (F : Ab X) : IsIso ((restrictGlobalSections f).app F) := by
  let : IsIso ((pullbackAdjunction f).unit.app F) := by
    apply isIso_unit_of_support f F
    intro x hx
    exact (hx (f.surjective _)).elim
  rw [restrictGlobalSections_app_eq]
  infer_instance

end PhilipponEtaleIteratedFiberSections

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver evalAtLift_naturality)
namespace PhilipponEtaleBaseChangeGerms
universe u
variable {K : Type u} [Field K] [IsSepClosed K]
private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev stalk {X : Scheme.{u}} (s : Spec (.of K) ⟶ X) :=
  (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})
@[reassoc]
theorem evalAtLiftOver_naturality {X Y : Scheme.{u}} (p : Y ⟶ X) (v : Spec (.of K) ⟶ Y)
    (s : Spec (.of K) ⟶ X) (h : v ≫ p = s) {F G : Ab Y} (a : F ⟶ G) :
    (stalk s).map ((pushforward p).map a) ≫ evalAtLiftOver p v s h G =
      evalAtLiftOver p v s h F ≫ (stalk v).map a := by
  subst s
  simpa only [evalAtLiftOver, eqToHom_refl, Category.id_comp] using evalAtLift_naturality p v a


end PhilipponEtaleBaseChangeGerms

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
namespace PhilipponEtaleAcyclicCohomology
universe u
private abbrev AbelianSheaves (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
/-- An exact direct image has no positive right derived functors. -/
theorem isZero_higherDirectImage_of_exact {X Y : Scheme.{u}} (f : Y ⟶ X)
    [PreservesFiniteColimits (pushforward f)] (F : AbelianSheaves Y) (q : ℕ) :
    IsZero (((pushforward f).rightDerived (q + 1)).obj F) := by
  let I := injectiveResolution F
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj (pushforward f) (q + 1))
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
  exact (show (I.cocomplex.sc (q + 1)).Exact from I.cocomplex_exactAt_succ q).map (pushforward f)

/-- An exact direct image preserves étale cohomology in all degrees. -/
def cohomologyEquivOfExact {X Y : Scheme.{u}} (f : Y ⟶ X)
    [PreservesFiniteColimits (pushforward f)] (F : AbelianSheaves Y) (n : ℕ) :
    ((pushforward f).obj F).H n ≃+ F.H n :=
  cohomologyEquiv f F (isZero_higherDirectImage_of_exact f F) n

end PhilipponEtaleAcyclicCohomology

end

section

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (cohomologyEquivOfExact)
open PhilipponEtaleBaseChangeGerms (evalAtLiftOver_naturality)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLiftOver evalAtLiftOver_unit)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap algebraicallyClosedGeometricPoints_conservative)
open PhilipponEtaleHenselianStalk (henselianLocalRing residueEmbedding residueFieldIsSepClosed)
open PhilipponEtaleIteratedFiberSections (isIso_restrictGlobalSections_of_isIso)
open PhilipponEtaleLocalRing (evaluateGerm stalkRing)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSectionFiniteRefinement (restrictGlobalSections_germ)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponEtaleStrictHenselization (toBase evaluation_comp_toBase)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm terminalGerm_bijective_at_closedPoint)
open PhilipponStrictHenselianIntegral (isLocalRing_of_integral_injective_comap
  henselianLocalRing_of_integral sepClosed_residue_of_integral)
open PhilipponStrictLocalPresheaf (stalkDirectImageIsoStrictLocalSections
  germ_of_stalkDirectImageIsoStrictLocalSections)


namespace PhilipponEtaleIntegralRadicial

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev stalk {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (s : Spec (.of K) ⟶ X) := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

/-- Over a strictly henselian local base, an integral radicial surjection has
strictly henselian local source. Its global sections are the stalk at the lifted center. -/
private theorem exists_strict_center_germ {A K : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [Field K] [IsAlgClosed K]
    {T : Scheme.{u}} (t : T ⟶ Spec (.of A))
    [IsIntegralHom t] [UniversallyInjective t] [Surjective t]
    (ι : IsLocalRing.ResidueField A →+* K) :
    ∃ w : Spec (.of K) ⟶ T,
      w ≫ t = Spec.map (CommRingCat.ofHom (ι.comp (IsLocalRing.residue A))) ∧
      ∀ F : Ab T, IsIso ((terminalGerm w).app F) := by
  let : IsAffine T := isAffine_of_isAffineHom t
  let B := Γ(T, ⊤)
  let e : Spec B ≅ T := T.isoSpec.symm
  let φ := Spec.preimage (e.hom ≫ t)
  let : Algebra A B := φ.hom.toAlgebra
  have hφ : Spec.map φ = e.hom ≫ t := Spec.map_preimage _
  have hIntegral : IsIntegralHom (Spec.map φ) := hφ ▸ inferInstanceAs (IsIntegralHom (e.hom ≫ t))
  let : Algebra.IsIntegral A B := algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp hIntegral)
  obtain ⟨x, _⟩ := t.surjective (IsLocalRing.closedPoint A)
  let : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨e.inv x⟩
  have hInjective : Function.Injective (PrimeSpectrum.comap (algebraMap A B)) := by
    change Function.Injective (Spec.map φ : Spec B ⟶ Spec (.of A))
    rw [hφ]
    exact t.injective.comp e.hom.injective
  let : IsLocalRing B := isLocalRing_of_integral_injective_comap hInjective
  let : HenselianLocalRing B := henselianLocalRing_of_integral (A := A)
  let : IsSepClosed (IsLocalRing.ResidueField B) := sepClosed_residue_of_integral (A := A)
  obtain ⟨w₀, hw₀, hc⟩ := PhilipponFiniteLocalGeometricPoint.exists_closed_lift_of_integral
    (e.hom ≫ t) ι
  refine ⟨w₀ ≫ e.hom, (Category.assoc _ _ _).trans hw₀, fun F => ?_⟩
  let : IsIso ((restrictGlobalSections e.hom).app F) := isIso_restrictGlobalSections_of_isIso e.hom F
  let : IsIso ((terminalGerm w₀).app ((pullbackSheaves e.hom).obj F)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (terminalGerm_bijective_at_closedPoint B w₀ hc _)
  have hGerm : (restrictGlobalSections e.hom).app F ≫
      (terminalGerm w₀).app ((pullbackSheaves e.hom).obj F) ≫
      (stalkPullbackIso e.hom w₀).hom.app F = (terminalGerm (w₀ ≫ e.hom)).app F :=
    restrictGlobalSections_germ e.hom w₀ F
  rw [← hGerm]
  infer_instance

/-- Evaluation at the lift of an algebraically closed geometric point is an
isomorphism on every stalk of the direct image of an integral radicial surjection. -/
theorem exists_evalAtLiftOver_isIso {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (f : Y ⟶ X) [IsIntegralHom f] [UniversallyInjective f] [Surjective f] (s : Spec (.of K) ⟶ X) :
    ∃ (r : Spec (.of K) ⟶ Y) (hr : r ≫ f = s), ∀ F : Ab Y, IsIso (evalAtLiftOver f r s hr F) := by
  let t := pullback.fst (toBase s) f
  let a := pullback.snd (toBase s) f
  let : IsIntegralHom t := inferInstanceAs (IsIntegralHom (pullback.fst (toBase s) f))
  let : Surjective t := inferInstanceAs (Surjective (pullback.fst (toBase s) f))
  let : UniversallyInjective t := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (toBase s) f).flip (inferInstance : UniversallyInjective f)
  obtain ⟨w, hw, hGerm⟩ := @exists_strict_center_germ (stalkRing s) K _
    (henselianLocalRing s) (residueFieldIsSepClosed s) _ _ _ t _ _ _ (residueEmbedding s)
  have hw' : w ≫ t = Spec.map (evaluateGerm s) := by
    rw [hw]
    congr 1
  have hLift : (w ≫ a) ≫ f = s := by
    change (w ≫ pullback.snd (toBase s) f) ≫ f = s
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ toBase s) hw').trans (evaluation_comp_toBase s)
  refine ⟨w ≫ a, hLift, fun F => ?_⟩
  let : IsIso ((terminalGerm w).app ((pullbackSheaves a).obj F)) := hGerm _
  rw [← germ_of_stalkDirectImageIsoStrictLocalSections s f w hw' hLift F]
  infer_instance

/-- The pullback unit is invertible along an integral radicial surjection. -/
theorem isIso_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f]
    (F : Ab X) : IsIso ((pullbackAdjunction f).unit.app F) := by
  let η := (pullbackAdjunction f).unit.app F
  let Q := ObjectProperty.ofObj (fun x : X => Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x))
  have hQ : Q.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative X
  apply ((hQ.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff η).mpr
  intro Φ
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
  rw [← hx]
  let s := algebraicallyClosedGeometricMap x
  obtain ⟨r, hr, hIso⟩ := exists_evalAtLiftOver_isIso f s
  let G := (pullbackSheaves f).obj F
  let : IsIso (evalAtLiftOver f r s hr G) := hIso G
  let m := evalAtLiftOver f r s hr G ≫ (stalkPullbackIso f r).hom.app F ≫
    eqToHom (congrArg (fun y => (stalk y).obj F) hr)
  have hη : (stalk s).map η ≫ m = 𝟙 _ := evalAtLiftOver_unit f r s hr F
  let : IsIso m := inferInstanceAs (IsIso (evalAtLiftOver f r s hr G ≫ (stalkPullbackIso f r).hom.app F ≫
    eqToHom (congrArg (fun y => (stalk y).obj F) hr)))
  let : IsIso ((stalk s).map η ≫ m) := hη ▸ inferInstanceAs (IsIso (𝟙 ((stalk s).obj F)))
  exact IsIso.of_isIso_comp_right ((stalk s).map η) m

/-- Stalk evaluation shows that the direct image along an integral radicial
surjection is exact. -/
theorem pushforward_preservesFiniteColimits {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    PreservesFiniteColimits (pushforward f) := by
  let Q := ObjectProperty.ofObj (fun x : X => Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x))
  have hQ : Q.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative X
  let : (pushforward f).PreservesEpimorphisms := ⟨fun {F G} m hm => by
    let : Epi m := hm
    let : ∀ Φ : Q.FullSubcategory, Epi (Φ.obj.sheafFiber.map ((pushforward f).map m)) := by
      intro Φ
      obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
      rw [← hx]
      let s := algebraicallyClosedGeometricMap x
      obtain ⟨r, hr, hIso⟩ := exists_evalAtLiftOver_isIso f s
      let : IsIso (evalAtLiftOver f r s hr F) := hIso F
      let : IsIso (evalAtLiftOver f r s hr G) := hIso G
      have h := evalAtLiftOver_naturality f r s hr m
      have : Epi ((stalk s).map ((pushforward f).map m) ≫ evalAtLiftOver f r s hr G) := by
        rw [h]
        infer_instance
      let e := evalAtLiftOver f r s hr G
      let g := (stalk s).map ((pushforward f).map m)
      have he : (g ≫ e) ≫ inv e = g := by simp
      have hEpi : Epi ((g ≫ e) ≫ inv e) := inferInstance
      change Epi g
      exact he ▸ hEpi
    exact (hQ.jointlyReflectEpimorphisms AddCommGrpCat.{u}).epi ((pushforward f).map m)⟩
  have : (pushforward f).PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Integral radicial surjections preserve étale cohomology with inverse-image coefficients. -/
def cohomologyIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsIntegralHom f] [UniversallyInjective f] [Surjective f] (F : Ab X) (q : ℕ) :
    AddCommGrpCat.of (F.H q) ≅ AddCommGrpCat.of (((pullbackSheaves f).obj F).H q) := by
  let : IsIso ((pullbackAdjunction f).unit.app F) := isIso_unit f F
  let : PreservesFiniteColimits (pushforward f) := pushforward_preservesFiniteColimits f
  exact (Sheaf.functorH X.smallEtaleTopology q).mapIso (asIso ((pullbackAdjunction f).unit.app F)) ≪≫
    (cohomologyEquivOfExact f ((pullbackSheaves f).obj F) q).toAddCommGrpIso

private abbrev fieldMap (L E : Type u) [Field L] [Field E] [Algebra L E] :=
  Spec.map (CommRingCat.ofHom (algebraMap L E))

/-- Purely inseparable field extension preserves étale cohomology with
inverse-image coefficients, including when the field extension is infinite. -/
def cohomologyIso_of_purelyInseparable {L E : Type u} [Field L] [Field E] [Algebra L E]
    [IsPurelyInseparable L E] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of L)) (g : Y ⟶ Spec (.of E)) (a : Y ⟶ X)
    (h : IsPullback g a (fieldMap L E) f) (F : Ab X) (q : ℕ) :
    AddCommGrpCat.of (F.H q) ≅ AddCommGrpCat.of (((pullbackSheaves a).obj F).H q) := by
  let : IsIntegralHom (fieldMap L E) := IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  let : UniversallyInjective (fieldMap L E) := by
    apply ((tfae_universallyInjective (fieldMap L E)).out 0 1).mpr
    intro K _ s t h
    have hComp := congrArg Spec.preimage h
    simp only [fieldMap, Spec.preimage_comp, Spec.preimage_map] at hComp
    have hRing := congrArg CommRingCat.Hom.hom hComp
    have hEq := IsPurelyInseparable.injective_comp_algebraMap L E K hRing
    simpa only [Spec.map_preimage] using congrArg Spec.map (CommRingCat.hom_ext hEq)
  let : Surjective (fieldMap L E) := ⟨fun y => ⟨default, Subsingleton.elim _ y⟩⟩
  let : IsIntegralHom a := MorphismProperty.of_isPullback h (inferInstance : IsIntegralHom (fieldMap L E))
  let : UniversallyInjective a := MorphismProperty.of_isPullback h (inferInstance : UniversallyInjective (fieldMap L E))
  let : Surjective a := MorphismProperty.of_isPullback h (inferInstance : Surjective (fieldMap L E))
  exact cohomologyIso a F q

end PhilipponEtaleIntegralRadicial

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
namespace PhilipponEtaleProjectiveLineFiberComparison
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Line (R : Type u) [CommRing R] := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)
/-- Comparison after extension of a separably closed field. -/
def FieldComparison (R : Type u) [CommRing R] (N q : ℕ) : Prop :=
  ∀ (L E : Type u) [Field L] [IsSepClosed L] [Field E] [IsSepClosed E]
    (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Line R) (_ : IsPullback r d v (ProjSpace.π R 1))
    (j : T ⟶ Spec (.of E)) (a : T ⟶ P) (_ : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
    (F : Ab P) (_ : N • 𝟙 F = 0),
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅ AddCommGrpCat.of (((pullbackSheaves a).obj F).H (q + 1)))


end PhilipponEtaleProjectiveLineFiberComparison

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleProjectiveLineFiberComparison (FieldComparison)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleProjectiveLineAlgebraicClosures

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Line (R : Type u) [CommRing R] := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)
private abbrev cohomology {X : Scheme.{u}} (F : Ab X) (q : ℕ) := AddCommGrpCat.of (F.H q)

/-- For separably closed fields, field-extension invariance reduces to
purely inseparable extension and extension of algebraically closed fields. -/
theorem fieldComparison_of_algClosed_and_purelyInseparable (R : Type u) [CommRing R] (N q : ℕ)
    (hAlg : ∀ (L E : Type u) [Field L] [IsAlgClosed L] [Field E] [IsAlgClosed E]
      (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
      (r : P ⟶ Spec (.of L)) (d : P ⟶ Line R) (_ : IsPullback r d v (ProjSpace.π R 1))
      (j : T ⟶ Spec (.of E)) (a : T ⟶ P) (_ : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
      (F : Ab P) (_ : N • 𝟙 F = 0),
      Nonempty (cohomology F (q + 1) ≅ cohomology ((pullbackSheaves a).obj F) (q + 1)))
    (hPure : ∀ (L E : Type u) [Field L] [Field E] [Algebra L E] [IsPurelyInseparable L E]
      (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
      (r : P ⟶ Spec (.of L)) (d : P ⟶ Line R) (_ : IsPullback r d v (ProjSpace.π R 1))
      (j : T ⟶ Spec (.of E)) (a : T ⟶ P)
      (_ : IsPullback j a (Spec.map (CommRingCat.ofHom (algebraMap L E))) r)
      (F : Ab P) (_ : N • 𝟙 F = 0),
      Nonempty (cohomology F (q + 1) ≅ cohomology ((pullbackSheaves a).obj F) (q + 1))) :
    FieldComparison R N q := by
  intro L E _ _ _ _ φ v P T r d hr j a h F hF
  let L' := AlgebraicClosure L
  let E' := AlgebraicClosure E
  let γ : L →+* E' := (algebraMap E E').comp φ
  let : Algebra L E' := γ.toAlgebra
  let ψ : L' →ₐ[L] E' := IsAlgClosed.lift
  let sL := Spec.map (CommRingCat.ofHom (algebraMap L L'))
  let sE := Spec.map (CommRingCat.ofHom (algebraMap E E'))
  let f := Spec.map (CommRingCat.ofHom φ)
  let f' := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hw : sE ≫ f = f' ≫ sL := by
    dsimp only [sE, f, f', sL]
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext x
    exact (ψ.commutes x).symm
  let jL := pullback.fst sL r
  let aL := pullback.snd sL r
  have hL : IsPullback jL aL sL r := IsPullback.of_hasPullback sL r
  let jE := pullback.fst sE j
  let aE := pullback.snd sE j
  have hE : IsPullback jE aE sE j := IsPullback.of_hasPullback sE j
  have hOuter : IsPullback jE (aE ≫ a) (f' ≫ sL) r := hw ▸ (hE.paste_vert h)
  let b := hL.lift (jE ≫ f') (aE ≫ a) ((Category.assoc _ _ _).trans hOuter.w)
  have hb₁ : b ≫ jL = jE ≫ f' := hL.lift_fst _ _ _
  have hb₂ : b ≫ aL = aE ≫ a := hL.lift_snd _ _ _
  have hb : IsPullback jE b f' jL := by
    apply IsPullback.of_bot ?_ hb₁.symm hL
    rw [hb₂]
    exact hOuter
  have annihilated {Z W : Scheme.{u}} (c : W ⟶ Z) (G : Ab Z) (hG : N • 𝟙 G = 0) :
      N • 𝟙 ((pullbackSheaves c).obj G) = 0 := by
    let S := pullbackSheaves c
    let : S.Additive := (pullbackAdjunction c).left_adjoint_additive
    simpa only [S.map_nsmul, S.map_id, S.map_zero] using congrArg (fun m => S.map m) hG
  let FL := (pullbackSheaves aL).obj F
  let FE := (pullbackSheaves a).obj F
  obtain ⟨eL⟩ := hPure L L' v r d hr jL aL hL F hF
  obtain ⟨eA⟩ := hAlg L' E' ψ.toRingHom (sL ≫ v) jL (aL ≫ d) (hL.paste_vert hr)
    jE b hb FL (annihilated aL F hF)
  obtain ⟨eE⟩ := hPure E E' (f ≫ v) j (a ≫ d) (h.paste_vert hr) jE aE hE FE (annihilated a F hF)
  let β := (pullbackCompIso aL b).app F ≪≫ (eqToIso (congrArg pullbackSheaves hb₂)).app F ≪≫
    (pullbackCompIso a aE).symm.app F
  let H := Sheaf.functorH (pullback sE j).smallEtaleTopology (q + 1)
  exact ⟨eL ≪≫ eA ≪≫ H.mapIso β ≪≫ eE.symm⟩

end PhilipponEtaleProjectiveLineAlgebraicClosures

end

section

attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R L E : Type u) [CommRing R] [Field L] [IsSepClosed L] [Field E] [IsSepClosed E]
    (φ : L →+* E) (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R)) (hr : IsPullback r d v (ProjSpace.π R 1))
    (j : T ⟶ Spec (.of E)) (a : T ⟶ P) (ha : IsPullback j a (Spec.map (CommRingCat.ofHom φ)) r)
    (N : ℕ) (hN : N.Prime) (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) (hF : N • 𝟙 F = 0) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (F.H (q + 1)) ≅
      AddCommGrpCat.of (((PhilipponEtaleSmallSite.pullbackSheaves a).obj F).H (q + 1))) := by
  have comparison := PhilipponEtaleProjectiveLineAlgebraicClosures.fieldComparison_of_algClosed_and_purelyInseparable
    R N q ?_ ?_
  · exact comparison L E φ v r d hr j a ha F hF
  · intro K K' _ _ _ _ ψ w P' T' r' d' hr' j' a' ha' F' hF'
    exact AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_projectiveLine_field_extension_of_isAlgClosed R K K' ψ w r' d' hr' j' a' ha' N hN F' hF' q
  · intro K K' _ _ _ _ w P' T' r' d' hr' j' a' ha' F' hF'
    exact ⟨PhilipponEtaleIntegralRadicial.cohomologyIso_of_purelyInseparable r' j' a' ha' F' (q + 1)⟩

end

end
