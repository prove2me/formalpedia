-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitBoundaryMaps
-- name    : AlgebraicGeometry_EtaleAffineLimitBoundaryMaps
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T06:28:36.996792+00:00
-- url     : https://prove2.me/theorems/5499a887-4fa4-4662-9c56-d72e88263d52
-- title:
--   Connecting maps for limit and stage étale cohomology
-- statement:
--   Restriction to the limit and transition to an earlier stage both commute with the connecting maps of the long exact cohomology sequence.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitCoefficientMaps
import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestrictionComposition

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitExactness (atStageSheaf)
open PhilipponEtalePrimeTorsionComparison (restrict restrict_boundary_along)
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso pullbackConstantIso)
open PhilipponEtaleCohomologyRestrictionComp (sectionsEquiv sectionsEquiv_restrict)
open PhilipponEtalePullbackComposition (restrictGlobalSections_app_eq)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleClosedPushforward (pushforward)


namespace PhilipponEtaleStageCohomology

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}
  {i j : I} (a : i ⟶ j) (F : System (directImages D))

local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullbackSheaves f).Additive :=
  (pullbackAdjunction f).left_adjoint_additive

/-- The transition written with its small étale direct image. -/
def transitionMap : F.obj j ⟶ (pushforward (D.map a)).obj (F.obj i) := F.map a

/-- The transition on inverse-image coefficients is adjoint to the
system's map into the direct image. -/
def transitionCoefficients :
    (pullbackSheaves (D.map a)).obj (F.obj j) ⟶ F.obj i :=
  ((pullbackAdjunction (D.map a)).homEquiv _ _).symm (transitionMap a F)

/-- Cohomology transitions in a compatible system use ordinary pullback
followed by the transition on coefficients. -/
def transition (q : ℕ) : (F.obj j).H q →+ (F.obj i).H q :=
  (Sheaf.H.map (transitionCoefficients a F) q).comp (restrict (D.map a) (F.obj j) q)

theorem transitionCoefficients_naturality {G : System (directImages D)} (η : F ⟶ G) :
    transitionCoefficients a F ≫ η.app i =
      (pullbackSheaves (D.map a)).map (η.app j) ≫ transitionCoefficients a G := by
  let e := pullbackAdjunction (D.map a)
  have h : η.app j ≫ transitionMap a G = transitionMap a F ≫ (pushforward (D.map a)).map (η.app i) :=
    η.naturality a
  unfold transitionCoefficients
  rw [← e.homEquiv_naturality_right_symm, ← e.homEquiv_naturality_left_symm, h]

private def shortComplexMap (S : ShortComplex (System (directImages D))) :
    ((S.map (atStageSheaf j)).map (pullbackSheaves (D.map a))) ⟶ S.map (atStageSheaf i) where
  τ₁ := transitionCoefficients a S.X₁
  τ₂ := transitionCoefficients a S.X₂
  τ₃ := transitionCoefficients a S.X₃
  comm₁₂ := transitionCoefficients_naturality a S.X₁ S.f
  comm₂₃ := transitionCoefficients_naturality a S.X₂ S.g

/-- The transitions commute with connecting maps in cohomology. -/
theorem transition_boundary (S : ShortComplex (System (directImages D)))
    (hS : ∀ k, (S.map (atStageSheaf k)).ShortExact) (q : ℕ) (x : (S.X₃.obj j).H q) :
    transition a S.X₁ (q + 1) (x.comp (hS j).extClass rfl) =
      (transition a S.X₃ q x).comp (hS i).extClass rfl :=
  restrict_boundary_along (D.map a) (hS j) (hS i) (shortComplexMap a S) q x

/-- In degree zero, the transition is evaluation of the system map,
followed by the global-section identification for direct image. -/
theorem sectionsEquiv_transition (x : (F.obj j).H 0) :
    sectionsEquiv (F.obj i) (transition a F 0 x) =
      (globalSectionsIso (D.map a)).hom.app (F.obj i)
        ((globalSections (D.obj j)).map (transitionMap a F) (sectionsEquiv (F.obj j) x)) := by
  let f := D.map a
  let M := F.obj j
  let N := F.obj i
  let m := transitionCoefficients a F
  let e := pullbackAdjunction f
  have hm : e.unit.app M ≫ (pushforward f).map m = transitionMap a F := by
    exact (e.homEquiv_unit M N m).symm.trans ((e.homEquiv M N).apply_symm_apply _)
  change sectionsEquiv N (Sheaf.H.map m 0 (restrict f M 0 x)) = _
  rw [← Sheaf.H.equiv₀_naturality, sectionsEquiv_restrict f M x, restrictGlobalSections_app_eq]
  have h := (globalSectionsIso f).hom.naturality m
  change ((globalSections (D.obj j)).map ((pullbackAdjunction f).unit.app M) ≫
      (globalSectionsIso f).hom.app ((pullbackSheaves f).obj M) ≫
      (globalSections (D.obj i)).map m) (sectionsEquiv M x) = _
  rw [← h, Functor.comp_map, ← Functor.map_comp_assoc, hm]
  rfl

end PhilipponEtaleStageCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitAffinePresheaf (affineCharts exists_affineModel)
open PhilipponEtaleLimitFunctor (affineFunctor limitFunctor)
open PhilipponEtaleLimitSheaf (restriction topology)
open PhilipponEtaleLimitRepresentatives (modelIndices exists_rep)
open PhilipponEtaleLimitLocalImage (imageSieve_mem_of_rep)
open PhilipponEtaleLimitExactness (atStageSheaf exact_limit mono_limitMap)


namespace PhilipponEtaleLimitShortExact

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)

private theorem epi_affineMap {F G : System (directImages D)} (f : F ⟶ G)
    (hf : ∀ i, Epi (f.app i)) : Epi ((affineFunctor c hc).map f) := by
  let : Sheaf.IsLocallySurjective ((affineFunctor c hc).map f) := ⟨fun {U} x => by
    let : IsAffine U.obj.left := U.property
    let M := (exists_affineModel c hc U.obj).some
    obtain ⟨k, y, hy⟩ := exists_rep (M := M) hc x
    let j := (modelIndices c U M).obj k
    let A := j.left.unop
    let : IsAffine A.etale.left :=
      @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine (D.obj k.unop.left)
        M.chart.etale.left (D.obj M.chart.index)
        (D.map k.unop.hom) M.chart.etale.hom inferInstance M.affine inferInstance
    let η := f.app A.index
    let : Sheaf.IsLocallySurjective η :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} η).mpr (hf A.index)
    have hloc := Presheaf.imageSieve_mem (D.obj A.index).smallEtaleTopology η.hom
      (U := op A.etale) y
    rw [← hy]
    exact imageSieve_mem_of_rep c hc f j y hloc inferInstance⟩
  infer_instance

/-- A stagewise epimorphism is locally surjective after taking the limit. -/
theorem epi_limitMap {F G : System (directImages D)} (f : F ⟶ G)
    (hf : ∀ i, Epi (f.app i)) : Epi ((limitFunctor c hc).map f) := by
  let : Epi ((affineFunctor c hc).map f) := epi_affineMap c hc f hf
  exact (restriction c).asEquivalence.inverse.map_epi _

/-- A stagewise short exact sequence stays short exact on the limit. -/
abbrev limitShortComplex (S : ShortComplex (System (directImages D))) :
    ShortComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) :=
  S.map (limitFunctor c hc)

theorem shortExact_limit (S : ShortComplex (System (directImages D)))
    (hS : ∀ i, (S.map (atStageSheaf i)).ShortExact) :
    (limitShortComplex c hc S).ShortExact :=
  ShortComplex.ShortExact.mk'
    (exact_limit c hc S (fun i => (hS i).exact))
    (mono_limitMap c hc S.f (fun i => (hS i).mono_f))
    (epi_limitMap c hc S.g (fun i => (hS i).epi_g))

end PhilipponEtaleLimitShortExact

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitFunctor (limitFunctor)
open PhilipponEtaleLimitExactness (atStageSheaf)
open PhilipponEtaleLimitShortExact (limitShortComplex shortExact_limit)
open PhilipponEtaleLimitCanonical (restrictCoefficients restrictCoefficients_naturality)
open PhilipponEtaleLimitSheaf (limitSheaf)
open PhilipponEtalePrimeTorsionComparison (restrict restrict_boundary_along)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleLimitCohomologyTransport

universe u

private abbrev C (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)

local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullbackSheaves f).Additive :=
  (pullbackAdjunction f).left_adjoint_additive

/-- A cohomology class at one stage restricts to the corresponding
cohomology of the limit sheaf. -/
def stageRestriction (F : System (directImages D)) (i : I) (q : ℕ) :
    (F.obj i).H q →+ (limitSheaf c hc F).H q :=
  ((Ext.mk₀ (restrictCoefficients c hc F i)).postcomp (C c.pt) (add_zero q)).comp
    (restrict (c.π.app i) (F.obj i) q)

private def shortComplexMap (S : ShortComplex (System (directImages D))) (i : I) :
    ((S.map (atStageSheaf i)).map (pullbackSheaves (c.π.app i))) ⟶ limitShortComplex c hc S where
  τ₁ := restrictCoefficients c hc S.X₁ i
  τ₂ := restrictCoefficients c hc S.X₂ i
  τ₃ := restrictCoefficients c hc S.X₃ i
  comm₁₂ := (restrictCoefficients_naturality c hc S.X₁ S.f i).symm
  comm₂₃ := (restrictCoefficients_naturality c hc S.X₂ S.g i).symm

/-- The canonical restriction from a stage to the limit commutes with
the boundary maps of a stagewise short exact sequence. -/
theorem stageRestriction_boundary (S : ShortComplex (System (directImages D)))
    (hS : ∀ i, (S.map (atStageSheaf i)).ShortExact) (i : I) (q : ℕ)
    (x : (S.X₃.obj i).H q) :
    stageRestriction c hc S.X₁ i (q + 1) (x.comp (hS i).extClass rfl) =
      (stageRestriction c hc S.X₃ i q x).comp (shortExact_limit c hc S hS).extClass rfl :=
  restrict_boundary_along (c.π.app i) (hS i) (shortExact_limit c hc S hS)
    (shortComplexMap c hc S i) q x

end PhilipponEtaleLimitCohomologyTransport

end

end


