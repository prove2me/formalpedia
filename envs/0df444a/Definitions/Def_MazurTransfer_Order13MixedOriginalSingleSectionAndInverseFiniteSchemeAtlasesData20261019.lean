-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalSingleSectionAndInverseFiniteSchemeAtlasesData20261019
-- name    : MazurTransfer_Order13MixedOriginalSingleSectionAndInverseFiniteSchemeAtlasesData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T06:14:53.105046+00:00
-- url     : https://prove2.me/theorems/3ddb134a-d1f8-4e2a-96f5-47497d881c24
-- title:
--   Original mixed finite scheme atlases
-- statement:
--   Both original finite affine spectra and their two-chart atlases, overlaps and open immersions. Original constructor types, chosen values and prior constructor contexts are checked independently. Named downstream consumer: actual affine-complement comparisons.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both original finite algebra spectra, their original two-chart
scheme atlases, open chart maps and specified overlap morphisms for the mixed
single-section parameters. Named downstream consumer: identifying these
atlases with the actual affine complements and building FiniteMapData.
Original per-file headers and attribution are retained below.
-/
import Mathlib

import Definitions.Def_MazurTransfer_Order13MixedOriginalSingleSectionReciprocalPatchesAndChartEquivalencesDataExplicitEquationDegreeV220261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: spectrum of the literal mixed inverse finite algebra and
its finite parameter map, with the actual ordinary t-localized comparison.
Named downstream consumer: the second finite curve chart and its atlas.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial Order13MixedInverseParameterPolynomialIdentities
variable (R : Type u) [CommRing R]

open AlgebraicGeometry CategoryTheory

def inverseFiniteAffineScheme : Scheme := Spec (.of (candidateAlgebra R))

def inverseFiniteAffineMap : inverseFiniteAffineScheme R ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R)))

theorem inverseFiniteAffineMap_isFinite  :
    IsFinite (inverseFiniteAffineMap R) := by
  letI := candidateAlgebra_finite R
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial R) (candidateAlgebra R))))
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

def ordinaryLocalizedToInverseFinite : Spec (.of (ordinaryParameterLocalization R)) ⟶
    inverseFiniteAffineScheme R :=
  Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom)

theorem ordinaryLocalizedToInverseFinite_parameter :
    ordinaryLocalizedToInverseFinite R ≫ inverseFiniteAffineMap R =
      Spec.map (CommRingCat.ofHom (parameterMap R)) := by
  change Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact (candidateAlgebra R).val.commutes f

theorem ordinaryLocalizedToInverseFinite_base :
    ordinaryLocalizedToInverseFinite R ≫ inverseFiniteAffineMap R ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (ordinaryParameterLocalization R))) := by
  rw [← Category.assoc, ordinaryLocalizedToInverseFinite_parameter, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simp [parameterMap]

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseFiniteAffineMap_isFinite
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.ordinaryLocalizedToInverseFinite_base

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual two-member open cover of the finite coordinate
scheme by the ordinary t-open chart and the retained reciprocal patch.
Named downstream consumer: gluing this atlas to the exact section complement.
The global comparison and finite-map data are separate obligations.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
variable (R : Type u) [CommRing R] [IsDomain R]

def candidateParameterChartMap : Spec (.of (parameterLocalization R)) ⟶ inverseFiniteAffineScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (parameterLocalization R)))

def ordinaryParameterFiniteChartIso :
    Spec (.of (Order13MixedInverseParameterPolynomialIdentities.ordinaryParameterLocalization R)) ≅
      Spec (.of (parameterLocalization R)) :=
  Scheme.Spec.mapIso (parameterLocalizationEquiv R).toRingEquiv.toCommRingCatIso.op

def ordinaryParameterToFiniteAffineScheme :
    Spec (.of (Order13MixedInverseParameterPolynomialIdentities.ordinaryParameterLocalization R)) ⟶ inverseFiniteAffineScheme R :=
  (ordinaryParameterFiniteChartIso R).hom ≫ candidateParameterChartMap R

theorem ordinaryParameterToFiniteAffineScheme_isOpenImmersion :
    IsOpenImmersion (ordinaryParameterToFiniteAffineScheme R) := by
  let : IsOpenImmersion (candidateParameterChartMap R) := IsOpenImmersion.of_isLocalization (sElement R)
  unfold ordinaryParameterToFiniteAffineScheme
  infer_instance

theorem ordinaryParameterToFiniteAffineScheme_range :
    Set.range (ordinaryParameterToFiniteAffineScheme R) =
      (PrimeSpectrum.basicOpen (sElement R) : Set (PrimeSpectrum (candidateAlgebra R))) := by
  let : IsOpenImmersion (candidateParameterChartMap R) := IsOpenImmersion.of_isLocalization (sElement R)
  have he := Scheme.Hom.opensRange_comp_of_isIso
    (ordinaryParameterFiniteChartIso R).hom (candidateParameterChartMap R)
  exact (congrArg (fun U : (inverseFiniteAffineScheme R).Opens => (U : Set (inverseFiniteAffineScheme R))) he).trans
    (PrimeSpectrum.localization_away_comap_range (parameterLocalization R) (sElement R))

def candidateInfinityChartMap : Spec (.of (infinityLocalization R)) ⟶ inverseFiniteAffineScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (infinityLocalization R)))

def reciprocalFiniteChartIso  :
    Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) ≅
      Spec (.of (infinityLocalization R)) :=
  Scheme.Spec.mapIso (recoveredReciprocalPatchEquiv R).symm.toRingEquiv.toCommRingCatIso.op

def reciprocalToFiniteAffineScheme  :
    Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) ⟶ inverseFiniteAffineScheme R :=
  (reciprocalFiniteChartIso R).hom ≫ candidateInfinityChartMap R

theorem reciprocalToFiniteAffineScheme_isOpenImmersion  :
    IsOpenImmersion (reciprocalToFiniteAffineScheme R) := by
  let : IsOpenImmersion (candidateInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (infinityPatchElement R)
  unfold reciprocalToFiniteAffineScheme
  infer_instance

theorem reciprocalToFiniteAffineScheme_range  :
    Set.range (reciprocalToFiniteAffineScheme R) =
      (PrimeSpectrum.basicOpen (infinityPatchElement R) : Set (PrimeSpectrum (candidateAlgebra R))) := by
  let : IsOpenImmersion (candidateInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (infinityPatchElement R)
  have he := Scheme.Hom.opensRange_comp_of_isIso
    (reciprocalFiniteChartIso R).hom (candidateInfinityChartMap R)
  exact (congrArg (fun U : (inverseFiniteAffineScheme R).Opens => (U : Set (inverseFiniteAffineScheme R))) he).trans
    (PrimeSpectrum.localization_away_comap_range (infinityLocalization R) (infinityPatchElement R))

theorem finiteScheme_two_chart_range_cover  :
    Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
      Set.range (reciprocalToFiniteAffineScheme R) = Set.univ := by
  rw [ordinaryParameterToFiniteAffineScheme_range,reciprocalToFiniteAffineScheme_range]
  change ((PrimeSpectrum.basicOpen (sElement R) : Set (PrimeSpectrum (candidateAlgebra R))) ∪
    (PrimeSpectrum.basicOpen (infinityPatchElement R) : Set (PrimeSpectrum (candidateAlgebra R)))) = Set.univ
  have he := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum (candidateAlgebra R)) =>
    (U : Set (PrimeSpectrum (candidateAlgebra R))))
      (inverse_candidate_two_principal_open_cover R )
  simpa only [TopologicalSpace.Opens.coe_sup,TopologicalSpace.Opens.coe_top] using he

def finiteSchemeChart (b : Bool) : Scheme.{u} :=
  if b then Spec (.of (Order13MixedInverseParameterPolynomialIdentities.ordinaryParameterLocalization R))
  else Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))

def finiteSchemeChartMap  :
    (b : Bool) → finiteSchemeChart R b ⟶ inverseFiniteAffineScheme R
  | true => ordinaryParameterToFiniteAffineScheme R
  | false => reciprocalToFiniteAffineScheme R

theorem finiteSchemeChartMap_isOpenImmersion  (b : Bool) :
    IsOpenImmersion (finiteSchemeChartMap R b) := by
  cases b with
  | false => exact reciprocalToFiniteAffineScheme_isOpenImmersion R
  | true => exact ordinaryParameterToFiniteAffineScheme_isOpenImmersion R

def finiteSchemeOpenCover  : (inverseFiniteAffineScheme R).OpenCover where
  I₀ := Bool
  X := finiteSchemeChart R
  f := finiteSchemeChartMap R
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro a
      have ha : a ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
          Set.range (reciprocalToFiniteAffineScheme R) := by
        rw [finiteScheme_two_chart_range_cover]
        trivial
      rcases ha with ha | ha
      · exact ⟨true,ha⟩
      · exact ⟨false,ha⟩
    · exact finiteSchemeChartMap_isOpenImmersion R

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.reciprocalToFiniteAffineScheme_range
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.finiteSchemeOpenCover

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both inverse finite-chart sources map into the actual
original curve over its actual structural base, and the positive infinity
section lifts into the positive reciprocal patch. No gluing is assumed.
Named downstream consumer: the global inverse finite-chart comparison.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Polynomial CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve Order13MixedQuadraticInfinitySections
open Order13MixedInverseParameterPolynomialIdentities (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]

def ordinaryParameterCurveMap : Spec (.of (ordinaryParameterLocalization R)) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R))) ≫
    ordinaryChartMap R

def positiveReciprocalCurveMap :
    Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
    (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) ≫ reciprocalChartMap R

private theorem spec_structure (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
    Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R A B).symm

theorem ordinaryParameterCurveMap_base : ordinaryParameterCurveMap R ≫ curveToBase R =
    Spec.map (CommRingCat.ofHom (algebraMap R (ordinaryParameterLocalization R))) := by
  let j : Spec (.of (ordinaryParameterLocalization R)) ⟶ ordinaryScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)))
  have hj : j ≫ ordinaryToBase R =
      Spec.map (CommRingCat.ofHom (algebraMap R (ordinaryParameterLocalization R))) :=
    spec_structure R (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)
  have he := congrArg (fun k : ordinaryScheme R ⟶ Spec (.of R) => j ≫ k)
    (ordinaryChartMap_curveToBase R)
  exact (Category.assoc j (ordinaryChartMap R) (curveToBase R)).trans (he.trans hj)

theorem positiveReciprocalCurveMap_base : positiveReciprocalCurveMap R ≫ curveToBase R =
    Spec.map (CommRingCat.ofHom (algebraMap R (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) := by
  let j : Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) ⟶ reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
      (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)))
  have hj : j ≫ reciprocalToBase R = Spec.map (CommRingCat.ofHom
      (algebraMap R (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) :=
    spec_structure R (reciprocalCoordinateRing R) (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)
  have he := congrArg (fun k : reciprocalScheme R ⟶ Spec (.of R) => j ≫ k)
    (reciprocalChartMap_curveToBase R)
  exact (Category.assoc j (reciprocalChartMap R) (curveToBase R)).trans (he.trans hj)

def positiveInfinityPatchEvaluation  :
    Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R →+* R :=
  IsLocalization.Away.lift (g := (infinityPointZero R).toRingHom)
    (x := Order13MixedInverseParameterPositiveReciprocalPatch.f R *
      Order13MixedInverseParameterPositiveReciprocalPatch.g R) (by
    change IsUnit (infinityPointZero R
      (Order13MixedInverseParameterPositiveReciprocalPatch.f R *
        Order13MixedInverseParameterPositiveReciprocalPatch.g R))
    rw [Order13MixedInverseParameterPositiveReciprocalPatch.positive_infinity_denominator]
    exact isUnit_one)

theorem positiveInfinityPatchEvaluation_algebraMap  (c : reciprocalCoordinateRing R) :
    positiveInfinityPatchEvaluation R (algebraMap (reciprocalCoordinateRing R)
      (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R) c) =
      (infinityPointZero R).toRingHom c := by
  simp [positiveInfinityPatchEvaluation,IsLocalization.Away.lift_eq]

def positiveInfinityPatchMorphism  :
    Spec (.of R) ⟶ Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) :=
  Spec.map (CommRingCat.ofHom (positiveInfinityPatchEvaluation R))

theorem positiveInfinityPatchMorphism_curve  :
    positiveInfinityPatchMorphism R ≫ positiveReciprocalCurveMap R =
      infinitySectionZero R := by
  let e := positiveInfinityPatchMorphism R
  let j : Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) ⟶ reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
      (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)))
  let z : Spec (.of R) ⟶ reciprocalScheme R :=
    Spec.map (CommRingCat.ofHom (infinityPointZero R).toRingHom)
  have he : e ≫ j = z := by
    change Spec.map (CommRingCat.ofHom (positiveInfinityPatchEvaluation R)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
        (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) =
      Spec.map (CommRingCat.ofHom (infinityPointZero R).toRingHom)
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact positiveInfinityPatchEvaluation_algebraMap R
  exact (Category.assoc e j (reciprocalChartMap R)).symm.trans
    (congrArg (fun k : Spec (.of R) ⟶ reciprocalScheme R => k ≫ reciprocalChartMap R) he)

theorem positiveInfinityPatchMorphism_base  :
    positiveInfinityPatchMorphism R ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R))) = 𝟙 _ := by
  rw [← positiveReciprocalCurveMap_base,← Category.assoc,positiveInfinityPatchMorphism_curve,
    Order13MixedQuadraticInfinitySections.infinitySectionZero_comp]

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.ordinaryParameterCurveMap_base
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.positiveReciprocalCurveMap_base
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.positiveInfinityPatchMorphism_curve

#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.positiveInfinityPatchMorphism_base

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse infinity-localization inclusion is
injective over every commutative base, and its s and recovered z have no
multiplicative kernel. Named downstream consumer: the common inverse-chart
localization and original curve overlap comparison. No gluing is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
variable (R : Type u) [CommRing R]

def infinityMapAsAway : infinityLocalization R →ₐ[R] ordinaryInfinityLocalization R :=
  IsLocalization.Away.mapₐ _ _ (inclusion R) (infinityPatchElement R)

theorem infinityLocalizedInclusion_eq_mapAsAway : infinityLocalizedInclusion R = infinityMapAsAway R := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (infinityPatchElement R))
  apply RingHom.ext
  intro c
  change infinityLocalizedInclusion R (algebraMap (candidateAlgebra R) (infinityLocalization R) c) =
    infinityMapAsAway R (algebraMap (candidateAlgebra R) (infinityLocalization R) c)
  rw [infinityLocalizedInclusion_algebraMap]
  simp [infinityMapAsAway,IsLocalization.Away.mapₐ,IsLocalization.Away.map,IsLocalization.map_eq,
    ordinaryInfinityMap]

theorem infinityLocalizedInclusion_injective : Function.Injective (infinityLocalizedInclusion R) := by
  rw [infinityLocalizedInclusion_eq_mapAsAway]
  exact IsLocalization.Away.mapₐ_injective_of_injective (infinityPatchElement R)
    (f := inclusion R) Subtype.val_injective

theorem infinityS_mul_injective : Function.Injective (fun c : infinityLocalization R => infinityS R * c) := by
  intro c d h
  apply infinityLocalizedInclusion_injective R
  have hh := congrArg (infinityLocalizedInclusion R) h
  rw [map_mul,map_mul,infinityLocalizedInclusion_S] at hh
  exact (ordinaryS_isUnit R).mul_right_inj.mp hh

theorem infinityLocalizedInclusion_recoveredZ_isUnit :
    IsUnit (infinityLocalizedInclusion R (infinityRecoveredZ R)) := by
  apply isUnit_of_mul_isUnit_right
  rw [ordinaryX_mul_recoveredZ]
  exact isUnit_one

theorem infinityRecoveredZ_mul_injective :
    Function.Injective (fun c : infinityLocalization R => infinityRecoveredZ R * c) := by
  intro c d h
  apply infinityLocalizedInclusion_injective R
  have hh := congrArg (infinityLocalizedInclusion R) h
  rw [map_mul,map_mul] at hh
  exact (infinityLocalizedInclusion_recoveredZ_isUnit R).mul_right_inj.mp hh

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.infinityLocalizedInclusion_injective
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.infinityS_mul_injective
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.infinityRecoveredZ_mul_injective

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the reciprocal finite chart meets the ordinary finite chart
exactly in the original reciprocal z-open locus.
Named downstream consumer: the inverse finite atlas comparison with the
actual original curve. This does not assume a global comparison.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
variable (R : Type u) [CommRing R]

open Order13MixedInverseParameterPositiveReciprocalPatch in
theorem reciprocal_patch_parameter_basicOpen :
    PrimeSpectrum.basicOpen (s R) = PrimeSpectrum.basicOpen (z R) := by
  have he : PrimeSpectrum.basicOpen (F R) ⊓ PrimeSpectrum.basicOpen (r R) = ⊤ := by
    rw [← PrimeSpectrum.basicOpen_mul, F_mul_r, PrimeSpectrum.basicOpen_one]
  have hr : PrimeSpectrum.basicOpen (r R) = ⊤ :=
    top_unique (he.symm.le.trans inf_le_right)
  rw [s, PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_pow _ 3 (by norm_num), hr, inf_top_eq]

variable [IsDomain R]

def reciprocalFiniteChartRingHom  :
    candidateAlgebra R →+* Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R :=
  (recoveredReciprocalPatchEquiv R).symm.toRingHom.comp
    (algebraMap (candidateAlgebra R) (infinityLocalization R))

theorem reciprocalFiniteChartRingHom_s  :
    reciprocalFiniteChartRingHom R (sElement R) =
      Order13MixedInverseParameterPositiveReciprocalPatch.s R := by
  change (recoveredReciprocalPatchEquiv R).symm (infinityS R) = _
  apply (recoveredReciprocalPatchEquiv R).injective
  rw [AlgEquiv.apply_symm_apply, recoveredReciprocalPatchEquiv_s]

theorem reciprocalFiniteChart_parameter_preimage  :
    TopologicalSpace.Opens.comap
      ⟨PrimeSpectrum.comap (reciprocalFiniteChartRingHom R),
        PrimeSpectrum.continuous_comap (reciprocalFiniteChartRingHom R)⟩
      (PrimeSpectrum.basicOpen (sElement R)) =
        PrimeSpectrum.basicOpen (Order13MixedInverseParameterPositiveReciprocalPatch.z R) := by
  rw [PrimeSpectrum.comap_basicOpen, reciprocalFiniteChartRingHom_s,
    reciprocal_patch_parameter_basicOpen]

theorem reciprocalFiniteChartRingHom_Spec  :
    Spec.map (CommRingCat.ofHom (reciprocalFiniteChartRingHom R)) =
      reciprocalToFiniteAffineScheme R := by
  rw [reciprocalToFiniteAffineScheme, reciprocalFiniteChartIso, candidateInfinityChartMap]
  change Spec.map (CommRingCat.ofHom (reciprocalFiniteChartRingHom R)) =
    Spec.map (CommRingCat.ofHom (recoveredReciprocalPatchEquiv R).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (infinityLocalization R)))
  rw [← Spec.map_comp]
  rfl

theorem reciprocalToFiniteAffineScheme_parameter_preimage  :
    (reciprocalToFiniteAffineScheme R) ⁻¹ᵁ (PrimeSpectrum.basicOpen (sElement R)) =
      PrimeSpectrum.basicOpen (Order13MixedInverseParameterPositiveReciprocalPatch.z R) := by
  rw [← reciprocalFiniteChartRingHom_Spec]
  exact reciprocalFiniteChart_parameter_preimage R

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.reciprocal_patch_parameter_basicOpen
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.reciprocalToFiniteAffineScheme_parameter_preimage

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two inverse principal-open charts have the same
literal double localization, preserving coefficient and candidate maps.
Named downstream consumer: compatibility of the inverse atlas morphisms
into the actual original curve. No gluing is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open Order13MixedInverseParameterPolynomialIdentities (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R]

def parameterLocalizationEquivOverCandidate :
    parameterLocalization R ≃ₐ[candidateAlgebra R] ordinaryParameterLocalization R :=
  { (parameterLocalizationEquiv R).toRingEquiv with
    commutes' := localizedInclusion_algebraMap R }

scoped instance candidateOrdinaryLocalization :
    IsLocalization.Away (sElement R) (ordinaryParameterLocalization R) :=
  IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (sElement R))
    (parameterLocalizationEquivOverCandidate R)

scoped instance candidateOrdinaryBaseTower :
    IsScalarTower R (candidateAlgebra R) (ordinaryParameterLocalization R) :=
  IsScalarTower.of_algebraMap_eq fun c => ((inclusion R).commutes c).symm

abbrev infinityParameterLocalization := Localization.Away (infinityS R)

scoped instance infinityParameterDoubleLocalization :
    IsLocalization.Away (sElement R * infinityPatchElement R) (infinityParameterLocalization R) := by
  let : IsLocalization.Away (algebraMap (candidateAlgebra R) (infinityLocalization R) (sElement R))
      (infinityParameterLocalization R) := by
    change IsLocalization.Away (infinityS R) (Localization.Away (infinityS R))
    infer_instance
  exact IsLocalization.Away.mul (infinityLocalization R) (infinityParameterLocalization R)
    (infinityPatchElement R) (sElement R)

scoped instance ordinaryInfinityDoubleLocalization :
    IsLocalization.Away (sElement R * infinityPatchElement R) (ordinaryInfinityLocalization R) := by
  let : IsLocalization.Away (algebraMap (candidateAlgebra R) (ordinaryParameterLocalization R)
      (infinityPatchElement R)) (ordinaryInfinityLocalization R) := by
    change IsLocalization.Away (inclusion R (infinityPatchElement R))
      (Localization.Away (inclusion R (infinityPatchElement R)))
    infer_instance
  exact IsLocalization.Away.mul' (ordinaryParameterLocalization R) (ordinaryInfinityLocalization R)
    (sElement R) (infinityPatchElement R)

scoped instance candidateOrdinaryInfinityBaseTower :
    IsScalarTower R (candidateAlgebra R) (ordinaryInfinityLocalization R) :=
  IsScalarTower.to₁₂₄ R (candidateAlgebra R) (ordinaryParameterLocalization R)
    (ordinaryInfinityLocalization R)

def commonLocalizationEquiv :
    infinityParameterLocalization R ≃ₐ[R] ordinaryInfinityLocalization R :=
  (IsLocalization.algEquiv (Submonoid.powers (sElement R * infinityPatchElement R))
    (infinityParameterLocalization R) (ordinaryInfinityLocalization R)).restrictScalars R

theorem commonLocalizationEquiv_candidate (c : candidateAlgebra R) :
    commonLocalizationEquiv R (algebraMap (candidateAlgebra R) (infinityParameterLocalization R) c) =
      algebraMap (candidateAlgebra R) (ordinaryInfinityLocalization R) c := by
  exact (IsLocalization.algEquiv (Submonoid.powers (sElement R * infinityPatchElement R))
    (infinityParameterLocalization R) (ordinaryInfinityLocalization R)).commutes c

theorem commonLocalizationEquiv_infinity (c : infinityLocalization R) :
    commonLocalizationEquiv R (algebraMap (infinityLocalization R) (infinityParameterLocalization R) c) =
      infinityLocalizedInclusion R c := by
  have hh : (commonLocalizationEquiv R).toAlgHom.comp
      (IsScalarTower.toAlgHom R (infinityLocalization R) (infinityParameterLocalization R)) =
      infinityLocalizedInclusion R := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (infinityPatchElement R))
    apply RingHom.ext
    intro c
    change commonLocalizationEquiv R
      (algebraMap (infinityLocalization R) (infinityParameterLocalization R)
        (algebraMap (candidateAlgebra R) (infinityLocalization R) c)) =
      infinityLocalizedInclusion R (algebraMap (candidateAlgebra R) (infinityLocalization R) c)
    have hc : algebraMap (candidateAlgebra R) (infinityParameterLocalization R) c =
        algebraMap (infinityLocalization R) (infinityParameterLocalization R)
          (algebraMap (candidateAlgebra R) (infinityLocalization R) c) := rfl
    rw [← hc, commonLocalizationEquiv_candidate R c,
      infinityLocalizedInclusion_algebraMap R c]
    rfl
  exact DFunLike.congr_fun hh c

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.commonLocalizationEquiv
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.commonLocalizationEquiv_infinity

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal common affine chart is the categorical
intersection of the ordinary parameter and positive reciprocal maps into the inverse finite model.
Named downstream consumer: compatibility and global inverse-chart gluing.
No global comparison is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedInverseParameterPolynomialIdentities (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R] [IsDomain R]

def ordinaryInfinityChartMap : Spec (.of (ordinaryInfinityLocalization R)) ⟶
    Spec (.of (ordinaryParameterLocalization R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ordinaryParameterLocalization R) (ordinaryInfinityLocalization R)))

def ordinaryInfinityToReciprocalPatch  :
    Spec (.of (ordinaryInfinityLocalization R)) ⟶
      Spec (.of (Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R)) :=
  Spec.map (CommRingCat.ofHom
    ((infinityLocalizedInclusion R).comp (recoveredReciprocalPatchEquiv R).toAlgHom).toRingHom)

omit [IsDomain R] in
theorem ordinaryParameterToFiniteAffineScheme_eq_Spec :
    ordinaryParameterToFiniteAffineScheme R = Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (parameterLocalizationEquiv R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (parameterLocalization R))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact localizedInclusion_algebraMap R

theorem ordinaryInfinityChartMap_comparison  :
    ordinaryInfinityChartMap R ≫ ordinaryParameterToFiniteAffineScheme R =
      ordinaryInfinityToReciprocalPatch R ≫ reciprocalToFiniteAffineScheme R := by
  rw [ordinaryParameterToFiniteAffineScheme_eq_Spec, ← reciprocalFiniteChartRingHom_Spec]
  change Spec.map (CommRingCat.ofHom (algebraMap (ordinaryParameterLocalization R) (ordinaryInfinityLocalization R))) ≫
    Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) =
    Spec.map (CommRingCat.ofHom
      ((infinityLocalizedInclusion R).comp (recoveredReciprocalPatchEquiv R).toAlgHom).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (reciprocalFiniteChartRingHom R))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change ordinaryInfinityMap R (inclusion R c) =
    infinityLocalizedInclusion R ((recoveredReciprocalPatchEquiv R)
      ((recoveredReciprocalPatchEquiv R).symm
        (algebraMap (candidateAlgebra R) (infinityLocalization R) c)))
  rw [AlgEquiv.apply_symm_apply,infinityLocalizedInclusion_algebraMap]

theorem ordinaryInfinityChartMap_preimage  :
    letI := reciprocalToFiniteAffineScheme_isOpenImmersion R
    letI : IsOpenImmersion (ordinaryInfinityChartMap R) :=
      IsOpenImmersion.of_isLocalization (inclusion R (infinityPatchElement R))
    (ordinaryParameterToFiniteAffineScheme R) ⁻¹ᵁ
      (reciprocalToFiniteAffineScheme R).opensRange = (ordinaryInfinityChartMap R).opensRange := by
  let := reciprocalToFiniteAffineScheme_isOpenImmersion R
  let : IsOpenImmersion (ordinaryInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (inclusion R (infinityPatchElement R))
  rw [ordinaryParameterToFiniteAffineScheme_eq_Spec]
  apply TopologicalSpace.Opens.ext
  ext a
  change Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) a ∈ Set.range (reciprocalToFiniteAffineScheme R) ↔
    a ∈ Set.range (PrimeSpectrum.comap (algebraMap (ordinaryParameterLocalization R) (ordinaryInfinityLocalization R)))
  rw [reciprocalToFiniteAffineScheme_range,
    PrimeSpectrum.localization_away_comap_range (ordinaryInfinityLocalization R) (inclusion R (infinityPatchElement R))]
  change inclusion R (infinityPatchElement R) ∉ a.asIdeal ↔
    inclusion R (infinityPatchElement R) ∉ a.asIdeal
  rfl

theorem ordinaryInfinityOverlap_isPullback  :
    IsPullback (ordinaryInfinityToReciprocalPatch R) (ordinaryInfinityChartMap R)
      (reciprocalToFiniteAffineScheme R) (ordinaryParameterToFiniteAffineScheme R) := by
  let := reciprocalToFiniteAffineScheme_isOpenImmersion R
  let : IsOpenImmersion (ordinaryInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (inclusion R (infinityPatchElement R))
  exact IsOpenImmersion.isPullback _ _ _ _
    (ordinaryInfinityChartMap_comparison R) (ordinaryInfinityChartMap_preimage R)

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.ordinaryInfinityChartMap_comparison
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.ordinaryInfinityOverlap_isPullback

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual spectrum of the constructed t,p,q subalgebra,
its finite map to the affine line, and the actual ordinary chart morphism
with structural and parameter compatibility. Named downstream consumer:
identification with the complement of the positive infinity section.
No open immersion, free rank or curve-complement identification is claimed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open MazurTransfer.Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

def finiteAffineScheme : Scheme := Spec (.of (candidateAlgebra R))
def finiteAffineMap : finiteAffineScheme R ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R)))

theorem finiteAffineMap_isFinite  : IsFinite (finiteAffineMap R) := by
  letI := candidateAlgebra_finite R
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial R) (candidateAlgebra R))))
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

def ordinaryToFiniteAffineScheme : Order13DyadicMixedQuadraticCharts.ordinaryScheme R ⟶
    finiteAffineScheme R :=
  Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom)

theorem ordinaryToFiniteAffineScheme_parameter :
    ordinaryToFiniteAffineScheme R ≫ finiteAffineMap R =
    Spec.map (CommRingCat.ofHom (parameterMap R)) := by
  change Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R))) =
    Spec.map (CommRingCat.ofHom (parameterMap R))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  exact (candidateAlgebra R).val.commutes s

def finiteAffineSchemeToBase : finiteAffineScheme R ⟶ Spec (.of R) :=
  finiteAffineMap R ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))

theorem ordinaryToFiniteAffineScheme_base :
    ordinaryToFiniteAffineScheme R ≫ finiteAffineSchemeToBase R =
    ordinaryToBase R := by
  unfold finiteAffineSchemeToBase
  rw [← Category.assoc, ordinaryToFiniteAffineScheme_parameter]
  change Spec.map (CommRingCat.ofHom (parameterMap R)) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
    Spec.map (CommRingCat.ofHom (algebraMap R (ordinaryCoordinateRing R)))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simp [parameterMap]

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.finiteAffineMap_isFinite
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme_parameter
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme_base

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inclusion B[1/t] into A[1/t] is an R-algebra
isomorphism over every commutative ring, with both inverse maps constructed.
Named downstream consumer: identifying the D(t) chart of the actual
single-section affine complement. The full complement remains separate.
-/


noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticOrdinarySolutions
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

def inverseOnOrdinary : ordinaryCoordinateRing R →ₐ[R] parameterLocalization R :=
  solutionToAlgHom R (parameterLocalization R) (recoveredX R) (recoveredY R) (recovered_equation R)

theorem inverseOnOrdinary_x : inverseOnOrdinary R (xCoordinate R) = recoveredX R :=
  solutionToAlgHom_x R _ _ _ _

theorem inverseOnOrdinary_y : inverseOnOrdinary R (yCoordinate R) = recoveredY R :=
  solutionToAlgHom_y R _ _ _ _

theorem inverseOnOrdinary_t : inverseOnOrdinary R (t R) =
    algebraMap (candidateAlgebra R) (parameterLocalization R) (parameterElement R) := by
  simp only [t,map_add,map_pow,map_one,inverseOnOrdinary_x,inverseOnOrdinary_y]
  rw [recoveredY]
  ring

def inverseLocalizedInclusion : ordinaryParameterLocalization R →ₐ[R] parameterLocalization R :=
  IsLocalization.Away.liftAlgHom (t R) (f := inverseOnOrdinary R) (by
    rw [inverseOnOrdinary_t]
    exact IsLocalization.Away.algebraMap_isUnit (parameterElement R))

theorem inverseLocalizedInclusion_algebraMap (z : ordinaryCoordinateRing R) :
    inverseLocalizedInclusion R
      (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) z) =
      inverseOnOrdinary R z := by
  simp [inverseLocalizedInclusion, IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift_eq]

theorem localizedInclusion_comp_inverseOnOrdinary :
    (localizedInclusion R).comp (inverseOnOrdinary R) =
      IsScalarTower.toAlgHom R (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change localizedInclusion R (inverseOnOrdinary R (xCoordinate R)) = _
    rw [inverseOnOrdinary_x,localizedInclusion_recoveredX]
    rfl
  · change localizedInclusion R (inverseOnOrdinary R (yCoordinate R)) = _
    rw [inverseOnOrdinary_y,localizedInclusion_recoveredY]
    rfl

theorem localizedInclusion_inverseLocalizedInclusion :
    (localizedInclusion R).comp (inverseLocalizedInclusion R) =
      AlgHom.id R (ordinaryParameterLocalization R) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (t R))
  apply RingHom.ext
  intro z
  change localizedInclusion R (inverseLocalizedInclusion R
    (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) z)) = _
  rw [inverseLocalizedInclusion_algebraMap]
  exact DFunLike.congr_fun (localizedInclusion_comp_inverseOnOrdinary R) z

theorem inverseLocalizedInclusion_localizedInclusion :
    (inverseLocalizedInclusion R).comp (localizedInclusion R) =
      AlgHom.id R (parameterLocalization R) := by
  apply AlgHom.ext
  intro z
  apply localizedInclusion_injective R
  exact DFunLike.congr_fun (localizedInclusion_inverseLocalizedInclusion R) (localizedInclusion R z)

def parameterLocalizationEquiv : parameterLocalization R ≃ₐ[R] ordinaryParameterLocalization R :=
  AlgEquiv.ofAlgHom (localizedInclusion R) (inverseLocalizedInclusion R)
    (localizedInclusion_inverseLocalizedInclusion R)
    (inverseLocalizedInclusion_localizedInclusion R)

theorem parameterLocalizationEquiv_algebraMap (b : candidateAlgebra R) :
    parameterLocalizationEquiv R
      (algebraMap (candidateAlgebra R) (parameterLocalization R) b) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (b : ordinaryCoordinateRing R) :=
  localizedInclusion_algebraMap R b

theorem parameterLocalizationEquiv_symm_x :
    (parameterLocalizationEquiv R).symm
      (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (xCoordinate R)) =
      algebraMap (candidateAlgebra R) (parameterLocalization R) (pElement R) *
        IsLocalization.Away.invSelf (parameterElement R) := by
  exact (inverseLocalizedInclusion_algebraMap R _).trans (inverseOnOrdinary_x R)

theorem parameterLocalizationEquiv_symm_y :
    (parameterLocalizationEquiv R).symm
      (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R) (yCoordinate R)) =
      algebraMap (candidateAlgebra R) (parameterLocalization R) (parameterElement R) -
        recoveredX R ^ 3 - recoveredX R ^ 2 - 1 := by
  exact (inverseLocalizedInclusion_algebraMap R _).trans (inverseOnOrdinary_y R)

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.parameterLocalizationEquiv
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.parameterLocalizationEquiv_symm_x
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.parameterLocalizationEquiv_symm_y

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inclusion of the single-section coordinate
algebra is a ring epimorphism over every commutative coefficient ring. Its spectrum map is
therefore a monomorphism and injective. Named downstream consumer: gluing
the ordinary and reciprocal chart maps into the affine complement.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

theorem ringHom_eq_of_agree_on_candidate 
    {T : Type u} [CommRing T] (φ ψ : ordinaryCoordinateRing R →+* T)
    (h : ∀ b : candidateAlgebra R, φ b = ψ b) : φ = ψ := by
  have ht : φ (t R) = ψ (t R) := by
    simpa only [parameterElement_coe] using h (parameterElement R)
  have hp : φ (p R) = ψ (p R) := h (pElement R)
  have hq : φ (q R) = ψ (q R) := h (qElement R)
  have hmul : φ (xCoordinate R) * φ (t R) = ψ (xCoordinate R) * φ (t R) := by
    simpa only [p,map_mul,ht] using hp
  have hmulq : φ (xCoordinate R) * (φ (xCoordinate R) * φ (t R) + 1) =
      ψ (xCoordinate R) * (φ (xCoordinate R) * φ (t R) + 1) := by
    have hq' : φ (xCoordinate R) * (φ (p R) + 1) =
        ψ (xCoordinate R) * (ψ (p R) + 1) := by
      simpa only [q,map_mul,map_add,map_one] using hq
    rw [← hp] at hq'
    simpa only [p,map_mul] using hq'
  have hx : φ (xCoordinate R) = ψ (xCoordinate R) := by
    linear_combination hmulq - φ (xCoordinate R) * hmul
  have hy : φ (yCoordinate R) = ψ (yCoordinate R) := by
    simp only [t,map_add,map_pow,map_one,hx] at ht
    exact add_right_cancel ht
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      have hr := h (algebraMap (Polynomial R) (candidateAlgebra R) (C r))
      change φ (aeval (t R) (C r)) = ψ (aeval (t R) (C r)) at hr
      simpa only [aeval_C, RingHom.comp_apply, AdjoinRoot.algebraMap_eq', Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using hr
    · exact hx
  · exact hy

theorem candidateInclusion_epi  :
    Epi (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom) := by
  constructor
  intro T φ ψ h
  apply CommRingCat.hom_ext
  apply ringHom_eq_of_agree_on_candidate R φ.hom ψ.hom
  intro b
  exact ConcreteCategory.congr_hom h b

theorem ordinaryToFiniteAffineScheme_mono  :
    Mono (ordinaryToFiniteAffineScheme R) := by
  let := candidateInclusion_epi R
  change Mono (Scheme.Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom).op)
  infer_instance

theorem ordinaryToFiniteAffineScheme_injective  :
    Function.Injective (ordinaryToFiniteAffineScheme R) := by
  let := ordinaryToFiniteAffineScheme_mono R
  exact (ordinaryToFiniteAffineScheme R).injective

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ringHom_eq_of_agree_on_candidate
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme_injective

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the localized actual inclusion after p+1 is inverted,
with recovered x=q/(p+1) and y=t-x^3-x^2-1 satisfying the mixed equation.
Named downstream consumer: the ordinary-chart part of the actual
single-section affine complement. No full complement is asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

def inversionElement : candidateAlgebra R := pElement R + 1
abbrev adjustedLocalization := Localization.Away (inversionElement R)
abbrev ordinaryAdjustedLocalization := Localization.Away (p R + 1)

theorem inversionElement_coe : (inversionElement R : ordinaryCoordinateRing R) = p R + 1 := rfl

theorem inclusion_inversion : inclusion R (inversionElement R) = p R + 1 := rfl

def adjustedLocalizedInclusion : adjustedLocalization R →ₐ[R] ordinaryAdjustedLocalization R := by
  letI : IsLocalization.Away (inclusion R (inversionElement R))
      (ordinaryAdjustedLocalization R) := by
    rw [inclusion_inversion]
    infer_instance
  exact IsLocalization.Away.mapₐ _ _ (inclusion R) (inversionElement R)

theorem adjustedLocalizedInclusion_algebraMap (b : candidateAlgebra R) :
    adjustedLocalizedInclusion R (algebraMap (candidateAlgebra R) (adjustedLocalization R) b) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (b : ordinaryCoordinateRing R) := by
  simp [adjustedLocalizedInclusion, IsLocalization.Away.mapₐ, IsLocalization.Away.map,
    IsLocalization.map_eq, inclusion]

theorem adjustedLocalizedInclusion_injective : Function.Injective (adjustedLocalizedInclusion R) := by
  letI : IsLocalization.Away (inclusion R (inversionElement R))
      (ordinaryAdjustedLocalization R) := by
    rw [inclusion_inversion]
    infer_instance
  exact IsLocalization.Away.mapₐ_injective_of_injective (inversionElement R)
    (f := inclusion R) Subtype.val_injective

theorem adjustedLocalizedInclusion_invSelf :
    adjustedLocalizedInclusion R (IsLocalization.Away.invSelf (inversionElement R)) =
      IsLocalization.Away.invSelf ((p R + 1)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit ((p R + 1))
    (S := ordinaryAdjustedLocalization R)
  apply hu.mul_right_inj.mp
  calc
    _ = adjustedLocalizedInclusion R
        (algebraMap (candidateAlgebra R) (adjustedLocalization R) (inversionElement R) *
          IsLocalization.Away.invSelf (inversionElement R)) := by
      rw [map_mul, adjustedLocalizedInclusion_algebraMap, inversionElement_coe]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf ((p R + 1))).symm

def adjustedRecoveredX : adjustedLocalization R :=
  algebraMap (candidateAlgebra R) (adjustedLocalization R) (qElement R) *
    IsLocalization.Away.invSelf (inversionElement R)

def adjustedRecoveredY : adjustedLocalization R :=
  algebraMap (candidateAlgebra R) (adjustedLocalization R) (parameterElement R) -
    adjustedRecoveredX R ^ 3 - adjustedRecoveredX R ^ 2 - 1

theorem adjustedLocalizedInclusion_adjustedRecoveredX :
    adjustedLocalizedInclusion R (adjustedRecoveredX R) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (xCoordinate R) := by
  rw [adjustedRecoveredX, map_mul, adjustedLocalizedInclusion_algebraMap, adjustedLocalizedInclusion_invSelf]
  change algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (xCoordinate R * (p R + 1)) * _ = _
  rw [map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

theorem adjustedLocalizedInclusion_adjustedRecoveredY :
    adjustedLocalizedInclusion R (adjustedRecoveredY R) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (yCoordinate R) := by
  rw [adjustedRecoveredY, map_sub, map_sub, map_sub, map_pow, map_pow, map_one,
    adjustedLocalizedInclusion_algebraMap, parameterElement_coe, adjustedLocalizedInclusion_adjustedRecoveredX]
  change algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (t R) -
    algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (xCoordinate R) ^ 3 -
    algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (xCoordinate R) ^ 2 - 1 = _
  simp only [t,map_add,map_pow,map_one]
  ring

theorem adjusted_recovered_equation : adjustedRecoveredY R ^ 2 +
    (adjustedRecoveredX R ^ 3 + adjustedRecoveredX R ^ 2 + 1) * adjustedRecoveredY R -
    adjustedRecoveredX R * (adjustedRecoveredX R + 1) = 0 := by
  apply adjustedLocalizedInclusion_injective R
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero,
    adjustedLocalizedInclusion_adjustedRecoveredX, adjustedLocalizedInclusion_adjustedRecoveredY]
  have h := congrArg
    (algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R)) (ordinary_relation R)
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero] at h
  exact h

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.adjustedLocalizedInclusion_injective
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.adjusted_recovered_equation

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inclusion B[1/(p+1)] into A[1/(p+1)] is an R-algebra
isomorphism over every commutative ring, with both inverse maps constructed.
Named downstream consumer: identifying the D(p+1) chart of the actual
single-section affine complement. The full complement remains separate.
-/


noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticOrdinarySolutions
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

def inverseOnAdjustedOrdinary : ordinaryCoordinateRing R →ₐ[R] adjustedLocalization R :=
  solutionToAlgHom R (adjustedLocalization R) (adjustedRecoveredX R) (adjustedRecoveredY R) (adjusted_recovered_equation R)

theorem inverseOnAdjustedOrdinary_x : inverseOnAdjustedOrdinary R (xCoordinate R) = adjustedRecoveredX R :=
  solutionToAlgHom_x R _ _ _ _

theorem inverseOnAdjustedOrdinary_y : inverseOnAdjustedOrdinary R (yCoordinate R) = adjustedRecoveredY R :=
  solutionToAlgHom_y R _ _ _ _

theorem inverseOnAdjustedOrdinary_t : inverseOnAdjustedOrdinary R (t R) =
    algebraMap (candidateAlgebra R) (adjustedLocalization R) (parameterElement R) := by
  simp only [t,map_add,map_pow,map_one,inverseOnAdjustedOrdinary_x,inverseOnAdjustedOrdinary_y]
  rw [adjustedRecoveredY]
  ring

theorem adjustedLocalizedInclusion_comp_inverseOnAdjustedOrdinary :
    (adjustedLocalizedInclusion R).comp (inverseOnAdjustedOrdinary R) =
      IsScalarTower.toAlgHom R (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change adjustedLocalizedInclusion R (inverseOnAdjustedOrdinary R (xCoordinate R)) = _
    rw [inverseOnAdjustedOrdinary_x,adjustedLocalizedInclusion_adjustedRecoveredX]
    rfl
  · change adjustedLocalizedInclusion R (inverseOnAdjustedOrdinary R (yCoordinate R)) = _
    rw [inverseOnAdjustedOrdinary_y,adjustedLocalizedInclusion_adjustedRecoveredY]
    rfl

theorem inverseOnAdjustedOrdinary_inversion : inverseOnAdjustedOrdinary R (p R + 1) =
    algebraMap (candidateAlgebra R) (adjustedLocalization R) (inversionElement R) := by
  apply adjustedLocalizedInclusion_injective R
  rw [adjustedLocalizedInclusion_algebraMap,inversionElement_coe]
  exact DFunLike.congr_fun (adjustedLocalizedInclusion_comp_inverseOnAdjustedOrdinary R) (p R + 1)

def inverseAdjustedLocalizedInclusion : ordinaryAdjustedLocalization R →ₐ[R] adjustedLocalization R :=
  IsLocalization.Away.liftAlgHom (p R + 1) (f := inverseOnAdjustedOrdinary R) (by
    rw [inverseOnAdjustedOrdinary_inversion]
    exact IsLocalization.Away.algebraMap_isUnit (inversionElement R))

theorem inverseAdjustedLocalizedInclusion_algebraMap (z : ordinaryCoordinateRing R) :
    inverseAdjustedLocalizedInclusion R
      (algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) z) =
      inverseOnAdjustedOrdinary R z := by
  simp [inverseAdjustedLocalizedInclusion, IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift_eq]

theorem adjustedLocalizedInclusion_inverseAdjustedLocalizedInclusion :
    (adjustedLocalizedInclusion R).comp (inverseAdjustedLocalizedInclusion R) =
      AlgHom.id R (ordinaryAdjustedLocalization R) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (p R + 1))
  apply RingHom.ext
  intro z
  change adjustedLocalizedInclusion R (inverseAdjustedLocalizedInclusion R
    (algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) z)) = _
  rw [inverseAdjustedLocalizedInclusion_algebraMap]
  exact DFunLike.congr_fun (adjustedLocalizedInclusion_comp_inverseOnAdjustedOrdinary R) z

theorem inverseAdjustedLocalizedInclusion_adjustedLocalizedInclusion :
    (inverseAdjustedLocalizedInclusion R).comp (adjustedLocalizedInclusion R) =
      AlgHom.id R (adjustedLocalization R) := by
  apply AlgHom.ext
  intro z
  apply adjustedLocalizedInclusion_injective R
  exact DFunLike.congr_fun (adjustedLocalizedInclusion_inverseAdjustedLocalizedInclusion R) (adjustedLocalizedInclusion R z)

def adjustedLocalizationEquiv : adjustedLocalization R ≃ₐ[R] ordinaryAdjustedLocalization R :=
  AlgEquiv.ofAlgHom (adjustedLocalizedInclusion R) (inverseAdjustedLocalizedInclusion R)
    (adjustedLocalizedInclusion_inverseAdjustedLocalizedInclusion R)
    (inverseAdjustedLocalizedInclusion_adjustedLocalizedInclusion R)

theorem adjustedLocalizationEquiv_algebraMap (b : candidateAlgebra R) :
    adjustedLocalizationEquiv R
      (algebraMap (candidateAlgebra R) (adjustedLocalization R) b) =
      algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (b : ordinaryCoordinateRing R) :=
  adjustedLocalizedInclusion_algebraMap R b

theorem adjustedLocalizationEquiv_symm_x :
    (adjustedLocalizationEquiv R).symm
      (algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (xCoordinate R)) =
      algebraMap (candidateAlgebra R) (adjustedLocalization R) (qElement R) *
        IsLocalization.Away.invSelf (inversionElement R) := by
  exact (inverseAdjustedLocalizedInclusion_algebraMap R _).trans (inverseOnAdjustedOrdinary_x R)

theorem adjustedLocalizationEquiv_symm_y :
    (adjustedLocalizationEquiv R).symm
      (algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R) (yCoordinate R)) =
      algebraMap (candidateAlgebra R) (adjustedLocalization R) (parameterElement R) -
        adjustedRecoveredX R ^ 3 - adjustedRecoveredX R ^ 2 - 1 := by
  exact (inverseAdjustedLocalizedInclusion_algebraMap R _).trans (inverseOnAdjustedOrdinary_y R)

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.adjustedLocalizationEquiv
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.adjustedLocalizationEquiv_symm_x
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.adjustedLocalizationEquiv_symm_y

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual ordinary chart maps by an open immersion into
the single-section finite coordinate scheme over every commutative coefficient ring.
Named downstream consumer: gluing with the reciprocal patch into the exact
positive infinity complement. No global affine identification is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R]

def ordinaryParameterChartMap : Spec (.of (ordinaryParameterLocalization R)) ⟶
    Order13DyadicMixedQuadraticCharts.ordinaryScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)))

def candidateParameterChartMap : Spec (.of (parameterLocalization R)) ⟶ finiteAffineScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (parameterLocalization R)))

def parameterChartSchemeIso : Spec (.of (ordinaryParameterLocalization R)) ≅
    Spec (.of (parameterLocalization R)) :=
  Scheme.Spec.mapIso (parameterLocalizationEquiv R).toRingEquiv.toCommRingCatIso.op

theorem ordinaryParameterChartMap_comparison :
    ordinaryParameterChartMap R ≫ ordinaryToFiniteAffineScheme R =
      (parameterChartSchemeIso R).hom ≫ candidateParameterChartMap R := by
  change Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R))) ≫
    Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom) =
    Spec.map (CommRingCat.ofHom (parameterLocalizationEquiv R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (parameterLocalization R)))
  rw [← Spec.map_comp,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  exact (parameterLocalizationEquiv_algebraMap R b).symm

theorem ordinaryParameterChartMap_composite_isOpenImmersion :
    IsOpenImmersion (ordinaryParameterChartMap R ≫ ordinaryToFiniteAffineScheme R) := by
  rw [ordinaryParameterChartMap_comparison]
  let : IsOpenImmersion (candidateParameterChartMap R) :=
    IsOpenImmersion.of_isLocalization (parameterElement R)
  infer_instance

def ordinaryAdjustedChartMap : Spec (.of (ordinaryAdjustedLocalization R)) ⟶
    Order13DyadicMixedQuadraticCharts.ordinaryScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R)))

def candidateAdjustedChartMap : Spec (.of (adjustedLocalization R)) ⟶ finiteAffineScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (adjustedLocalization R)))

def adjustedChartSchemeIso : Spec (.of (ordinaryAdjustedLocalization R)) ≅
    Spec (.of (adjustedLocalization R)) :=
  Scheme.Spec.mapIso (adjustedLocalizationEquiv R).toRingEquiv.toCommRingCatIso.op

theorem ordinaryAdjustedChartMap_comparison :
    ordinaryAdjustedChartMap R ≫ ordinaryToFiniteAffineScheme R =
      (adjustedChartSchemeIso R).hom ≫ candidateAdjustedChartMap R := by
  change Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R))) ≫
    Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom) =
    Spec.map (CommRingCat.ofHom (adjustedLocalizationEquiv R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (adjustedLocalization R)))
  rw [← Spec.map_comp,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  exact (adjustedLocalizationEquiv_algebraMap R b).symm

theorem ordinaryAdjustedChartMap_composite_isOpenImmersion :
    IsOpenImmersion (ordinaryAdjustedChartMap R ≫ ordinaryToFiniteAffineScheme R) := by
  rw [ordinaryAdjustedChartMap_comparison]
  let : IsOpenImmersion (candidateAdjustedChartMap R) :=
    IsOpenImmersion.of_isLocalization (inversionElement R)
  infer_instance

theorem ordinaryToFiniteAffineScheme_isOpenImmersion  :
    IsOpenImmersion (ordinaryToFiniteAffineScheme R) := by
  apply IsOpenImmersion.of_forall_source_exists _
    (ordinaryToFiniteAffineScheme_injective R)
  intro a
  have ha : a ∈ PrimeSpectrum.basicOpen (t R) ⊔ PrimeSpectrum.basicOpen (p R + 1) := by
    rw [ordinary_two_principal_open_cover R]
    trivial
  rcases ha with ha | ha
  · let : IsOpenImmersion (ordinaryParameterChartMap R) :=
      IsOpenImmersion.of_isLocalization (t R)
    refine ⟨_,ordinaryParameterChartMap R,inferInstance,?_,
      ordinaryParameterChartMap_composite_isOpenImmersion R⟩
    change a ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)))
    rw [PrimeSpectrum.localization_away_comap_range (ordinaryParameterLocalization R) (t R)]
    exact ha
  · let : IsOpenImmersion (ordinaryAdjustedChartMap R) :=
      IsOpenImmersion.of_isLocalization (p R + 1)
    refine ⟨_,ordinaryAdjustedChartMap R,inferInstance,?_,
      ordinaryAdjustedChartMap_composite_isOpenImmersion R⟩
    change a ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R)))
    rw [PrimeSpectrum.localization_away_comap_range (ordinaryAdjustedLocalization R) (p R + 1)]
    exact ha

theorem ordinaryParameterChartMap_composite_range :
    Set.range (ordinaryParameterChartMap R ≫ ordinaryToFiniteAffineScheme R) =
      (PrimeSpectrum.basicOpen (parameterElement R) : Set (PrimeSpectrum (candidateAlgebra R))) := by
  rw [ordinaryParameterChartMap_comparison]
  let : IsOpenImmersion (candidateParameterChartMap R) :=
    IsOpenImmersion.of_isLocalization (parameterElement R)
  have he := Scheme.Hom.opensRange_comp_of_isIso
    (parameterChartSchemeIso R).hom (candidateParameterChartMap R)
  exact (congrArg (fun U : (finiteAffineScheme R).Opens => (U : Set (finiteAffineScheme R))) he).trans
    (PrimeSpectrum.localization_away_comap_range (parameterLocalization R) (parameterElement R))

theorem ordinaryAdjustedChartMap_composite_range :
    Set.range (ordinaryAdjustedChartMap R ≫ ordinaryToFiniteAffineScheme R) =
      (PrimeSpectrum.basicOpen (inversionElement R) : Set (PrimeSpectrum (candidateAlgebra R))) := by
  rw [ordinaryAdjustedChartMap_comparison]
  let : IsOpenImmersion (candidateAdjustedChartMap R) :=
    IsOpenImmersion.of_isLocalization (inversionElement R)
  have he := Scheme.Hom.opensRange_comp_of_isIso
    (adjustedChartSchemeIso R).hom (candidateAdjustedChartMap R)
  exact (congrArg (fun U : (finiteAffineScheme R).Opens => (U : Set (finiteAffineScheme R))) he).trans
    (PrimeSpectrum.localization_away_comap_range (adjustedLocalization R) (inversionElement R))

theorem ordinaryToFiniteAffineScheme_range  :
    Set.range (ordinaryToFiniteAffineScheme R) =
      (PrimeSpectrum.basicOpen (parameterElement R) ⊔
        PrimeSpectrum.basicOpen (inversionElement R) : Set (PrimeSpectrum (candidateAlgebra R))) := by
  change Set.range (ordinaryToFiniteAffineScheme R) =
    (PrimeSpectrum.basicOpen (parameterElement R) : Set (PrimeSpectrum (candidateAlgebra R))) ∪
      (PrimeSpectrum.basicOpen (inversionElement R) : Set (PrimeSpectrum (candidateAlgebra R)))
  rw [← ordinaryParameterChartMap_composite_range,← ordinaryAdjustedChartMap_composite_range]
  ext b
  constructor
  · rintro ⟨a,rfl⟩
    have ha : a ∈ PrimeSpectrum.basicOpen (t R) ⊔ PrimeSpectrum.basicOpen (p R + 1) := by
      rw [ordinary_two_principal_open_cover R]
      trivial
    rcases ha with ha | ha
    · have hr : a ∈ Set.range (ordinaryParameterChartMap R) := by
        change a ∈ Set.range (PrimeSpectrum.comap
          (algebraMap (ordinaryCoordinateRing R) (ordinaryParameterLocalization R)))
        rw [PrimeSpectrum.localization_away_comap_range (ordinaryParameterLocalization R) (t R)]
        exact ha
      obtain ⟨a',rfl⟩ := hr
      exact Or.inl ⟨a',rfl⟩
    · have hr : a ∈ Set.range (ordinaryAdjustedChartMap R) := by
        change a ∈ Set.range (PrimeSpectrum.comap
          (algebraMap (ordinaryCoordinateRing R) (ordinaryAdjustedLocalization R)))
        rw [PrimeSpectrum.localization_away_comap_range (ordinaryAdjustedLocalization R) (p R + 1)]
        exact ha
      obtain ⟨a',rfl⟩ := hr
      exact Or.inr ⟨a',rfl⟩
  · rintro (⟨a',rfl⟩ | ⟨a',rfl⟩)
    · exact ⟨ordinaryParameterChartMap R a',rfl⟩
    · exact ⟨ordinaryAdjustedChartMap R a',rfl⟩

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme_isOpenImmersion
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme_range

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual two-member open cover of the finite coordinate
scheme by the ordinary curve chart and the retained reciprocal patch.
Named downstream consumer: gluing this atlas to the exact section complement.
The global comparison and finite-map data are separate obligations.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry
variable (R : Type u) [CommRing R] [IsDomain R]

def candidateInfinityChartMap : Spec (.of (infinityLocalization R)) ⟶ finiteAffineScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (infinityLocalization R)))

def reciprocalFiniteChartIso  :
    Spec (.of (Order13MixedSingleSectionReciprocalPatch.PatchRing R)) ≅
      Spec (.of (infinityLocalization R)) :=
  Scheme.Spec.mapIso (recoveredReciprocalPatchEquiv R).symm.toRingEquiv.toCommRingCatIso.op

def reciprocalToFiniteAffineScheme  :
    Spec (.of (Order13MixedSingleSectionReciprocalPatch.PatchRing R)) ⟶ finiteAffineScheme R :=
  (reciprocalFiniteChartIso R).hom ≫ candidateInfinityChartMap R

theorem reciprocalToFiniteAffineScheme_isOpenImmersion  :
    IsOpenImmersion (reciprocalToFiniteAffineScheme R) := by
  let : IsOpenImmersion (candidateInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (infinityPatchElement R)
  unfold reciprocalToFiniteAffineScheme
  infer_instance

theorem reciprocalToFiniteAffineScheme_range  :
    Set.range (reciprocalToFiniteAffineScheme R) =
      (PrimeSpectrum.basicOpen (infinityPatchElement R) : Set (PrimeSpectrum (candidateAlgebra R))) := by
  let : IsOpenImmersion (candidateInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (infinityPatchElement R)
  have he := Scheme.Hom.opensRange_comp_of_isIso
    (reciprocalFiniteChartIso R).hom (candidateInfinityChartMap R)
  exact (congrArg (fun U : (finiteAffineScheme R).Opens => (U : Set (finiteAffineScheme R))) he).trans
    (PrimeSpectrum.localization_away_comap_range (infinityLocalization R) (infinityPatchElement R))

theorem finiteScheme_two_chart_range_cover  :
    Set.range (ordinaryToFiniteAffineScheme R) ∪
      Set.range (reciprocalToFiniteAffineScheme R) = Set.univ := by
  rw [ordinaryToFiniteAffineScheme_range R ,
    reciprocalToFiniteAffineScheme_range]
  change ((PrimeSpectrum.basicOpen (parameterElement R) : Set (PrimeSpectrum (candidateAlgebra R))) ∪
    (PrimeSpectrum.basicOpen (inversionElement R) : Set (PrimeSpectrum (candidateAlgebra R)))) ∪
      (PrimeSpectrum.basicOpen (infinityPatchElement R) : Set (PrimeSpectrum (candidateAlgebra R))) = Set.univ
  have he := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum (candidateAlgebra R)) =>
    (U : Set (PrimeSpectrum (candidateAlgebra R))))
      (candidate_three_principal_open_cover R )
  simpa only [inversionElement,TopologicalSpace.Opens.coe_sup,TopologicalSpace.Opens.coe_top,Set.union_assoc] using he

def finiteSchemeChart (b : Bool) : Scheme.{u} :=
  if b then Order13DyadicMixedQuadraticCharts.ordinaryScheme R
  else Spec (.of (Order13MixedSingleSectionReciprocalPatch.PatchRing R))

def finiteSchemeChartMap  :
    (b : Bool) → finiteSchemeChart R b ⟶ finiteAffineScheme R
  | true => ordinaryToFiniteAffineScheme R
  | false => reciprocalToFiniteAffineScheme R

theorem finiteSchemeChartMap_isOpenImmersion  (b : Bool) :
    IsOpenImmersion (finiteSchemeChartMap R b) := by
  cases b with
  | false => exact reciprocalToFiniteAffineScheme_isOpenImmersion R
  | true => exact ordinaryToFiniteAffineScheme_isOpenImmersion R 

def finiteSchemeOpenCover  : (finiteAffineScheme R).OpenCover where
  I₀ := Bool
  X := finiteSchemeChart R
  f := finiteSchemeChartMap R
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro a
      have ha : a ∈ Set.range (ordinaryToFiniteAffineScheme R) ∪
          Set.range (reciprocalToFiniteAffineScheme R) := by
        rw [finiteScheme_two_chart_range_cover]
        trivial
      rcases ha with ha | ha
      · exact ⟨true,ha⟩
      · exact ⟨false,ha⟩
    · exact finiteSchemeChartMap_isOpenImmersion R

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.reciprocalToFiniteAffineScheme_range
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.finiteSchemeOpenCover

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal common affine chart is the categorical
intersection of the ordinary and reciprocal maps into the finite model.
Named downstream consumer: compatibility and global section-complement gluing.
No global comparison is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedSingleSectionPolynomialIdentities
variable (R : Type u) [CommRing R] [IsDomain R]

def ordinaryInfinityChartMap : Spec (.of (ordinaryInfinityLocalization R)) ⟶
    Order13DyadicMixedQuadraticCharts.ordinaryScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R)))

def ordinaryInfinityToReciprocalPatch  :
    Spec (.of (ordinaryInfinityLocalization R)) ⟶
      Spec (.of (Order13MixedSingleSectionReciprocalPatch.PatchRing R)) :=
  Spec.map (CommRingCat.ofHom
    ((infinityLocalizedInclusion R).comp (recoveredReciprocalPatchEquiv R).toAlgHom).toRingHom)

theorem ordinaryInfinityChartMap_comparison  :
    ordinaryInfinityChartMap R ≫ ordinaryToFiniteAffineScheme R =
      ordinaryInfinityToReciprocalPatch R ≫ reciprocalToFiniteAffineScheme R := by
  change Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R))) ≫
    Spec.map (CommRingCat.ofHom (candidateAlgebra R).val.toRingHom) =
    Spec.map (CommRingCat.ofHom
      ((infinityLocalizedInclusion R).comp (recoveredReciprocalPatchEquiv R).toAlgHom).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (recoveredReciprocalPatchEquiv R).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (infinityLocalization R))))
  rw [← Category.assoc,← Spec.map_comp,← Spec.map_comp,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  change algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R) (b : ordinaryCoordinateRing R) =
    infinityLocalizedInclusion R ((recoveredReciprocalPatchEquiv R)
      ((recoveredReciprocalPatchEquiv R).symm
        (algebraMap (candidateAlgebra R) (infinityLocalization R) b)))
  rw [AlgEquiv.apply_symm_apply,infinityLocalizedInclusion_algebraMap]

theorem ordinaryInfinityChartMap_preimage  :
    letI := reciprocalToFiniteAffineScheme_isOpenImmersion R
    letI : IsOpenImmersion (ordinaryInfinityChartMap R) :=
      IsOpenImmersion.of_isLocalization (p R * (p R + t R))
    (ordinaryToFiniteAffineScheme R) ⁻¹ᵁ
      (reciprocalToFiniteAffineScheme R).opensRange = (ordinaryInfinityChartMap R).opensRange := by
  let := reciprocalToFiniteAffineScheme_isOpenImmersion R
  let : IsOpenImmersion (ordinaryInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (p R * (p R + t R))
  apply TopologicalSpace.Opens.ext
  ext a
  change ordinaryToFiniteAffineScheme R a ∈ Set.range (reciprocalToFiniteAffineScheme R) ↔
    a ∈ Set.range (PrimeSpectrum.comap (algebraMap (ordinaryCoordinateRing R) (ordinaryInfinityLocalization R)))
  rw [reciprocalToFiniteAffineScheme_range,
    PrimeSpectrum.localization_away_comap_range (ordinaryInfinityLocalization R) (p R * (p R + t R))]
  change (infinityPatchElement R : ordinaryCoordinateRing R) ∉ a.asIdeal ↔ p R * (p R + t R) ∉ a.asIdeal
  have he : (infinityPatchElement R : ordinaryCoordinateRing R) = p R * (p R + t R) :=
    inclusion_infinityPatchElement R
  rw [he]

theorem ordinaryInfinityOverlap_isPullback  :
    IsPullback (ordinaryInfinityToReciprocalPatch R) (ordinaryInfinityChartMap R)
      (reciprocalToFiniteAffineScheme R) (ordinaryToFiniteAffineScheme R) := by
  let := reciprocalToFiniteAffineScheme_isOpenImmersion R
  let : IsOpenImmersion (ordinaryInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (p R * (p R + t R))
  exact IsOpenImmersion.isPullback _ _ _ _
    (ordinaryInfinityChartMap_comparison R) (ordinaryInfinityChartMap_preimage R)

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinaryInfinityChartMap_comparison
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.ordinaryInfinityOverlap_isPullback

end


