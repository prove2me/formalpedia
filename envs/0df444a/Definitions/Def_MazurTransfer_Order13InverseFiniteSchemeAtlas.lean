-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseFiniteSchemeAtlas
-- name    : MazurTransfer_Order13InverseFiniteSchemeAtlas
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:08:15.553569+00:00
-- url     : https://prove2.me/theorems/878782e8-8423-434d-a93c-2e0ae4dd843c
-- title:
--   The actual two-chart atlas of the inverse finite coordinate scheme
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible, and let $B=R[S][a,b]$ be the actual inverse-parameter coordinate algebra. The ordinary parameter localization and the positive reciprocal patch give the specified two-member open cover of $\operatorname{Spec}B$. Their images are the literal principal opens $D(s)$ and $D((1-2s-2b-4a^2)(1-2s-2b))$. The constructor records both chart maps and the actual open cover. It supplies the domain atlas for gluing the inverse finite chart to the order-thirteen curve.
-- source:
--   Fifteen original declarations from MazurTheorem Order13InverseParameterFiniteSchemeAtlas.lean, Apache-2.0, Vas and contributors. Only the import changes to the public canonical finite-map primitive scopes interface; every original declaration body is unchanged. All fifteen original closed types and nine original data values are compared in the kernel. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: the global inverse finite-chart comparison and actual integral FiniteMapData. The global comparison remains a separate theorem.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual two-member open cover of the finite coordinate
scheme by the ordinary t-open chart and the retained reciprocal patch.
Named downstream consumer: gluing this atlas to the exact section complement.
The global comparison and finite-map data are separate obligations.
-/
import Definitions.Def_MazurTransfer_Order13CanonicalFiniteMapPrimitiveScopes

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

def candidateParameterChartMap : Spec (.of (parameterLocalization R)) ⟶ inverseFiniteAffineScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (parameterLocalization R)))

def ordinaryParameterFiniteChartIso :
    Spec (.of (Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R)) ≅
      Spec (.of (parameterLocalization R)) :=
  Scheme.Spec.mapIso (parameterLocalizationEquiv R).toRingEquiv.toCommRingCatIso.op

def ordinaryParameterToFiniteAffineScheme :
    Spec (.of (Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R)) ⟶ inverseFiniteAffineScheme R :=
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

def reciprocalFiniteChartIso (h104 : IsUnit (104 : R)) :
    Spec (.of (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) ≅
      Spec (.of (infinityLocalization R)) :=
  Scheme.Spec.mapIso (recoveredReciprocalPatchEquiv R h104).symm.toRingEquiv.toCommRingCatIso.op

def reciprocalToFiniteAffineScheme (h104 : IsUnit (104 : R)) :
    Spec (.of (Order13InverseParameterPositiveReciprocalPatch.PatchRing R)) ⟶ inverseFiniteAffineScheme R :=
  (reciprocalFiniteChartIso R h104).hom ≫ candidateInfinityChartMap R

theorem reciprocalToFiniteAffineScheme_isOpenImmersion (h104 : IsUnit (104 : R)) :
    IsOpenImmersion (reciprocalToFiniteAffineScheme R h104) := by
  let : IsOpenImmersion (candidateInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (infinityPatchElement R)
  unfold reciprocalToFiniteAffineScheme
  infer_instance

theorem reciprocalToFiniteAffineScheme_range (h104 : IsUnit (104 : R)) :
    Set.range (reciprocalToFiniteAffineScheme R h104) =
      (PrimeSpectrum.basicOpen (infinityPatchElement R) : Set (PrimeSpectrum (candidateAlgebra R))) := by
  let : IsOpenImmersion (candidateInfinityChartMap R) :=
    IsOpenImmersion.of_isLocalization (infinityPatchElement R)
  have he := Scheme.Hom.opensRange_comp_of_isIso
    (reciprocalFiniteChartIso R h104).hom (candidateInfinityChartMap R)
  exact (congrArg (fun U : (inverseFiniteAffineScheme R).Opens => (U : Set (inverseFiniteAffineScheme R))) he).trans
    (PrimeSpectrum.localization_away_comap_range (infinityLocalization R) (infinityPatchElement R))

theorem finiteScheme_two_chart_range_cover (h104 : IsUnit (104 : R)) :
    Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
      Set.range (reciprocalToFiniteAffineScheme R h104) = Set.univ := by
  rw [ordinaryParameterToFiniteAffineScheme_range,reciprocalToFiniteAffineScheme_range]
  change ((PrimeSpectrum.basicOpen (sElement R) : Set (PrimeSpectrum (candidateAlgebra R))) ∪
    (PrimeSpectrum.basicOpen (infinityPatchElement R) : Set (PrimeSpectrum (candidateAlgebra R)))) = Set.univ
  have he := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum (candidateAlgebra R)) =>
    (U : Set (PrimeSpectrum (candidateAlgebra R))))
      (inverse_candidate_two_principal_open_cover R (two_isUnit_of_104 R h104))
  simpa only [TopologicalSpace.Opens.coe_sup,TopologicalSpace.Opens.coe_top] using he

def finiteSchemeChart (b : Bool) : Scheme.{u} :=
  if b then Spec (.of (Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R))
  else Spec (.of (Order13InverseParameterPositiveReciprocalPatch.PatchRing R))

def finiteSchemeChartMap (h104 : IsUnit (104 : R)) :
    (b : Bool) → finiteSchemeChart R b ⟶ inverseFiniteAffineScheme R
  | true => ordinaryParameterToFiniteAffineScheme R
  | false => reciprocalToFiniteAffineScheme R h104

theorem finiteSchemeChartMap_isOpenImmersion (h104 : IsUnit (104 : R)) (b : Bool) :
    IsOpenImmersion (finiteSchemeChartMap R h104 b) := by
  cases b with
  | false => exact reciprocalToFiniteAffineScheme_isOpenImmersion R h104
  | true => exact ordinaryParameterToFiniteAffineScheme_isOpenImmersion R

def finiteSchemeOpenCover (h104 : IsUnit (104 : R)) : (inverseFiniteAffineScheme R).OpenCover where
  I₀ := Bool
  X := finiteSchemeChart R
  f := finiteSchemeChartMap R h104
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro a
      have ha : a ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
          Set.range (reciprocalToFiniteAffineScheme R h104) := by
        rw [finiteScheme_two_chart_range_cover]
        trivial
      rcases ha with ha | ha
      · exact ⟨true,ha⟩
      · exact ⟨false,ha⟩
    · exact finiteSchemeChartMap_isOpenImmersion R h104

end MazurTransfer.Order13InverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.reciprocalToFiniteAffineScheme_range
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteSchemeOpenCover


