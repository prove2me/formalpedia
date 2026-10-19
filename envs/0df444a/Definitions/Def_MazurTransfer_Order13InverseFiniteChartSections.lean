-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseFiniteChartSections
-- name    : MazurTransfer_Order13InverseFiniteChartSections
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T06:38:58.395756+00:00
-- url     : https://prove2.me/theorems/e8999d8a-d1dc-4fb8-99d1-1a52035968dc
-- title:
--   Structural sections and literal parameter of the actual inverse finite chart
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $V$ be the actual inverse finite chart and $B=R[S][a,b]$ its actual finite coordinate algebra. The original affine-open presentation determines the specified structural isomorphism $E:\Gamma(V)\cong_R B$ and section $g=E^{-1}(S)$. On the ordinary parameter localization, its pullback is the literal inverse parameter $s=1/t$. These are the structural constructors used by the inverse polynomial basis and parameter reciprocity.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Nine closed declarations using the original public inverse affine-open presentation and Proved structural base compatibility. The generic public section R-algebra constructor and public section-pullback theorem supply the actual structural coefficient action and literal ordinary-localization parameter value. All underlying curve maps and the chosen original inverse presentation are retained. Named downstream consumers: inverse polynomial basis, inverse parameter powers, overlap and parameter reciprocity in unchanged integral FiniteMapData. Native, strict and full frontend checks pass with standard axioms only.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original actual inverse affine chart carries its structural section R-algebra comparison and literal inverse parameter section.
Named downstream consumers: inverse-chart polynomial basis, finite parameter powers, actual overlap and parameter reciprocity in unchanged integral FiniteMapData. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteAffineOpenPresentation
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelBaseMaps
import Definitions.Def_MazurTransfer_AffineOpenSectionsAlgEquiv
import Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_finiteModelToCurve_base
import Theorems.Thm_MazurTransfer_ActualAffineSectionRingRestrictionTransport_transportedSection_pullback
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open scoped MazurTransfer.Order13InverseParameterFiniteAlgebra
namespace MazurTransfer.Order13InverseFiniteChartFromPublicTheorems
open Order13InverseParameterFiniteAlgebra
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

abbrev specIso (h104 : IsUnit (104 : R)) :
    Spec (.of (candidateAlgebra R)) ≅ (inverseChartOpen R).toScheme :=
  finiteModelInverseChartIso R h104

theorem specIso_over_base (h104 : IsUnit (104 : R)) :
    (specIso R h104).hom ≫ (inverseChartOpen R).ι ≫ curveToBase R =
      Spec.map (CommRingCat.ofHom (algebraMap R (candidateAlgebra R))) := by
  change (finiteModelInverseChartIso R h104).hom ≫
    (inverseChartOpen R).ι ≫ curveToBase R = _
  rw [← Category.assoc, finiteModelInverseChartIso_hom_ι, finiteModelToCurve_base]
  change Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) = _
  rw [← Spec.map_comp]
  rfl

def sectionsAlgEquiv (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    Γ(curveScheme R, inverseChartOpen R) ≃ₐ[R] candidateAlgebra R :=
  ActualAffineSectionRingBasicOpenTransport.sectionsAlgEquiv_of_over R (curveToBase R)
    (inverseChartOpen R) (candidateAlgebra R) (specIso R h104) (specIso_over_base R h104)

def parameterSection (h104 : IsUnit (104 : R)) :
    Γ(curveScheme R, inverseChartOpen R) :=
  ActualAffineSectionRingBasicOpenTransport.transportedSection (inverseChartOpen R)
    (specIso R h104) (sElement R)

theorem sectionsAlgEquiv_parameter (h104 : IsUnit (104 : R)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    sectionsAlgEquiv R h104 (parameterSection R h104) = sElement R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  exact (ActualAffineSectionRingBasicOpenTransport.sectionsRingIso
    (inverseChartOpen R) (specIso R h104)).commRingCatIsoToRingEquiv.apply_symm_apply _

theorem ordinaryToFinite_eq_Spec :
    ordinaryParameterToFiniteAffineScheme R = Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (parameterLocalizationEquiv R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (parameterLocalization R))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact localizedInclusion_algebraMap R

theorem specIso_ordinary (h104 : IsUnit (104 : R)) :
    Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) ≫
      (specIso R h104).hom ≫ (inverseChartOpen R).ι = ordinaryParameterCurveMap R := by
  rw [← ordinaryToFinite_eq_Spec]
  change ordinaryParameterToFiniteAffineScheme R ≫
    (finiteModelInverseChartIso R h104).hom ≫ (inverseChartOpen R).ι = _
  rw [finiteModelInverseChartIso_hom_ι, ordinaryParameterToFiniteAffineScheme_finiteModelToCurve]

theorem ordinary_le_preimage_chartOpen : ⊤ ≤
    (ordinaryParameterCurveMap R) ⁻¹ᵁ inverseChartOpen R := by
  intro x _
  change ordinaryParameterCurveMap R x ∈ Set.range (ordinaryParameterCurveMap R) ∨
    ordinaryParameterCurveMap R x ∈ Set.range (positiveReciprocalCurveMap R)
  exact Or.inl ⟨x, rfl⟩

theorem parameterSection_ordinary_pullback (h104 : IsUnit (104 : R)) :
    (Scheme.ΓSpecIso (.of (MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R))).hom
      ((ordinaryParameterCurveMap R).appLE (inverseChartOpen R) ⊤
        (ordinary_le_preimage_chartOpen R) (parameterSection R h104)) =
      Order13InverseParameterPolynomialIdentities.s R := by
  have hp := ActualAffineSectionRingRestrictionTransport.transportedSection_pullback
    (inverseChartOpen R) (specIso R h104) (inclusion R).toRingHom (sElement R)
    (show ⊤ ≤ (Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) ≫
      (specIso R h104).hom ≫ (inverseChartOpen R).ι) ⁻¹ᵁ inverseChartOpen R by
        rw [specIso_ordinary]; exact ordinary_le_preimage_chartOpen R)
  have hp' : (Scheme.ΓSpecIso
      (.of (MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R))).hom
      ((ordinaryParameterCurveMap R).appLE (inverseChartOpen R) ⊤
        (ordinary_le_preimage_chartOpen R) (parameterSection R h104)) =
      (inclusion R).toRingHom (sElement R) := by
    simpa only [specIso_ordinary, parameterSection] using hp
  exact hp'.trans (inclusion_sElement R)

end MazurTransfer.Order13InverseFiniteChartFromPublicTheorems
#print axioms MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.sectionsAlgEquiv
#print axioms MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.parameterSection_ordinary_pullback


