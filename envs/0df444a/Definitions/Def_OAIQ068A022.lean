-- Prove2me | Definitions.Def_OAIQ068A022
-- name    : OAIQ068A022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:53:52.233384+00:00
-- url     : https://prove2.me/theorems/5e3b0890-c9e4-483e-b2bd-19b6d1a1a835
-- title:
--   Definitions bundle OAIQ068A022 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 25 definitions, 4 instances and 54 theorems. The definitions and types are `OAI.PiExponent.CurveCenters.Centered`, `OAI.PiExponent.CurveCenters.centerPlaces`, `OAI.PiExponent.CurveContactFamily.places`, `OAI.PiExponent.CurveContactSum.coordinateOrderDivisor`, `OAI.PiExponent.CurveContactSum.weightedPoleDivisor`, `OAI.PiExponent.CurveModelPlaces.chartPlace`, `OAI.PiExponent.CurveNormalizationModel.parameterCurveProjection`, `OAI.PiExponent.CurveNormalizationModel.parameterCurveStructureMap`, `OAI.PiExponent.GlobalSectionClearing.affineSpecSections`, `OAI.PiExponent.GlobalSectionClearing.openRestriction`, `OAI.PiExponent.PlaceCenteredBranch.lift`, `OAI.PiExponent.ProjectiveLine.affineChartCover`, `OAI.PiExponent.ProjectiveLine.chartMap`, `OAI.PiExponent.ProjectiveLine.chartRingEquiv`, `OAI.PiExponentSeshadri.Geometry.cohomology`, `OAI.PiExponentSeshadri.Geometry.complexExtModule`, `OAI.PiExponentSeshadri.LineBundleFrameCocycle.coeff`, `OAI.PiExponentSeshadri.LineBundleFrameCocycle.frame`, `OAI.PiExponentSeshadri.LineBundleFrameCocycle.isoSheaf`, `OAI.PiExponentSeshadri.LineBundleFrameCocycle.ofFrames`, `OAI.PiExponentSeshadri.LineBundleFrameCocycle.presheafHom`, `OAI.PiExponentSeshadri.LineBundleFrameCocycle.toSections`, `OAI.PiExponentSeshadri.LineBundleFrameCocycle.transition`, `OAI.PiExponentSeshadri.LineBundleGluing.trivialCoefficientMap`, `OAI.PiExponentSeshadri.LineBundleGluing.trivialSheafIso`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AmpleIso`, `PiExponent_Ampleness_ClosedAmpleRestriction`, `PiExponent_Approximation_CocycleTensor`, `PiExponent_Approximation_CocycleTensorIso`, `PiExponent_Approximation_GlobalSectionClearing`, `PiExponent_Cohomology_CurveEuler`, `PiExponent_Cohomology_EulerExact`, `PiExponent_Geometry_CurveCenters`, `PiExponent_Geometry_CurveContactFamily`, `PiExponent_Geometry_CurveContactSum`, `PiExponent_Geometry_CurveModelPlaces`, `PiExponent_Geometry_CurveNormalizationProper`, `PiExponent_Geometry_CurveProductFormula`, `PiExponent_Geometry_LineBundleFrameCocycle`, `PiExponent_Geometry_PlaceCenteredBranch`, `PiExponent_Geometry_ProjectiveFrameNaturality`, `PiExponent_Geometry_ProjectiveLineCharts`, `PiExponent_Geometry_ProjectiveLineReciprocal`, `PiExponent_Geometry_ProjectivePullbackFrames`, `PiExponent_Geometry_ProjectiveSectionsPullback`, `PiExponent_Polynomials_FrameCoefficientLaws`, `PiExponent_Polynomials_PullbackFrameCoefficient`.
--
--   **Imports.** It imports the bundles `OAIQ068A012`, `OAIQ068A013` and `OAIQ068A014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A028`, `OAIQ068A029`, `OAIQ068A030`, `OAIQ068A031`, `OAIQ068A032`, `OAIQ068A033` and `OAIQ068A034`; the statements `OAI_PiExponent_GeometrySupport_NoetherianAmpleSerreVanishing_ample_power_cohomology_zero`, `OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_power_cohomology_zero_q68`, `OAI_PiExponent_GeometrySupport_NoetherianAmpleSerreVanishing_ample_serre_tensor_vanishing`, `OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_tensor_vanishing_q68`, `OAI_PiExponent_NumericalAmpleness_lineBundle_cohomology_zero_of_dimension_le` and `OAI.PiExponent.NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A012
import Definitions.Def_OAIQ068A013
import Definitions.Def_OAIQ068A014

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleIso
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AmpleIso

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

variable {X : Scheme}

theorem sectionOpen_postcomp_iso {M N : X.Modules}
    (s : GlobalSections X M) (e : M ≅ N) :
    sectionOpen X (s ≫ e.hom) = sectionOpen X s := by
  simp only [sectionOpen, Functor.map_comp, isIso_comp_right_iff]

end
end PiExponent.AmpleIso

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ClosedAmpleRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X Y : Scheme.{0}}

theorem pullback_isoOpen_eq (L : LineBundle X) (s : O X ⟶ L.sheaf) (f : Y ⟶ X) :
    isoOpen (pullbackSection f s) = f ⁻¹ᵁ isoOpen s := by
  ext y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame f U e s
  calc
    y ∈ isoOpen (pullbackSection f s) ↔
        (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ (f ⁻¹ᵁ U).toScheme.basicOpen
          (coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s))) :=
      (congrArg (fun V => (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ V)
        (preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι eF)).to_iff
    _ ↔ (⟨f y,hy⟩ : U.toScheme) ∈ U.toScheme.basicOpen
          (coefficient e (restrictSection U.ι s)) := by
      rw [he,← Scheme.preimage_basicOpen_top]
      change (f ∣_ U) ⟨y,hy⟩ ∈ U.toScheme.basicOpen
        (coefficient e (restrictSection U.ι s)) ↔ _
      rw [morphismRestrict_base]
      rfl
    _ ↔ f y ∈ isoOpen s :=
      (congrArg (fun V => (⟨f y,hy⟩ : U.toScheme) ∈ V)
        (preimage_isoOpen s U.ι e)).to_iff.symm

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CocycleTensor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def trivialCoefficientMap : (structureSheaf X).val ⟶ presheaf (Cocycle.one (U := U)) where
  app V := ModuleCat.ofHom (R := Γ(X, V.unop))
    (X := ModuleCat.of Γ(X, V.unop) Γ(X, V.unop))
    (Y := ModuleCat.of Γ(X, V.unop) (sections (Cocycle.one (U := U)) V.unop)) {
    toFun a := ⟨fun p => X.presheaf.map (homOfLE p.2.property.1).op a, by
      constructor
      · intro i W W' hW hi h
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        rw [← Functor.map_comp]
        rfl
      · intros; exact (one_mul _).symm⟩
    map_add' a b := by apply Subtype.ext; funext p; exact map_add _ _ _
    map_smul' a b := by apply Subtype.ext; funext p; exact map_mul _ _ _ }
  naturality {V W} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext p
    change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
    rw [← Functor.map_comp]
    rfl

lemma cocycleUnit_restrict_isIso (c : Cocycle U) (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map ((adj X).unit.app (presheaf c))) := by
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules (U i).toScheme.ringCatSheaf.obj := modulePresheafRestrict (U i).ι
  have hη : IsIso ((adj (U i).toScheme).unit.app (R.obj (presheaf c))) :=
    sheafification_unit_isIso_of_iso _ (structureSheaf (U i).toScheme)
      (chartPresheafFrame c i)
  have hh : IsIso (R.map ((adj X).unit.app (presheaf c)) ≫
      ((moduleSheafificationRestrict (U i).ι).hom.app (presheaf c)).val) := by
    erw [sheafify_restrict_unit]
    exact hη
  let V : (U i).toScheme.Modules ⥤ PresheafOfModules (U i).toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget (U i).toScheme.ringCatSheaf
  let hv : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (((moduleSheafificationRestrict (U i).ι).hom.app (presheaf c)).val) :=
    (V.mapIso ((moduleSheafificationRestrict (U i).ι).app (presheaf c))).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hv).mp hh

lemma trivialCoefficientMap_frame (i : ι) :
    (modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U)) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom =
    (Scheme.Modules.restrictUnitIso (U i).ι).hom.val := by
  ext V a
  change X.presheaf.map (homOfLE (show (U i).ι ''ᵁ V.unop ≤ (U i).ι ''ᵁ V.unop from le_rfl)).op a = _
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  change a = ((U i).ι.appIso V.unop).hom a
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
  rfl

lemma trivialCoefficientMap_restrict_isIso (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U))) := by
  let V : (U i).toScheme.Modules ⥤ PresheafOfModules (U i).toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget (U i).toScheme.ringCatSheaf
  have hv : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      ((Scheme.Modules.restrictUnitIso (U i).ι).hom.val) :=
    (V.mapIso (Scheme.Modules.restrictUnitIso (U i).ι)).isIso_hom
  have hh : IsIso ((modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U)) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom) := by
    rw [trivialCoefficientMap_frame]
    exact hv
  let hc : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom :=
    (chartPresheafFrame (Cocycle.one (U := U)) i).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

lemma inverseProductMap_frame (c : Cocycle U) (i : ι) :
    (modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom =
    (modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse)).hom ≫
      PresheafOfModules.Monoidal.tensorHom (R := (U i).toScheme.presheaf)
        (chartPresheafFrame c i).hom (chartPresheafFrame c.inverse i).hom ≫
      (by
        let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
          PresheafOfModules.monoidalCategory (R := (U i).toScheme.presheaf)
        exact (λ_ (structureSheaf (U i).toScheme).val).hom) := by
  let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := (U i).toScheme.presheaf)
  let l := (modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
    (chartPresheafFrame (Cocycle.one (U := U)) i).hom
  let r := (modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse)).hom ≫
    PresheafOfModules.Monoidal.tensorHom (R := (U i).toScheme.presheaf)
      (chartPresheafFrame c i).hom (chartPresheafFrame c.inverse i).hom ≫
    (λ_ (structureSheaf (U i).toScheme).val).hom
  change l = r
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | tmul s t => rfl
  | add a b ha hb =>
      exact ((l.app V).hom.map_add a b).trans
        ((congrArg₂ (· + ·) ha hb).trans ((r.app V).hom.map_add a b).symm)

lemma inverseProductMap_restrict_isIso (c : Cocycle U) (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (inverseProductMap c)) := by
  let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := (U i).toScheme.presheaf)
  let e := modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse) ≪≫
    tensorIso (chartPresheafFrame c i) (chartPresheafFrame c.inverse i) ≪≫
      λ_ (structureSheaf (U i).toScheme).val
  have hh : IsIso ((modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom) := by
    rw [inverseProductMap_frame]
    exact e.isIso_hom
  let hc : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom :=
    (chartPresheafFrame (Cocycle.one (U := U)) i).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

end PiExponentSeshadri.LineBundleGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CocycleTensorIso
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def trivialSheafIso (hcover : ⊤ ≤ ⨆ i, U i) :
    sheaf (Cocycle.one (U := U)) ≅ structureSheaf X := by
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (trivialCoefficientMap (U := U))) :=
    sheafification_isIso_of_chart _ hcover trivialCoefficientMap_restrict_isIso
  exact (@asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (trivialCoefficientMap (U := U))) ht).symm ≪≫
      (asIso (adj X).counit).app (structureSheaf X)

end
end PiExponentSeshadri.LineBundleGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalSectionClearing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GlobalSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

def openRestriction (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    OpenSections M V →ₗ[Γ(X,⊤)] OpenSections M U where
  toFun := M.val.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := by
    intro r m
    let : Module Γ(X,V) (OpenSections M V) := (M.val.obj (op V)).isModule
    let : Module Γ(X,U) (OpenSections M U) := (M.val.obj (op U)).isModule
    change M.presheaf.map (homOfLE h).op (restrictScalar X V r • (m : Γ(M,V))) =
      restrictScalar X U r • M.presheaf.map (homOfLE h).op m
    erw [M.map_smul, restrictScalar_naturality]

def affineSpecSections [IsAffine X] (M : X.Modules)
    (U : (Spec Γ(X,⊤)).Opens) :
    ((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.obj (op U)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (X.toSpecΓ ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    let : Module Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) :=
      (M.val.obj (op (X.toSpecΓ ⁻¹ᵁ U))).isModule
    change @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
      ((X.toSpecΓ.app U).hom
        ((Spec Γ(X,⊤)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
        (restrictScalar X (X.toSpecΓ ⁻¹ᵁ U) r) m
    congr 1
    have h := congrArg (fun f : Γ(Spec Γ(X,⊤),⊤) ⟶ Γ(X,X.toSpecΓ ⁻¹ᵁ U) =>
      f ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) (X.toSpecΓ.naturality U.leTop.op)
    simp only [CommRingCat.comp_apply, Scheme.toSpecΓ_appTop] at h
    change _ = restrictScalar X (X.toSpecΓ ⁻¹ᵁ U)
      ((Scheme.ΓSpecIso Γ(X,⊤)).hom ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) at h
    rw [(Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r] at h
    exact h

lemma openSectionsCongr_restriction (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : OpenSections M ⊤) :
    openSectionsCongr M h (openRestriction M (show U ≤ ⊤ from le_top) m) = openRestriction M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

theorem affine_openRestriction_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r (openRestriction M (X.basicOpen_le r)) := by
  let F := modulesSpecToSheaf.obj (affineToSpecModule M)
  let f := (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  let e0 : (F.obj.obj (op ⊤)) ≃ₗ[Γ(X,⊤)] OpenSections M ⊤ := affineSpecSections M ⊤
  let e1 := (affineSpecSections M (PrimeSpectrum.basicOpen r)).trans
    (openSectionsCongr M (Scheme.toSpecΓ_preimage_basicOpen X r))
  have hf : IsLocalizedModule.Away r f := affine_sections_localize M r
  have hq : IsLocalizedModule.Away r (e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap) := by
    let := hf
    let := IsLocalizedModule.of_linearEquiv (.powers r) f e1
    exact IsLocalizedModule.of_linearEquiv_right (.powers r) (e1.toLinearMap ∘ₗ f) e0.symm
  have he : e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap =
      openRestriction M (X.basicOpen_le r) := by
    ext m
    exact openSectionsCongr_restriction M (Scheme.toSpecΓ_preimage_basicOpen X r) m
  rwa [he] at hq

theorem affine_basicOpen_denominators [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M (X.basicOpen r)) :
    ∃ n : ℕ, ∃ y : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) y = r^n • x := by
  let f := openRestriction M (X.basicOpen_le r)
  let : IsLocalizedModule.Away r f := affine_openRestriction_localize M r
  obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away r f).surj _ _ x
  exact ⟨n,y,hy.symm⟩

end
end PiExponent.GlobalSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveEuler
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {X : Scheme.{0}}

abbrev cohomology (M : X.Modules) (n : ℕ) : Type 1 :=
  Abelian.Ext.{1} (C := X.Modules) (structureSheaf X) M n

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian Opposite

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerExact
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ))

@[instance_reducible]
def complexExtModule (M : X.Modules) (n : ℕ) : Module ℂ (cohomology M n) :=
  letI := sheafComplexLinear f
  inferInstance

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveProductFormula
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveProductFormula
open PiExponent.CurveZeroPole PiExponent.CurveValuationCenter
open PiExponent.WeightedCurveDegree

theorem valuation_constant_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (c : F) (hc : c ≠ 0) :
    p.valuation (algebraMap F E c) = 0 := by
  let z : Eˣ := Units.mk0 (algebraMap F E c) ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hc)
  have hpos : 0 ≤ integerOrder p.valuation z := by
    apply WithTop.coe_le_coe.mp
    rw [coe_integerOrder]
    exact p.constants_nonneg c
  have hinv : 0 ≤ integerOrder p.valuation z⁻¹ := by
    apply WithTop.coe_le_coe.mp
    rw [coe_integerOrder]
    simpa [z] using p.constants_nonneg c⁻¹
  rw [integerOrder_inv] at hinv
  have hz : integerOrder p.valuation z = 0 := by omega
  have he := coe_integerOrder p.valuation z
  rw [hz] at he
  exact he.symm

theorem placeOrder_constant_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (c : F) (hc : c ≠ 0) :
    placeOrder p (Units.mk0 (algebraMap F E c) ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hc)) = 0 := by
  apply WithTop.coe_injective
  rw [placeOrder, coe_integerOrder]
  exact valuation_constant_eq_zero p c hc

end PiExponent.CurveProductFormula

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactSum
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveContactSum

open WeightedPolynomialPole WeightedCurveDegree CurveValuationCenter PolynomialPoleBound

theorem coordinateOrder_constant_eq_zero {E : Type*} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (c : ℂ) : coordinateOrder p.valuation (algebraMap ℂ E c) = 0 := by
  by_cases hc : c = 0
  · simp [hc, coordinateOrder]
  have hm : algebraMap ℂ E c ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hc
  rw [coordinateOrder, dite_eq_right hm]
  exact CurveProductFormula.placeOrder_constant_eq_zero p c hc

def coordinateOrderDivisor {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) : NormalizedPlace ℂ E →₀ ℤ := by
  classical
  exact if ht : Transcendental ℂ f then
    letI := hfinite f ht
    CurveProductFormula.principalDivisor f ht
  else 0

@[simp] theorem coordinateOrderDivisor_apply {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) (p : NormalizedPlace ℂ E) :
    coordinateOrderDivisor hfinite f p = coordinateOrder p.valuation f := by
  classical
  by_cases ht : Transcendental ℂ f
  · let := hfinite f ht
    simp only [coordinateOrderDivisor, dite_eq_left ht, CurveProductFormula.principalDivisor_apply,
      coordinateOrder, dite_eq_right ht.ne_zero]
    rfl
  · rw [coordinateOrderDivisor, dite_eq_right ht]
    obtain ⟨c,rfl⟩ := exists_constant_of_isAlgebraic f (not_not.mp ht)
    exact (coordinateOrder_constant_eq_zero p c).symm

def weightedPoleDivisor {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) : NormalizedPlace ℂ E →₀ ℚ :=
  Finsupp.ofSupportFinite (fun p => coordinatePole p.valuation x w)
    (coordinatePole_finite_support (fun p : NormalizedPlace ℂ E => p.valuation) x w (by
      intro i
      simpa only [Function.HasFiniteSupport, Function.support, coordinateOrderDivisor_apply] using
        (coordinateOrderDivisor hfinite (x i)).hasFiniteSupport))

@[simp] theorem weightedPoleDivisor_apply {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (p : NormalizedPlace ℂ E) :
    weightedPoleDivisor hfinite x w p = coordinatePole p.valuation x w := rfl

end PiExponent.CurveContactSum

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveCenters
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.PlaceValuationRing.constantsAlgebra _root_.OAI.PiExponent.PlaceValuationRing.discreteValuationRing _root_.OAI.PiExponent.PlaceValuationRing.valuation_nontrivial _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveCenters

open CurveValuationCenter

variable {E ι J : Type*} [Field E] [Algebra ℂ E]

def Centered (x : ι → E) (a : ι → ℂ) (p : NormalizedPlace ℂ E) : Prop :=
  ∀ i, 0 < p.valuation (x i - algebraMap ℂ E (a i))

theorem finite_centered (x : ι → E) (a : ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Set.Finite {p : NormalizedPlace ℂ E | Centered x a p} := by
  obtain ⟨i, hi⟩ := hx
  have ht := transcendental_sub_constant hi (a i)
  let := hfinite (x i - algebraMap ℂ E (a i)) ht
  exact (finite_positivePlaces (x i - algebraMap ℂ E (a i)) ht).subset
    (fun p hp => hp i)

theorem finite_centered_family [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Set.Finite {p : NormalizedPlace ℂ E | ∃ j, Centered x (a j) p} := by
  have he : {p : NormalizedPlace ℂ E | ∃ j, Centered x (a j) p} =
      ⋃ j, {p : NormalizedPlace ℂ E | Centered x (a j) p} := by ext p; simp
  rw [he]
  exact Set.finite_iUnion (fun j => finite_centered x (a j) hx hfinite)

def centerPlaces [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Finset (NormalizedPlace ℂ E) :=
  (finite_centered_family x a hx hfinite).toFinset

@[simp] theorem mem_centerPlaces [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E)
    (p : NormalizedPlace ℂ E) :
    p ∈ centerPlaces x a hx hfinite ↔ ∃ j, Centered x (a j) p :=
  (finite_centered_family x a hx hfinite).mem_toFinset

theorem Centered.coordinate_nonneg {x : ι → E} {a : ι → ℂ} {p : NormalizedPlace ℂ E}
    (ha : Centered x a p) (i : ι) : 0 ≤ p.valuation (x i) := by
  have h := (le_min (ha i).le (p.constants_nonneg (a i))).trans
    (p.valuation.map_add (x i - algebraMap ℂ E (a i)) (algebraMap ℂ E (a i)))
  simpa only [sub_add_cancel] using h

end PiExponent.CurveCenters
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceCenteredBranch
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PlaceCenteredBranch

open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole

variable {E ι : Type*} [Field E] [Algebra ℂ E]

def lift (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (i : ι) : ring p :=
  ⟨z i, hc.coordinate_nonneg i⟩

@[simp] theorem lift_coe (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (i : ι) : (lift p z c hc i : E) = z i := rfl

theorem lift_nonconstant (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i)) :
    ∃ i, lift p z c hc i ≠ algebraMap ℂ (ring p) (c i) := by
  obtain ⟨i,hi⟩ := hnc
  refine ⟨i,?_⟩
  intro he
  exact hi (congrArg (fun a : ring p => (a : E)) he)

end PiExponent.PlaceCenteredBranch

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveContactFamily
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveContactFamily

open CurveValuationCenter CurveCenters PlaceValuationRing

variable {E : Type*} [Field E] {m K : ℕ}

variable [Algebra ℂ E]

def places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) : Finset (NormalizedPlace ℂ E) :=
  centerPlaces z (fun j => fullCenter (c j)) hz hfinite

theorem mem_places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (p : NormalizedPlace ℂ E) :
    p ∈ places hfinite z c hz ↔ ∃ j : Fin K, Centered z (fullCenter (c j)) p := by
  exact mem_centerPlaces z (fun j => fullCenter (c j)) hz hfinite p

end PiExponent.CurveContactFamily
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveModelPlaces
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveModelPlaces
universe u
open CurveZeroPole CurveValuationCenter WeightedCurveDegree
open CurveNormalizationModel
open AlgebraicGeometry CategoryTheory

def chartPlace
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    NormalizedPlace F E where
  valuation := chartValuation f hf q
  constants_nonneg c := by
    let := parameterPolynomialAlgebra f hf
    have hmap : ((algebraMap F[X] (parameterChart f hf) (Polynomial.C c)) : E) =
        algebraMap F E c := by
      change algebraMap F[X] E (Polynomial.C c) = _
      rw [parameterPolynomialAlgebra_map, Polynomial.aeval_C]
    rw [← hmap]
    exact chartValuation_nonneg f hf q _
  normalized := by
    let := parameterAlgebra f hf
    let := parameterPolynomialAlgebra f hf
    let := parameter_scalarTower f hf
    let := parameter_finite f hf
    exact primeFieldValuation_normalized (parameterChart f hf) E q

theorem chartPlace_parameter_nonneg
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    0 ≤ (chartPlace f hf q).valuation f := by
  let := parameterPolynomialAlgebra f hf
  have hmap : ((algebraMap F[X] (parameterChart f hf) Polynomial.X) : E) = f := by
    change algebraMap F[X] E Polynomial.X = f
    rw [parameterPolynomialAlgebra_map, Polynomial.aeval_X]
  have hn := chartValuation_nonneg f hf q
    (algebraMap F[X] (parameterChart f hf) Polynomial.X)
  exact (congrArg (fun x : E => 0 ≤ chartValuation f hf q x) hmap).mp hn

end PiExponent.CurveModelPlaces

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLineCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (F : Type u) [CommRing F]

def chartRingEquiv (i : Bool) : PolyChart (R := F) i ≃+* Polynomial F :=
  (polynomialChartEquiv i).trans
    (MvPolynomial.uniqueAlgEquiv F (ChartVariables i)).toRingEquiv

lemma chartRingEquiv_eq_evalAway (i : Bool) :
    (chartRingEquiv F i).toRingHom =
      evalAway (𝒜 := PolyGrade F Bool) (lineEvaluation F i) (MvPolynomial.X i)
        (by simp) := by
  apply RingHom.ext
  intro x
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (poly_X_mem (R := F) i) x
  change (MvPolynomial.uniqueAlgEquiv F (ChartVariables i))
    (chartToPoly i (Away.mk _ (poly_X_mem (R := F) i) n p hp)) = _
  rw [chartToPoly_mk]
  have h := RingHom.congr_fun (unique_dehomogenize F i) p
  change (MvPolynomial.uniqueAlgEquiv F (ChartVariables i)) (dehomogenize i p) = _ at h
  rw [h]
  symm
  simpa using evalAway_mk_clear (lineEvaluation F i) (poly_X_mem (R := F) i)
    (by simp) n p hp

def chartMap (i : Bool) : Spec (CommRingCat.of (Polynomial F)) ⟶ projectiveLine F :=
  Spec.map (CommRingCat.ofHom (chartRingEquiv F i).toRingHom) ≫
    Proj.awayι (PolyGrade F Bool) (MvPolynomial.X i) (poly_X_mem i) (by decide)

instance chartRingEquiv_isIso (i : Bool) :
    IsIso (CommRingCat.ofHom (chartRingEquiv F i).toRingHom) :=
  (chartRingEquiv F i).toCommRingCatIso.isIso_hom

instance chartMap_isOpenImmersion (i : Bool) : IsOpenImmersion (chartMap F i) := by
  unfold chartMap
  infer_instance

lemma chartMap_eq_fromUnitCoordinate (i : Bool) :
    chartMap F i = fromUnitCoordinate (𝒜 := PolyGrade F Bool)
      (lineEvaluation F i) (by decide) (poly_X_mem i) (by simp) := by
  unfold chartMap fromUnitCoordinate
  rw [chartRingEquiv_eq_evalAway]

@[simp] lemma chartMap_opensRange (i : Bool) :
    (chartMap F i).opensRange = Proj.basicOpen (PolyGrade F Bool) (MvPolynomial.X i) := by
  unfold chartMap
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

lemma chartMap_cover : (⨆ i : Bool, (chartMap F i).opensRange) = ⊤ := by
  simp only [chartMap_opensRange]
  exact standardChart_cover

lemma chartMap_preimage (i j : Bool) :
    chartMap F i ⁻¹ᵁ Proj.basicOpen (PolyGrade F Bool) (MvPolynomial.X j) =
      PrimeSpectrum.basicOpen (if j = i then (1 : Polynomial F) else Polynomial.X) := by
  rw [chartMap_eq_fromUnitCoordinate, fromUnitCoordinate_preimage _ (poly_X_mem i)
    (by simp) (by simp) (by decide) (poly_X_mem j), lineEvaluation_X]

lemma chartMap_preimage_other (i : Bool) :
    chartMap F i ⁻¹ᵁ (chartMap F (!i)).opensRange =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial F) := by
  rw [chartMap_opensRange, chartMap_preimage]
  cases i <;> simp <;> rfl

@[reassoc] lemma chartMap_structureMap (i : Bool) :
    chartMap F i ≫ structureMap F = Spec.map (CommRingCat.ofHom Polynomial.C) := by
  unfold chartMap structureMap
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change (chartRingEquiv F i) (chartConstants i r) = Polynomial.C r
  change (MvPolynomial.uniqueAlgEquiv F (ChartVariables i))
    (chartToPoly i (chartConstants i r)) = _
  simp [MvPolynomial.uniqueAlgEquiv_apply]

end PiExponent.ProjectiveLine

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLineReciprocal
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (F : Type u) [CommRing F]

@[reassoc] theorem reciprocalChart_compatibility :
    zeroChartOverlap F ≫ chartMap F false =
      infinityChartOverlap F ≫ chartMap F true := by
  unfold zeroChartOverlap infinityChartOverlap
  rw [chartMap_eq_fromUnitCoordinate, chartMap_eq_fromUnitCoordinate,
    fromUnitCoordinate_natural, fromUnitCoordinate_natural]
  let f := (zeroPolynomialMap F).comp (lineEvaluation F false)
  let g := (infinityPolynomialMap F).comp (lineEvaluation F true)
  have hf : IsUnit (f (MvPolynomial.X false)) := by simp [f, zeroPolynomialMap]
  have hg : IsUnit (g (MvPolynomial.X false)) := by
    simpa [g, infinityPolynomialMap] using LaurentPolynomial.isUnit_T (R := F) (-1)
  have hg' : IsUnit (g (MvPolynomial.X true)) := by simp [g, infinityPolynomialMap]
  have H : ∀ n p, p ∈ PolyGrade F Bool n →
      g p = (inverseCoordinateUnit F : LaurentPolynomial F) ^ n * f p := by
    intro n p hp
    change ((infinityPolynomialMap F).comp (lineEvaluation F true)) p = _
    rw [infinityEvaluation_eq]
    change MvPolynomial.eval₂ _ _ p = _
    rw [homogeneous_eval₂_scale hp]
    congr 1
    exact (RingHom.congr_fun (zeroEvaluation_eq F) p).symm
  exact (fromUnitCoordinate_scale (𝒜 := PolyGrade F Bool) f (by decide)
    (poly_X_mem false) hf g hg (inverseCoordinateUnit F) H).trans
      (fromUnitCoordinate_eq (𝒜 := PolyGrade F Bool) g (by decide) (by decide)
        (poly_X_mem false) (poly_X_mem true) hg hg')

def affineChartCover : (projectiveLine F).OpenCover where
  I₀ := Bool
  X _ := Spec (CommRingCat.of (Polynomial F))
  f := chartMap F
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => inferInstance⟩
    intro x
    have hx : x ∈ (⨆ i : Bool, (chartMap F i).opensRange) := by
      rw [chartMap_cover]
      trivial
    rcases TopologicalSpace.Opens.mem_iSup.mp hx with ⟨i, hi⟩
    exact ⟨i, hi⟩

end PiExponent.ProjectiveLine

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationProper
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

@[reassoc] theorem zeroOverlap_projection :
    zeroOverlap f hf ≫ parameterChartProjection f hf =
      parameterOverlapProjection f hf ≫ ProjectiveLine.zeroChartOverlap F := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  unfold zeroOverlap parameterChartProjection parameterOverlapProjection
    ProjectiveLine.zeroChartOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply F[X] (LaurentPolynomial F) E p

@[reassoc] theorem infinityOverlap_projection :
    infinityOverlap f hf ≫ parameterChartProjection f⁻¹ (transcendental_inverse f hf) =
      parameterOverlapProjection f hf ≫ ProjectiveLine.infinityChartOverlap F := by
  let := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
  let := parameterLaurentAlgebra f hf
  unfold infinityOverlap parameterChartProjection parameterOverlapProjection
    ProjectiveLine.infinityChartOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    apply Subtype.ext
    change algebraMap F[X] E (Polynomial.C c) =
      parameterLaurentMap f hf (ProjectiveLine.infinityPolynomialMap F (Polynomial.C c))
    rw [parameterPolynomialAlgebra_map]
    simp [parameterLaurentMap, LaurentPolynomial.eval₂_C]
  · apply Subtype.ext
    change algebraMap F[X] E Polynomial.X =
      parameterLaurentMap f hf (ProjectiveLine.infinityPolynomialMap F Polynomial.X)
    rw [parameterPolynomialAlgebra_map]
    simp

def parameterCurveProjection : parameterCurve f hf ⟶ ProjectiveLine.projectiveLine F :=
  Limits.pushout.desc
    (parameterChartProjection f hf ≫ ProjectiveLine.chartMap F false)
    (parameterChartProjection f⁻¹ (transcendental_inverse f hf) ≫
      ProjectiveLine.chartMap F true) (by
      rw [zeroOverlap_projection_assoc, infinityOverlap_projection_assoc]
      rw [ProjectiveLine.reciprocalChart_compatibility])

@[reassoc] theorem zeroChart_projection :
    zeroChartInclusion f hf ≫ parameterCurveProjection f hf =
      parameterChartProjection f hf ≫ ProjectiveLine.chartMap F false :=
  Limits.pushout.inl_desc _ _ _

@[reassoc] theorem infinityChart_projection :
    infinityChartInclusion f hf ≫ parameterCurveProjection f hf =
      parameterChartProjection f⁻¹ (transcendental_inverse f hf) ≫
        ProjectiveLine.chartMap F true :=
  Limits.pushout.inr_desc _ _ _

theorem parameterCurveProjection_preimage_zero :
    parameterCurveProjection f hf ⁻¹ᵁ (ProjectiveLine.chartMap F false).opensRange =
      (zeroChartInclusion f hf).opensRange := by
  ext x
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · change parameterCurveProjection f hf (zeroChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F false).opensRange ↔
        zeroChartInclusion f hf q ∈ Set.range (zeroChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, zeroChart_projection, Scheme.Hom.comp_apply]
    exact iff_of_true ⟨_, rfl⟩ ⟨q, rfl⟩
  · change parameterCurveProjection f hf (infinityChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F false).opensRange ↔
        infinityChartInclusion f hf q ∈ Set.range (zeroChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, infinityChart_projection, Scheme.Hom.comp_apply,
      infinityChart_mem_zero_iff]
    change parameterChartProjection f⁻¹ (transcendental_inverse f hf) q ∈
      (ProjectiveLine.chartMap F true ⁻¹ᵁ (ProjectiveLine.chartMap F (!true)).opensRange) ↔ _
    rw [ProjectiveLine.chartMap_preimage_other]
    let := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
    change q ∈ PrimeSpectrum.basicOpen
      (algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf)) Polynomial.X) ↔ _
    rw [infinityOverlap_range]
    rfl

theorem parameterCurveProjection_preimage_infinity :
    parameterCurveProjection f hf ⁻¹ᵁ (ProjectiveLine.chartMap F true).opensRange =
      (infinityChartInclusion f hf).opensRange := by
  ext x
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · change parameterCurveProjection f hf (zeroChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F true).opensRange ↔
        zeroChartInclusion f hf q ∈ Set.range (infinityChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, zeroChart_projection, Scheme.Hom.comp_apply,
      zeroChart_mem_infinity_iff]
    change parameterChartProjection f hf q ∈
      (ProjectiveLine.chartMap F false ⁻¹ᵁ (ProjectiveLine.chartMap F (!false)).opensRange) ↔ _
    rw [ProjectiveLine.chartMap_preimage_other]
    let := parameterPolynomialAlgebra f hf
    change q ∈ PrimeSpectrum.basicOpen
      (algebraMap F[X] (parameterChart f hf) Polynomial.X) ↔ _
    rw [zeroOverlap_range]
    rfl
  · change parameterCurveProjection f hf (infinityChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F true).opensRange ↔
        infinityChartInclusion f hf q ∈ Set.range (infinityChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, infinityChart_projection, Scheme.Hom.comp_apply]
    exact iff_of_true ⟨_, rfl⟩ ⟨q, rfl⟩

theorem zeroChartProjection_isPullback :
    IsPullback (zeroChartInclusion f hf) (parameterChartProjection f hf)
      (parameterCurveProjection f hf) (ProjectiveLine.chartMap F false) :=
  (IsOpenImmersion.isPullback _ _ _ _ (zeroChart_projection f hf)
    (parameterCurveProjection_preimage_zero f hf)).flip

theorem infinityChartProjection_isPullback :
    IsPullback (infinityChartInclusion f hf)
      (parameterChartProjection f⁻¹ (transcendental_inverse f hf))
      (parameterCurveProjection f hf) (ProjectiveLine.chartMap F true) :=
  (IsOpenImmersion.isPullback _ _ _ _ (infinityChart_projection f hf)
    (parameterCurveProjection_preimage_infinity f hf)).flip

instance parameterCurveProjection_isFinite [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsFinite (parameterCurveProjection f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let hAffine := AlgebraicGeometry.IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop.{u}
  let : IsZariskiLocalAtTarget (@AlgebraicGeometry.IsFinite.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hAffine
  apply IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.IsFinite.{u})
    (ProjectiveLine.affineChartCover F)
  intro i
  cases i
  · change IsFinite (Limits.pullback.snd (parameterCurveProjection f hf)
      (ProjectiveLine.chartMap F false))
    rw [← (zeroChartProjection_isPullback f hf).isoPullback_inv_snd]
    infer_instance
  · change IsFinite (Limits.pullback.snd (parameterCurveProjection f hf)
      (ProjectiveLine.chartMap F true))
    rw [← (infinityChartProjection_isPullback f hf).isoPullback_inv_snd]
    infer_instance

def parameterCurveStructureMap : parameterCurve f hf ⟶ Spec (.of F) :=
  parameterCurveProjection f hf ≫ ProjectiveLine.structureMap F

instance parameterCurveStructureMap_isProper [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsProper (parameterCurveStructureMap f hf) := by
  unfold parameterCurveStructureMap
  infer_instance

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveFrameNaturality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology Frames
variable {X : Scheme} {U V : X.Opens} (M : X.Modules)
lemma framedSectionsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedSectionsEquiv V M (restrictOpenFrame h e) (M.presheaf.map (homOfLE h).op s) =
      (X.homOfLE h).appTop (framedSectionsEquiv U M e s) := by
  change (restrictOpenFrame h e).hom.app ⊤
    ((restrictionSectionsIso V M).inv (M.presheaf.map (homOfLE h).op s)) =
    (X.homOfLE h).appTop (e.hom.app ⊤ ((restrictionSectionsIso U M).inv s))
  simp only [restrictOpenFrame, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, Iso.app_inv, Iso.app_hom,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    restrictionSectionsIso,
    Scheme.Modules.restrictAppIso]
  let φ := X.homOfLE h
  let W := φ ''ᵁ (⊤ : V.toScheme.Opens)
  let y := (restrictionSectionsIso U M).inv s
  have hn : e.hom.app W ((M.restrict U.ι).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op y) =
      U.toScheme.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (e.hom.app ⊤ y) :=
    CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality (homOfLE (show W ≤ ⊤ from le_top)).op) y
  calc
    _ = (φ.appIso ⊤).hom (e.hom.app W
        ((M.restrict U.ι).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op y)) := by
      change (φ.appIso ⊤).hom (e.hom.app W _) = _
      apply congrArg (φ.appIso ⊤).hom
      apply congrArg (e.hom.app W)
      change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _) s =
        (M.presheaf.map _ ≫ M.presheaf.map _) s
      simp only [← Functor.map_comp]
      congr 2
    _ = (φ.appIso ⊤).hom (U.toScheme.presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op (e.hom.app ⊤ y)) := congrArg _ hn
    _ = _ := by
      change (U.toScheme.presheaf.map _ ≫ (φ.appIso ⊤).hom) (e.hom.app ⊤ y) = _
      rw [Scheme.Hom.appIso_hom']
      simp only [φ, Scheme.Hom.appTop, Scheme.homOfLE_app, Scheme.homOfLE_appLE,
        Scheme.Opens.toScheme_presheaf_map]
      erw [← Functor.map_comp]
      congr 2

lemma framedCoefficientsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedCoefficientsEquiv V M (restrictOpenFrame h e)
      (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (framedCoefficientsEquiv U M e s) := by
  change V.topIso.hom (framedSectionsEquiv V M (restrictOpenFrame h e)
    (M.presheaf.map (homOfLE h).op s)) =
    X.presheaf.map (homOfLE h).op (U.topIso.hom (framedSectionsEquiv U M e s))
  erw [framedSectionsEquiv_restrict, topIso_hom_restrict]

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_FrameCoefficientLaws
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology Frames
variable {X : Scheme} (U : X.Opens) (M : X.Modules)

lemma framedCoefficientsEquiv_smul
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (a : Γ(X,U)) (s : Γ(M,U)) :
    framedCoefficientsEquiv U M e (a • s) =
      a * framedCoefficientsEquiv U M e s := by
  have hs : (restrictionSectionsIso U M).inv (a • s) =
      U.topIso.inv a • (restrictionSectionsIso U M).inv s := by
    change M.presheaf.map (eqToHom U.ι_image_top).op (a • s) =
      (U.ι.appIso ⊤).inv (U.topIso.inv a) •
        M.presheaf.map (eqToHom U.ι_image_top).op s
    rw [M.map_smul, U.ι_appIso]
    rfl
  change U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv (a • s))) =
    a * U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv s))
  rw [hs, e.hom.app_smul]
  change U.topIso.hom (U.topIso.inv a * _) = _
  erw [map_mul]
  erw [Iso.inv_hom_id_apply]

lemma framedCoefficientsEquiv_change
    (e f : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedCoefficientsEquiv U M f s =
      U.topIso.hom (frameChange e f : Γ(U.toScheme,⊤)) *
        framedCoefficientsEquiv U M e s := by
  let t := (restrictionSectionsIso U M).inv s
  have he : e.inv.app ⊤ (e.hom.app ⊤ t) = t := by
    exact congrArg (fun q => q.app ⊤ t) e.hom_inv_id
  have h := end_apply (e.inv ≫ f.hom) ⊤ (e.hom.app ⊤ t)
  change f.hom.app ⊤ (e.inv.app ⊤ (e.hom.app ⊤ t)) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ t) *
      (frameChange e f : Γ(U.toScheme,⊤)) at h
  rw [he, mul_comm] at h
  change U.topIso.hom (f.hom.app ⊤ t) =
    U.topIso.hom (frameChange e f : Γ(U.toScheme,⊤)) * U.topIso.hom (e.hom.app ⊤ t)
  rw [h, map_mul]

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleFrameCocycle
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.LineBundleFrameCocycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ProjectiveChartSections

variable {X : Scheme} {ι : Type} (M : X.Modules) (U : ι → X.Opens)
  (e : ∀ i, M.restrict (U i).ι ≅ structureSheaf (U i).toScheme)

abbrev frame (i : ι) (W : X.Opens) (hi : W ≤ U i) := restrictOpenFrame hi (e i)

abbrev coeff (i : ι) (W : X.Opens) (hi : W ≤ U i) :=
  framedCoefficientsEquiv W M (frame M U e i W hi)

lemma coeff_restrict {V W : X.Opens} (h : V ≤ W) (i : ι) (hi : W ≤ U i)
    (s : Γ(M,W)) :
    coeff M U e i V (h.trans hi) (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (coeff M U e i W hi s) := by
  change framedCoefficientsEquiv V M (restrictOpenFrame (h.trans hi) (e i)) _ = _
  rw [← restrictOpenFrame_trans h hi (e i)]
  exact framedCoefficientsEquiv_restrict M h _ s

def transition (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) : Γ(X,W)ˣ :=
  Units.map W.topIso.hom.hom.toMonoidHom
    (frameChange (frame M U e j W hj) (frame M U e i W hi))

lemma coeff_change (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j)
    (s : Γ(M,W)) :
    coeff M U e i W hi s = (transition M U e i j W hi hj : Γ(X,W)) *
      coeff M U e j W hj s := by
  exact framedCoefficientsEquiv_change W M (frame M U e j W hj) (frame M U e i W hi) s

def ofFrames : LineBundleGluing.Cocycle U where
  transition := transition M U e
  restriction i j {V W} h hi hj := by
    let s := (coeff M U e j W hj).symm 1
    have hj1 : coeff M U e j W hj s = (1 : Γ(X,W)) :=
      (coeff M U e j W hj).apply_symm_apply 1
    have hi1 : coeff M U e i W hi s = (transition M U e i j W hi hj : Γ(X,W)) := by
      rw [coeff_change M U e i j W hi hj, hj1, mul_one]
    have hjV : coeff M U e j V (h.trans hj) (M.presheaf.map (homOfLE h).op s) = 1 := by
      rw [coeff_restrict M U e h j hj, hj1]
      exact map_one (X.presheaf.map (homOfLE h).op).hom
    calc
      _ = X.presheaf.map (homOfLE h).op (coeff M U e i W hi s) := congrArg _ hi1.symm
      _ = coeff M U e i V (h.trans hi) (M.presheaf.map (homOfLE h).op s) :=
        (coeff_restrict M U e h i hi s).symm
      _ = _ := by rw [coeff_change M U e i j V (h.trans hi) (h.trans hj), hjV, mul_one]
  identity i W hi := by
    apply Units.ext
    change W.topIso.hom (endValue ((frame M U e i W hi).inv ≫
      (frame M U e i W hi).hom)) = 1
    simp
  cocycle i j k W hi hj hk := by
    apply Units.ext
    change W.topIso.hom (endValue ((frame M U e j W hj).inv ≫
      (frame M U e i W hi).hom)) *
      W.topIso.hom (endValue ((frame M U e k W hk).inv ≫
        (frame M U e j W hj).hom)) =
      W.topIso.hom (endValue ((frame M U e k W hk).inv ≫
        (frame M U e i W hi).hom))
    rw [← map_mul, mul_comm, ← endValue_comp]
    simp

def toSections (V : X.Opens) (s : Γ(M,V)) : LineBundleGluing.sections (ofFrames M U e) V :=
  ⟨fun p => coeff M U e p.1 p.2.val p.2.property.2
    (M.presheaf.map (homOfLE p.2.property.1).op s), by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op
        (coeff M U e i W hi (M.presheaf.map (homOfLE hW).op s)) = _
      rw [← coeff_restrict]
      congr 1
      change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
      rw [← Functor.map_comp]
      rfl
    · intro i j W hW hi hj
      exact coeff_change M U e i j W hi hj _⟩

lemma chartEquiv_toSections (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : Γ(M,V)) :
    LineBundleGluing.chartEquiv (ofFrames M U e) i hi (toSections M U e V s) =
      coeff M U e i V hi s := by
  change coeff M U e i V hi (M.presheaf.map (homOfLE (le_refl V)).op s) = _
  simp

lemma toSections_bijective (i : ι) (V : X.Opens) (hi : V ≤ U i) :
    Function.Bijective (toSections M U e V) := by
  constructor
  · intro s t h
    apply (coeff M U e i V hi).injective
    simpa only [chartEquiv_toSections] using
      congrArg (LineBundleGluing.chartEquiv (ofFrames M U e) i hi) h
  · intro t
    refine ⟨(coeff M U e i V hi).symm
      (LineBundleGluing.chartEquiv (ofFrames M U e) i hi t), ?_⟩
    apply (LineBundleGluing.chartEquiv (ofFrames M U e) i hi).injective
    rw [chartEquiv_toSections, AddEquiv.apply_symm_apply]

def presheafHom : M.val ⟶ LineBundleGluing.presheaf (ofFrames M U e) where
  app V := ModuleCat.ofHom
    (X := M.val.obj V)
    (Y := (LineBundleGluing.presheaf (ofFrames M U e)).obj V)
    { toFun := toSections M U e V.unop
      map_add' := by
        intro s t
        apply Subtype.ext
        funext p
        change coeff M U e p.1 p.2.val p.2.property.2
          (M.presheaf.map (homOfLE p.2.property.1).op (s + t)) = _
        erw [map_add]
        exact map_add _ _ _
      map_smul' := by
        intro a s
        apply Subtype.ext
        funext p
        change coeff M U e p.1 p.2.val p.2.property.2
          (M.presheaf.map (homOfLE p.2.property.1).op (a • s)) =
          X.presheaf.map (homOfLE p.2.property.1).op a *
            coeff M U e p.1 p.2.val p.2.property.2
              (M.presheaf.map (homOfLE p.2.property.1).op s)
        erw [M.map_smul]
        exact framedCoefficientsEquiv_smul _ _ _ _ _ }
  naturality {V W} f := by
    ext s
    apply Subtype.ext
    funext p
    change coeff M U e p.1 p.2.val p.2.property.2
      (M.presheaf.map (homOfLE p.2.property.1).op (M.presheaf.map f s)) =
      coeff M U e p.1 p.2.val p.2.property.2 (M.presheaf.map _ s)
    congr 1
    change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
    rw [← Functor.map_comp]
    rfl

lemma restrict_presheafHom_isIso (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (presheafHom M U e)) := by
  let f := (modulePresheafRestrict (U i).ι).map (presheafHom M U e)
  have (V : (U i).toScheme.Opensᵒᵖ) : IsIso (f.app V) := by
    apply (ConcreteCategory.isIso_iff_bijective (f.app V)).mpr
    exact toSections_bijective M U e i ((U i).ι ''ᵁ V.unop) ((U i).ι_image_le V.unop)
  let a := PresheafOfModules.isoMk (fun V => asIso (f.app V))
    (fun {_ _} k => f.naturality k)
  change IsIso a.hom
  infer_instance

lemma sheafification_presheafHom_isIso (hcover : ⊤ ≤ ⨆ i, U i) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (presheafHom M U e)) := by
  apply SectionOpens.isIso_of_locally_isIso
  intro x
  have hx : x ∈ ⨆ i, U i := hcover (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨U i, hi, ?_⟩
  let := restrict_presheafHom_isIso M U e i
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict (U i).ι)
    (presheafHom M U e)).mpr
  change IsIso ((PresheafOfModules.sheafification (𝟙 (U i).toScheme.ringCatSheaf.obj)).map
    ((modulePresheafRestrict (U i).ι).map (presheafHom M U e)))
  infer_instance

def isoSheaf (hcover : ⊤ ≤ ⨆ i, U i) :
    M ≅ LineBundleGluing.sheaf (ofFrames M U e) := by
  letI := sheafification_presheafHom_isIso M U e hcover
  exact ((asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).counit).app M).symm ≪≫
    @asIso _ _ _ _
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (presheafHom M U e))
      (sheafification_presheafHom_isIso M U e hcover)

end
end PiExponentSeshadri.LineBundleFrameCocycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PullbackFrameCoefficient
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.PullbackFrameCoefficient

theorem exists_frame_natIso_all {X Y : Scheme.{0}}
    (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) :
    ∃ eF : F.obj M ≅ O Y, ∀ s : O X ⟶ M,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  intro s
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b (uG.inv ≫ G.map s ≫ e.hom)

end PiExponent.PullbackFrameCoefficient

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectivePullbackFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

theorem exists_restricted_pullback_frame_all_of_factor
    (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict V.ι ≅ O V.toScheme,
      ∀ s : O X ⟶ M,
      coefficient eF (restrictSection V.ι (pullbackSection f s)) =
        g.appTop (coefficient e (restrictSection U.ι s)) := by
  let F : X.Modules ⥤ V.toScheme.Modules :=
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι
  let G : X.Modules ⥤ V.toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g
  let uF : F.obj (O X) ≅ O V.toScheme :=
    (Scheme.Modules.restrictFunctor V.ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso V.ι
  let uG : G.obj (O X) ≅ O V.toScheme :=
    (Scheme.Modules.pullback g).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso g
  obtain ⟨eF, he⟩ := PiExponent.PullbackFrameCoefficient.exists_frame_natIso_all
    F G (pullbackRestrictFactorNatIso f U V g h) uF uG (pullbackFrame g e)
  refine ⟨eF, fun s => ?_⟩
  have hs : coefficient eF (restrictSection V.ι (pullbackSection f s)) =
      coefficient (pullbackFrame g e) (pullbackSection g (restrictSection U.ι s)) := by
    let P : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback f
    let R : Y.Modules ⥤ V.toScheme.Modules :=
      Scheme.Modules.restrictFunctor V.ι
    let S : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let Q : U.toScheme.Modules ⥤ V.toScheme.Modules :=
      Scheme.Modules.pullback g
    let p : P.obj (O X) ≅ O Y := pullbackUnitIso f
    let r : R.obj (O Y) ≅ O V.toScheme :=
      Scheme.Modules.restrictUnitIso V.ι
    let a : S.obj (O X) ≅ O U.toScheme := Scheme.Modules.restrictUnitIso U.ι
    let q : Q.obj (O U.toScheme) ≅ O V.toScheme := pullbackUnitIso g
    have hl : restrictSection V.ι (pullbackSection f s) = uF.inv ≫ F.map s := by
      change r.inv ≫ R.map (p.inv ≫ P.map s) = (r.inv ≫ R.map p.inv) ≫ R.map (P.map s)
      exact (congrArg (fun k => r.inv ≫ k) (R.map_comp p.inv (P.map s))).trans
        (Category.assoc r.inv (R.map p.inv) (R.map (P.map s))).symm
    have hr : pullbackSection g (restrictSection U.ι s) = uG.inv ≫ G.map s := by
      change q.inv ≫ Q.map (a.inv ≫ S.map s) = (q.inv ≫ Q.map a.inv) ≫ Q.map (S.map s)
      exact (congrArg (fun k => q.inv ≫ k) (Q.map_comp a.inv (S.map s))).trans
        (Category.assoc q.inv (Q.map a.inv) (Q.map (S.map s))).symm
    exact (congrArg (coefficient eF) hl).trans
      ((he s).trans (congrArg (coefficient (pullbackFrame g e)) hr).symm)
  rw [hs, coefficient_pullback]

theorem exists_restricted_pullback_frame_all (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      ∀ s : O X ⟶ M,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) :=
  exists_restricted_pullback_frame_all_of_factor f U (f ⁻¹ᵁ U) (f ∣_ U)
    (morphismRestrict_ι f U).symm e

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionsPullback
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] {X Y : Scheme.{0}}

lemma pullback_isoOpen_le {M : X.Modules} (s : O X ⟶ M) (f : Y ⟶ X) :
    f ⁻¹ᵁ SectionOpens.isoOpen s ≤ SectionOpens.isoOpen (pullbackSection f s) := by
  let U := SectionOpens.isoOpen s
  obtain ⟨e,he⟩ := exists_restricted_pullback_frame_all f U (sectionFrame s)
  have hn : coefficient e (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) = 1 := by
    rw [he,sectionFrame_normalized,map_one]
  have hp : (f ⁻¹ᵁ U).ι ⁻¹ᵁ SectionOpens.isoOpen (pullbackSection f s) = ⊤ := by
    rw [preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι e, hn]
    exact (isUnit_iff_basicOpen_top _).mp isUnit_one
  intro x hx
  have h : (⟨x,hx⟩ : (f ⁻¹ᵁ U).toScheme) ∈
      (f ⁻¹ᵁ U).ι ⁻¹ᵁ SectionOpens.isoOpen (pullbackSection f s) := by rw [hp]; trivial
  exact h

lemma pullback_sections_cover {M : X.Modules} (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (f : Y ⟶ X) :
    (⨆ i, SectionOpens.isoOpen (pullbackSection f (s i))) = ⊤ := by
  apply top_le_iff.mp
  rw [← Scheme.Hom.preimage_top f, ← hs, Scheme.Hom.preimage_iSup]
  exact iSup_mono fun i => pullback_isoOpen_le (s i) f

end
end PiExponentSeshadri.Projective

end OAI
end


