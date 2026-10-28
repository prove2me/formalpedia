-- Prove2me | Definitions.Def_OAIQ068A023
-- name    : OAIQ068A023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:54:45.520987+00:00
-- url     : https://prove2.me/theorems/2d40a5e8-8766-45b8-99a6-3f40e97c5f5d
-- title:
--   Definitions bundle OAIQ068A023 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 138 declarations of OpenAI's Lean: 68 definitions, 10 instances and 60 theorems. The definitions and types are `OAI.PiExponent.CurveFinitePushforwardCohomology.sectionsEquiv`, `OAI.PiExponent.CurveNormalizationModel.parameterCurveFunctionFieldEquiv`, `OAI.PiExponent.CurveNormalizationModel.parameterCurveOpenCover`, `OAI.PiExponent.GeometrySupport.CechExtFinite.LocallyAcyclic`, `OAI.PiExponent.GeometrySupport.CechExtFinite.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.CechHigher.Cochain`, `OAI.PiExponent.GeometrySupport.CechHigher.HasPrimitives`, `OAI.PiExponent.GeometrySupport.CechHigher.augmentation`, `OAI.PiExponent.GeometrySupport.CechHigher.differential`, `OAI.PiExponent.GeometrySupport.CechHigher.evaluate`, `OAI.PiExponent.GeometrySupport.CechHigher.map`, `OAI.PiExponent.GeometrySupport.CechHigher.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.CechHigher.sectionZero`, `OAI.PiExponent.GeometrySupport.CechLinear.Cochain`, `OAI.PiExponent.GeometrySupport.CechLinear.boundaryToCycles`, `OAI.PiExponent.GeometrySupport.CechLinear.cycles`, `OAI.PiExponent.GeometrySupport.CechLinear.differentialLinear`, `OAI.PiExponent.GeometrySupport.CechLinear.freeOpenHomAddCommGroup`, `OAI.PiExponent.GeometrySupport.CechLinear.freeOpenHomModule`, `OAI.PiExponent.GeometrySupport.CechLinear.higherCochainAddCommGroup`, `OAI.PiExponent.GeometrySupport.CechLinear.mapCycles`, `OAI.PiExponent.GeometrySupport.CechLinear.mapLinear`, `OAI.PiExponent.GeometrySupport.CechLinear.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.CechOne.restrictHom`, `OAI.PiExponent.GeometrySupport.FreeCechSections.canonicalTuple`, `OAI.PiExponent.GeometrySupport.FreeCechSections.generator`, `OAI.PiExponent.GeometrySupport.FreeCechSections.tupleEmbedding`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.chartToFull`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.laurentToFull`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.overlapToFull`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentTransitions.zeroDegreeExponent`, `OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.freeOpenHomCongr`, `OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.schemeFreeOpen`, `OAI.PiExponent.GlobalSectionClearing.affineOpenPrincipalEquiv`, `OAI.PiExponent.GlobalSectionClearing.affineOpenTopEquiv`, `OAI.PiExponent.GlobalSectionClearing.restrictedOpenSections`, `OAI.PiExponent.GlueGlobalGenerators.globalGenerators`, `OAI.PiExponent.PlaceParameterModel.parameterCenterLocalAlgEquiv`, `OAI.PiExponent.PlaceParameterModel.parameterCenterLocalRingEquiv`, `OAI.PiExponent.ProjectivePencil.scalars` and 28 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Approximation_CoherentTwistPresentation`, `PiExponent_Approximation_GlobalSectionClearing`, `PiExponent_Approximation_GlueGlobalGenerators`, `PiExponent_Approximation_ProjectionFormula`, `PiExponent_Cohomology_CechExtFinite`, `PiExponent_Cohomology_CechHigher`, `PiExponent_Cohomology_CechLinear`, `PiExponent_Cohomology_CechOne`, `PiExponent_Cohomology_CurveEuler`, `PiExponent_Cohomology_CurveFinitePushforwardCohomology`, `PiExponent_Cohomology_FiniteCoverCohomology`, `PiExponent_Cohomology_FreeCechSections`, `PiExponent_Cohomology_PencilCohomology`, `PiExponent_Cohomology_PencilCohomologyCech`, `PiExponent_Cohomology_PencilCohomologyCharts`, `PiExponent_Cohomology_PencilCohomologyFiniteCharts`, `PiExponent_Cohomology_PencilCohomologyPencil`, `PiExponent_Cohomology_PencilCohomologySections`, `PiExponent_Cohomology_ProjectiveFramedCech`, `PiExponent_Cohomology_ProjectiveLaurentTransitions`, `PiExponent_Geometry_CurveNormalizationDimension`, `PiExponent_Geometry_CurveNormalizationModel`, `PiExponent_Geometry_PlaceParameterModel`, `PiExponent_Geometry_ProjectiveCoordinateRatios`, `PiExponent_Geometry_ProjectiveCurveTwoAffine`, `PiExponent_Geometry_ProjectiveFinitePencil`, `PiExponent_Geometry_ProjectivePencilScalars`, `PiExponent_Geometry_ProjectiveTupleCharts`, `PiExponent_Geometry_SheafSectionGluing`.
--
--   **Imports.** It imports the bundles `OAIQ068A012`, `OAIQ068A013`, `OAIQ068A014` and `OAIQ068A015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A029`, `OAIQ068A030`, `OAIQ068A031`, `OAIQ068A032`, `OAIQ068A033` and `OAIQ068A034`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A012
import Definitions.Def_OAIQ068A013
import Definitions.Def_OAIQ068A014
import Definitions.Def_OAIQ068A015

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteCoverCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace ModuleFlasque
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpenEquiv_naturality (M : SheafOfModules.{u} R) {U V : Opens X}
    (i : U ⟶ V) (f : freeOpen R V ⟶ M) :
    freeOpenEquiv R M U (freeOpenMap R i ≫ f) =
      M.val.map i.op (freeOpenEquiv R M V f) := by
  unfold freeOpenEquiv
  dsimp only [Equiv.trans_apply]
  change PresheafOfModules.freeYonedaEquiv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ (_ ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact freeYoneda_naturality R i
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) f)

end ModuleFlasque

namespace ModuleMayerVietoris
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpen_isPushout (U V : Opens X) :
    ((Opens.mayerVietorisSquare U V).toSquare.map (freeOpenFunctor R)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro M
  have h := (Opens.mayerVietorisSquare U V).sheafCondition_of_sheaf
    ((sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M))
  apply (Square.IsPullback.iff_of_equiv _ _
    (freeOpenEquiv R M (U ⊔ V)) (freeOpenEquiv R M U)
    (freeOpenEquiv R M V) (freeOpenEquiv R M (U ⊓ V))
    ?_ ?_ ?_ ?_).mpr h
  all_goals
    ext f
    exact freeOpenEquiv_naturality R M _ f

def shortComplex (U V : Opens X) : ShortComplex (SheafOfModules.{u} R) where
  X₁ := freeOpen R (U ⊓ V)
  X₂ := freeOpen R U ⊞ freeOpen R V
  X₃ := freeOpen R (U ⊔ V)
  f := biprod.lift (freeOpenMap R (homOfLE inf_le_left))
    (-(freeOpenMap R (homOfLE inf_le_right)))
  g := biprod.desc (freeOpenMap R (homOfLE le_sup_left))
    (freeOpenMap R (homOfLE le_sup_right))
  zero := ((Opens.mayerVietorisSquare U V).toSquare.map
    (freeOpenFunctor R)).cokernelCofork.condition

end ModuleMayerVietoris

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentTwistPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace PiExponentSeshadri.Geometry
open MonoidalCategory
variable {X : Scheme}

def moduleTwistUnitIso (L : LineBundle X) : ∀ n : ℕ,
    (moduleTwistFunctor L n).obj (structureSheaf X) ≅ modulePow X L.sheaf n
  | 0 => Iso.refl _
  | n+1 => moduleTensorIso (moduleTwistUnitIso L n) (Iso.refl L.sheaf) ≪≫
      moduleTensorComm (modulePow X L.sheaf n) L.sheaf

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalSectionClearing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
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

def restrictedOpenSections (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : Y.Opens) :
    letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
    OpenSections (M.restrict f) U ≃ₗ[Γ(X,⊤)] OpenSections M (f ''ᵁ U) := by
  letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
  letI : Module Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) := (M.val.obj (op (f ''ᵁ U))).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _
      ((f.appIso U).inv (restrictScalar Y U (f.appTop r))) m =
    @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _ (restrictScalar X (f ''ᵁ U) r) m
  rw [restrictScalar_appIso]

def affineOpenPrincipalEquiv (M : X.Modules) (r : Γ(X,⊤)) (U : X.Opens) :
    letI := Module.compHom (OpenSections (M.restrict U.ι)
      (U.toScheme.basicOpen (U.ι.appTop r))) U.ι.appTop.hom
    OpenSections (M.restrict U.ι) (U.toScheme.basicOpen (U.ι.appTop r)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (U ⊓ X.basicOpen r) :=
  (restrictedOpenSections M U.ι _).trans (openSectionsCongr M (principal_open_image r U))

def affineOpenTopEquiv (M : X.Modules) (U : X.Opens) :
    letI := Module.compHom (OpenSections (M.restrict U.ι) ⊤) U.ι.appTop.hom
    OpenSections (M.restrict U.ι) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections M U :=
  (restrictedOpenSections M U.ι ⊤).trans (openSectionsCongr M U.ι_image_top)

end
end PiExponent.GlobalSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlueGlobalGenerators
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GlueGlobalGenerators
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
  (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
  (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections)
  (t : ∀ i, (σ i).I → GlobalSections X M)
  (ht : ∀ i j, restrictSection (U i).ι (t i j) =
    (M.restrict (U i).ι).unitHomEquiv.symm ((σ i).s j))

include hcover ht

theorem globalEvaluation_epi : Epi
    (M.freeHomEquiv.symm (fun ij : Σ i, (σ i).I => M.unitHomEquiv (t ij.1 ij.2))) := by
  let q := M.freeHomEquiv.symm (fun ij : Σ i, (σ i).I => M.unitHomEquiv (t ij.1 ij.2))
  have hq (i : ι) (j : (σ i).I) : SheafOfModules.ιFree ⟨i,j⟩ ≫ q = t i j := by
    erw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp only [q, Equiv.apply_symm_apply]
    exact M.unitHomEquiv.symm_apply_apply (t i j)
  change Epi (C := X.Modules) q
  apply (Preadditive.epi_iff_cancel_zero (C := X.Modules) q).mpr
  intro N g hg
  have hz (i : ι) (j : (σ i).I) : t i j ≫ g = 0 := by
    erw [← hq i j, Category.assoc, hg, comp_zero]
  apply CoherentTwist.eq_zero_of_local
  intro x
  have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  refine ⟨U i,hxi,?_⟩
  apply (@cancel_epi _ _ _ _ _ (σ i).π (σ i).epi _ _).mp
  erw [comp_zero]
  apply (SheafOfModules.isColimitFreeCofan (σ i).I).hom_ext
  intro j
  change SheafOfModules.ιFree j.as ≫ ((σ i).π ≫
    (Scheme.Modules.restrictFunctor (U i).ι).map g) = SheafOfModules.ιFree j.as ≫ 0
  erw [comp_zero, ← Category.assoc,
    ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply]
  erw [← ht i j.as]
  let R : X.Modules ⥤ (U i).toScheme.Modules := Scheme.Modules.restrictFunctor (U i).ι
  let e : R.obj (O X) ≅ O (U i).toScheme := Scheme.Modules.restrictUnitIso (U i).ι
  change (e.inv ≫ R.map (t i j.as)) ≫ R.map g = 0
  erw [Category.assoc, ← Functor.map_comp, hz, Functor.map_zero, comp_zero]

def globalGenerators : M.GeneratingSections where
  I := Σ i, (σ i).I
  s ij := M.unitHomEquiv (t ij.1 ij.2)
  epi := globalEvaluation_epi M U hcover σ t ht

instance instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme [Finite ι] [hσ : ∀ i, (σ i).IsFiniteType] :
    (globalGenerators M U hcover σ t ht).IsFiniteType where
  finite := by
    let (i : ι) : Finite (σ i).I := (hσ i).finite
    exact inferInstanceAs (Finite (Σ i, (σ i).I))

theorem exists_finite_global_generators [Finite ι] [∀ i, (σ i).IsFiniteType] :
    ∃ q : M.GeneratingSections, q.IsFiniteType :=
  ⟨globalGenerators M U hcover σ t ht, inferInstance⟩

end
end PiExponent.GlueGlobalGenerators

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ProjectionFormula
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectionFormula
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma pullback_unit_apply (U : Y.Opens) (a : Γ(Y,U)) :
    (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureSheaf Y)).app U a) =
    (f.app U) a := by
  have hu := congrArg (fun q => q.app U a) (pullbackUnit_adjunction f)
  exact hu

end
end PiExponent.ProjectionFormula

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechOne
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechOne

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def restrictHom {M : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f : freeOpen R V ⟶ M) : freeOpen R U ⟶ M :=
  freeOpenMap R (homOfLE h) ≫ f

@[simp] theorem restrictHom_restrictHom {M : SheafOfModules.{u} R} {U V W : Opens X}
    (h : U ≤ V) (k : V ≤ W) (f : freeOpen R W ⟶ M) :
    restrictHom R h (restrictHom R k f) = restrictHom R (h.trans k) f := by
  change (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (homOfLE h) ≫
      (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (homOfLE k) ≫ f =
    (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (homOfLE (h.trans k)) ≫ f
  erw [← Category.assoc, ← Functor.map_comp]
  rfl

@[simp] theorem restrictHom_comp {M N : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f : freeOpen R V ⟶ M) (g : M ⟶ N) :
    restrictHom R h (f ≫ g) = restrictHom R h f ≫ g := by
  simp only [restrictHom, Category.assoc]

@[simp] theorem restrictHom_add {M : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f g : freeOpen R V ⟶ M) :
    restrictHom R h (f + g) = restrictHom R h f + restrictHom R h g := by
  simp only [restrictHom, Preadditive.comp_add]

@[simp] theorem restrictHom_sub {M : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f g : freeOpen R V ⟶ M) :
    restrictHom R h (f - g) = restrictHom R h f - restrictHom R h g := by
  simp only [restrictHom, Preadditive.comp_sub]

end
end PiExponent.GeometrySupport.CechOne

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open CechOne
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

abbrev Cochain (q : ℕ) :=
  ∀ t : Fin (q + 1) → J, freeOpen R (intersection U t) ⟶ M

def differential {q : ℕ} (c : Cochain R U M q) : Cochain R U M (q + 1) :=
  fun t => ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
    restrictHom R (faceLE U t k) (c (t ∘ k.succAbove))

def HasPrimitives (q : ℕ) : Prop :=
  ∀ c : Cochain R U M (q + 1), differential R U M c = 0 →
    ∃ b : Cochain R U M q, differential R U M b = c

@[simp] theorem restrictHom_refl {W : Opens X} (f : freeOpen R W ⟶ M) :
    restrictHom R le_rfl f = f := by
  change (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (𝟙 W) ≫ f = f
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp f

@[simp] theorem restrictHom_sum {W V : Opens X} (h : W ≤ V)
    {T : Type*} (s : Finset T) (f : T → (freeOpen R V ⟶ M)) :
    restrictHom R h (∑ i ∈ s, f i) = ∑ i ∈ s, restrictHom R h (f i) := by
  simp only [restrictHom, Preadditive.comp_sum]

@[simp] theorem restrictHom_zsmul {W V : Opens X} (h : W ≤ V)
    (z : ℤ) (f : freeOpen R V ⟶ M) :
    restrictHom R h (z • f) = z • restrictHom R h f := by
  simp only [restrictHom, Preadditive.comp_zsmul]

def evaluate {L : Type*} (W : Opens X) (f : L → J)
    (hf : ∀ l, W ≤ U (f l)) {q : ℕ} (c : Cochain R U M q) :
    ProjectiveMonomialCechHigher.Cochain L (freeOpen R W ⟶ M) q :=
  fun t => restrictHom R (le_iInf fun i => hf (t i)) (c (f ∘ t))

theorem evaluate_differential {L : Type*} (W : Opens X) (f : L → J)
    (hf : ∀ l, W ≤ U (f l)) {q : ℕ} (c : Cochain R U M q) :
    evaluate R U M W f hf (differential R U M c) =
      ProjectiveMonomialCechHigher.differential (evaluate R U M W f hf c) := by
  funext t
  simp only [evaluate, differential, ProjectiveMonomialCechHigher.differential]
  erw [restrictHom_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [restrictHom_zsmul, restrictHom_restrictHom]
  rfl

theorem differential_squared {q : ℕ} (c : Cochain R U M q) :
    differential R U M (differential R U M c) = 0 := by
  funext t
  let W := intersection U t
  have hf : ∀ i, W ≤ U (t i) := fun i => iInf_le (fun j => U (t j)) i
  have h := congrFun (ProjectiveMonomialCechHigher.differential_squared
    (evaluate R U M W t hf c)) id
  rw [← evaluate_differential, ← evaluate_differential] at h
  change restrictHom R le_rfl (differential R U M (differential R U M c) t) = 0 at h
  simpa only [restrictHom_refl, Pi.zero_apply] using h

def map {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c : Cochain R U M q) : Cochain R U N q := fun t => c t ≫ g

theorem map_differential {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c : Cochain R U M q) :
    map R U M g (differential R U M c) = differential R U N (map R U M g c) := by
  funext t
  simp only [map, differential, Preadditive.sum_comp, Preadditive.zsmul_comp,
    restrictHom_comp]

@[simp] theorem differential_zero {q : ℕ} :
    differential R U M (0 : Cochain R U M q) = 0 := by
  funext t
  simp only [differential, Pi.zero_apply, restrictHom, comp_zero, smul_zero,
    Finset.sum_const_zero]

theorem differential_sub {q : ℕ} (c e : Cochain R U M q) :
    differential R U M (c - e) = differential R U M c - differential R U M e := by
  funext t
  simp only [differential, Pi.sub_apply, restrictHom_sub, smul_sub, Finset.sum_sub_distrib]

@[simp] theorem map_zero {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ} :
    map R U M g (0 : Cochain R U M q) = 0 := by
  funext t
  exact zero_comp

def sectionZero (c : Cochain R U M 0) (i : J) : freeOpen R (U i) ⟶ M :=
  restrictHom R (le_iInf fun _ => le_rfl) (c (fun _ => i))

def augmentation (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (f : freeOpen R V ⟶ M) : Cochain R U M 0 :=
  fun t => restrictHom R ((iInf_le (fun j => U (t j)) 0).trans (hUV (t 0))) f

@[simp] theorem augmentation_closed (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (f : freeOpen R V ⟶ M) : differential R U M (augmentation R U M V hUV f) = 0 := by
  funext t
  simp only [differential, augmentation, Pi.zero_apply]
  calc
    _ = ∑ k : Fin 2, (-1 : ℤ) ^ k.val •
        restrictHom R ((iInf_le (fun j => U (t j)) 0).trans (hUV (t 0))) f := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun g : freeOpen R (intersection U t) ⟶ M => (-1 : ℤ) ^ k.val • g)
        (restrictHom_restrictHom R _ _ f)
    _ = 0 := by rw [Fin.sum_univ_two]; simp

@[simp] theorem sectionZero_augmentation (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (f : freeOpen R V ⟶ M) (i : J) :
    sectionZero R U M (augmentation R U M V hUV f) i = restrictHom R (hUV i) f := by
  simp only [sectionZero, augmentation]
  exact restrictHom_restrictHom R _ _ f

abbrev schemeFreeOpen (Y : Scheme.{u}) (V : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveEuler
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian Opposite
variable {X : Scheme}

def globalHomLinearEquiv (M : X.Modules) :
    GlobalSections X M ≃ₗ[Γ(X,⊤)] Γ(M,⊤) where
  toEquiv := FlasqueCohomology.globalHomEquiv X.ringCatSheaf M
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    change restrictScalar X ⊤ r • f.app ⊤ (1 : Γ(X,⊤)) = r • f.app ⊤ (1 : Γ(X,⊤))
    congr 1
    change (X.presheaf.map (𝟙 (op ⊤))) r = r
    rw [X.presheaf.map_id]
    rfl

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FreeCechSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.FreeCechSections

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechHigher FreeCechResolution
open scoped Simplicial BigOperators

universe u
variable {X : TopCat.{u}} {J : Type u} (U : J → Opens X)

def canonicalTuple {q : ℕ} (t : Fin (q + 1) → J) :
    ((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)).obj (op (intersection U t)) :=
  fun i => ⟨t i, iInf_le (fun j => U (t j)) i⟩

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (M : SheafOfModules.{u} R)

def tupleEmbedding {q : ℕ} (t : Fin (q + 1) → J) :
    yoneda.obj (intersection U t) ⟶ (tuplePresheaf (coverVertices U)).obj (op ⦋q⦌) :=
  yonedaEquiv.symm (canonicalTuple U t)

def generator {q : ℕ} (t : Fin (q + 1) → J) :
    freeOpen R (intersection U t) ⟶ freeTerm U R q :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (tupleEmbedding U t))

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.FreeCechSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechLinear
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechLinear

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped BigOperators AlgebraicGeometry

universe v
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
  {K : Type v} [Field K]

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

@[instance_reducible] def freeOpenHomAddCommGroup (V : X.Opens) (M : X.Modules) :
    AddCommGroup (freeOpen X.ringCatSheaf V ⟶ M) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen V ⟶ M))

@[instance_reducible] def higherCochainAddCommGroup (M : X.Modules) (q : ℕ) :
    AddCommGroup (CechHigher.Cochain X.ringCatSheaf U M q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen (CechHigher.intersection U t) ⟶ M))

attribute [local instance] freeOpenHomAddCommGroup higherCochainAddCommGroup

@[instance_reducible] def freeOpenHomModule (V : X.Opens) (M : X.Modules) :
    Module Γ(X, ⊤) (freeOpen X.ringCatSheaf V ⟶ M) :=
  sheafHomModule X (schemeFreeOpen V) M

attribute [local instance] freeOpenHomModule

def Cochain (_ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) : Type :=
  CechHigher.Cochain X.ringCatSheaf U M q

instance cochainAddCommGroup (ρ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    AddCommGroup (Cochain U ρ M q) :=
  inferInstanceAs (AddCommGroup (CechHigher.Cochain X.ringCatSheaf U M q))

instance cochainGlobalModule (ρ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    Module Γ(X, ⊤) (Cochain U ρ M q) :=
  letI (t : Fin (q + 1) → J) :
      Module Γ(X, ⊤) (freeOpen X.ringCatSheaf (CechHigher.intersection U t) ⟶ M) :=
    sheafHomModule X _ M
  inferInstanceAs (Module Γ(X, ⊤) (CechHigher.Cochain X.ringCatSheaf U M q))

instance cochainModule (ρ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    Module K (Cochain U ρ M q) :=
  Module.compHom _ ρ

variable (ρ : K →+* Γ(X, ⊤)) (M : X.Modules)

def differentialLinear (q : ℕ) : Cochain U ρ M q →ₗ[K] Cochain U ρ M (q + 1) where
  toFun := CechHigher.differential X.ringCatSheaf U M
  map_add' c e := by
    let D : Cochain U ρ M q → Cochain U ρ M (q + 1) :=
      CechHigher.differential X.ringCatSheaf U M
    have hsub (c e : Cochain U ρ M q) : D (c - e) = D c - D e :=
      CechHigher.differential_sub X.ringCatSheaf U M c e
    have hzero : D 0 = 0 := CechHigher.differential_zero X.ringCatSheaf U M
    have hn : D (-e) = -D e := by
      simpa only [zero_sub, hzero] using hsub 0 e
    change D (c + e) = D c + D e
    simpa only [sub_neg_eq_add, hn] using hsub c (-e)
  map_smul' r c := by
    let (A B : SheafOfModules.{0} X.ringCatSheaf) : Module Γ(X, ⊤) (A ⟶ B) := sheafHomModule X A B
    let : Linear Γ(X, ⊤) (SheafOfModules.{0} X.ringCatSheaf) := sheafLinear X
    funext t
    change (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
      CechOne.restrictHom X.ringCatSheaf (CechHigher.faceLE U t k)
        (ρ r • c (t ∘ k.succAbove))) =
      ρ r • (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        CechOne.restrictHom X.ringCatSheaf (CechHigher.faceLE U t k)
          (c (t ∘ k.succAbove)))
    simp only [CechOne.restrictHom, Finset.smul_sum, smul_comm (ρ r)]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun f : schemeFreeOpen (CechHigher.intersection U t) ⟶ M =>
      (-1 : ℤ) ^ k.val • f)
      (Linear.comp_smul (C := X.Modules) _ _ _
        (freeOpenMap X.ringCatSheaf (homOfLE (CechHigher.faceLE U t k))) (ρ r)
        (c (t ∘ k.succAbove)))

@[simp] theorem differentialLinear_apply (q : ℕ) (c : Cochain U ρ M q) :
    differentialLinear U ρ M q c = CechHigher.differential X.ringCatSheaf U M c := rfl

def cycles (q : ℕ) : Submodule K (Cochain U ρ M q) :=
  (differentialLinear U ρ M q).ker

@[simp] theorem mem_cycles (q : ℕ) (c : Cochain U ρ M q) :
    c ∈ cycles U ρ M q ↔ CechHigher.differential X.ringCatSheaf U M c = 0 := Iff.rfl

def boundaryToCycles (q : ℕ) : Cochain U ρ M q →ₗ[K] cycles U ρ M (q + 1) :=
  (differentialLinear U ρ M q).codRestrict (cycles U ρ M (q + 1))
    (fun c => CechHigher.differential_squared X.ringCatSheaf U M c)

@[simp] theorem boundaryToCycles_val (q : ℕ) (c : Cochain U ρ M q) :
    (boundaryToCycles U ρ M q c).val =
      CechHigher.differential X.ringCatSheaf U M c := rfl

variable {M} {N P : X.Modules}

def mapLinear (g : M ⟶ N) (q : ℕ) : Cochain U ρ M q →ₗ[K] Cochain U ρ N q where
  toFun := CechHigher.map X.ringCatSheaf U M g
  map_add' c e := by
    funext t
    change (c t + e t) ≫ g = c t ≫ g + e t ≫ g
    exact Preadditive.add_comp (C := SheafOfModules.{0} X.ringCatSheaf) _ _ _ (c t) (e t) g
  map_smul' r c := by
    let (A B : SheafOfModules.{0} X.ringCatSheaf) : Module Γ(X, ⊤) (A ⟶ B) := sheafHomModule X A B
    let : Linear Γ(X, ⊤) (SheafOfModules.{0} X.ringCatSheaf) := sheafLinear X
    funext t
    exact Linear.smul_comp (C := SheafOfModules.{0} X.ringCatSheaf) _ _ _ (ρ r) (c t) g

@[simp] theorem mapLinear_apply (g : M ⟶ N) (q : ℕ) (c : Cochain U ρ M q) :
    mapLinear U ρ g q c = CechHigher.map X.ringCatSheaf U M g c := rfl

@[simp] theorem mapLinear_comp (g : M ⟶ N) (h : N ⟶ P) (q : ℕ) :
    mapLinear U ρ (g ≫ h) q = (mapLinear U ρ h q).comp (mapLinear U ρ g q) := by
  apply LinearMap.ext
  intro c
  funext t
  exact (Category.assoc (c t) g h).symm

@[simp] theorem mapLinear_zero (q : ℕ) :
    mapLinear U ρ (0 : M ⟶ N) q = 0 := by
  apply LinearMap.ext
  intro c
  funext t
  exact comp_zero (C := SheafOfModules.{0} X.ringCatSheaf)

def mapCycles (g : M ⟶ N) (q : ℕ) : cycles U ρ M q →ₗ[K] cycles U ρ N q :=
  ((mapLinear U ρ g q).comp (cycles U ρ M q).subtype).codRestrict
    (cycles U ρ N q) (fun c => by
      change CechHigher.differential X.ringCatSheaf U N
        (CechHigher.map X.ringCatSheaf U M g c.val) = 0
      have hc : CechHigher.differential X.ringCatSheaf U M c.val = 0 := c.property
      exact (CechHigher.map_differential X.ringCatSheaf U M g c.val).symm.trans
        ((congrArg (fun c : Cochain U ρ M (q + 1) => CechHigher.map X.ringCatSheaf U M g c) hc).trans
          (CechHigher.map_zero X.ringCatSheaf U M g)))

@[simp] theorem mapCycles_val (g : M ⟶ N) (q : ℕ) (c : cycles U ρ M q) :
    (mapCycles U ρ g q c).val = mapLinear U ρ g q c.val := rfl

end
end PiExponent.GeometrySupport.CechLinear

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechExtFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechExtFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
variable {K : Type*} [Field K] (ρ : K →+* Γ(X,⊤))

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

def LocallyAcyclic (M : X.Modules) : Prop :=
  ∀ (q : ℕ) (t : Fin (q+1) → J) (k : ℕ)
    (x : Ext.{1} (schemeFreeOpen (CechHigher.intersection U t)) M (k+1)), x = 0

open CechLinear

end
end PiExponent.GeometrySupport.CechExtFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologySections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ModuleFlasque
variable {X : Scheme.{0}}

instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections (M : X.Modules) (U : X.Opens) : Module Γ(X,⊤) (OpenSections M U) :=
  Module.compHom Γ(M,U) (restrictScalar X U)

attribute [local instance] freeOpenHomAddCommGroup

attribute [local instance] OAI.PiExponentSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen
def freeOpenLinearEquiv (M : X.Modules) (U : X.Opens) :
    (freeOpen X.ringCatSheaf U ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M U where
  toEquiv := freeOpenEquiv X.ringCatSheaf M U
  map_add' := by intro f g; rfl
  map_smul' := by intro r f; rfl

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

lemma freeOpenLinearEquiv_naturality (M : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (f : freeOpen X.ringCatSheaf V ⟶ M) :
    freeOpenLinearEquiv M U (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ f) =
      openRestriction M h (freeOpenLinearEquiv M V f) :=
  freeOpenEquiv_naturality X.ringCatSheaf M _ f

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

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

def openSectionsCongr (M : X.Modules) {U V : X.Opens} (h : U = V) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections M V := by
  subst V
  exact LinearEquiv.refl _ _

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

def openTopSections (M : X.Modules) :
    letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
    OpenSections M ⊤ ≃ₗ[Γ(X,⊤)] Γ(M,⊤) := by
  letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,⊤) Γ(M,⊤) _ (restrictScalar X ⊤ r) m =
    @SMul.smul Γ(X,⊤) Γ(M,⊤) _ r m
  congr 1
  change (X.presheaf.map (𝟙 (op ⊤))) r = r
  rw [X.presheaf.map_id]
  rfl

def restrictedOpenSections (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : Y.Opens) :
    letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
    OpenSections (M.restrict f) U ≃ₗ[Γ(X,⊤)] OpenSections M (f ''ᵁ U) := by
  letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
  letI : Module Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) := (M.val.obj (op (f ''ᵁ U))).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _
      ((f.appIso U).inv (restrictScalar Y U (f.appTop r))) m =
    @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _ (restrictScalar X (f ''ᵁ U) r) m
  rw [restrictScalar_appIso]

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y Z : Scheme.{0}}

def moduleIsoSections {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections N U where
  toFun := e.hom.val.app (op U)
  invFun := e.inv.val.app (op U)
  left_inv m := by
    have h := congrArg (fun f : M ⟶ M => f.val.app (op U) m) e.hom_inv_id
    exact h
  right_inv m := by
    have h := congrArg (fun f : N ⟶ N => f.val.app (op U) m) e.inv_hom_id
    exact h
  map_add' := map_add _
  map_smul' r m := (e.hom.val.app (op U)).hom.map_smul (restrictScalar X U r) m

def openImmersionTop (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections (M.restrict f) ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (restrictedOpenSections M f ⊤).symm.toLinearMap ∘ₗ
    openRestriction M (show f ''ᵁ ⊤ ≤ ⊤ from le_top)

theorem openImmersionTop_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (t : Γ(X,⊤))
    (hf : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    IsLocalizedModule.Away t (openImmersionTop M f) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have he : X.basicOpen t = f ''ᵁ (⊤ : Y.Opens) :=
    hf.symm.trans (Scheme.Hom.image_top_eq_opensRange f).symm
  let e := (openSectionsCongr M he).trans (restrictedOpenSections M f ⊤).symm
  let g := openRestriction M (X.basicOpen_le t)
  let : IsLocalizedModule.Away t g := affine_openRestriction_localize M t
  have h := IsLocalizedModule.of_linearEquiv (.powers t) g e
  have hp : e.toLinearMap ∘ₗ g = openImmersionTop M f := by
    ext m
    change (restrictedOpenSections M f ⊤).symm
      (openSectionsCongr M he (openRestriction M (X.basicOpen_le t) m)) = _
    rw [openSectionsCongr_restriction]
    rfl
  rwa [hp] at h

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

instance globalModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) (Sections k M U) := inferInstanceAs (Module Γ(X,⊤) (OpenSections M U))
instance baseModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K (Sections k M U) := Module.compHom (OpenSections M U) k

def res (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    Sections k M V →ₗ[K] Sections k M U where
  toFun := openRestriction M h
  map_add' := map_add _
  map_smul' r m := (openRestriction M h).map_smul (k r) m

def congr (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U = V) :
    Sections k M U ≃ₗ[K] Sections k M V := by
  subst V
  exact LinearEquiv.refl K _

def restrictEquiv (k : K →+* Γ(X,⊤)) (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens) :
    Sections (f.appTop.hom.comp k) (M.restrict f) U ≃ₗ[K]
      Sections k M (f ''ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' r m := (restrictedOpenSections M f U).map_smul (k r) m

def chartTop (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤ ≃ₗ[K] Sections k M U :=
  (restrictEquiv k M U.ι ⊤).trans (congr k M (chart_image_top U))

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [CommRing K] {X : Scheme.{0}}

@[instance_reducible]
def polynomialModule (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K[X] (Sections k M U) :=
  Module.compHom (Sections k M U) (Polynomial.eval₂RingHom k t)

theorem polynomialTower (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    letI := polynomialModule k t M U
    IsScalarTower K K[X] (Sections k M U) := by
  let := polynomialModule k t M U
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (Polynomial.eval₂RingHom k t) (Polynomial.C r) • (m : OpenSections M U) =
    k r • (m : OpenSections M U)
  simp

end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

def chartModuleEquiv (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections (M.restrict f) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let E := moduleIsoSections e ⊤
  exact { E.toEquiv with
    map_add' := E.map_add
    map_smul' := fun r m => E.map_smul (f.appTop r) m }

def chartModuleMap (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (chartModuleEquiv M f e).toLinearMap ∘ₗ openImmersionTop M f

theorem chartModuleMap_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    IsLocalizedModule.Away t (chartModuleMap M f e) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsLocalizedModule.Away t (openImmersionTop M f) :=
    openImmersionTop_localize M f t ht
  exact IsLocalizedModule.of_linearEquiv (.powers t) (openImmersionTop M f)
    (chartModuleEquiv M f e)

namespace BaseSections
variable {K : Type} [CommRing K]

def chartMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) :
    Sections kX M ⊤ →ₗ[K] Sections kY N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  refine { toFun := chartModuleMap M f e
           map_add' := (chartModuleMap M f e).map_add
           map_smul' := ?_ }
  intro r m
  have h := (chartModuleMap M f e).map_smul (kX r) m
  change _ = (f.appTop (kX r)) • (chartModuleMap M f e m) at h
  exact h.trans (congrArg (fun c : Γ(Y,⊤) => c • chartModuleMap M f e m)
    (RingHom.congr_fun hk r))

lemma chartMap_smul (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (r : Γ(X,⊤)) (m : Sections kX M ⊤) :
    chartMap kX kY f hk M e (r • m) = f.appTop r • chartMap kX kY f hk M e m := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  exact (chartModuleMap M f e).map_smul r m

end BaseSections
end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry.BaseSections
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def chartPolynomialMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) (t : Γ(X,⊤)) :
    letI := polynomialModule kX t M ⊤
    letI := polynomialModule kY (f.appTop t) N ⊤
    Sections kX M ⊤ →ₗ[K[X]] Sections kY N ⊤ := by
  letI := polynomialModule kX t M ⊤
  letI := polynomialModule kY (f.appTop t) N ⊤
  refine { toFun := chartMap kX kY f hk M e
           map_add' := (chartMap kX kY f hk M e).map_add
           map_smul' := ?_ }
  intro p m
  change chartMap kX kY f hk M e ((Polynomial.eval₂RingHom kX t) p • m) =
    (Polynomial.eval₂RingHom kY (f.appTop t)) p • chartMap kX kY f hk M e m
  rw [chartMap_smul, eval_transport kX kY f hk]

theorem chartPolynomialMap_localize [IsAffine X]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) [M.IsQuasicoherent] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := polynomialModule kX t M ⊤
    letI := polynomialModule kY (f.appTop t) N ⊤
    IsLocalizedModule.Away (Polynomial.X : K[X])
      (chartPolynomialMap kX kY f hk M e t) := by
  let : Algebra K[X] Γ(X,⊤) := (Polynomial.eval₂RingHom kX t).toAlgebra
  let := polynomialModule kX t M ⊤
  let := polynomialModule kY (f.appTop t) N ⊤
  let : Module Γ(X,⊤) (Sections kY N ⊤) :=
    Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsScalarTower K[X] Γ(X,⊤) (Sections kX M ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower K[X] Γ(X,⊤) (Sections kY N ⊤) :=
    .of_algebraMap_smul (fun p m => by
      change f.appTop ((Polynomial.eval₂RingHom kX t) p) • (m : OpenSections N ⊤) =
        (Polynomial.eval₂RingHom kY (f.appTop t)) p • (m : OpenSections N ⊤)
      rw [eval_transport kX kY f hk])
  let F : Sections kX M ⊤ →ₗ[Γ(X,⊤)] Sections kY N ⊤ := chartModuleMap M f e
  have he : algebraMap K[X] Γ(X,⊤) Polynomial.X = t := by
    change (Polynomial.eval₂RingHom kX t) Polynomial.X = t
    simp
  let : IsLocalizedModule (.powers (algebraMap K[X] Γ(X,⊤) Polynomial.X)) F := by
    rw [he]
    exact chartModuleMap_localize M f e t ht
  have h := IsLocalizedModule.restrictScalars_powers (Polynomial.X : K[X]) F
  exact h
end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque
variable {X : Scheme.{0}}

abbrev schemeShortComplex (U V : X.Opens) : ShortComplex X.Modules :=
  ModuleMayerVietoris.shortComplex X.ringCatSheaf U V

abbrev schemeFreeOpenEquiv (M : X.Modules) (U : X.Opens) :
    (schemeFreeOpen_p0 U ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M U :=
  freeOpenLinearEquiv M U

def twoChartImage (M : X.Modules) (U V : X.Opens) :
    Submodule Γ(X,⊤) (OpenSections M (U ⊓ V)) :=
  (openRestriction M (show U ⊓ V ≤ U from inf_le_left)).range ⊔
  (openRestriction M (show U ⊓ V ≤ V from inf_le_right)).range

lemma twoChartImage_eq (M : X.Modules) (U V : X.Opens) :
    (LinearMap.range (Linear.leftComp (C := X.Modules) (X := schemeFreeOpen_p0 (U ⊓ V))
      (Y := schemeFreeOpen_p0 U ⊞ schemeFreeOpen_p0 V) Γ(X,⊤) M
      (schemeShortComplex U V).f)).map
      (schemeFreeOpenEquiv M (U ⊓ V)).toLinearMap = twoChartImage M U V := by
  simp only [schemeShortComplex, ModuleMayerVietoris.shortComplex]
  let P := twoChartImage M U V
  let l : schemeFreeOpen_p0 (U ⊓ V) ⟶ schemeFreeOpen_p0 U :=
    freeOpenMap X.ringCatSheaf (homOfLE (show U ⊓ V ≤ U from inf_le_left))
  let r : schemeFreeOpen_p0 (U ⊓ V) ⟶ schemeFreeOpen_p0 V :=
    freeOpenMap X.ringCatSheaf (homOfLE (show U ⊓ V ≤ V from inf_le_right))
  have hl (f : schemeFreeOpen_p0 U ⟶ M) :
      schemeFreeOpenEquiv M (U ⊓ V) (l ≫ f) =
        openRestriction M inf_le_left (schemeFreeOpenEquiv M U f) :=
    freeOpenLinearEquiv_naturality M inf_le_left f
  have hr (f : schemeFreeOpen_p0 V ⟶ M) :
      schemeFreeOpenEquiv M (U ⊓ V) (r ≫ f) =
        openRestriction M inf_le_right (schemeFreeOpenEquiv M V f) :=
    freeOpenLinearEquiv_naturality M inf_le_right f
  apply le_antisymm
  · rintro x ⟨f,⟨g,rfl⟩,rfl⟩
    have he : biprod.lift l (-r) ≫ g =
        l ≫ (biprod.inl ≫ g) - r ≫ (biprod.inr ≫ g) := by
      rw [biprod.lift_eq]
      simp only [Preadditive.add_comp, Category.assoc, Preadditive.neg_comp,
        sub_eq_add_neg]
    change schemeFreeOpenEquiv M (U ⊓ V)
      (biprod.lift l (-r) ≫ g) ∈ P
    rw [he, map_sub, hl, hr]
    exact P.sub_mem
      ((show (openRestriction M inf_le_left).range ≤ P from le_sup_left)
        ((openRestriction M inf_le_left).mem_range_self _))
      ((show (openRestriction M inf_le_right).range ≤ P from le_sup_right)
        ((openRestriction M inf_le_right).mem_range_self _))
  · apply sup_le
    · rintro x ⟨a,rfl⟩
      refine ⟨_, ⟨biprod.desc ((schemeFreeOpenEquiv M U).symm a) 0,rfl⟩, ?_⟩
      change schemeFreeOpenEquiv M (U ⊓ V)
        (biprod.lift l (-r) ≫ biprod.desc ((schemeFreeOpenEquiv M U).symm a) 0) = _
      rw [biprod.lift_desc, comp_zero, add_zero, hl, LinearEquiv.apply_symm_apply]
    · rintro x ⟨b,rfl⟩
      refine ⟨_, ⟨biprod.desc 0 (-((schemeFreeOpenEquiv M V).symm b)),rfl⟩, ?_⟩
      change schemeFreeOpenEquiv M (U ⊓ V)
        (biprod.lift l (-r) ≫ biprod.desc 0 (-((schemeFreeOpenEquiv M V).symm b))) = _
      rw [biprod.lift_desc, comp_zero, zero_add, Preadditive.neg_comp,
        Preadditive.comp_neg, neg_neg, hr, LinearEquiv.apply_symm_apply]

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseImage (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Submodule K (Sections k M (U ⊓ V)) :=
  (res k M (show U ⊓ V ≤ U from inf_le_left)).range ⊔
    (res k M (show U ⊓ V ≤ V from inf_le_right)).range

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveFinitePushforwardCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveFinitePushforwardCohomology
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X Y : Scheme.{0}}

def sectionsEquiv (f : Y ⟶ X) (k : K →+* Γ(X,⊤)) (M : Y.Modules) (U : X.Opens) :
    Sections k ((Scheme.Modules.pushforward f).obj M) U ≃ₗ[K]
      Sections (f.appTop.hom.comp k) M (f ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change Γ(M,f ⁻¹ᵁ U) at m
    let : Module Γ(Y,f ⁻¹ᵁ U) Γ(M,f ⁻¹ᵁ U) := (M.val.obj (op (f ⁻¹ᵁ U))).isModule
    change f.app U (restrictScalar X U (k r)) • (m : Γ(M,f ⁻¹ᵁ U)) =
      restrictScalar Y (f ⁻¹ᵁ U) (f.appTop (k r)) • m
    congr 1
    exact CategoryTheory.congr_fun (f.naturality (homOfLE le_top).op) (k r)

lemma sectionsEquiv_image (f : Y ⟶ X) (k : K →+* Γ(X,⊤)) (M : Y.Modules)
    (U V : X.Opens) :
    (twoBaseImage k ((Scheme.Modules.pushforward f).obj M) U V).map
        (sectionsEquiv f k M (U ⊓ V)).toLinearMap =
      twoBaseImage (f.appTop.hom.comp k) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, twoBaseImage] at hy ⊢
    obtain ⟨a, ha, b, hb, h⟩ :=
      (Submodule.mem_sup (R := K)
        (M := Sections k ((Scheme.Modules.pushforward f).obj M) (U ⊓ V))).mp hy
    exact (Submodule.mem_sup (R := K)
      (M := Sections (f.appTop.hom.comp k) M ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V)))).mpr
      ⟨a, ha, b, hb, h⟩
  · intro hx
    refine ⟨x, ?_, rfl⟩
    simp only [twoBaseImage] at hx ⊢
    obtain ⟨a, ha, b, hb, h⟩ :=
      (Submodule.mem_sup (R := K)
        (M := Sections (f.appTop.hom.comp k) M ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V)))).mp hx
    exact (Submodule.mem_sup (R := K)
      (M := Sections k ((Scheme.Modules.pushforward f).obj M) (U ⊓ V))).mpr
      ⟨a, ha, b, hb, h⟩

end
end PiExponent.CurveFinitePushforwardCohomology

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyFiniteCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K]

open PiExponentSeshadri.Frames

instance boolChartUnique (i : Bool) : Unique (ChartVariables i) where
  default := ⟨!i, by cases i <;> decide⟩
  uniq j := by rcases j with ⟨j,hj⟩; cases i <;> cases j <;> simp_all

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}} {M : X.Modules}

lemma pencil_overlap_basic (s : Bool → (O X ⟶ M)) (i : Bool) :
    (SectionOpens.isoOpen (s i)).ι ⁻¹ᵁ SectionOpens.isoOpen (s (!i)) =
      (SectionOpens.isoOpen (s i)).toScheme.basicOpen
        (coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i)))) :=
  preimage_isoOpen _ _ _

lemma pencil_overlap_reciprocal (s : Bool → (O X ⟶ M)) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    let a := X.homOfLE (show U ⊓ V ≤ U from inf_le_left)
    let b := X.homOfLE (show U ⊓ V ≤ V from inf_le_right)
    a.appTop (coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))) *
      b.appTop (coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))) = 1 := by
  intro U V a b
  obtain ⟨c,hc⟩ := overlap_coefficients U.ι V.ι a b
    (by simp only [a,b, Scheme.homOfLE_ι])
    (sectionFrame (s false)) (sectionFrame (s true))
  have h0 := hc (s false)
  have h1 := hc (s true)
  have hv : b.appTop (coefficient (sectionFrame (s true))
      (restrictSection V.ι (s false))) = c := by
    simpa only [U, sectionFrame_normalized, map_one, mul_one] using h0
  rw [hv, mul_comm]
  simpa only [V, sectionFrame_normalized, map_one] using h1.symm

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyPencil
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [CommRing K] {X : Scheme.{0}}

lemma congr_apply (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens}
    (h : U = V) (m : Sections k M U) :
    congr k M h m = M.presheaf.map (eqToHom h.symm).op m := by
  subst V
  change m = M.presheaf.map (𝟙 (op U)) m
  exact congrArg (fun f : M.presheaf.obj (op U) ⟶ M.presheaf.obj (op U) => f m)
    (M.presheaf.map_id (op U)).symm

lemma chartTop_nested (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartTop k M W (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k)
      (X.homOfLE h) (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h) m) =
        res k M h (chartTop k M U m) := by
  simp only [chartTop, LinearEquiv.trans_apply, restrictEquiv, congr_apply,
    chartMap, chartModuleMap, LinearMap.coe_comp,
    chartModuleEquiv, moduleIsoSections, openImmersionTop, restrictedOpenSections,
    nestedRestriction, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ m))) =
    M.presheaf.map _ (M.presheaf.map _ m)
  have map_comp_apply {A B C : X.Opensᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
      (x : M.presheaf.obj A) :
      M.presheaf.map g (M.presheaf.map f x) = M.presheaf.map (f ≫ g) x := by
    exact (congrArg (fun h : M.presheaf.obj A ⟶ M.presheaf.obj C => h x)
      (M.presheaf.map_comp f g)).symm
  simp only [map_comp_apply]
  refine (map_comp_apply _ _ _).trans ?_
  symm
  exact map_comp_apply _ _ _

lemma chartMap_range_coherent (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U) :
    (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k) (X.homOfLE h)
      (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h)).range.map
        (chartTop k M W).toLinearMap = (res k M h).range := by
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨chartTop k M U z, (chartTop_nested k M h z).symm⟩
  · rintro ⟨z,rfl⟩
    refine ⟨_, ⟨(chartTop k M U).symm z,rfl⟩, ?_⟩
    exact (chartTop_nested k M h _).trans
      (congrArg (res k M h) ((chartTop k M U).apply_symm_apply z))

end
end PiExponentSeshadri.Geometry.BaseSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames
variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseIntersection (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Submodule K (Sections k M (U ⊓ V)) :=
  (res k M (show U ⊓ V ≤ U from inf_le_left)).range ⊓
    (res k M (show U ⊓ V ≤ V from inf_le_right)).range

end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames BaseSections
variable {K : Type} [Field K] {X : Scheme.{0}}

lemma BaseSections.res_comp (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U V W : X.Opens} (h : U ≤ V) (g : V ≤ W) (m : Sections k M W) :
    res k M h (res k M g m) = res k M (h.trans g) m := by
  change M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE g).op m) = _
  exact (congrArg (fun f : M.presheaf.obj (op W) ⟶ M.presheaf.obj (op U) => f m)
    (M.presheaf.map_comp (homOfLE g).op (homOfLE h).op)).symm

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_SheafSectionGluing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SheafSectionGluing
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponent.GlobalSectionClearing
universe u
variable {X : Scheme.{u}} {P Q : X.Modules}

def mapSection (f : P ⟶ Q) (U : X.Opens) :
    OpenSections P U →ₗ[Γ(X,⊤)] OpenSections Q U where
  toFun := f.app U
  map_add' := map_add _
  map_smul' r x := by
    exact f.app_smul (r := restrictScalar X U r) (x := x)

@[simp] lemma mapSection_comp {R : X.Modules} (f : P ⟶ Q) (g : Q ⟶ R)
    (U : X.Opens) (x : OpenSections P U) :
    mapSection (f ≫ g) U x = mapSection g U (mapSection f U x) := rfl

lemma mapSection_congr (f : P ⟶ Q) {U V : X.Opens} (h : U = V)
    (x : OpenSections P U) :
    openSectionsCongr Q h (mapSection f U x) = mapSection f V (openSectionsCongr P h x) := by
  subst V
  rfl

end
end PiExponent.SheafSectionGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveLaurentTransitions
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveLaurentTransitions
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {ι R : Type*} [Fintype ι] [CommRing R]

def zeroDegreeExponent (i : ι) : ({j : ι // j ≠ i} → ℤ) →+ (ι → ℤ) where
  toFun b := (fullEncode i 0 b).val
  map_zero' := by
    funext k
    by_cases hk : k = i
    · subst k; simp
    · exact fullEncode_other i 0 0 ⟨k, hk⟩
  map_add' a b := by
    funext k
    by_cases hk : k = i
    · subst k; simp [fullEncode_self, Finset.sum_add_distrib, add_comm]
    · change (fullEncode i 0 (a + b)).val (⟨k, hk⟩ : {j : ι // j ≠ i}) = _
      rw [fullEncode_other i 0 (a + b) ⟨k, hk⟩]
      change a ⟨k, hk⟩ + b ⟨k, hk⟩ = (fullEncode i 0 a).val k + (fullEncode i 0 b).val k
      rw [show (fullEncode i 0 a).val k = a ⟨k, hk⟩ from fullEncode_other i 0 a ⟨k, hk⟩,
        show (fullEncode i 0 b).val k = b ⟨k, hk⟩ from fullEncode_other i 0 b ⟨k, hk⟩]

theorem fullEncode_eq_standard_add (i : ι) (d : ℤ)
    (b : {j : ι // j ≠ i} → ℤ) :
    (fullEncode i d b).val = standardExponent i d + zeroDegreeExponent i b := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [zeroDegreeExponent, sub_eq_add_neg]
  · simp only [Pi.add_apply, standardExponent_other i k d hk, zero_add]
    exact (fullEncode_other i d b ⟨k, hk⟩).trans (fullEncode_other i 0 b ⟨k, hk⟩).symm

def chartToFull (i : ι) : chartGroupAlgebra (R := R) i →+* FullGroupAlgebra (ι := ι) (R := R) :=
  AddMonoidAlgebra.mapDomainRingHom R (zeroDegreeExponent i)

def laurentToFull (d : ℤ) : Laurent ι R d →+ FullGroupAlgebra (ι := ι) (R := R) :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    (Finsupp.mapDomain.addMonoidHom (fun a : Monomial ι d => a.val))

@[simp] theorem laurentToFull_single (d : ℤ) (a : Monomial ι d) (r : R) :
    laurentToFull d (Finsupp.single a r) = AddMonoidAlgebra.single a.val r := by
  simp [laurentToFull]

theorem laurentToFull_groupAlgebraToLaurent (i : ι) (d : ℤ)
    (p : chartGroupAlgebra (R := R) i) :
    laurentToFull d (groupAlgebraToLaurent i d p) =
      AddMonoidAlgebra.single (standardExponent i d) 1 * chartToFull i p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]
  | single a r =>
      change laurentToFull d (Finsupp.domCongr (fullExponentEquiv i d) (Finsupp.single a r)) = _
      simp [chartToFull, laurentToFull_single,
        fullExponentEquiv, AddMonoidAlgebra.single_mul_single]
      exact congrArg (fun exponent => AddMonoidAlgebra.single exponent r)
        (fullEncode_eq_standard_add i d a)

def overlapToFull (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+* FullGroupAlgebra (ι := ι) (R := R) :=
  (chartToFull i).comp (overlapToGroupAlgebra i s)

@[simp] theorem laurentToFull_overlapLaurent (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (z : Localization.Away (chartProduct (R := R) i s)) :
    laurentToFull d (overlapLaurent i d s z) =
      AddMonoidAlgebra.single (standardExponent i d) 1 * overlapToFull i s z :=
  laurentToFull_groupAlgebraToLaurent i d _

end
end PiExponent.GeometrySupport.ProjectiveLaurentTransitions

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateRatios
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry Frames ModuleFlasque RestrictionCohomology
open PiExponentSeshadri.ProjectiveChartSections
variable {X : Scheme} {M : X.Modules}

def coordinateRatioOn (si sk : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) : Γ(X,W) :=
  X.presheaf.map (homOfLE hi).op
    ((SectionOpens.isoOpen si).topIso.hom
      (coefficient (sectionFrame si)
        (restrictSection (SectionOpens.isoOpen si).ι sk)))

@[simp] lemma coordinateRatioOn_self (si : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) : coordinateRatioOn si si hi = 1 := by
  simp only [coordinateRatioOn, sectionFrame_normalized, map_one]

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveTupleCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveTupleCharts

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry

universe u
variable {σ : Type u} [Fintype σ]

theorem coordinateFiniteOpen_tuple {X : Scheme} {σ : Type} [Fintype σ]
    (M : X.Modules) (s : σ → (structureSheaf X ⟶ M)) {q : ℕ}
    (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    coordinateFiniteOpen M s (t p) (tupleVariables t p) =
      CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t := by
  change PiExponentSeshadri.SectionOpens.isoOpen (s (t p)) ⊓
    (tupleVariables t p).inf (fun j => PiExponentSeshadri.SectionOpens.isoOpen (s j.val)) = _
  exact tupleVariables_inf (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t p

open PiExponentSeshadri.ModuleFlasque
open PiExponent.ProjectiveMonomialCech
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

def freeOpenHomCongr {X : Scheme} (M : X.Modules) {U V : X.Opens} (h : U = V) :
    (schemeFreeOpen X V ⟶ M) ≃+ (schemeFreeOpen X U ⟶ M) where
  toFun b := freeOpenMap X.ringCatSheaf (eqToHom h) ≫ b
  invFun b := freeOpenMap X.ringCatSheaf (eqToHom h.symm) ≫ b
  left_inv b := by
    subst h
    simp [freeOpenMap]
    erw [Category.id_comp, Category.id_comp]
  right_inv b := by
    subst h
    simp [freeOpenMap]
    erw [Category.id_comp, Category.id_comp]
  map_add' b c := Preadditive.comp_add (C := X.Modules) _ _ _ _ b c

attribute [local irreducible] coordinatePowerOverlap modulePow

end
end PiExponent.GeometrySupport.ProjectiveTupleCharts

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveFramedCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (N : X.Modules)
variable (e : ∀ i, N.restrict (SectionOpens.isoOpen (s i)).ι ≅
  structureSheaf (SectionOpens.isoOpen (s i)).toScheme) (d : ℤ)

abbrev schemeFreeOpen_p0 (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationModel
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterChartProjection_isFinite _root_.OAI.PiExponent.CurveNormalizationModel.parameterChart_noetherian _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
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

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

instance parameterCurve_compactSpace : CompactSpace (parameterCurve f hf) := by
  rw [← isCompact_univ_iff]
  have hcover : Set.range (zeroChartInclusion f hf) ∪
      Set.range (infinityChartInclusion f hf) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    exact parameterCurve_twoChartCover f hf x
  rw [← hcover]
  exact (isCompact_range (zeroChartInclusion f hf).continuous).union
    (isCompact_range (infinityChartInclusion f hf).continuous)

def parameterCurveFunctionFieldEquiv
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (parameterCurve f hf).functionField ≃+* E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  letI : Algebra (parameterChart f hf) (Spec (.of (parameterChart f hf))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (parameterChart f hf))
  letI : IsFractionRing (parameterChart f hf) (Spec (.of (parameterChart f hf))).functionField :=
    functionField_isFractionRing_of_affine (.of (parameterChart f hf))
  exact (parameterCurveFunctionFieldIso f hf).commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (nonZeroDivisors (parameterChart f hf))
      (Spec (.of (parameterChart f hf))).functionField E).toRingEquiv

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponent.CurveZeroPole
open scoped Polynomial

universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterCurveOpenCover : (parameterCurve f hf).OpenCover where
  I₀ := Bool
  X b := if b then Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))
    else Spec (.of (parameterChart f hf))
  f b := by
    cases b
    · exact zeroChartInclusion f hf
    · exact infinityChartInclusion f hf
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
      · exact ⟨false, q, rfl⟩
      · exact ⟨true, q, rfl⟩
    · intro b
      cases b <;> infer_instance

instance parameterCurve_noetherian [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsNoetherian (parameterCurve f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  have hlocal : ∀ b, IsLocallyNoetherian ((parameterCurveOpenCover f hf).X b) := by
    intro b
    cases b <;> dsimp [parameterCurveOpenCover] <;> infer_instance
  have : IsLocallyNoetherian (parameterCurve f hf) :=
    (isLocallyNoetherian_iff_openCover (parameterCurveOpenCover f hf)).mpr hlocal
  exact ⟨⟩

attribute [local instance] specializationOrder

theorem parameterCurve_isClosed_of_ne_generic [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) (hx : x ≠ genericPoint (parameterCurve f hf)) :
    IsClosed ({x} : Set (parameterCurve f hf)) := by
  apply closure_subset_iff_isClosed.mp
  intro y hy
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hylt : y < x := lt_of_le_of_ne hyx (by simpa using hne)
  have hdim : Order.krullDim (parameterCurve f hf) ≤ 1 := by
    have h := parameterCurve_dimension_le_one f hf
    change Order.krullDim (IrreducibleCloseds (parameterCurve f hf)) ≤ 1 at h
    rwa [Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := parameterCurve f hf))] at h
  have hyco : Order.coheight y ≤ (1 : ℕ∞) := by
    exact_mod_cast (Order.coheight_le_krullDim y).trans hdim
  have hxco : Order.coheight x < (1 : ℕ∞) :=
    Order.coheight_le_coe_iff.mp hyco x hylt
  have hxmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp hxco)
  exact hx hxmax.eq_top

theorem parameterCurve_exists_nongeneric [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    ∃ x : parameterCurve f hf, x ≠ genericPoint (parameterCurve f hf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  obtain ⟨q⟩ := (inferInstance : Nonempty ((zeroPrime F).primesOver S))
  let z : PrimeSpectrum S := ⟨q.val, q.property.1⟩
  have hz : z.asIdeal ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F) q.property
  refine ⟨zeroChartInclusion f hf z, ?_⟩
  intro heq
  have hgen := genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
  have he : z = genericPoint (Spec (.of S)) :=
    (zeroChartInclusion f hf).isOpenEmbedding.injective (heq.trans hgen.symm)
  apply hz
  rw [he, genericPoint_eq_bot_of_affine]
  rfl

theorem parameterCurve_isClosed_iff_ne_generic [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) :
    IsClosed ({x} : Set (parameterCurve f hf)) ↔
      x ≠ genericPoint (parameterCurve f hf) := by
  constructor
  · intro hclosed heq
    subst x
    obtain ⟨y, hy⟩ := parameterCurve_exists_nongeneric f hf
    have hy' : y ∈ closure ({genericPoint (parameterCurve f hf)} :
        Set (parameterCurve f hf)) := by rw [genericPoint_closure]; trivial
    rw [hclosed.closure_eq] at hy'
    exact hy hy'
  · exact parameterCurve_isClosed_of_ne_generic f hf x

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceParameterModel
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.infinityChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.infinityOverlap_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.parameterChartProjection_isFinite _root_.OAI.PiExponent.CurveNormalizationModel.parameterChart_noetherian _root_.OAI.PiExponent.CurveNormalizationModel.zeroChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.zeroOverlap_isOpenImmersion _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.PlaceParameterModel
open CurveZeroPole CurveValuationCenter WeightedCurveDegree

def parameterCenterLocalRingEquiv
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 < p.valuation f) :
    Localization.AtPrime (parameterCenterPlace f hf p.valuation p.constants_nonneg hp).1 ≃+*
      p.valuation.toValuation.valuationSubring := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  let q := parameterValuationCenter f hf p.valuation p.constants_nonneg hp.le
  have hq : q ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F)
      (parameterCenterPlace f hf p.valuation p.constants_nonneg hp).property
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq A
  let φ := parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp.le
  have he : p.valuation = CurveLocalOrder.fractionAddValuation A E :=
    valuation_eq_parameterPlaceValuation f hf p.valuation p.constants_nonneg hp p.normalized
  apply RingEquiv.ofBijective φ
  constructor
  · intro a b hab
    apply IsFractionRing.injective A E
    have hh := congrArg (fun x : p.valuation.toValuation.valuationSubring => (x : E)) hab
    simpa only [φ, parameterCenterLocalHom_coe] using hh
  · intro x
    have hx : 0 ≤ CurveLocalOrder.fractionAddValuation A E (x : E) := by
      rw [← he]
      exact x.property
    obtain ⟨a, ha⟩ := (WeightedLocalLattice.exists_local_element_iff_nonnegative_order
      (A := A) (x : E)).mpr hx
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact (parameterCenterLocalHom_coe f hf p.valuation p.constants_nonneg hp.le a).trans ha

def parameterCenterLocalAlgEquiv
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 < p.valuation f) :
    letI := ParameterResidueField.parameterChartConstants f hf
    Localization.AtPrime (parameterCenterPlace f hf p.valuation p.constants_nonneg hp).1 ≃ₐ[F]
      PlaceValuationRing.ring p := by
  let := ParameterResidueField.parameterChartConstants f hf
  refine { parameterCenterLocalRingEquiv f hf p hp with commutes' := ?_ }
  intro c
  apply Subtype.ext
  change (parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp.le
    (algebraMap F _ c) : E) = algebraMap F E c
  rw [IsScalarTower.algebraMap_apply F (parameterChart f hf)
    (Localization.AtPrime (parameterValuationCenter f hf p.valuation p.constants_nonneg hp.le))]
  rw [parameterCenterLocalHom_algebraMap]
  let := parameterPolynomialAlgebra f hf
  change (algebraMap F[X] E (Polynomial.C c)) = algebraMap F E c
  rw [parameterPolynomialAlgebra_map f hf, Polynomial.aeval_C]

end PiExponent.PlaceParameterModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCurveTwoAffine
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveCurveTwoAffine
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] [Fintype σ]

theorem exists_hyperplane_avoiding {K σ ι : Type} [Field K] [Infinite K]
    [Fintype σ] [Finite ι] (x : ι → Proj (PolyGrade K σ)) :
    ∃ v : σ → K, ∀ i, x i ∈ Proj.basicOpen (PolyGrade K σ) (linearEquation v) := by
  classical
  let bad (i : ι) : Submodule K (σ → K) :=
    ((x i).asHomogeneousIdeal.toIdeal.restrictScalars K).comap
      (linearEquationLinear (K := K) (σ := σ))
  have hbad (i : ι) : bad i ≠ ⊤ := by
    intro h
    have hx : x i ∈ ⨆ j : σ, Proj.basicOpen (PolyGrade K σ) (X j) := by
      rw [standardChart_cover]
      trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    have hm : Pi.single j (1 : K) ∈ bad i := h ▸ Submodule.mem_top
    change linearEquation (Pi.single j (1 : K)) ∈ (x i).asHomogeneousIdeal at hm
    rw [linearEquation_single_one] at hm
    exact hj hm
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨v, hv⟩

theorem two_affine_cover_of_affine_projective_map
    {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {Y : Scheme.{0}} [IsIntegral Y] [NoetherianSpace Y]
    (j : Y ⟶ Proj (PolyGrade K σ)) [IsAffineHom j]
    (hd : topologicalKrullDim Y ≤ 1) :
    ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  classical
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  have hy : j y ∈ ⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (X i) := by
    rw [standardChart_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  let U := j ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (X i)
  have hU : IsAffineOpen U := (standardChart_isAffineOpen i).preimage j
  let Z : Set Y := (U : Set Y)ᶜ
  have hZ : Z.Finite := proper_closed_finite_of_dimension_one hd U.isOpen.isClosed_compl (by
    intro h
    have hyZ : y ∈ Z := h ▸ Set.mem_univ y
    exact hyZ hi)
  let : Finite Z := hZ.to_subtype
  obtain ⟨v, hv⟩ := exists_hyperplane_avoiding (fun z : Z => j z.val)
  let V := j ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (linearEquation v)
  have hV : IsAffineOpen V :=
    (Proj.isAffineOpen_basicOpen _ _ (linearEquation_homogeneous v) (by decide)).preimage j
  refine ⟨U, V, hU, hV, top_unique ?_⟩
  intro z _
  by_cases hz : z ∈ U
  · exact Or.inl hz
  · exact Or.inr (hv ⟨z, hz⟩)

theorem two_affine_cover_of_closed_embedding
    {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {Y : Scheme.{0}} [IsIntegral Y] [IsNoetherian Y]
    (j : Y ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion j]
    (hd : topologicalKrullDim Y ≤ 1) :
    ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ :=
  two_affine_cover_of_affine_projective_map j hd

end
end PiExponent.ProjectiveCurveTwoAffine

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectivePencilScalars
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectivePencilScalars
noncomputable section
open AlgebraicGeometry CategoryTheory

theorem scalars_comp_eq_structureScalars {F : Type} [CommRing F] {Y : Scheme.{0}}
    (f : Y ⟶ ProjectiveLine.projectiveLine F) :
    f.appTop.hom.comp (ProjectiveO1.scalars (R := F) (σ := Bool)) =
      (f ≫ ProjectiveLine.structureMap F).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom := by
  rw [ProjectiveO1.scalars, Scheme.Hom.comp_appTop, ← projection_eq_structureMap F]
  rfl

theorem scalars_comp_eq_baseScalars {Y : Scheme.{0}}
    (f : Y ⟶ ProjectiveLine.projectiveLine ℂ) :
    f.appTop.hom.comp (ProjectiveO1.scalars (R := ℂ) (σ := Bool)) =
      PiExponentSeshadri.Geometry.baseScalars (f ≫ ProjectiveLine.structureMap ℂ) :=
  scalars_comp_eq_structureScalars f

end
end PiExponent.ProjectivePencilScalars

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveFinitePencil
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectivePencil

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry PiExponentSeshadri.Projective


variable {K σ : Type} [CommRing K] {X : Scheme.{0}}

def scalars (f : X ⟶ ProjectiveO1.projectiveSpace K σ) : K →+* Γ(X,⊤) :=
  f.appTop.hom.comp (ProjectiveO1.scalars (R := K) (σ := σ))

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem scalars_eq_baseScalars
    (f : X ⟶ ProjectiveLine.projectiveLine ℂ) :
    scalars f = baseScalars (f ≫ ProjectiveLine.structureMap ℂ) :=
  ProjectivePencilScalars.scalars_comp_eq_baseScalars f

end PiExponent.ProjectivePencil

end

end OAI
end


