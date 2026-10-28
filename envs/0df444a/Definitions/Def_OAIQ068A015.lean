-- Prove2me | Definitions.Def_OAIQ068A015
-- name    : OAIQ068A015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:47:20.336976+00:00
-- url     : https://prove2.me/theorems/ec94c174-ccdf-4dce-9b7e-53e1f518a8cc
-- title:
--   Definitions bundle OAIQ068A015 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 114 declarations of OpenAI's Lean: 27 definitions, 20 instances and 67 theorems. The definitions and types are `OAI.PiExponent.CurveImageAffineCoordinates.fieldAlgEquiv`, `OAI.PiExponent.CurveMonomialMap.genericMonomialMap`, `OAI.PiExponent.GeometrySupport.CechExtFinite.ActualExt`, `OAI.PiExponent.GeometrySupport.CechExtFinite.connecting`, `OAI.PiExponent.ProjectiveMonomialCech.RegularOn`, `OAI.PiExponent.ProjectiveMonomialCechHigher.Regular`, `OAI.PiExponent.ProjectiveMonomialCechHigher.contraction`, `OAI.PiExponent.ProjectiveMonomialCechHigher.differential`, `OAI.PiExponent.ProjectiveMonomialCechHigher.insertionSupport`, `OAI.PiExponent.ProjectiveMonomialCohomology.boundaryMap`, `OAI.PiExponent.ProjectiveMonomialCohomology.cycles`, `OAI.PiExponent.ProjectiveMonomialCohomology.degreeZeroCoefficients`, `OAI.PiExponent.ProjectiveMonomialCohomology.differentialLinear`, `OAI.PiExponent.ProjectiveMonomialCohomology.negativeCoefficients`, `OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles`, `OAI.PiExponent.ProjectiveMonomialCohomology.regularCochains`, `OAI.PiExponent.ProjectiveMonomialFinite.AllNegative`, `OAI.PiExponent.ProjectiveMonomialFinite.filterCochain`, `OAI.PiExponentSeshadri.FreeOpenUnit.freeTopIso`, `OAI.PiExponentSeshadri.Geometry.extSourceIso`, `OAI.PiExponentSeshadri.Geometry.freeOpenHomAddCommGroup`, `OAI.PiExponentSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen`, `OAI.PiExponentSeshadri.Geometry.schemeFreeOpen`, `OAI.PiExponentSeshadri.Geometry.schemeFreeOpen`, `OAI.PiExponentSeshadri.RestrictionCohomology.restrictionGenerator`, `OAI.PiExponentSeshadri.RestrictionCohomology.restrictionHomEquiv`, `OAI.PiExponentSeshadri.schemeFreeOpen`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AmpleGlobalGeneration`, `PiExponent_Ampleness_CoherentAffineFinite`, `PiExponent_Approximation_ClosedImmersionSerreTransfer`, `PiExponent_Approximation_ClosedPushforwardAffine`, `PiExponent_Approximation_ClosedPushforwardCoherent`, `PiExponent_Approximation_ClosedPushforwardLinear`, `PiExponent_Approximation_CoherentTwistPresentation`, `PiExponent_Approximation_FrameSubopens`, `PiExponent_Approximation_GlobalSectionClearing`, `PiExponent_Approximation_InverseFrames`, `PiExponent_Cohomology_CechExtFinite`, `PiExponent_Cohomology_CechHigher`, `PiExponent_Cohomology_FiniteCoverCohomology`, `PiExponent_Cohomology_PencilCohomologyCech`, `PiExponent_Cohomology_PencilCohomologyCharts`, `PiExponent_Cohomology_PencilCohomologySections`, `PiExponent_Cohomology_ProjectiveMonomialCech`, `PiExponent_Cohomology_ProjectiveMonomialCechHigher`, `PiExponent_Cohomology_ProjectiveMonomialCohomology`, `PiExponent_Geometry_CurveFinitePushforwardCoherent`, `PiExponent_Geometry_CurveImageAffineCoordinates`, `PiExponent_Geometry_CurveMonomialMap`, `PiExponent_Geometry_CurveNormalizationDegree`, `PiExponent_Geometry_CurveNormalizationDimension`, `PiExponent_Geometry_CurveZeroPole`, `PiExponent_Geometry_ProjectiveCoordinateRingNaturality`, `PiExponent_Geometry_ProjectiveCurveTwoAffine`, `PiExponent_Geometry_ProjectiveMonomialFinite`, `PiExponent_Geometry_ProjectivePencilScalars`, `PiExponent_LocalAlgebra_CoherentExtFiniteness`, `PiExponent_LocalAlgebra_FiniteGlobalPresentation`.
--
--   **Imports.** It imports the bundles `OAIQ068A000`, `OAIQ068A001`, `OAIQ068A002`, `OAIQ068A003`, `OAIQ068A004`, `OAIQ068A005` and `OAIQ068A010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A023`, `OAIQ068A024`, `OAIQ068A025` and `OAIQ068A026`; the proofs of `OAI_PiExponent_AdmissibleBlowupGeometry_uniform_curve_margin_of_affine_curve_data`, `OAI_PiExponent_AdmissibleMatrixInterpolation_globalInterpolation`, `OAI_PiExponent_BlowupJetSurjectivity_eventual_blowup_jetRestriction_surjective`, `OAI_PiExponent_GlobalReesRecoveryComparison_eventually_ordinaryMap_app_bijective` and `OAI_PiExponent_NumericalAmpleness_isAmple_of_lower_ampleness_of_euler_growth`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A000
import Definitions.Def_OAIQ068A001
import Definitions.Def_OAIQ068A002
import Definitions.Def_OAIQ068A003
import Definitions.Def_OAIQ068A004
import Definitions.Def_OAIQ068A005
import Definitions.Def_OAIQ068A010

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteCoverCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace TildeExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {R : CommRingCat.{u}}

instance preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

end TildeExact

namespace ModuleGrothendieck
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] (R₀ : Cᵒᵖ ⥤ RingCat.{u})

instance presheafGrothendieck : IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R₀) where

end ModuleGrothendieck

abbrev schemeFreeOpen (X : AlgebraicGeometry.Scheme) (U : X.Opens) : X.Modules :=
  ModuleFlasque.freeOpen X.ringCatSheaf U

namespace AffineCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open FlasqueCohomology
universe u
variable {R : CommRingCat.{u}}

lemma globalHom_tilde_surjective {M N : ModuleCat.{u} R} (g : M ⟶ N) [Epi g] :
    Function.Surjective (fun f : schemeUnit (Spec R) ⟶ tilde M =>
      f ≫ tilde.map g) := by
  intro f
  obtain ⟨q,hq⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen N ⊤)).surjective
    (globalHomEquiv (Spec R).ringCatSheaf (tilde N) f)
  obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective g).mp inferInstance q
  refine ⟨(globalHomEquiv (Spec R).ringCatSheaf (tilde M)).symm (tilde.toOpen M ⊤ p), ?_⟩
  apply (globalHomEquiv (Spec R).ringCatSheaf (tilde N)).injective
  erw [globalHomEquiv_comp, Equiv.apply_symm_apply]
  change ((modulesSpecToSheaf.map (tilde.map g)).hom.app (op ⊤)) (tilde.toOpen M ⊤ p) = _
  have h := CategoryTheory.congr_fun (tilde.toOpen_map_app g ⊤) p
  exact h.trans (by change tilde.toOpen N ⊤ (g p) = _; rw [hp, hq])

end AffineCohomology

namespace RestrictionExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance restriction_preservesMonomorphisms :
    (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms where
  preserves g _ := restriction_mono f g

instance restriction_preservesHomology :
    (Scheme.Modules.restrictFunctor f).PreservesHomology :=
  (Scheme.Modules.restrictFunctor f).preservesHomology_of_preservesMonos_and_cokernels

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
  (Scheme.Modules.restrictFunctor f).preservesFiniteLimits_of_preservesHomology

end RestrictionExact

namespace RestrictionCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open ModuleFlasque FlasqueCohomology
universe u
variable {X : Scheme.{u}} (U : X.Opens)

lemma freeOpenEquiv_comp {M N : X.Modules}
    (f : schemeFreeOpen X U ⟶ M) (g : M ⟶ N) :
    freeOpenEquiv X.ringCatSheaf N U (f ≫ g) =
      g.val.app (op U) (freeOpenEquiv X.ringCatSheaf M U f) := rfl

def restrictionHomEquiv (M : X.Modules) :
    (schemeFreeOpen X U ⟶ M) ≃
      (schemeUnit U.toScheme ⟶ M.restrict U.ι) :=
  (freeOpenEquiv X.ringCatSheaf M U).trans
    ((restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.toEquiv.symm.trans
      (globalHomEquiv U.toScheme.ringCatSheaf (M.restrict U.ι)).symm)

lemma restrictionHomEquiv_comp {M N : X.Modules}
    (f : schemeFreeOpen X U ⟶ M) (g : M ⟶ N) :
    restrictionHomEquiv U N (f ≫ g) =
      restrictionHomEquiv U M f ≫ (Scheme.Modules.restrictFunctor U.ι).map g := by
  have hsection (P : X.Modules) (h : schemeFreeOpen X U ⟶ P) :
      globalHomEquiv U.toScheme.ringCatSheaf (P.restrict U.ι) (restrictionHomEquiv U P h) =
        (restrictionSectionsIso U P).inv (freeOpenEquiv X.ringCatSheaf P U h) := by
    simp only [restrictionHomEquiv]
    exact (globalHomEquiv U.toScheme.ringCatSheaf (P.restrict U.ι)).apply_symm_apply _
  apply (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι)).injective
  erw [globalHomEquiv_comp, hsection, hsection, freeOpenEquiv_comp]
  change (restrictionSectionsIso U N).inv (g.val.app (op U)
    (freeOpenEquiv X.ringCatSheaf M U f)) =
    ((Scheme.Modules.restrictFunctor U.ι).map g).val.app (op ⊤)
      ((restrictionSectionsIso U M).inv (freeOpenEquiv X.ringCatSheaf M U f))
  exact (CategoryTheory.congr_fun (g.mapPresheaf.naturality
    (eqToHom U.ι_image_top).op) _).symm

def restrictionGenerator : schemeUnit U.toScheme ⟶
    (Scheme.Modules.restrictFunctor U.ι).obj (schemeFreeOpen X U) :=
  restrictionHomEquiv U _ (𝟙 _)

lemma restrictionGenerator_comp {M : X.Modules}
    (f : schemeFreeOpen X U ⟶ M) :
    restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f =
      restrictionHomEquiv U M f := by
  simpa only [restrictionGenerator, Category.id_comp] using
    (restrictionHomEquiv_comp U (𝟙 _) f).symm

end RestrictionCohomology

namespace FreeOpenUnit
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque FlasqueCohomology
universe u v

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeTopIso : freeOpen R ⊤ ≅ SheafOfModules.unit R :=
  isoFromHomEquiv
    (fun M => (freeOpenEquiv R M ⊤).trans (globalHomEquiv R M).symm)
    (by
      intro M N f g
      apply (globalHomEquiv R N).injective
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, globalHomEquiv_comp]
      rfl)

end FreeOpenUnit

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentTwistPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace PiExponent.CoherentTwist

universe u
variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]

open TopologicalSpace
variable {X : Scheme.{u}} {P Q : X.Modules}

lemma exact_of_local (S : ShortComplex X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (S.map (Scheme.Modules.restrictFunctor U.ι)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply eq_zero_of_local
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  have hz : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj S.homology) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp hU).of_iso
      (S.mapHomologyIso (Scheme.Modules.restrictFunctor U.ι)).symm
  refine ⟨U, hx, ?_⟩
  rw [CategoryTheory.Functor.map_id]
  exact hz.eq_of_src _ _

end PiExponent.CoherentTwist

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_CoherentAffineFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentAffineFinite
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

theorem spec_sections_finite_of_generators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (s : M.GeneratingSections) [hs : s.IsFiniteType] :
    Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)) := by
  let : Finite s.I := hs.finite
  let : Fintype s.I := Fintype.ofFinite s.I
  let N : ModuleCat R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  let a : tilde (ModuleCat.of R (s.I →₀ R)) ⟶ tilde N :=
    (tildeFinsupp s.I).hom ≫ s.π ≫ (asIso M.fromTildeΓ).inv
  let f : ModuleCat.of R (s.I →₀ R) ⟶ N := (tilde.functor R).preimage a
  have : Epi s.π := s.epi
  have : Epi (asIso M.fromTildeΓ).inv := inferInstance
  have ha : Epi a := by
    change Epi ((tildeFinsupp s.I).hom ≫ s.π ≫ (asIso M.fromTildeΓ).inv)
    exact epi_iso_comp_iso (tildeFinsupp s.I) s.π s.epi (asIso M.fromTildeΓ).symm
  have hf : Epi f := (tilde.functor R).epi_of_epi_map (by
    change Epi ((tilde.functor R).map ((tilde.functor R).preimage a))
    exact (Functor.map_preimage (tilde.functor R) a).symm ▸ ha)
  exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp hf)

theorem affine_sections_finite_of_generators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent]
    (s : M.GeneratingSections) [hs : s.IsFiniteType] : Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let f := X.isoSpec.inv
  let F : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf :=
    Scheme.Modules.restrictFunctor f
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction f).leftAdjoint_preservesColimits
  let J := M.restrict f
  let t := s.map F (Scheme.Modules.restrictUnitIso f).symm
  let : t.IsFiniteType := ⟨hs.finite⟩
  let R := Γ(X,⊤)
  let N := (modulesSpecToSheaf.obj J).obj.obj (op ⊤)
  let : Module.Finite R N := spec_sections_finite_of_generators J t
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : N →ₛₗ[σ] Γ(M,f ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

theorem locallyFinitelyGenerated_of_finitePresentation {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] : LocallyFinitelyGenerated M := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  intro x
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i by rw [hcov]; trivial)
  refine ⟨q.X i, hi, ?_⟩
  let F : SheafOfModules (Sheaf.over X.ringCatSheaf (q.X i)) ⥤
      SheafOfModules (Scheme.Opens.toScheme (X := X) (q.X i)).ringCatSheaf :=
    (Scheme.Modules.overEquiv (q.X i)).functor
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.overEquiv (q.X i)).toAdjunction.leftAdjoint_preservesColimits
  let t := (q.presentation i).generators.map F (Iso.refl _)
  let e := (Scheme.Modules.overFunctorEquiv (q.X i)).app M
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e t,
    ⟨(hq.isFinite_presentation i).isFiniteType_generators.finite⟩⟩

theorem affine_open_sections_finite_of_generators {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (s : (M.restrict U.ι).GeneratingSections) [s.IsFiniteType] :
    Module.Finite Γ(X,U) Γ(M,U) := by
  let : IsAffine U.toScheme := hU
  let : Module.Finite Γ(U.toScheme,⊤) Γ(M.restrict U.ι,⊤) :=
    affine_sections_finite_of_generators (M.restrict U.ι) s
  let σ := (U.ι.appIso ⊤).inv.hom
  let φ : Γ(M.restrict U.ι,⊤) →ₛₗ[σ] Γ(M,U.ι ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso U.ι ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso U.ι ⊤).hom).surjective
  have h := Module.Finite.of_surjective φ hφ
  rwa [U.ι_image_top] at h

theorem spec_sections_finite_of_localGenerators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)) := by
  classical
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let t : Set R := {r | ∃ s : (M.restrict (D r).ι).GeneratingSections, s.IsFiniteType}
  have ht : Ideal.span t = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x hx
    obtain ⟨U,hxU,s,hs⟩ := hM x
    obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hxr,hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr
      ⟨finite_generators_of_le M hrU s,hxr⟩⟩
  let N := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  let A (r : t) := Γ(Spec R, PrimeSpectrum.basicOpen r.val)
  let P (r : t) := Γ(M, PrimeSpectrum.basicOpen r.val)
  let (r : t) : Algebra R (A r) := StructureSheaf.openAlgebra (R := R) (op (PrimeSpectrum.basicOpen r.val))
  let (r : t) : IsLocalization.Away r.val (A r) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen R r.val
  let (r : t) : Module (A r) (P r) :=
    (M.val.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : Module R (P r) :=
    ((modulesSpecToSheaf.obj M).obj.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : IsScalarTower R (A r) (P r) :=
    IsScalarTower.of_compHom R (A r) (P r)
  let f (r : t) : N →ₗ[R] P r :=
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  let (r : t) : IsLocalizedModule.Away r.val (f r) := hloc r.val
  have hfin (r : t) : Module.Finite (A r) (P r) := by
    obtain ⟨s, hs⟩ := r.property
    exact affine_open_sections_finite_of_generators M (D r.val)
      (IsAffineOpen.Spec_basicOpen r.val) s
  exact Module.Finite.of_localizationSpan' t ht f hfin

theorem LocallyFinitelyGenerated.restrict {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : LocallyFinitelyGenerated M) (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyFinitelyGenerated (M.restrict f) := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := hM (f x)
  let V := f ⁻¹ᵁ U
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (f ∣_ U)
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let t := s.map F
    (Scheme.Modules.restrictUnitIso (f ∣_ U)).symm
  let e := (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app M
  have e' : M.restrict (V.ι ≫ f) ≅ (M.restrict U.ι).restrict (f ∣_ U) := by
    change M.restrict ((f ∣_ U) ≫ U.ι) ≅ (M.restrict U.ι).restrict (f ∣_ U) at e
    simpa only [V, morphismRestrict_ι] using e
  let e'' := ((Scheme.Modules.restrictFunctorComp V.ι f).app M).symm ≪≫ e'
  exact ⟨V, hxU, SheafOfModules.GeneratingSections.equivOfIso e''.symm t,
    ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := s)⟩⟩

theorem affine_sections_finite_of_localGenerators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let f := X.isoSpec.inv
  let J := M.restrict f
  let R := Γ(X,⊤)
  let N := (modulesSpecToSheaf.obj J).obj.obj (op ⊤)
  let : Module.Finite R N := spec_sections_finite_of_localGenerators J
    (hM.restrict f)
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : N →ₛₗ[σ] Γ(M,f ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

theorem affine_sections_finite {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsFinitePresentation] : Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let := finitePresentation_quasicoherent M
  exact affine_sections_finite_of_localGenerators M (locallyFinitelyGenerated_of_finitePresentation M)

theorem spec_exists_finite_generators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let N : ModuleCat R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  obtain ⟨I,hI,v,hv⟩ : ∃ (I : Type u) (_ : Finite I) (v : I → N),
      Submodule.span R (Set.range v) = ⊤ :=
    Submodule.fg_iff_exists_finite_generating_family.mp (Module.Finite.fg_top (R := R) (M := N))
  let f : ModuleCat.of R (I →₀ R) ⟶ N := ModuleCat.ofHom (X := I →₀ R) (Y := N) (Finsupp.linearCombination (M := N) R v)
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr <| by
    change Function.Surjective (Finsupp.linearCombination (M := N) R v)
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hv]
  let p : SheafOfModules.free I ⟶ M :=
    (tildeFinsupp I).inv ≫ (tilde.functor R).map f ≫ M.fromTildeΓ
  have hmap : Epi ((tilde.functor R).map f) := inferInstance
  have : Epi M.fromTildeΓ := inferInstance
  have hp : Epi p := by
    change Epi ((tildeFinsupp I).inv ≫ (tilde.functor R).map f ≫ M.fromTildeΓ)
    let hΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
    exact epi_iso_comp_iso (tildeFinsupp I).symm ((tilde.functor R).map f) hmap
      (@asIso _ _ _ _ M.fromTildeΓ hΓ)
  let s : M.GeneratingSections := {
    I := I
    s := M.freeHomEquiv p
    epi := by simpa only [Equiv.symm_apply_apply] using hp }
  exact ⟨s, ⟨hI⟩⟩

theorem affine_exists_finite_generators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let f := X.isoSpec.inv
  let J := M.restrict f
  let : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj J).obj.obj (op ⊤)) :=
    finite_isoSpec_sections M
  obtain ⟨s,hs⟩ := spec_exists_finite_generators J
  let g := X.isoSpec.hom
  let F : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor g
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction g).leftAdjoint_preservesColimits
  let t := s.map F (Scheme.Modules.restrictUnitIso g).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp g f).app M
  have e₂ : M.restrict (𝟙 X) ≅ J.restrict g := by
    change M.restrict (g ≫ f) ≅ J.restrict g at e₁
    simpa only [g, f, Iso.hom_inv_id] using e₁
  let e := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app M
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e t,
    ⟨hs.finite⟩⟩

end
end PiExponent.CoherentAffineFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalSectionClearing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
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

lemma restrictScalar_appIso (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens)
    (r : Γ(X,⊤)) :
    (f.appIso U).inv (restrictScalar Y U (f.appTop r)) =
      restrictScalar X (f ''ᵁ U) r := by
  have h := congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,f ''ᵁ U) => g r)
    (Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := U) (by simp))
  change (f.appIso U).inv ((f.appLE ⊤ U (by simp)) r) = _ at h
  have he : f.appLE ⊤ U (by simp) = f.appTop ≫ Y.presheaf.map U.leTop.op := by
    erw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rw [he] at h
  exact h

end
end PiExponent.GlobalSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteGlobalPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FiniteGlobalPresentation
noncomputable section
universe u v₁ v₂ u₁ u₂
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.CoherentAffineFinite

theorem spec_kernel_isQuasicoherent {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  let hm := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let hn := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let em := @asIso _ _ _ _ M.fromTildeΓ hm
  let en := @asIso _ _ _ _ N.fromTildeΓ hn
  let g := (tilde.functor R).preimage
    (em.hom ≫ f ≫ en.inv)
  let e : (tilde.functor R).obj (kernel g) ≅ kernel f :=
    PreservesKernel.iso (tilde.functor R) g ≪≫
      kernel.mapIso ((tilde.functor R).map g) f em
        en (by
          change (tilde.functor R).map ((tilde.functor R).preimage _) ≫ _ = _
          erw [Functor.map_preimage]
          exact (Category.assoc em.hom (f ≫ en.inv) en.hom).trans
            (congrArg (fun q => em.hom ≫ q)
              ((Category.assoc f en.inv en.hom).trans
                ((congrArg (fun q => f ≫ q) en.inv_hom_id).trans (Category.comp_id f)))))
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    (inferInstanceAs (tilde (kernel g)).IsQuasicoherent)

theorem spec_exists_finitePresentation_of_sections {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] :
    ∃ P : M.Presentation, P.IsFinite := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  obtain ⟨P,hP⟩ := tilde_exists_finitePresentation
    ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))
  let h := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact ⟨presentationOfIso (@asIso _ _ _ _ M.fromTildeΓ h) P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem spec_kernel_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] (f : M ⟶ N) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  have := spec_kernel_isQuasicoherent f
  have : (moduleSpecΓFunctor (R := R)).IsRightAdjoint := tilde.adjunction.isRightAdjoint
  have : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    inferInstanceAs (Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)))
  let g := moduleSpecΓFunctor.map (kernel.ι f)
  have : Mono g := inferInstanceAs (Mono (moduleSpecΓFunctor.map (kernel.ι f)))
  have : Module.Finite R ((modulesSpecToSheaf.obj (kernel f)).obj.obj (op ⊤)) :=
    Module.Finite.of_injective g.hom ((ModuleCat.mono_iff_injective g).mp inferInstance)
  exact spec_exists_finitePresentation_of_sections (kernel f)

theorem isFinitePresentation_of_affine_presentations {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ U : X.affineOpens, ∃ P : (M.restrict U.1.ι).Presentation, P.IsFinite) :
    M.IsFinitePresentation := by
  classical
  let pres (U : X.affineOpens) := (h U).choose
  have hpres (U : X.affineOpens) : (pres U).IsFinite := (h U).choose_spec
  let q : M.QuasicoherentData := {
    I := X.affineOpens
    X U := U.1
    coversTop := by
      rw [Opens.coversTop_iff]
      apply top_unique
      intro x hx
      obtain ⟨U,hU,hxU,hUt⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Opens.mem_iSup.mpr ⟨⟨U,hU⟩,hxU⟩
    presentation U := presentationOver_of_restrict M U.1 (pres U) }
  have : q.IsFinitePresentation := by
    constructor
    intro U
    change (presentationOver_of_restrict M U.1 (pres U)).IsFinite
    infer_instance
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem affine_kernel_exists_finitePresentation {X : Scheme.{u}}
    [IsAffine X] [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hM : LocallyFinitelyGenerated M) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let F := Scheme.Modules.restrictFunctor a
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (M.restrict a)).obj.obj (op ⊤)) :=
    spec_sections_finite_of_localGenerators (M.restrict a) (hM.restrict a)
  obtain ⟨P,hP⟩ := spec_kernel_exists_finitePresentation (F.map f)
  let e := PreservesKernel.iso F f
  let : IsIso e.inv := e.isIso_inv
  let P' := presentationOfIso e.symm P
  let b := X.isoSpec.hom
  let G : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{u,u} G :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P'.map G (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app (kernel f)
  have e₂ : (kernel f).restrict (𝟙 X) ≅ ((kernel f).restrict a).restrict b := by
    change (kernel f).restrict (b ≫ a) ≅ ((kernel f).restrict a).restrict b at e₁
    simpa only [b, a, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app (kernel f)
  let : IsIso e₃.hom := e₃.isIso_hom
  exact ⟨presentationOfIso e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem kernel_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  obtain ⟨P,hP⟩ := affine_kernel_exists_finitePresentation (F.map f)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.1.ι)
  let e := PreservesKernel.iso F f
  let : IsIso e.inv := e.isIso_inv
  exact ⟨presentationOfIso e.symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponent.FiniteGlobalPresentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleGlobalGeneration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CoherentAffineFinite
variable {X : Scheme.{0}}

lemma openSectionEquiv_restrict_from_top (M : X.Modules) (U : X.Opens)
    (z : Γ(M,⊤)) :
    openSectionEquiv M U (restrictSection U.ι ((moduleSectionEquiv M).symm z)) =
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op z := by
  rw [openSectionEquiv_restrict]
  have h := section_value_natural ((moduleSectionEquiv M).symm z)
    (homOfLE (show U ≤ ⊤ from le_top))
  rw [← moduleSectionEquiv_apply, Equiv.apply_symm_apply] at h
  exact h.symm

theorem affine_local_generators (M : X.Modules) [M.IsFinitePresentation]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ σ : (M.restrict U.ι).GeneratingSections, σ.IsFiniteType := by
  have : IsAffine U.toScheme := hU
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have := affine_sections_finite_of_localGenerators (M.restrict U.ι)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.ι)
  exact affine_exists_finite_generators (M.restrict U.ι)

end
end PiExponent.AmpleGlobalGeneration

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardAffine
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ClosedPushforwardAffine
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CoherentAffineFinite FiniteGlobalPresentation
variable {X Y : Scheme.{0}}

theorem affine_pushforward_quasicoherent [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  let MX := (Scheme.Modules.pushforward X.isoSpec.hom).obj M
  have : MX.IsQuasicoherent := GlobalSectionClearing.quasicoherent_pushforward_iso X.isoSpec M
  let MY := (Scheme.Modules.pushforward (Spec.map f.appTop)).obj MX
  have : MY.IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ MY).mpr (isIso_fromTildeΓ_pushforward f.appTop MX)
  have hback : ((Scheme.Modules.pushforward Y.isoSpec.inv).obj MY).IsQuasicoherent :=
    GlobalSectionClearing.quasicoherent_pushforward_iso Y.isoSpec.symm MY
  let e₁ := (Scheme.Modules.pushforward Y.isoSpec.inv).mapIso
    ((Scheme.Modules.pushforwardComp X.isoSpec.hom (Spec.map f.appTop)).app M)
  let e₂ := (Scheme.Modules.pushforwardComp (X.isoSpec.hom ≫ Spec.map f.appTop) Y.isoSpec.inv).app M
  have hf : (X.isoSpec.hom ≫ Spec.map f.appTop) ≫ Y.isoSpec.inv = f := by
    rw [Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let e₃ := (Scheme.Modules.pushforwardCongr hf).app M
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso (e₁ ≪≫ e₂ ≪≫ e₃) hback

theorem affine_exists_finitePresentation_of_sections [IsAffine X] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    ∃ P : M.Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let b := X.isoSpec.hom
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (M.restrict a)).obj.obj (op ⊤)) :=
    finite_isoSpec_sections M
  obtain ⟨P,hP⟩ := spec_exists_finitePresentation_of_sections (M.restrict a)
  let F : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{0,0} F :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P.map F (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app M
  have e₂ : M.restrict (𝟙 X) ≅ ((M.restrict a).restrict b) := by
    change M.restrict (b ≫ a) ≅ ((M.restrict a).restrict b) at e₁
    simpa only [a, b, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app M
  exact ⟨transportPresentation (Z := X) e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponent.ClosedPushforwardAffine

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardCoherent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ClosedPushforward

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma map_epi (f : X ⟶ Y) [IsClosedImmersion f] {M N : X.Modules}
    (φ : M ⟶ N) [Epi φ] : Epi ((Scheme.Modules.pushforward f).map φ) := by
  let FX := SheafOfModules.toSheaf.{0} X.ringCatSheaf
  let FY := SheafOfModules.toSheaf.{0} Y.ringCatSheaf
  let S := ShortComplex.mk _ _ (kernel.condition φ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel φ }
  have hepi : Epi (FX.map φ) := (ModuleSheafExact.shortExact_map X.ringCatSheaf hS).epi_g
  have hφ : TopCat.Presheaf.IsLocallySurjective (FX.map φ).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hepi
  have hloc : TopCat.Presheaf.IsLocallySurjective
      (FY.map ((Scheme.Modules.pushforward f).map φ)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    by_cases him : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := him
      obtain ⟨W,hWU,⟨s,hs⟩,hxW⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff _).mp hφ (f ⁻¹ᵁ U) t x hy
      obtain ⟨V',hV',hpre⟩ := f.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
      let V : Y.Opens := ⟨V', hV'⟩ ⊓ U
      have hV : f ⁻¹ᵁ V = W := by
        ext z
        change (f z ∈ V' ∧ f z ∈ U) ↔ z ∈ W
        have hh : f z ∈ V' ↔ z ∈ W := Set.ext_iff.mp hpre z
        exact ⟨fun h => hh.mp h.1, fun h => ⟨hh.mpr h,hWU h⟩⟩
      refine ⟨V,inf_le_right,?_,?_,⟩
      · change ∃ s, (φ.val.app (op (f ⁻¹ᵁ V))) s =
          N.val.map ((Opens.map f.base).map (homOfLE inf_le_right)).op t
        subst W
        exact ⟨s,hs⟩
      · exact ⟨(Set.ext_iff.mp hpre x).mpr hxW,hy⟩
    · let V : Y.Opens := U ⊓ ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      have hV : f ⁻¹ᵁ V = ⊥ := by
        ext x
        change (f x ∈ U ∧ f x ∉ Set.range f) ↔ False
        simp
      have := sections_empty N (f ⁻¹ᵁ V) hV
      refine ⟨V,inf_le_left,⟨0,?_⟩,⟨hy,him⟩⟩
      exact @Subsingleton.elim (N.val.obj (op (f ⁻¹ᵁ V))) (sections_empty N _ hV) _ _
  let : Epi (FY.map ((Scheme.Modules.pushforward f).map φ)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact FY.epi_of_epi_map inferInstance

instance preservesEpis (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).PreservesEpimorphisms where
  preserves {_ _} φ _ := map_epi f φ

instance preservesHomology (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance preservesFiniteColimits (f : X ⟶ Y) [IsClosedImmersion f] :
    PreservesFiniteColimits (Scheme.Modules.pushforward f) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

open PiExponent.CoherentAffineFinite PiExponent.FiniteGlobalPresentation
open PiExponent.ClosedPushforwardAffine

end PiExponentSeshadri.ClosedPushforward

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedImmersionSerreTransfer
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.FlasqueCohomology

namespace PiExponent.ClosedImmersionSerreTransfer

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma globalHom_push_bijective (M : X.Modules) :
    Function.Bijective (fun g : schemeUnit X ⟶ M =>
      structureMap f ≫ (Scheme.Modules.pushforward f).map g) := by
  constructor
  · intro a b h
    apply (globalHomEquiv X.ringCatSheaf M).injective
    exact (globalHom_push f M a).symm.trans
      ((congrArg (globalHomEquiv Y.ringCatSheaf _) h).trans (globalHom_push f M b))
  · intro b
    obtain ⟨a, ha⟩ := (globalHomEquiv X.ringCatSheaf M).surjective
      (globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M) b)
    refine ⟨a, ?_⟩
    apply (globalHomEquiv Y.ringCatSheaf _).injective
    exact (globalHom_push f M a).trans ha

end PiExponent.ClosedImmersionSerreTransfer

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardLinear
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ClosedImmersionSerreTransfer

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma baseScalars_comp_actual (p : Y ⟶ Spec (CommRingCat.of ℂ)) :
    baseScalars (f ≫ p) = f.appTop.hom.comp (baseScalars p) := by
  ext c
  simp only [baseScalars, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

lemma scalar_naturality (p : Y ⟶ Spec (CommRingCat.of ℂ)) (U : Y.Opens) (r : ℂ) :
    restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) =
      f.app U (restrictScalar Y U (baseScalars p r)) := by
  rw [baseScalars_comp_actual]
  change X.presheaf.map (homOfLE le_top).op (f.appTop (baseScalars p r)) = _
  exact (CategoryTheory.congr_fun (f.naturality (homOfLE le_top).op) (baseScalars p r)).symm

end
end PiExponent.ClosedImmersionSerreTransfer

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FrameSubopens
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} {M : X.Modules}

lemma restrictOpenFrame_coefficient_global {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (restrictOpenFrame h e) (restrictSection V.ι s) =
      (X.homOfLE h).appTop (coefficient e (restrictSection U.ι s)) := by
  unfold restrictOpenFrame
  rw [coefficient_transport]
  rw [← restrictSection_congr (X.homOfLE_ι h) s, Category.assoc]
  have he : (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).hom.app M ≫
      ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm.hom = 𝟙 _ :=
    Iso.hom_inv_id ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M)
  rw [he, Category.comp_id]
  exact coefficient_restrict_comp (X.homOfLE h) U.ι e s

end
end PiExponentSeshadri.Frames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InverseFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

lemma frame_generator_change (e f : M ≅ O X) :
    f.inv.app ⊤ (1 : Γ(X,⊤)) = (frameChange f e : Γ(X,⊤)) • e.inv.app ⊤ (1 : Γ(X,⊤)) := by
  have h := e.inv.app_smul (r := (frameChange f e : Γ(X,⊤)))
    (x := (1 : Γ(X,⊤)))
  change e.inv.app ⊤ ((frameChange f e : Γ(X,⊤)) * (1 : Γ(X,⊤)) : Γ(X,⊤)) = _ at h
  rw [mul_one] at h
  rw [← h]
  change f.inv.app ⊤ (1 : Γ(X,⊤)) = e.inv.app ⊤ (e.hom.app ⊤ (f.inv.app ⊤ (1 : Γ(X,⊤))))
  exact (congrArg (fun t => t.app ⊤ (f.inv.app ⊤ (1 : Γ(X,⊤)))) e.hom_inv_id).symm

end
end PiExponent.InverseFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveMonomialCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialCech

noncomputable section

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [AddCommGroup K]

def RegularOn {d : ℤ} (s : Set ι) (f : Laurent ι K d) : Prop :=
  ∀ a, f a ≠ 0 → ∀ k, a.val k < 0 → k ∈ s

end
end PiExponent.ProjectiveMonomialCech

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveMonomialCechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialCechHigher

noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech

variable {ι A K : Type*} [AddCommGroup A]

def differential {q : ℕ} (c : Cochain ι A q) : Cochain ι A (q + 1) :=
  fun t => ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • c (t ∘ k.succAbove)

theorem differential_cons {q : ℕ} (c : Cochain ι A (q + 1))
    (p : ι) (t : Fin (q + 2) → ι) :
    differential c (Fin.cons p t) =
      c t - differential (fun s : Fin (q + 1) → ι => c (Fin.cons p s)) t := by
  rw [differential, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ,
    Fin.succAbove_zero, Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove]
  change c t + (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k.val + 1) •
    c (Fin.cons p (t ∘ k.succAbove))) =
    c t - differential (fun s : Fin (q + 1) → ι => c (Fin.cons p s)) t
  rw [differential, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ, mul_neg_one, neg_zsmul]

theorem differential_sub {q : ℕ} (c e : Cochain ι A q) :
    differential (c - e) = differential c - differential e := by
  funext t
  simp only [differential, Pi.sub_apply, zsmul_sub, Finset.sum_sub_distrib]

@[simp] theorem differential_zero {q : ℕ} :
    differential (0 : Cochain ι A q) = 0 := by
  funext t
  simp only [differential, Pi.zero_apply, zsmul_zero, Finset.sum_const_zero]

theorem differential_squared {q : ℕ} (c : Cochain ι A q) :
    differential (differential c) = 0 := by
  induction q with
  | zero =>
      funext t
      simp only [differential, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_zsmul,
        Fin.val_succ, Fin.sum_univ_zero, add_zero]
      have hsingleton (f : Fin 1 → ι) : f = fun _ => f 0 := by
        funext i
        exact congrArg f (Subsingleton.elim i 0)
      simp only [hsingleton, Function.comp_apply]
      simp [Fin.succAbove]
      abel
  | succ q ih =>
      funext t
      let p := t 0
      let u := Fin.tail t
      have ht : t = Fin.cons p u := (Fin.cons_self_tail t).symm
      rw [ht, differential_cons]
      have hfun : (fun s : Fin (q + 1 + 1) → ι => differential c (Fin.cons p s)) =
          c - differential (fun s : Fin (q + 1) → ι => c (Fin.cons p s)) := by
        funext s
        exact differential_cons c p s
      rw [hfun, differential_sub, ih]
      simp

variable [Fintype ι] [AddCommGroup K]

def Regular {d : ℤ} {q : ℕ} (c : Cochain ι (Laurent ι K d) q) : Prop :=
  ∀ t, RegularOn (Set.range t) (c t)

def insertionSupport {d : ℤ} {q : ℕ} (c : Cochain ι (Laurent ι K d) (q + 1))
    (t : Fin (q + 1) → ι) : Finset (Monomial ι d) := by
  classical
  exact Finset.univ.biUnion fun p : ι => (c (Fin.cons p t)).support

def contraction {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1)) : Cochain ι (Laurent ι K d) q := by
  classical
  exact fun t => Finsupp.onFinset (insertionSupport c t)
    (fun a => c (Fin.cons (pivot a) t) a)
    (fun a ha => Finset.mem_biUnion.mpr
      ⟨pivot a, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ha⟩)

@[simp] theorem contraction_apply {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1))
    (t : Fin (q + 1) → ι) (a : Monomial ι d) :
    contraction pivot c t a = c (Fin.cons (pivot a) t) a := rfl

theorem differential_apply {d : ℤ} {q : ℕ} (c : Cochain ι (Laurent ι K d) q)
    (t : Fin (q + 2) → ι) (a : Monomial ι d) :
    differential c t a = differential (fun s => c s a) t := by
  simp only [differential, Finsupp.finsetSum_apply, Finsupp.smul_apply]

theorem differential_regular {d : ℤ} {q : ℕ}
    (c : Cochain ι (Laurent ι K d) q) (hc : Regular c) :
    Regular (differential c) := by
  intro t a ha k hk
  by_contra hnot
  apply ha
  rw [differential_apply]
  unfold differential
  apply Finset.sum_eq_zero
  intro i _
  have hz : c (t ∘ i.succAbove) a = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := hc (t ∘ i.succAbove) a hne k hk
    exact hnot ⟨i.succAbove j, hj⟩
  change (-1 : ℤ) ^ i.val • c (t ∘ i.succAbove) a = 0
  rw [hz, smul_zero]

theorem contraction_identity {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1)) :
    contraction pivot (differential c) + differential (contraction pivot c) = c := by
  funext t
  ext a
  simp only [Pi.add_apply, Finsupp.add_apply, contraction_apply, differential_apply]
  have h := differential_cons (fun s => c s a) (pivot a) t
  rw [h]
  exact sub_add_cancel _ _

end
end PiExponent.ProjectiveMonomialCechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem faceLE {q : ℕ} (t : Fin (q + 2) → J) (k : Fin (q + 2)) :
    intersection U t ≤ intersection U (t ∘ k.succAbove) :=
  intersectionLE U t k.succAbove

theorem scalar_differential_zero_degree {B I : Type*} [AddCommGroup B]
    (c : ProjectiveMonomialCechHigher.Cochain I B 0) (i j : I) :
    ProjectiveMonomialCechHigher.differential c (Fin.cons i (fun _ => j)) =
      c (fun _ => j) - c (fun _ => i) := by
  have hsingleton (f : Fin 1 → I) : f = fun _ => f 0 := by
    funext k
    exact congrArg f (Subsingleton.elim k 0)
  simp only [ProjectiveMonomialCechHigher.differential]
  simp only [hsingleton, Function.comp_apply]
  simp [Fin.succAbove, sub_eq_add_neg]

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechExtFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

def ActualExt (_ρ : K →+* Γ(X,⊤)) (A M : X.Modules) (q : ℕ) : Type 1 := Ext.{1} A M q

instance instAddCommGroupActualExt (A M : X.Modules) (q : ℕ) : AddCommGroup (ActualExt ρ A M q) :=
  inferInstanceAs (AddCommGroup (Ext.{1} A M q))

instance globalModule (A M : X.Modules) (q : ℕ) :
    Module Γ(X,⊤) (ActualExt ρ A M q) :=
  inferInstanceAs (Module Γ(X,⊤) (Ext.{1} A M q))

instance scalarModule (A M : X.Modules) (q : ℕ) : Module K (ActualExt ρ A M q) :=
  Module.compHom _ ρ

def connecting (A : X.Modules) (S : ShortComplex X.Modules) (hS : S.ShortExact) (q : ℕ) :
    ActualExt ρ A S.X₃ q →ₗ[K] ActualExt ρ A S.X₁ (q+1) where
  toFun x := Ext.comp x hS.extClass rfl
  map_add' x y := Ext.add_comp x y hS.extClass rfl
  map_smul' a x := by
    change Ext.comp ((ρ a) • (show Ext.{1} A S.X₃ q from x)) hS.extClass rfl =
      (ρ a) • Ext.comp x hS.extClass rfl
    exact Ext.smul_comp (C := X.Modules) (R := Γ(X, ⊤)) x hS.extClass rfl (ρ a)

lemma connecting_surjective (A : X.Modules) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ) :
    Function.Surjective (connecting ρ A S hS q) := by
  intro x
  exact Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl

end
end PiExponent.GeometrySupport.CechExtFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologySections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

abbrev schemeFreeOpen_p1 (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

@[instance_reducible] def freeOpenHomAddCommGroup (U : X.Opens) (M : X.Modules) :
    AddCommGroup (freeOpen X.ringCatSheaf U ⟶ M) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen_p1 U ⟶ M))

attribute [local instance] freeOpenHomAddCommGroup

local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) (freeOpen X.ringCatSheaf U ⟶ M) := sheafHomModule X _ _

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma restrictScalar_appIso (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens)
    (r : Γ(X,⊤)) :
    (f.appIso U).inv (restrictScalar Y U (f.appTop r)) =
      restrictScalar X (f ''ᵁ U) r := by
  have h := congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,f ''ᵁ U) => g r)
    (Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := U) (by simp))
  change (f.appIso U).inv ((f.appLE ⊤ U (by simp)) r) = _ at h
  have he : f.appLE ⊤ U (by simp) = f.appTop ≫ Y.presheaf.map U.leTop.op := by
    erw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rw [he] at h
  exact h

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

instance instAddCommGroupCarrierSections (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    AddCommGroup (Sections k M U) := inferInstanceAs (AddCommGroup (OpenSections M U))

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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
local instance instHasExtSheafOfModulesOpensCarrierCarrierCommRingCatRingCatSheaf_solutions : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt

abbrev schemeFreeOpen_p0 (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

def extSourceIso {E F : X.Modules} (e : E ≅ F) (M : X.Modules) (n : ℕ) :
    Ext.{1} (C := X.Modules) E M n ≃ₗ[Γ(X,⊤)] Ext.{1} (C := X.Modules) F M n where
  toFun := (Ext.mk₀ e.inv).precompOfLinear Γ(X,⊤) M (zero_add n)
  invFun := (Ext.mk₀ e.hom).precompOfLinear Γ(X,⊤) M (zero_add n)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveMonomialFinite
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialFinite
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open ProjectiveMonomialCech ProjectiveMonomialCechHigher

variable {ι K : Type*} [Fintype ι]

def AllNegative {d : ℤ} (a : Monomial ι d) : Prop := ∀ i, a.val i < 0

theorem allNegative_coordinate_bounds {d : ℤ} {a : Monomial ι d}
    (ha : AllNegative a) (i : ι) : d ≤ a.val i ∧ a.val i ≤ 0 := by
  classical
  refine ⟨?_, le_of_lt (ha i)⟩
  calc
    d = ∑ j, a.val j := a.property.symm
    _ ≤ a.val i := by
      simpa using Finset.sum_le_sum_of_subset_of_nonpos'
        (f := a.val) (show ({i} : Finset ι) ⊆ Finset.univ by simp)
        (fun j _ _ => le_of_lt (ha j))

instance allNegative_finite (d : ℤ) : Finite {a : Monomial ι d // AllNegative a} := by
  let f : {a : Monomial ι d // AllNegative a} → (ι → Set.Icc d 0) :=
    fun a i => ⟨a.val.val i, allNegative_coordinate_bounds a.property i⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i))

instance allNonnegative_finite (d : ℤ) :
    Finite {a : Monomial ι d // ∀ i, 0 ≤ a.val i} := by
  classical
  have hb (a : Monomial ι d) (ha : ∀ i, 0 ≤ a.val i) (i : ι) :
      a.val i ∈ Set.Icc 0 d := by
    refine ⟨ha i, ?_⟩
    calc
      a.val i ≤ ∑ j, a.val j := Finset.single_le_sum (fun j _ => ha j) (by simp)
      _ = d := a.property
  let f : {a : Monomial ι d // ∀ i, 0 ≤ a.val i} → (ι → Set.Icc 0 d) :=
    fun a i => ⟨a.val.val i, hb a.val a.property i⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i))

instance monomial_subsingleton [Subsingleton ι] (d : ℤ) : Subsingleton (Monomial ι d) := by
  classical
  constructor
  intro a b
  apply Subtype.ext
  funext i
  have hi : (Finset.univ : Finset ι) = {i} := by
    ext j
    simp [Subsingleton.elim j i]
  have ha : a.val i = d := by simpa only [hi, Finset.sum_singleton] using a.property
  have hb : b.val i = d := by simpa only [hi, Finset.sum_singleton] using b.property
  exact ha.trans hb.symm

variable [AddCommGroup K]

def filterCochain {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) : Cochain ι (Laurent ι K d) q := by
  classical
  exact fun t => (c t).filter p

@[simp] theorem filterCochain_apply {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) (t : Fin (q + 1) → ι)
    (a : Monomial ι d) : filterCochain p c t a = if p a then c t a else 0 := by
  classical
  rfl

theorem filterCochain_regular {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) (hc : Regular c) :
    Regular (filterCochain p c) := by
  classical
  intro t a ha i hi
  have hn : c t a ≠ 0 := by
    intro hz
    simp [filterCochain_apply, hz] at ha
  exact hc t a hn i hi

theorem differential_filterCochain {d : ℤ} {q : ℕ}
    (p : Monomial ι d → Prop) (c : Cochain ι (Laurent ι K d) q) :
    differential (filterCochain p c) = filterCochain p (differential c) := by
  classical
  funext t
  ext a
  simp only [differential_apply, filterCochain_apply]
  by_cases h : p a
  · simp only [h, ite_true]
  · simp [differential, h]

theorem filterCochain_closed {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) (hc : differential c = 0) :
    differential (filterCochain p c) = 0 := by
  rw [differential_filterCochain, hc]
  funext t
  ext a
  simp

theorem exact_of_obstruction_zero {d : ℤ} {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hclosed : differential c = 0)
    (hzero : ∀ t a, AllNegative a → c t a = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      refine ⟨fun t => isEmptyElim (t 0), ?_, ?_⟩
      · intro t
        exact isEmptyElim (t 0)
      · funext t
        exact isEmptyElim (t 0)
  | inr h =>
      let pivot : Monomial ι d → ι := fun a =>
        if ha : ∃ i, 0 ≤ a.val i then Classical.choose ha else Classical.choice h
      have hpivot (a : Monomial ι d) (ha : ¬ AllNegative a) : 0 ≤ a.val (pivot a) := by
        have hex : ∃ i, 0 ≤ a.val i := by
          simpa only [AllNegative, not_forall, not_lt] using ha
        simp only [pivot, dite_eq_left hex]
        exact Classical.choose_spec hex
      refine ⟨contraction pivot c, ?_, ?_⟩
      · intro t a ha k hk
        have hn : ¬ AllNegative a := by
          intro hb
          exact ha (hzero (Fin.cons (pivot a) t) a hb)
        obtain ⟨j, hj⟩ := hc (Fin.cons (pivot a) t) a ha k hk
        cases j using Fin.cases with
        | zero =>
            simp only [Fin.cons_zero] at hj
            rw [← hj] at hk
            exact False.elim ((not_lt_of_ge (hpivot a hn)) hk)
        | succ j => exact ⟨j, by simpa only [Fin.cons_succ] using hj⟩
      · have hid := contraction_identity pivot c
        rw [hclosed] at hid
        have hz : contraction pivot (0 : Cochain ι (Laurent ι K d) (q + 2)) = 0 := by
          funext t
          ext a
          rfl
        simpa only [hz, zero_add] using hid

theorem cocycle_eq_boundary_add_negative {d : ℤ} {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hclosed : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q,
      Regular b ∧ c = differential b + filterCochain AllNegative c := by
  classical
  let good := filterCochain (fun a => ¬ AllNegative a) c
  have hgood : Regular good := filterCochain_regular _ c hc
  have hgoodclosed : differential good = 0 := filterCochain_closed _ c hclosed
  obtain ⟨b, hb, hdb⟩ := exact_of_obstruction_zero good hgood hgoodclosed (by
    intro t a ha
    simp [good, ha])
  refine ⟨b, hb, ?_⟩
  rw [hdb]
  funext t
  ext a
  simp only [Pi.add_apply, Finsupp.add_apply, good, filterCochain_apply]
  by_cases ha : AllNegative a <;> simp [ha]

end
end PiExponent.ProjectiveMonomialFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveMonomialCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveMonomialCohomology
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech ProjectiveMonomialCechHigher ProjectiveMonomialFinite

variable {ι K : Type*} [Fintype ι] [CommRing K]

def differentialLinear (d : ℤ) (q : ℕ) :
    Cochain ι (Laurent ι K d) q →ₗ[K] Cochain ι (Laurent ι K d) (q + 1) where
  toFun := differential
  map_add' c e := by
    funext t
    simp only [differential, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext t
    simp only [differential, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

def regularCochains (d : ℤ) (q : ℕ) : Submodule K (Cochain ι (Laurent ι K d) q) where
  carrier := {c | Regular c}
  zero_mem' := by intro t a h; exact (h rfl).elim
  add_mem' {c e} hc he := by
    intro t a h i hi
    by_cases hca : c t a = 0
    · apply he t a _ i hi
      simpa only [Pi.add_apply, Finsupp.add_apply, hca, zero_add] using h
    · exact hc t a hca i hi
  smul_mem' r c hc := by
    intro t a h i hi
    apply hc t a _ i hi
    intro hz
    apply h
    simp [hz]

def cycles (d : ℤ) (q : ℕ) : Submodule K (Cochain ι (Laurent ι K d) q) :=
  regularCochains d q ⊓ (differentialLinear d q).ker

theorem degreeZero_coeff_eq {d : ℤ} (c : cycles (ι := ι) (K := K) d 0) (i j : ι) :
    c.val (fun _ => i) = c.val (fun _ => j) := by
  have hc := congrFun c.property.2 ![i, j]
  change differential c.val ![i, j] = 0 at hc
  rw [differential, Fin.sum_univ_two] at hc
  have h0 : (![i, j] ∘ (0 : Fin 2).succAbove) = (fun _ : Fin 1 => j) := by
    funext k
    fin_cases k
    rfl
  have h1 : (![i, j] ∘ (1 : Fin 2).succAbove) = (fun _ : Fin 1 => i) := by
    funext k
    fin_cases k
    rfl
  have hh : c.val (fun _ => j) - c.val (fun _ => i) = 0 := by
    simpa only [h0, h1, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
      neg_one_zsmul, sub_eq_add_neg] using hc
  exact (sub_eq_zero.mp hh).symm

theorem degreeZero_nonnegative [Nontrivial ι] {d : ℤ}
    (c : cycles (ι := ι) (K := K) d 0) (t : Fin 1 → ι) (a : Monomial ι d)
    (ha : c.val t a ≠ 0) : ∀ i, 0 ≤ a.val i := by
  intro i
  by_contra hi
  have hin : a.val i < 0 := lt_of_not_ge hi
  obtain ⟨j, hj⟩ := exists_ne i
  have ht : t = (fun _ => t 0) := by
    funext k
    exact congrArg t (Fin.eq_zero k)
  have he : c.val t = c.val (fun _ => j) := by
    rw [ht]
    exact degreeZero_coeff_eq c (t 0) j
  rw [he] at ha
  obtain ⟨k, hk⟩ := c.property.1 (fun _ => j) a ha i hin
  exact hj hk

def degreeZeroCoefficients (d : ℤ) (i : ι) :
    cycles (ι := ι) (K := K) d 0 →ₗ[K]
      ({a : Monomial ι d // ∀ j, 0 ≤ a.val j} → K) where
  toFun c a := c.val (fun _ => i) a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem degreeZeroCoefficients_injective [Nontrivial ι] (d : ℤ) (i : ι) :
    Function.Injective (degreeZeroCoefficients (ι := ι) (K := K) d i) := by
  intro c e h
  apply Subtype.ext
  funext t
  ext a
  by_cases ha : ∀ j, 0 ≤ a.val j
  · have hc : c.val t = c.val (fun _ => i) := by
      have ht : t = (fun _ => t 0) := by
        funext k
        exact congrArg t (Fin.eq_zero k)
      rw [ht]
      exact degreeZero_coeff_eq c (t 0) i
    have he : e.val t = e.val (fun _ => i) := by
      have ht : t = (fun _ => t 0) := by
        funext k
        exact congrArg t (Fin.eq_zero k)
      rw [ht]
      exact degreeZero_coeff_eq e (t 0) i
    rw [hc, he]
    exact congrFun h ⟨a, ha⟩
  · have hc : c.val t a = 0 := by
      by_contra hh
      exact ha (degreeZero_nonnegative c t a hh)
    have he : e.val t a = 0 := by
      by_contra hh
      exact ha (degreeZero_nonnegative e t a hh)
    rw [hc, he]

instance degreeZero_finite [IsNoetherianRing K] (d : ℤ) :
    Module.Finite K (cycles (ι := ι) (K := K) d 0) := by
  cases subsingleton_or_nontrivial ι with
  | inl h => infer_instance
  | inr h =>
      let i : ι := Classical.choice (inferInstance : Nonempty ι)
      exact Module.Finite.of_injective (degreeZeroCoefficients d i)
        (degreeZeroCoefficients_injective d i)

def boundaryMap (d : ℤ) (q : ℕ) :
    regularCochains (ι := ι) (K := K) d q →ₗ[K] cycles (ι := ι) (K := K) d (q + 1) :=
  ((differentialLinear (ι := ι) (K := K) d q).comp (regularCochains d q).subtype).codRestrict
    (cycles d (q + 1)) (fun c =>
      ⟨differential_regular c.val c.property, differential_squared c.val⟩)

def negativeCycles (d : ℤ) (q : ℕ) : Submodule K (cycles (ι := ι) (K := K) d (q + 1)) where
  carrier := {c | ∀ t a, ¬ AllNegative a → c.val t a = 0}
  zero_mem' := by
    intro t a ha
    rfl
  add_mem' {c e} hc he := by
    intro t a ha
    change c.val t a + e.val t a = 0
    rw [hc t a ha, he t a ha, zero_add]
  smul_mem' r c hc := by
    intro t a ha
    change r • (c.val t a) = 0
    rw [hc t a ha, smul_zero]

def negativeCoefficients (d : ℤ) (q : ℕ) :
    negativeCycles (ι := ι) (K := K) d q →ₗ[K]
      ((Fin (q + 2) → ι) → ({a : Monomial ι d // AllNegative a} → K)) where
  toFun c t a := c.val.val t a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem negativeCoefficients_injective (d : ℤ) (q : ℕ) :
    Function.Injective (negativeCoefficients (ι := ι) (K := K) d q) := by
  intro c e h
  apply Subtype.ext
  apply Subtype.ext
  funext t
  ext a
  by_cases ha : AllNegative a
  · exact congrFun (congrFun h t) ⟨a, ha⟩
  · rw [c.property t a ha, e.property t a ha]

instance negativeCycles_finite [IsNoetherianRing K] (d : ℤ) (q : ℕ) :
    Module.Finite K (negativeCycles (ι := ι) (K := K) d q) :=
  Module.Finite.of_injective (negativeCoefficients d q) (negativeCoefficients_injective d q)

theorem exists_negative_representative (d : ℤ) (q : ℕ)
    (c : cycles (ι := ι) (K := K) d (q + 1)) :
    ∃ z : negativeCycles (ι := ι) (K := K) d q,
      ∃ b : regularCochains (ι := ι) (K := K) d q,
        c = boundaryMap d q b + z.val := by
  classical
  let z : cycles (ι := ι) (K := K) d (q + 1) :=
    ⟨filterCochain AllNegative c.val,
      filterCochain_regular _ c.val c.property.1,
      filterCochain_closed _ c.val c.property.2⟩
  have hz : z ∈ negativeCycles d q := by
    intro t a ha
    change filterCochain AllNegative c.val t a = 0
    simp [ha]
  obtain ⟨b, hb, heq⟩ := cocycle_eq_boundary_add_negative c.val c.property.1 c.property.2
  exact ⟨⟨z, hz⟩, ⟨b, hb⟩, Subtype.ext heq⟩

theorem finite_of_boundary_annihilating_surjective [IsNoetherianRing K] (d : ℤ) (q : ℕ)
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : cycles (ι := ι) (K := K) d (q + 1) →ₗ[K] V)
    (hboundary : ∀ b, f (boundaryMap d q b) = 0)
    (hsurj : Function.Surjective f) : Module.Finite K V := by
  let g : negativeCycles (ι := ι) (K := K) d q →ₗ[K] V :=
    f.comp (negativeCycles d q).subtype
  apply Module.Finite.of_surjective g
  intro x
  obtain ⟨c, hc⟩ := hsurj x
  obtain ⟨z, b, heq⟩ := exists_negative_representative d q c
  refine ⟨z, ?_⟩
  change f z.val = x
  rw [← hc, heq, map_add, hboundary, zero_add]

end
end PiExponent.ProjectiveMonomialCohomology

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveFinitePushforwardCoherent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveFinitePushforwardCoherent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CoherentAffineFinite FiniteGlobalPresentation ClosedPushforwardAffine
variable {X Y : Scheme.{0}}

theorem affine_pushforward_sections_finite [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent]
    (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(Y,⊤) Γ((Scheme.Modules.pushforward f).obj M,⊤) := by
  have hfin : Module.Finite Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := by
    simpa only [Scheme.Hom.preimage_top] using! affine_sections_finite_of_localGenerators M hM
  let σ : Γ(Y,⊤) →+* Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) := (f.app ⊤).hom
  let : Algebra Γ(Y,⊤) Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) := σ.toAlgebra
  let : Module.Finite Γ(Y,⊤) Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) :=
    f.finite_app ⊤ (isAffineOpen_top Y)
  let : Module Γ(Y,⊤) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := Module.compHom _ σ
  let : IsScalarTower Γ(Y,⊤) Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) :=
    IsScalarTower.of_compHom _ _ _
  have h := Module.Finite.trans (R := Γ(Y,⊤))
    Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens))
  exact h

theorem affine_pushforward_exists_finitePresentation [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    ∃ P : ((Scheme.Modules.pushforward f).obj M).Presentation, P.IsFinite := by
  have := affine_pushforward_quasicoherent f M
  have := affine_pushforward_sections_finite f M hM
  exact affine_exists_finitePresentation_of_sections ((Scheme.Modules.pushforward f).obj M)

instance pushforward_isFinitePresentation (f : X ⟶ Y) [IsFinite f]
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  have hM := (locallyFinitelyGenerated_of_finitePresentation M).restrict (f ⁻¹ᵁ U.1).ι
  let : (M.restrict (f ⁻¹ᵁ U.1).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ U.1).ι M
  obtain ⟨P,hP⟩ := affine_pushforward_exists_finitePresentation (f ∣_ U.1)
    (M.restrict (f ⁻¹ᵁ U.1).ι) hM
  exact ⟨presentationOfIso U.1.toScheme
    (PiExponentSeshadri.OpenBaseChange.iso f U.1 M).symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponent.CurveFinitePushforwardCoherent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveZeroPole
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Polynomial nonZeroDivisors

namespace PiExponent.CurveZeroPole

instance zeroPrime_isPrime (F : Type*) [Field F] : (zeroPrime F).IsPrime :=
  RingHom.ker_isPrime Polynomial.constantCoeff

end PiExponent.CurveZeroPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveImageAffineCoordinates
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} [IsIntegral C]
variable {ι : Type}

def fieldAlgEquiv {D : Scheme.{0}} [IsIntegral D]
    (pC : C ⟶ Spec (.of ℂ)) (pD : D ⟶ Spec (.of ℂ))
    (e : C.functionField ≅ D.functionField)
    (he : Spec.map e.hom ≫ C.fromSpecStalk (genericPoint C) ≫ pC =
      D.fromSpecStalk (genericPoint D) ≫ pD) :
    letI := IntegralAffineOpenDimension.functionFieldAlgebra pC
    letI := IntegralAffineOpenDimension.functionFieldAlgebra pD
    C.functionField ≃ₐ[ℂ] D.functionField := by
  letI := IntegralAffineOpenDimension.functionFieldAlgebra pC
  letI := IntegralAffineOpenDimension.functionFieldAlgebra pD
  refine { e.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  have h : Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ pC) ≫ e.hom =
      Spec.preimage (D.fromSpecStalk (genericPoint D) ≫ pD) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact he
  exact congrArg (fun φ : CommRingCat.of ℂ ⟶ D.functionField => φ c) h

end PiExponent.CurveImageAffineCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveMonomialMap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveMonomialMap
open AlgebraicGeometry CategoryTheory MvPolynomial
open PiExponentSeshadri.Projective
open WeightedCompactification
attribute [local instance] MvPolynomial.gradedAlgebra

def genericMonomialMap
    {F E ι σ : Type u} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (x : ι → E) :
    Spec (CommRingCat.of E) ⟶ Proj (imageGrade (R := F) a) :=
  Spec.map (CommRingCat.ofHom (eval₂Hom (algebraMap F E) x)) ≫
    affineChartMap a z hz coordinate hcoordinate

end PiExponent.CurveMonomialMap

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

lemma cokernel_stalk_subsingleton {M N : X.Modules} (s : M ⟶ N) (x : X)
    (hx : x ∈ isoOpen s) :
    Subsingleton ((cokernel s).presheaf.stalk x) := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf ⋙
    TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let : F.PreservesZeroMorphisms := by
    constructor
    intro M N
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (0 : M ⟶ N)).hom = 0
    rw [Functor.map_zero]
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map 0 = 0
    exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_zero _ _
  let : PreservesColimitsOfSize.{0,0} F := by
    refine @comp_preservesColimits _ _ _ _ _ _ _ _ ?_ ?_
    · exact PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits X.ringCatSheaf
    · exact inferInstanceAs (PreservesColimitsOfSize.{0,0}
        (TopCat.Sheaf.forget AddCommGrpCat.{0} (X : TopCat) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x))
  obtain ⟨U,hx,hU⟩ := (mem_isoOpen_iff s x).mp hx
  let := hU
  let : IsIso (F.map s) := stalk_isIso_of_restrict s U.ι ⟨x,hx⟩
  have hz : IsZero (F.obj (cokernel s)) :=
    (isZero_cokernel_of_epi (F.map s)).of_iso (PreservesCokernel.iso F s)
  exact AddCommGrpCat.subsingleton_of_isZero hz

theorem finite_closed_complement [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (U : X.Opens) (hU : U ≠ ⊥) :
    ((U : Set X)ᶜ).Finite ∧ ∀ x ∉ U, IsClosed ({x} : Set X) := by
  have hproper : (U : Set X)ᶜ ≠ Set.univ := by
    intro he
    apply hU
    apply SetLike.coe_injective
    simpa using he
  refine ⟨proper_closed_finite_of_dimension_one hd U.isOpen.isClosed_compl hproper, ?_⟩
  intro x hx
  have hc : closure ({x} : Set X) ⊆ (U : Set X)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) U.isOpen.isClosed_compl
  have hsub : (closure ({x} : Set X)).Subsingleton :=
    proper_irreducible_closed_subsingleton hd isClosed_closure
      isIrreducible_singleton.closure (fun he => hproper (Set.eq_univ_of_univ_subset (he ▸ hc)))
  have he : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact hsub hy (subset_closure (Set.mem_singleton x))
    · exact subset_closure
  exact he ▸ isClosed_closure

end PiExponent.CurveNormalizationDegree

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

instance parameterChart_noetherian [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsNoetherianRing (parameterChart f hf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  infer_instance

attribute [local instance] specializationOrder

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateRingNaturality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri
namespace Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
lemma isoPreimageSectionRingEquiv_symm (X Y : Scheme) (f : X ≅ Y) (V : Y.Opens)
    (a : Γ(Y,V)) :
    (isoPreimageSectionRingEquiv f V).symm a = f.hom.app V a := by
  change (((IsOpenImmersion.ΓIso f.hom V) ≪≫
    Y.presheaf.mapIso (eqToIso (show V = f.hom.opensRange ⊓ V by
      rw [Scheme.Hom.opensRange_of_isIso, top_inf_eq])).op).inv).hom a = _
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    IsOpenImmersion.ΓIso_inv, Scheme.Hom.map_appLE, Scheme.Hom.appLE_eq_app]

lemma isoPreimageSectionRingEquiv_appLE {X Y : Scheme} (f : X ≅ Y)
    (V : Y.Opens) (U : X.Opens) (h : U = f.hom ⁻¹ᵁ V) (a : Γ(Y,V)) :
    (isoPreimageSectionRingEquiv f V)
      (X.presheaf.map (eqToHom h.symm).op (f.hom.appLE V U h.le a)) = a := by
  subst U
  simpa [Scheme.Hom.appLE_eq_app, isoPreimageSectionRingEquiv_symm] using
    (isoPreimageSectionRingEquiv f V).apply_symm_apply a

attribute [local instance] MvPolynomial.gradedAlgebra

end

end Projective
end PiExponentSeshadri

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

theorem linearEquation_homogeneous (v : σ → K) :
    linearEquation v ∈ PolyGrade K σ 1 :=
  IsHomogeneous.sum _ _ _ (fun _i _ => isHomogeneous_C_mul_X _ _)

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

theorem projection_eq_structureMap (F : Type) [CommRing F] :
    polynomialProjectiveProjection F Bool = ProjectiveLine.structureMap F := by
  have hc : (polynomialGradeZeroEquiv F Bool).toRingHom =
      ProjectiveLine.constantsInDegreeZero F := by
    ext r
    rfl
  rw [polynomialProjectiveProjection, ProjectiveLine.structureMap, hc]

end
end PiExponent.ProjectivePencilScalars

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoherentExtFiniteness
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentExtFiniteness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry

universe w v u t k
variable {K : Type k} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
    [Linear K C] [HasExt.{w} C]

theorem ext_finite_of_presentations {ι : Type t} (A : C) (F : ι → C) (l : ℕ)
    (hbound : ∀ i q, l ≤ q → ∀ x : Ext.{w} A (F i) q, x = 0)
    (presentation : ∀ i, FiniteCohomologyPresentation (K := K) A F i)
    (i : ι) (q : ℕ) : Module.Finite K (Ext.{w} A (F i) q) := by
  have hdown : ∀ k q, l ≤ q + k → ∀ i, Module.Finite K (Ext.{w} A (F i) q) := by
    intro k
    induction k with
    | zero =>
      intro q hq i
      let : Subsingleton (Ext.{w} A (F i) q) :=
        ⟨fun x y => (hbound i q (by omega) x).trans (hbound i q (by omega) y).symm⟩
      infer_instance
    | succ k ih =>
      intro q hq i
      let P := presentation i
      let S := ShortComplex.mk P.left P.right P.comp_zero
      let : Module.Finite K (Ext.{w} A S.X₂ q) := P.finite q
      let : Module.Finite K (Ext.{w} A S.X₁ (q+1)) := ih (q+1) (by omega) P.kernel
      exact finite_middle_of_exact
        (PiExponentSeshadri.Cohomology.cohomologyMap₂ (K := K) A (S := S) q)
        (PiExponentSeshadri.Cohomology.cohomologyBoundary (K := K) A P.shortExact q)
        (PiExponentSeshadri.Cohomology.cohomology_exact₃ (K := K) A P.shortExact q)
  exact hdown l q (Nat.le_add_left _ _) i

end
end PiExponent.CoherentExtFiniteness

end OAI
end


