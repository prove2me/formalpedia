-- Prove2me | Definitions.Def_OAIQ068A045
-- name    : OAIQ068A045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:28:26.111978+00:00
-- url     : https://prove2.me/theorems/48723212-01f9-4d67-8107-b3f2c4d2d160
-- title:
--   Definitions bundle OAIQ068A045 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 definitions. The definitions and types are `OAI.PiExponent.ProjectiveSectionExtension.quotientPowerIso`, `OAI.PiExponent.ProjectiveSectionExtension.quotientSectionsEquiv`, `OAI.PiExponentSeshadri.Geometry.closedLineUnitKernelIso`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: [`PiExponent_Approximation_ClosedUnitKernel`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/ClosedUnitKernel.lean), [`PiExponent_Geometry_ProjectiveSectionPullback`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionPullback.lean).
--
--   **Imports.** It imports the bundles `OAIQ068A040`, `OAIQ068A041` and `OAIQ068A042` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI_PiExponentSeshadri_ComponentAmpleDescent_isAmple_of_reduced_closed_cover`, `OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover_q68`, `OAI_PiExponent_ProjectiveSectionExtension_eventual_projective_pullbackPowerSection_surjective` and `OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A041
import Definitions.Def_OAIQ068A042

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedUnitKernel
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open PiExponentSeshadri.TensorPure


variable {X Y : Scheme.{0}}

def closedLineUnitKernelIso (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X) :
    moduleTensor X (PiExponentSeshadri.IdealModule.idealModule f) M.sheaf ≅
      kernel ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf) := by
  let S := ShortComplex.mk (PiExponentSeshadri.IdealModule.inclusion f)
    (PiExponentSeshadri.IdealModule.structureMap f) (kernel.condition _)
  let T := S.map (moduleTwistFunctor M 1)
  have hT : T.ShortExact := moduleTwistFunctor_shortExact M 1 S
    (PiExponentSeshadri.IdealModule.closedSequence_exact f)
  let e : T.X₁ ≅ kernel T.g :=
    hT.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  exact e ≪≫ kernel.mapIso T.g
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf)
    (moduleTensorUnit M.sheaf) (closedLineQuotientIso f M)
    (closedLineQuotientIso_map f M)

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionPullback
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveSectionExtension
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X Y : Scheme.{0}}

def quotientPowerIso (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ) :
    (moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj (structureSheaf X)) ≅
      (Scheme.Modules.pushforward f).obj (modulePow X (L.pullback f).sheaf n) :=
  (ProjectionFormula.twistIso f (structureSheaf X) L n).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTwistUnitIso (L.pullback f) n)

def quotientSectionsEquiv (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ) :
    GlobalSections Y ((moduleTwistFunctor L n).obj
      ((Scheme.Modules.pushforward f).obj (structureSheaf X))) ≃
    GlobalSections X (modulePow X (L.pullback f).sheaf n) :=
  (Iso.homCongr (Iso.refl (structureSheaf Y)) (quotientPowerIso L f n)).trans
    (globalPushEquiv f _).symm

end PiExponent.ProjectiveSectionExtension
end

end OAI
end


