-- Prove2me | Definitions.Def_OAIQ068A036
-- name    : OAIQ068A036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:14:55.49051+00:00
-- url     : https://prove2.me/theorems/c88051cf-aa53-45bd-b2e2-e686d23d39f5
-- title:
--   Definitions bundle OAIQ068A036 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 65 declarations of OpenAI's Lean: 9 definitions, 3 instances and 53 theorems. The definitions and types are `OAI.PiExponent.AdmissibleBlowupGeometry.exceptionalInclusion`, `OAI.PiExponent.CurveDegree.FiniteLineCohomology`, `OAI.PiExponent.CurveDegree.LineCohomologyTwoZero`, `OAI.PiExponent.CurveNormalizationDegree.pushforwardPullbackIso`, `OAI.PiExponent.CurveNormalizationModel.parameterCurvePolarization`, `OAI.PiExponent.ProjectionFormula.hom`, `OAI.PiExponent.ProjectionFormula.iso`, `OAI.PiExponent.SectionOrderDivisor.divisor`, `OAI.PiExponent.SectionOrderDivisor.zeroPointEmbedding`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AdmissibleBlowupGeometry`, `PiExponent_Ampleness_CurveBlowupImage`, `PiExponent_Ampleness_CurveNormalizationPolarization`, `PiExponent_Approximation_CoherentTwistPresentation`, `PiExponent_Approximation_InverseDualRestriction`, `PiExponent_Approximation_InverseFrames`, `PiExponent_Approximation_ProjectionFormula`, `PiExponent_Cohomology_CohomologyIso`, `PiExponent_Cohomology_CurveFinitePushforwardCohomology`, `PiExponent_Cohomology_CurveNormalizationEuler`, `PiExponent_Cohomology_FiniteCoverCohomology`, `PiExponent_Cohomology_PencilCohomology`, `PiExponent_Cohomology_PencilCohomologyCech`, `PiExponent_Cohomology_PencilCohomologyCharts`, `PiExponent_Cohomology_PencilCohomologySections`, `PiExponent_Cohomology_SerreVanishing`, `PiExponent_Geometry_AdmissibleCurveImage`, `PiExponent_Geometry_CurveDegreeAdditivity`, `PiExponent_Geometry_CurveNormalizationDegree`, `PiExponent_Geometry_CurveNormalizationInvariance`, `PiExponent_Geometry_CurveNormalizationUnit`, `PiExponent_Geometry_CurveSectionDegree`, `PiExponent_Geometry_ProjectiveFinitePencil`, `PiExponent_Geometry_SectionOrderDivisor`, `PiExponent_LocalAlgebra_SectionZeroIdeal`.
--
--   **Imports.** It imports the bundles `OAIQ068A028`, `OAIQ068A029` and `OAIQ068A030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A040`, `OAIQ068A041` and `OAIQ068A042`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A028
import Definitions.Def_OAIQ068A029
import Definitions.Def_OAIQ068A030

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

namespace ModuleMayerVietoris
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

variable [HasExt.{w} (SheafOfModules.{u} R)]

lemma union_ext_zero (U V : Opens X) (M : SheafOfModules.{u} R) (n : ℕ)
    (hU : ∀ x : Ext (freeOpen R U) M (n+1), x = 0)
    (hV : ∀ x : Ext (freeOpen R V) M (n+1), x = 0)
    (hUV : ∀ x : Ext (freeOpen R (U ⊓ V)) M n, x = 0)
    (x : Ext (freeOpen R (U ⊔ V)) M (n+1)) : x = 0 := by
  have hS := shortComplex_shortExact R U V
  have hmid (y : Ext (freeOpen R U ⊞ freeOpen R V) M (n+1)) : y = 0 := by
    apply Ext.biprodAddEquiv.injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        hU ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        hV ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃ hS M x (hmid _) (n₀ := n) (by omega)
  have hz0 : z = 0 := hUV z
  rw [hz0, Ext.comp_zero] at hz
  exact hz.symm

end ModuleMayerVietoris

namespace FiniteCoverCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

attribute [local instance] OAI.PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme
theorem affine_union_ext_zero (n : ℕ) (U : Fin (n+1) → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X (⨆ i, U i)) M (n+k+1)) : x = 0 := by
  induction n generalizing k with
  | zero =>
    have hsup : (⨆ i, U i) = U 0 := by
      apply le_antisymm
      · apply iSup_le
        intro i
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        exact le_rfl
      · exact le_iSup U 0
    revert x
    rw [hsup]
    exact affine_open_ext_zero (U 0) (hU 0) M (0+k)
  | succ n ih =>
    have hsup : (⨆ i, U i) = U 0 ⊔ ⨆ i : Fin (n+1), U i.succ :=
      le_antisymm (iSup_le (Fin.cases le_sup_left (fun i =>
        (le_iSup (fun i : Fin (n+1) => U i.succ) i).trans le_sup_right)))
        (sup_le (le_iSup U 0) (iSup_le (fun i => le_iSup U i.succ)))
    have hinf : U 0 ⊓ (⨆ i : Fin (n+1), U i.succ) =
        ⨆ i : Fin (n+1), U 0 ⊓ U i.succ := inf_iSup_eq _ _
    revert x
    rw [hsup, show n+1+k+1 = n+k+1+1 from by omega]
    intro x
    apply ModuleMayerVietoris.union_ext_zero X.ringCatSheaf (U 0)
      (⨆ i : Fin (n+1), U i.succ) M (n+k+1) ?_ ?_ ?_ x
    · intro y
      exact affine_open_ext_zero (U 0) (hU 0) M (n+k+1) y
    · intro y
      exact ih (fun i => U i.succ) (fun i => hU i.succ) (k+1) y
    · rw [hinf]
      intro y
      exact ih (fun i => U 0 ⊓ U i.succ) (fun i => (hU 0).inf (hU i.succ)) k y

end FiniteCoverCohomology

namespace FiniteCoverCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

attribute [local instance] OAI.PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'
theorem cover_ext_zero (n : ℕ) (U : Fin (n+1) → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M (n+k+1)) : x = 0 := by
  let e := FreeOpenUnit.freeTopIso X.ringCatSheaf
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X ⊤) M (n+k+1), z = 0 := by
    rw [← hcover]
    exact affine_union_ext_zero n U hU M k
  have h := congrArg (fun y => (Ext.mk₀ e.inv).comp y (zero_add (n+k+1)))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add _)))
  erw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp,
    Ext.comp_zero] at h
  exact h

end FiniteCoverCohomology

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentTwistPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

theorem moduleTensorRightFunctor_exact (L : LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.Exact) :
    (S.map (moduleTensorRightFunctor L.sheaf)).Exact := by
  apply PiExponent.CoherentTwist.exact_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  exact ShortComplex.exact_of_iso
    (S.mapNatIso (moduleTensorRestrictFrame U L.sheaf e)).symm
    (hS.map (Scheme.Modules.restrictFunctor U.ι))

theorem moduleTensorRightFunctor_shortExact (L : LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTensorRightFunctor L.sheaf)).ShortExact where
  exact := moduleTensorRightFunctor_exact L S hS.exact
  mono_f := by
    have := hS.mono_f
    exact moduleTensorMap_mono S.f L
  epi_g := by
    have := hS.epi_g
    exact moduleTensorMap_epi S.g L

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupGeometry
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

abbrev exceptionalInclusion : (J d).sheaf ⟶ structureSheaf (blowup d) :=
  PiExponentSeshadri.BlowupGluing.exceptionalInclusion (centerIdeal d)

theorem exceptional_presents :
    PresentsPullbackIdeal (centerIdeal d) (projection d) (J d) (exceptionalInclusion d) :=
  PiExponentSeshadri.BlowupGluing.exceptional_presents (centerIdeal d)

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_CurveBlowupImage
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
open PiExponentSeshadri.Geometry
variable {X B : Scheme.{0}}

theorem blowup_restrict_isIso {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) : IsIso (π ∣_ I.support.compl) := by
  apply (hπ.morphismRestrict I.support.compl).isIso_of_invertible
  have he : I.comap (Scheme.Opens.ι (X := X) I.support.compl) = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.val ∈ I.support ↔ False)
    exact iff_false_intro x.property
  rw [he]
  exact invertible_top _

end PiExponent.CurveBlowupImage

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_SerreVanishing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SerreVanishing

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian

universe u

variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem ext_eq_zero_of_affine_cover (l : ℕ) (hl : 0 < l)
    (U : Fin l → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) (M : X.Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : l ≤ q)
    (x : Abelian.Ext.{u+1} (C := X.Modules) (schemeUnit X) M q) : x = 0 := by
  cases l with
  | zero => exact False.elim (Nat.not_lt_zero 0 hl)
  | succ l =>
      have he : l + (q - (l + 1)) + 1 = q := by omega
      revert x
      clear hq
      rw [← he]
      exact PiExponentSeshadri.FiniteCoverCohomology.cover_ext_zero
        l U hU hcover M _

end

end PiExponent.SerreVanishing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CohomologyIso
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
variable {X : Scheme.{0}}

lemma eulerCharacteristic_iso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (d : ℕ) :
    eulerCharacteristic f d M = eulerCharacteristic f d N := by
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars f)
  let := Module.compHom (cohomology N n) (baseScalars f)
  exact (cohomologyIso f e n).finrank_eq

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InverseFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
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

lemma unit_inv_pure (N : X.Modules) (U : X.Opens) (x : N.val.obj (op U)) :
    (moduleTensorUnit N).inv.app U x = PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x := by
  have h : (moduleTensorUnit N).hom.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x) = x := by
    change (moduleTensorUnit N).hom.app U
      (PiExponentSeshadri.TensorPure.pure (structureSheaf X) N U (1 : Γ(X,U)) x) = x
    exact (unit_pure N U (1 : Γ(X,U)) x).trans (one_smul Γ(X,U) (show Γ(N,U) from x))
  calc
    (moduleTensorUnit N).inv.app U x =
        (moduleTensorUnit N).inv.app U
          ((moduleTensorUnit N).hom.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x)) :=
      congrArg (fun z => (moduleTensorUnit N).inv.app U z) h.symm
    _ = _ := congrArg (fun f => f.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x))
      (moduleTensorUnit N).hom_inv_id

lemma pairingFrame_apply (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (x : N.val.obj (op U)) :
    (pairingFrame E e).hom.app U x =
      E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U (e.inv.app U (1 : Γ(X,U))) x) := by
  change E.hom.app U ((moduleTensorMap e.inv (𝟙 N)).app U
    ((moduleTensorUnit N).inv.app U x)) = _
  rw [unit_inv_pure]
  exact congrArg (fun z => E.hom.app U z)
    (PiExponentSeshadri.TensorPure.map_pure e.inv (𝟙 N) U (1 : Γ(X,U)) x)

lemma pairing_apply (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U m n) =
      regularValue e.hom U m * regularValue (pairingFrame E e).hom U n := by
  have hm : m = (regularValue e.hom U m) • e.inv.app U (1 : Γ(X,U)) := by
    have h := e.inv.app_smul (r := (regularValue e.hom U m))
      (x := (1 : Γ(X,U)))
    change e.inv.app U (regularValue e.hom U m * (1 : Γ(X,U)) : Γ(X,U)) = _ at h
    rw [mul_one] at h
    rw [← h]
    exact (congrArg (fun t => t.app U m) e.hom_inv_id).symm
  calc
    regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U m n) =
        regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U ((regularValue e.hom U m) • e.inv.app U (1 : Γ(X,U))) n) :=
      congrArg (fun z => regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U z n)) hm
    _ = (regularValue e.hom U m) * regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U (e.inv.app U (1 : Γ(X,U))) n) := by
      erw [pure_smul_left]
      exact E.hom.app_smul _ _
    _ = _ := by
      dsimp only [regularValue]
      rw [pairingFrame_apply]

lemma pairing_inverse_generator (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (m : M.val.obj (op U)) :
    E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m ((pairingFrame E e).inv.app U (1 : Γ(X,U)))) = e.hom.app U m := by
  change regularValue E.hom U _ = regularValue e.hom U m
  erw [pairing_apply]
  have h := congrArg (fun t => t.app U (1 : Γ(X,U))) (pairingFrame E e).inv_hom_id
  change (pairingFrame E e).hom.app U ((pairingFrame E e).inv.app U (1 : Γ(X,U))) = (1 : Γ(X,U)) at h
  have hv : regularValue (pairingFrame E e).hom U
      ((pairingFrame E e).inv.app U (1 : Γ(X,U))) = 1 := h
  rw [hv, mul_one]

lemma dualMap_apply (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M)
    (U : X.Opens) (n : N.val.obj (op U)) :
    (dualMap E s).app U n = E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U (s.app U (1 : Γ(X,U))) n) := by
  change E.hom.app U ((moduleTensorMap s (𝟙 N)).app U
    ((moduleTensorUnit N).inv.app U n)) = _
  rw [unit_inv_pure]
  exact congrArg (fun z => E.hom.app U z)
    (PiExponentSeshadri.TensorPure.map_pure s (𝟙 N) U (1 : Γ(X,U)) n)

lemma dualMap_coefficient (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (s : O X ⟶ M) :
    endValue ((pairingFrame E e).inv ≫ dualMap E s) = coefficient e s := by
  change (dualMap E s).app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = e.hom.app ⊤ (s.app ⊤ (1 : Γ(X,⊤)))
  exact (dualMap_apply E s ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤)))).trans
    (pairing_inverse_generator E e ⊤ (s.app ⊤ (1 : Γ(X,⊤))))

end
end PiExponent.InverseFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InverseDualRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

lemma dualMap_restrict (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map (dualMap E s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
    dualMap (restrictPairing E U) (restrictSection U.ι s) := by
  ext A n
  change Γ(N, U.ι ''ᵁ A) at n
  change (U.ι.appIso A).hom ((dualMap E s).app (U.ι ''ᵁ A) n) =
    (dualMap (restrictPairing E U) (restrictSection U.ι s)).app A n
  erw [dualMap_apply E s (U.ι ''ᵁ A) n,
    dualMap_apply (restrictPairing E U) (restrictSection U.ι s) A n]
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) (1 : Γ(X,U.ι ''ᵁ A))) n)) =
    (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      ((moduleTensorRestrict U M N).inv.app A
        (PiExponentSeshadri.TensorPure.pure (M.restrict U.ι) (N.restrict U.ι) A
          ((restrictSection U.ι s).app A (1 : Γ(U.toScheme,A))) n)))
  erw [restrict_pure_inv U M N A
    ((restrictSection U.ι s).app A (1 : Γ(U.toScheme,A))) n]
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) (1 : Γ(X,U.ι ''ᵁ A))) n)) =
    (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) ((U.ι.appIso A).inv (1 : Γ(U.toScheme,A)))) n))
  rw [show (U.ι.appIso A).inv (1 : Γ(U.toScheme,A)) = (1 : Γ(X,U.ι ''ᵁ A)) from
    (U.ι.appIso A).inv.hom.map_one]

lemma dualMap_restrict_coefficient (E : moduleTensor X M N ≅ O X)
    (s : O X ⟶ M) (U : X.Opens) (e : M.restrict U.ι ≅ O U.toScheme) :
    endValue ((inverseOpenFrame E U e).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (dualMap E s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) =
    coefficient e (restrictSection U.ι s) := by
  erw [dualMap_restrict]
  exact dualMap_coefficient (restrictPairing E U) e (restrictSection U.ι s)

lemma dualSection_restrict_coefficient (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    endValue ((inverseOpenFrame (lineTensorInverseIso L) U e).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (L.dualSection s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) =
    coefficient e (restrictSection U.ι s) :=
  dualMap_restrict_coefficient (lineTensorInverseIso L) s U e

end
end PiExponent.InverseFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_SectionZeroIdeal
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SectionZeroIdeal
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionImageIdeal PiExponent.InverseFrames
variable {X : Scheme.{0}}

theorem zeroIdeal_on_frame (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    (zeroIdeal L s).ideal U =
      Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  let : L.inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  change (imageIdealSheaf (L.dualSection s)).ideal U = _
  rw [imageIdealSheaf_on_frame (L.dualSection s) U
    (inverseOpenFrame (lineTensorInverseIso L) U.1 e), dualSection_restrict_coefficient]

theorem zeroIdeal_ne_bot [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : zeroIdeal L s ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨V,hxV,⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨U,hU,hxU,hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let e := restrictOpenFrame hUV eV
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  intro h
  have hi := zeroIdeal_on_frame L s ⟨U,hU⟩ e
  rw [h] at hi
  have hz : U.topIso.hom (coefficient e (restrictSection U.ι s)) = 0 := by
    have hm := Ideal.subset_span (Set.mem_singleton
      (U.topIso.hom (coefficient e (restrictSection U.ι s))))
    rw [← hi] at hm
    exact hm
  have hc : coefficient e (restrictSection U.ι s) = 0 := by
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective).mp hz
  apply hs
  apply L.restricted_coefficient_injective U.ι e
  exact hc.trans ((congrArg (coefficient e) (restrictSection_zero U.ι)).trans
    (coefficient_zero e)).symm

end
end PiExponent.SectionZeroIdeal

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveDegreeAdditivity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

def FiniteLineCohomology (p : X ⟶ Spec (CommRingCat.of ℂ)) : Prop :=
  ∀ L : LineBundle X, ∀ n ≤ 1,
    let := Module.compHom (cohomology L.sheaf n) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf n)

def LineCohomologyTwoZero (X : Scheme.{0}) : Prop :=
  ∀ L : LineBundle X, Subsingleton (cohomology L.sheaf 2)

end
end PiExponent.CurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologySections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme.{0}}

instance LineBundle.quasicoherent (L : LineBundle X) : L.sheaf.IsQuasicoherent := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact ⟨⟨(SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf).choose⟩⟩

theorem LineBundle.affine_sections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) Γ(L.sheaf,⊤) := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact PiExponent.CoherentAffineFinite.affine_sections_finite L.sheaf

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

theorem LineBundle.affine_openSections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) (OpenSections L.sheaf ⊤) := by
  let : Module Γ(X,⊤) Γ(L.sheaf,⊤) := (L.sheaf.val.obj (op ⊤)).isModule
  let := L.affine_sections_finite
  exact Module.Finite.of_surjective (openTopSections L.sheaf).symm.toLinearMap
    (openTopSections L.sheaf).symm.surjective

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [CommRing K] {X : Scheme.{0}}

theorem polynomial_finite [IsAffine X] (k : K →+* Γ(X,⊤))
    (t : Γ(X,⊤)) (L : LineBundle X)
    (h : (Polynomial.eval₂RingHom k t).Finite) :
    letI := polynomialModule k t L.sheaf ⊤
    Module.Finite K[X] (Sections k L.sheaf ⊤) := by
  let : Algebra K[X] Γ(X,⊤) := (Polynomial.eval₂RingHom k t).toAlgebra
  let : Module.Finite K[X] Γ(X,⊤) := h
  let := polynomialModule k t L.sheaf ⊤
  let : Module.Finite Γ(X,⊤) (Sections k L.sheaf ⊤) := L.affine_openSections_finite
  let : IsScalarTower K[X] Γ(X,⊤) (Sections k L.sheaf ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  exact Module.Finite.trans Γ(X,⊤) (Sections k L.sheaf ⊤)

end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_cokernel_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K (Sections kW N ⊤ ⧸
      ((chartMap kU kW a hka L.sheaf e).range ⊔
        (chartMap kV kW b hkb P.sheaf d).range)) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  let := polynomialTower kU u L.sheaf ⊤
  let := polynomialTower kV v P.sheaf ⊤
  let := polynomialTower kW (a.appTop u) N ⊤
  let : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  let : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  have hDen (x : Sections kW N ⊤) : ∃ n : ℕ, ∃ y : Sections kV P.sheaf ⊤,
      (Polynomial.X : K[X])^n • G y = x := by
    let : Module Γ(V,⊤) (OpenSections N ⊤) :=
      Module.compHom (OpenSections N ⊤) b.appTop.hom
    let G' := chartModuleMap P.sheaf b d
    let : IsLocalizedModule.Away v G' := chartModuleMap_localize P.sheaf b d v hb
    obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away v G').surj _ _ x
    refine ⟨n,y,?_⟩
    change (Polynomial.eval₂RingHom kW (a.appTop u)) (Polynomial.X^n) • G y = x
    simp only [map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change b.appTop (v^n) • (x : OpenSections N ⊤) = G' y at hy
    change (a.appTop u)^n • (G' y : OpenSections N ⊤) = x
    erw [← hy, map_pow, ← mul_smul, ← mul_pow, huv, one_pow, one_smul]
  exact LaurentCech.cokernel_finite F G hInv hDen
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_intersection_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (_hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (hv : (Polynomial.eval₂RingHom kV v).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K ↥((chartMap kU kW a hka L.sheaf e).range ⊓
        (chartMap kV kW b hkb P.sheaf d).range) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  let := polynomialTower kU u L.sheaf ⊤
  let := polynomialTower kV v P.sheaf ⊤
  let := polynomialTower kW (a.appTop u) N ⊤
  let : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let : Module.Finite K[X] (Sections kV P.sheaf ⊤) := polynomial_finite kV v P hv
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  let : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  exact LaurentCech.intersection_finite F G hInv
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames
variable {K : Type} [Field K] {X : Scheme.{0}}

theorem finite_pencil_intersection (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    Module.Finite K ↥(twoBaseIntersection k L.sheaf U V) := by
  intro U V
  let W := U ⊓ V
  let a := X.homOfLE (show W ≤ U from inf_le_left)
  let b := X.homOfLE (show W ≤ V from inf_le_right)
  let kU := U.ι.appTop.hom.comp k
  let kV := V.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let u := coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))
  let v := coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))
  obtain ⟨hU,hu⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,hv⟩ := finite_pencil_chart k s hs true
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : a.opensRange = U.toScheme.basicOpen u := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact pencil_overlap_basic s false
  have hb : b.opensRange = V.toScheme.basicOpen v := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact pencil_overlap_basic s true
  let e := nestedRestriction L.sheaf (show W ≤ U from inf_le_left)
  let d := nestedRestriction L.sheaf (show W ≤ V from inf_le_right)
  let F := chartMap kU kW a (nestedBase k inf_le_left) (L.restrict U.ι).sheaf e
  let G := chartMap kV kW b (nestedBase k inf_le_right) (L.restrict V.ι).sheaf d
  let : Module.Finite K ↥(F.range ⊓ G.range) :=
    two_chart_intersection_finite kU kV kW a b (nestedBase k inf_le_left)
      (nestedBase k inf_le_right) u v ha hb (pencil_overlap_reciprocal s) hu hv
      (L.restrict U.ι) (L.restrict V.ι) (L.sheaf.restrict W.ι) e d
  let E := chartTop k L.sheaf W
  have he : (F.range ⊓ G.range).map E.toLinearMap = twoBaseIntersection k L.sheaf U V := by
    rw [Submodule.map_inf E.toLinearMap E.injective]
    exact congrArg₂ (· ⊓ ·) (chartMap_range_coherent k L.sheaf inf_le_left)
      (chartMap_range_coherent k L.sheaf inf_le_right)
  let : Module.Finite K ↥((F.range ⊓ G.range).map E.toLinearMap) :=
    Module.Finite.equiv (E.submoduleMap (F.range ⊓ G.range))
  rw [← he]
  infer_instance
end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames BaseSections
variable {K : Type} [Field K] {X : Scheme.{0}}

theorem finite_pencil_H0_finite [IsIntegral X]
    (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0) k
    Module.Finite K (cohomology L.sheaf 0) := by
  let U := SectionOpens.isoOpen (s false)
  let V := SectionOpens.isoOpen (s true)
  obtain ⟨hU,_⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,_⟩ := finite_pencil_chart k s hs true
  have hc : U ⊔ V = ⊤ := by
    apply top_unique
    intro x hx
    have : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp this
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  have hneU : (U : Set X).Nonempty := by
    by_contra h
    have he : U = ⊥ := by ext x; simp [Set.not_nonempty_iff_eq_empty.mp h]
    rw [he, bot_sup_eq] at hc
    have : IsAffine (⊤ : X.Opens).toScheme := hc ▸ hV
    exact hn (.of_isIso X.topIso.inv)
  have hneV : (V : Set X).Nonempty := by
    by_contra h
    have he : V = ⊥ := by ext x; simp [Set.not_nonempty_iff_eq_empty.mp h]
    rw [he, sup_bot_eq] at hc
    have : IsAffine (⊤ : X.Opens).toScheme := hc ▸ hU
    exact hn (.of_isIso X.topIso.inv)
  obtain ⟨x,hxU,hxV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen hneU hneV
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x,hxU,hxV⟩⟩
  let := finite_pencil_intersection k s hs L
  let : Module.Finite K (Sections k L.sheaf ⊤) := Module.Finite.of_injective
    (globalIntersection k L U V) (globalIntersection_injective k L U V)
  let := Module.compHom (cohomology L.sheaf 0) k
  exact Module.Finite.equiv (cohomologyZero k L.sheaf).symm

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry.BaseSections
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames
variable {K : Type} [Field K] {X : Scheme.{0}}

theorem finite_pencil_cokernel (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    Module.Finite K (Sections k L.sheaf (U ⊓ V) ⧸ twoBaseImage k L.sheaf U V) := by
  intro U V
  let W := U ⊓ V
  let a := X.homOfLE (show W ≤ U from inf_le_left)
  let b := X.homOfLE (show W ≤ V from inf_le_right)
  let kU := U.ι.appTop.hom.comp k
  let kV := V.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let u := coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))
  let v := coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))
  obtain ⟨hU,hu⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,hv⟩ := finite_pencil_chart k s hs true
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : a.opensRange = U.toScheme.basicOpen u := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact pencil_overlap_basic s false
  have hb : b.opensRange = V.toScheme.basicOpen v := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact pencil_overlap_basic s true
  let e := nestedRestriction L.sheaf (show W ≤ U from inf_le_left)
  let d := nestedRestriction L.sheaf (show W ≤ V from inf_le_right)
  let F := chartMap kU kW a (nestedBase k inf_le_left) (L.restrict U.ι).sheaf e
  let G := chartMap kV kW b (nestedBase k inf_le_right) (L.restrict V.ι).sheaf d
  let : Module.Finite K (Sections kW (L.sheaf.restrict W.ι) ⊤ ⧸ (F.range ⊔ G.range)) :=
    two_chart_cokernel_finite kU kV kW a b (nestedBase k inf_le_left)
      (nestedBase k inf_le_right) u v ha hb (pencil_overlap_reciprocal s) hu
      (L.restrict U.ι) (L.restrict V.ι) (L.sheaf.restrict W.ι) e d
  let E := chartTop k L.sheaf W
  have he : (F.range ⊔ G.range).map E.toLinearMap = twoBaseImage k L.sheaf U V := by
    rw [Submodule.map_sup]
    exact congrArg₂ (· ⊔ ·) (chartMap_range_coherent k L.sheaf inf_le_left)
      (chartMap_range_coherent k L.sheaf inf_le_right)
  let q := Submodule.Quotient.equiv (F.range ⊔ G.range)
    (twoBaseImage k L.sheaf U V) E he
  exact Module.Finite.of_surjective q.toLinearMap q.surjective
end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames BaseSections
variable {K : Type} [Field K] {X : Scheme.{0}} [IsNoetherian X]

theorem finite_pencil_H1_finite (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) k
    Module.Finite K (cohomology L.sheaf 1) := by
  let U := SectionOpens.isoOpen (s false)
  let V := SectionOpens.isoOpen (s true)
  obtain ⟨hU,_⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,_⟩ := finite_pencil_chart k s hs true
  have hc : U ⊔ V = ⊤ := by
    apply top_unique
    intro x hx
    have : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp this
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  let := Module.compHom (cohomology L.sheaf 1) k
  let := finite_pencil_cokernel k s hs L
  let e := twoBaseCohomologyOne k L.sheaf U V hU hV hc
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveFinitePencil
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurveProjection_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectiveLine.chartMap_isOpenImmersion _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectivePencil

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {K : Type} [Field K] {X : Scheme.{0}}

theorem H0_finite [IsIntegral X]
    (f : X ⟶ ProjectiveO1.projectiveSpace K Bool) [IsFinite f]
    (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0) (scalars f)
    Module.Finite K (cohomology L.sheaf 0) :=
  finite_pencil_H0_finite (scalars f) (coordinateSection f) (sections_cover f) hn L

theorem H1_finite [IsNoetherian X]
    (f : X ⟶ ProjectiveO1.projectiveSpace K Bool) [IsFinite f] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) (scalars f)
    Module.Finite K (cohomology L.sheaf 1) :=
  finite_pencil_H1_finite (scalars f) (coordinateSection f) (sections_cover f) L

end
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem H0_finite_complex [IsIntegral X]
    (f : X ⟶ ProjectiveLine.projectiveLine ℂ) [IsFinite f]
    (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0)
      (baseScalars (f ≫ ProjectiveLine.structureMap ℂ))
    Module.Finite ℂ (cohomology L.sheaf 0) := by
  rw [← scalars_eq_baseScalars f]
  exact H0_finite f hn L

theorem H1_finite_complex [IsNoetherian X]
    (f : X ⟶ ProjectiveLine.projectiveLine ℂ) [IsFinite f] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1)
      (baseScalars (f ≫ ProjectiveLine.structureMap ℂ))
    Module.Finite ℂ (cohomology L.sheaf 1) := by
  rw [← scalars_eq_baseScalars f]
  exact H1_finite f L

end PiExponent.ProjectivePencil

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_CurveNormalizationPolarization
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

def parameterCurvePolarization : LineBundle (parameterCurve f hf) :=
  (ProjectiveO1.lineBundle (R := ℂ) (σ := Bool)).pullback (parameterCurveProjection f hf)

theorem parameterCurve_finiteLineCohomology :
    CurveDegree.FiniteLineCohomology (parameterCurveStructureMap f hf) := by
  intro L n hn
  have h0 := ProjectivePencil.H0_finite_complex (parameterCurveProjection f hf)
    (parameterCurve_not_isAffine f hf) L
  have h1 := ProjectivePencil.H1_finite_complex (parameterCurveProjection f hf) L
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact h0
  · exact h1

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ProjectionFormula
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

def hom (M : X.Modules) (L : Y.Modules) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) L ⟶
      (Scheme.Modules.pushforward f).obj
        (moduleTensor X M ((Scheme.Modules.pullback f).obj L)) :=
  moduleTensorMap (𝟙 _) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L) ≫
    PiExponentSeshadri.PushforwardTensor.hom f _ _

lemma hom_pure (M : X.Modules) (L : Y.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (s : L.val.obj (op U)) :
    (hom f M L).app U (pure ((Scheme.Modules.pushforward f).obj M) L U m s) =
      pure M ((Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U) m
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).app U s) := by
  have ht := map_pure (𝟙 ((Scheme.Modules.pushforward f).obj M))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L) U m s
  have hp := PiExponentSeshadri.PushforwardTensor.hom_pure f M
    ((Scheme.Modules.pullback f).obj L) U m
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).app U s)
  exact (congrArg (fun z => (PiExponentSeshadri.PushforwardTensor.hom f M
    ((Scheme.Modules.pullback f).obj L)).app U z) ht).trans hp

@[reassoc] lemma naturality {M N : X.Modules} {L K : Y.Modules}
    (a : M ⟶ N) (b : L ⟶ K) :
    moduleTensorMap ((Scheme.Modules.pushforward f).map a) b ≫ hom f N K =
      hom f M L ≫ (Scheme.Modules.pushforward f).map
        (moduleTensorMap a ((Scheme.Modules.pullback f).map b)) := by
  unfold hom
  rw [← Category.assoc, ← moduleTensorMap_comp]
  rw [Category.comp_id, ← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]
  have ht := moduleTensorMap_comp (𝟙 _) ((Scheme.Modules.pushforward f).map a)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)
    ((Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map b))
  simp only [Category.id_comp] at ht
  rw [ht, Category.assoc, PiExponentSeshadri.PushforwardTensor.naturality]
  simp only [Category.assoc]

lemma unit_compatibility (M : X.Modules) :
    hom f M (structureSheaf Y) ≫
      (Scheme.Modules.pushforward f).map
        (moduleTensorMap (𝟙 M) (pullbackUnitIso f).hom ≫ (moduleTensorRightUnit M).hom) =
      (moduleTensorRightUnit ((Scheme.Modules.pushforward f).obj M)).hom := by
  apply PiExponentSeshadri.TensorPure.hom_ext
  intro U m a
  change Γ(M, f ⁻¹ᵁ U) at m
  change Γ(Y,U) at a
  let b : ((Scheme.Modules.pullback f).obj (structureSheaf Y)).val.obj (op (f ⁻¹ᵁ U)) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureSheaf Y)).app U a
  have hp := hom_pure f M (structureSheaf Y) U m a
  have ht := map_pure (𝟙 M) (pullbackUnitIso f).hom (f ⁻¹ᵁ U) m b
  have hu := right_unit_pure M (f ⁻¹ᵁ U) m ((pullbackUnitIso f).hom.app (f ⁻¹ᵁ U) b)
  have hv := right_unit_pure ((Scheme.Modules.pushforward f).obj M) U m a
  have hs := congrArg (fun r : Γ(X, f ⁻¹ᵁ U) => r • m) (pullback_unit_apply f U a)
  exact (congrArg (fun z => (moduleTensorRightUnit M).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (𝟙 M) (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U) z)) hp).trans
    ((congrArg (fun z => (moduleTensorRightUnit M).hom.app (f ⁻¹ᵁ U) z) ht).trans
      (hu.trans (hs.trans hv.symm)))

instance unit_isIso (M : X.Modules) : IsIso (hom f M (structureSheaf Y)) := by
  let e : moduleTensor X M ((Scheme.Modules.pullback f).obj (structureSheaf Y)) ≅ M :=
    moduleTensorIso (Iso.refl M) (pullbackUnitIso f) ≪≫ moduleTensorRightUnit M
  have hi : IsIso (hom f M (structureSheaf Y) ≫
      (Scheme.Modules.pushforward f).map
        (moduleTensorMap (𝟙 M) (pullbackUnitIso f).hom ≫ (moduleTensorRightUnit M).hom)) := by
    rw [unit_compatibility]
    infer_instance
  exact (isIso_comp_right_iff (C := Y.Modules) (hom f M (structureSheaf Y))
    ((Scheme.Modules.pushforward f).mapIso e).hom).mp hi

lemma framed_isIso (M : X.Modules) (L : Y.Modules) (e : L ≅ structureSheaf Y) :
    IsIso (hom f M L) := by
  have hn := naturality f (𝟙 M) e.hom
  have hi : IsIso (moduleTensorMap ((Scheme.Modules.pushforward f).map (𝟙 M)) e.hom ≫
      hom f M (structureSheaf Y)) := by
    infer_instance
  have hj : IsIso (hom f M L ≫ (Scheme.Modules.pushforward f).map
      (moduleTensorMap (𝟙 M) ((Scheme.Modules.pullback f).map e.hom))) := by
    rw [← hn]
    exact hi
  exact (isIso_comp_right_iff _ _).mp hj

lemma restrict_compatibility (U : Y.Opens) (M : X.Modules) (L : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (hom f M L) ≫
      (PiExponentSeshadri.OpenBaseChange.iso f U
        (moduleTensor X M ((Scheme.Modules.pullback f).obj L))).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M ((Scheme.Modules.pullback f).obj L)).hom =
    (moduleTensorRestrict U ((Scheme.Modules.pushforward f).obj M) L).hom ≫
      moduleTensorMap (PiExponentSeshadri.OpenBaseChange.iso f U M).hom (𝟙 _) ≫
      hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (L.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorMap (𝟙 _) ((PiExponentSeshadri.OpenBaseChange.leftSquare f U).hom.app L)) := by
  unfold hom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [PiExponentSeshadri.OpenBaseChange.tensor_square]
  rw [← Category.assoc, ← Category.assoc]
  erw [PiExponentSeshadri.TensorPure.restrict_map U (𝟙 ((Scheme.Modules.pushforward f).obj M))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)]
  simp only [Category.assoc]
  rw [← moduleTensorMap_comp_assoc]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_id]
  rw [Category.id_comp, PiExponentSeshadri.OpenBaseChange.unit_compatibility]
  have ht := moduleTensorMap_comp
    (PiExponentSeshadri.OpenBaseChange.iso f U M).hom (𝟙 _)
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (L.restrict U.ι))
    ((Scheme.Modules.pushforward (f ∣_ U)).map
      ((PiExponentSeshadri.OpenBaseChange.leftSquare f U).hom.app L))
  simp only [Category.comp_id] at ht
  rw [ht]
  simp only [Category.assoc]
  have hn := PiExponentSeshadri.PushforwardTensor.naturality (f ∣_ U)
    (𝟙 (M.restrict (f ⁻¹ᵁ U).ι))
    ((PiExponentSeshadri.OpenBaseChange.leftSquare f U).hom.app L)
  erw [(Scheme.Modules.pushforward (f ∣_ U)).map_id] at hn
  erw [hn]
  rw [← moduleTensorMap_comp_assoc, Category.comp_id, Category.id_comp]
  rfl

instance line_isIso (M : X.Modules) (L : LineBundle Y) : IsIso (hom f M L.sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U, hy, ?_⟩
  let : IsIso (hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (L.sheaf.restrict U.ι)) :=
    framed_isIso (f ∣_ U) _ _ e
  have hi : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (hom f M L.sheaf) ≫
      (PiExponentSeshadri.OpenBaseChange.iso f U
        (moduleTensor X M ((Scheme.Modules.pullback f).obj L.sheaf))).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M ((Scheme.Modules.pullback f).obj L.sheaf)).hom) := by
    rw [restrict_compatibility]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

def iso (M : X.Modules) (L : LineBundle Y) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) L.sheaf ≅
      (Scheme.Modules.pushforward f).obj (moduleTensor X M (L.pullback f).sheaf) :=
  @asIso Y.Modules _ _ _ (hom f M L.sheaf) (line_isIso f M L)

end
end PiExponent.ProjectionFormula

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveFinitePushforwardCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

theorem finiteDimensional_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (k : K →+* Γ(X,⊤))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (n : ℕ) (hn : n ≤ 1)
    (hfinite : letI := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
      FiniteDimensional K (cohomology M n)) :
    let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
    FiniteDimensional K (cohomology ((Scheme.Modules.pushforward f).obj M) n) := by
  let := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
  have := hfinite
  let e := cohomologyLowEquiv f k M U V hU hV hcover n hn
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

end
end PiExponent.CurveFinitePushforwardCohomology

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

theorem tensor_stalk_subsingleton (M : X.Modules) (L : LineBundle X) (x : X)
    [Subsingleton (M.presheaf.stalk x)] :
    Subsingleton ((moduleTensor X M L.sheaf).presheaf.stalk x) := by
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  exact stalk_subsingleton_of_localIso _ M x U hx
    ((moduleTensorRestrictFrame U L.sheaf e).app M)

theorem finite_support_tensor_euler (p : X ⟶ Spec (.of ℂ)) (M : X.Modules)
    (L : LineBundle X) (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) (d : ℕ) :
    eulerCharacteristic p d (moduleTensor X M L.sheaf) = eulerCharacteristic p d M := by
  have ht (x : X) (hx : x ∉ S) :
      Subsingleton ((moduleTensor X M L.sheaf).presheaf.stalk x) := by
    let := hsupp x hx
    exact tensor_stalk_subsingleton M L x
  let e := finiteSupportLocallyIsoGlobal (moduleTensor X M L.sheaf) M S hfin hclosed ht hsupp
    (fun x _ => by
      obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
      exact ⟨U,hx,⟨(moduleTensorRestrictFrame U L.sheaf e).app M⟩⟩)
  let := Module.compHom Γ(moduleTensor X M L.sheaf,⊤) (baseScalars p)
  let := Module.compHom Γ(M,⊤) (baseScalars p)
  let ec : Γ(moduleTensor X M L.sheaf,⊤) ≃ₗ[ℂ] Γ(M,⊤) :=
    { e.toAddEquiv with
      map_smul' := fun r x => e.map_smul (baseScalars p r) x }
  rw [finite_support_euler p _ S hfin hclosed ht,
    finite_support_euler p M S hfin hclosed hsupp]
  exact_mod_cast ec.finrank_eq

theorem cokernel_tensor_euler [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    {M N : X.Modules} (u : M ⟶ N) (hu : isoOpen u ≠ ⊥) (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic p d (moduleTensor X (cokernel u) L.sheaf) =
      eulerCharacteristic p d (cokernel u) := by
  obtain ⟨hfin,hclosed⟩ := finite_closed_complement hd (isoOpen u) hu
  exact finite_support_tensor_euler p _ L (isoOpen u : Set X)ᶜ hfin hclosed
    (fun x hx => cokernel_stalk_subsingleton u x (not_not.mp hx)) d

end PiExponent.CurveNormalizationDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveNormalizationEuler
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

theorem generic_extension_tensor_euler [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (B : X.Modules) (u : structureSheaf X ⟶ B) [Mono u]
    (hu : isoOpen u ≠ ⊥) (L : LineBundle X)
    (hO : LowCohomologyFinite p (structureSheaf X))
    (hB : LowCohomologyFinite p B) (hL : LowCohomologyFinite p L.sheaf)
    (hBL : LowCohomologyFinite p (moduleTensor X B L.sheaf))
    [Subsingleton (cohomology (structureSheaf X) 2)]
    [Subsingleton (cohomology L.sheaf 2)] :
    eulerCharacteristic p 1 (moduleTensor X B L.sheaf) - eulerCharacteristic p 1 B =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let T := ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel T (cokernelIsCokernel u) }
  let TL := T.map (moduleTensorRightFunctor L.sheaf)
  have hTL : TL.ShortExact := moduleTensorRightFunctor_shortExact L T hT
  let S : Set X := (isoOpen u : Set X)ᶜ
  obtain ⟨hfin,hclosed⟩ := finite_closed_complement hd (isoOpen u) hu
  have hsupp (x : X) (hx : x ∉ S) : Subsingleton ((cokernel u).presheaf.stalk x) :=
    cokernel_stalk_subsingleton u x (not_not.mp hx)
  have hsuppt (x : X) (hx : x ∉ S) :
      Subsingleton ((moduleTensor X (cokernel u) L.sheaf).presheaf.stalk x) := by
    let := hsupp x hx
    exact tensor_stalk_subsingleton _ L x
  have hOL := lowCohomologyFinite_of_iso p (moduleTensorUnit L.sheaf) hL
  have hQ := finite_supported_quotient p T hT hO hB S hfin hclosed hsupp
  have hQL := finite_supported_quotient p TL hTL hOL hBL S hfin hclosed hsuppt
  let : Subsingleton (cohomology (moduleTensor X (structureSheaf X) L.sheaf) 2) := by
    let := Module.compHom (cohomology (moduleTensor X (structureSheaf X) L.sheaf) 2) (baseScalars p)
    let := Module.compHom (cohomology L.sheaf 2) (baseScalars p)
    exact (cohomologyIso p (moduleTensorUnit L.sheaf) 2).injective.subsingleton
  let : Subsingleton (cohomology TL.X₁ (1+1)) := by
    change Subsingleton (cohomology (moduleTensor X (structureSheaf X) L.sheaf) 2)
    infer_instance
  have h₀ := eulerCharacteristic_add p hT 1 hO hB hQ
  have h₁ := eulerCharacteristic_add p hTL 1 hOL hBL hQL
  change eulerCharacteristic p 1 B = eulerCharacteristic p 1 (structureSheaf X) +
    eulerCharacteristic p 1 (cokernel u) at h₀
  change eulerCharacteristic p 1 (moduleTensor X B L.sheaf) =
    eulerCharacteristic p 1 (moduleTensor X (structureSheaf X) L.sheaf) +
    eulerCharacteristic p 1 (moduleTensor X (cokernel u) L.sheaf) at h₁
  rw [eulerCharacteristic_iso p (moduleTensorUnit L.sheaf),
    cokernel_tensor_euler p hd u hu L 1] at h₁
  omega

end PiExponent.CurveNormalizationDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveImage
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.AdmissibleCurveImage
open AdmissibleBlowupGeometry CurveBlowupImage
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem center_point_isClosed (x : compactification d)
    (hx : x ∈ (centerIdeal d).support) : IsClosed ({x} : Set (compactification d)) := by
  change x ∈ ((centerIdeal d).support : Set (compactification d)) at hx
  rw [centerIdeal_support d] at hx
  obtain ⟨j, z, rfl⟩ := Set.mem_iUnion.mp hx
  let q := CompactLogJetIdeal.point (d.curveCenters j) ≫ affineChart d
  let : IsClosedImmersion q := CompactJetIdeal.section_isClosedImmersion
    (compactificationStructureMap d) q (by
      dsimp [q]
      rw [Category.assoc, affineChart_over, CompactLogJetIdeal.point_section])
  have he : Set.range q = {q z} := by
    ext x
    constructor
    · rintro ⟨z',rfl⟩
      exact congrArg q (Subsingleton.elim z' z)
    · rintro rfl
      exact ⟨z,rfl⟩
  rw [← he]
  exact q.isClosedEmbedding.isClosed_range

theorem meets_center_complement (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :
    ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (centerIdeal d).support.compl :=
  exists_image_outside_closed_points (C.embedding ≫ projection d)
    (centerIdeal d).support (center_point_isClosed d) hn

end PiExponent.AdmissibleCurveImage

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationUnit
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X Y : Scheme.{0}}

def pushforwardPullbackIso (f : Y ⟶ X) (L : LineBundle X) :
    moduleTensor X ((Scheme.Modules.pushforward f).obj (structureSheaf Y)) L.sheaf ≅
      (Scheme.Modules.pushforward f).obj (L.pullback f).sheaf :=
  ProjectionFormula.iso f (structureSheaf Y) L ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTensorUnit (L.pullback f).sheaf)

end PiExponent.CurveNormalizationDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationInvariance
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem lowCohomologyFinite_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Spec (.of ℂ))
    (M : Y.Modules) [M.IsFinitePresentation]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (hM : LowCohomologyFinite (f ≫ p) M) :
    LowCohomologyFinite p ((Scheme.Modules.pushforward f).obj M) := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj M)).choose.isQuasicoherent
  intro n hn
  apply CurveFinitePushforwardCohomology.finiteDimensional_pushforward
    f (baseScalars p) M U V hU hV hcover n hn
  have hm := hM n hn
  rw [CurveFinitePushforwardCohomology.baseScalars_comp] at hm
  exact hm

theorem pullback_euler_degree_of_open_iso [IsIntegral X]
    [IsNoetherian X] [IsNoetherian Y] (f : Y ⟶ X) [IsFinite f]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (W : X.Opens) (hW : W ≠ ⊥) [IsIso (f ∣_ W)]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (L : LineBundle X)
    (hO : LowCohomologyFinite p (structureSheaf X))
    (hL : LowCohomologyFinite p L.sheaf)
    (hOY : LowCohomologyFinite (f ≫ p) (structureSheaf Y))
    (hLY : LowCohomologyFinite (f ≫ p) (L.pullback f).sheaf)
    [Subsingleton (cohomology (structureSheaf X) 2)]
    [Subsingleton (cohomology L.sheaf 2)] :
    eulerCharacteristic (f ≫ p) 1 (L.pullback f).sheaf -
        eulerCharacteristic (f ≫ p) 1 (structureSheaf Y) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let : IsDominant f := dominant_of_iso_restrict f W hW
  let : Mono (unitMap f) := unitMap_mono f
  let : (structureSheaf Y).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (L.pullback f).sheaf.IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (L.pullback f)
  let : (structureSheaf Y).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (structureSheaf Y)).choose.isQuasicoherent
  let : ((Scheme.Modules.pushforward f).obj (structureSheaf Y)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj (structureSheaf Y))).choose.isQuasicoherent
  let : ((Scheme.Modules.pushforward f).obj (L.pullback f).sheaf).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj (L.pullback f).sheaf)).choose.isQuasicoherent
  have hB := lowCohomologyFinite_pushforward f p (structureSheaf Y) U V hU hV hcover hOY
  have hPL := lowCohomologyFinite_pushforward f p (L.pullback f).sheaf U V hU hV hcover hLY
  have hBL := lowCohomologyFinite_of_iso p (pushforwardPullbackIso f L) hPL
  have h := generic_extension_tensor_euler p hd
    ((Scheme.Modules.pushforward f).obj (structureSheaf Y)) (unitMap f)
    (unitMap_isoOpen_ne_bot f W hW) L hO hB hL hBL
  rw [eulerCharacteristic_iso p (pushforwardPullbackIso f L)] at h
  rw [CurveFinitePushforwardCohomology.euler_one_pushforward f p
    (L.pullback f).sheaf U V hU hV hcover,
    CurveFinitePushforwardCohomology.euler_one_pushforward f p
      (structureSheaf Y) U V hU hV hcover] at h
  exact h

end PiExponent.CurveNormalizationDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveSectionDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.CurveSectionDegree


variable {X : Scheme.{0}}

theorem zeroPoint_ne_generic [IsIntegral X]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme) :
    (SectionZeroIdeal.zeroIdeal L s).subschemeι y ≠ genericPoint X := by
  let I := SectionZeroIdeal.zeroIdeal L s
  intro hy
  have hg : genericPoint X ∈ (I.support : Set X) := by
    rw [← I.range_subschemeι]
    exact ⟨y,hy⟩
  have htop : (Set.univ : Set X) ⊆ I.support := by
    rw [← genericPoint_spec X]
    exact closure_minimal (Set.singleton_subset_iff.mpr hg) I.support.isClosed
  apply SectionZeroIdeal.zeroIdeal_ne_bot L s hs
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  exact TopologicalSpace.Closeds.ext (Set.Subset.antisymm (Set.subset_univ _) htop)

end PiExponent.CurveSectionDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_SectionOrderDivisor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveSectionDegree

namespace PiExponent.SectionOrderDivisor


variable {X : Scheme.{0}} [IsIntegral X]

omit [IsIntegral X] in
theorem mem_zero_support_iff_not_isUnit (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (x : X) : x ∈ (SectionZeroIdeal.zeroIdeal L s).support ↔ ¬ IsUnit (coefficientGermAt L s x) := by
  let F := affineFrameAt L x
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := F.openSet) F.mem,
    SectionZeroIdeal.zeroIdeal_on_frame L s F.openSet F.frame,
    X.zeroLocus_span, X.zeroLocus_singleton]
  apply not_congr
  exact X.toRingedSpace.mem_basicOpen _ x F.mem

theorem orderAt_eq_zero_of_not_mem
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (x : CurvePoint X)
    (hx : x.1 ∉ (SectionZeroIdeal.zeroIdeal L s).support) : orderAt hDVR L s x = 0 := by
  let := hDVR x.1 x.2
  have hu : IsUnit (coefficientGermAt L s x.1) :=
    not_not.mp ((mem_zero_support_iff_not_isUnit L s x.1).not.mp hx)
  unfold orderAt
  rw [IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu]
  rfl

def zeroPointEmbedding (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    (SectionZeroIdeal.zeroIdeal L s).subscheme ↪ CurvePoint X where
  toFun y := ⟨(SectionZeroIdeal.zeroIdeal L s).subschemeι y, zeroPoint_ne_generic L s hs y⟩
  inj' _y _z h := (SectionZeroIdeal.zeroIdeal L s).subschemeι.isEmbedding.injective
    (congrArg (fun q : CurvePoint X => (q : X)) h)

theorem orderAt_finite_support
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    (Function.support (orderAt hDVR L s)).Finite := by
  let : Finite (SectionZeroIdeal.zeroIdeal L s).subscheme :=
    finite_subscheme_of_curve p hd _ (SectionZeroIdeal.zeroIdeal_ne_bot L s hs)
  apply (Set.finite_range (zeroPointEmbedding L s hs)).subset
  intro x hx
  have hmem : x.1 ∈ (SectionZeroIdeal.zeroIdeal L s).support := by
    by_contra hn
    exact hx (orderAt_eq_zero_of_not_mem hDVR L s x hn)
  change x.1 ∈ ((SectionZeroIdeal.zeroIdeal L s).support : Set X) at hmem
  rw [← (SectionZeroIdeal.zeroIdeal L s).range_subschemeι] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, Subtype.ext hy⟩

def divisor
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : CurvePoint X →₀ ℕ :=
  Finsupp.ofSupportFinite (orderAt hDVR L s) (orderAt_finite_support p hd hDVR L s hs)

@[simp] theorem divisor_apply
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (x : CurvePoint X) :
    divisor p hd hDVR L s hs x = orderAt hDVR L s x := rfl

end PiExponent.SectionOrderDivisor

end

end OAI
end


