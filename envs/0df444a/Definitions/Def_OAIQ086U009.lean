-- Prove2me | Definitions.Def_OAIQ086U009
-- name    : OAIQ086U009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:35:53.062178+00:00
-- url     : https://prove2.me/theorems/ce69ce3c-eda5-4db7-aca5-b68a4a6c3f7f
-- title:
--   Definitions bundle OAIQ086U009 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 108 declarations of OpenAI's Lean: 65 definitions, 2 instances and 41 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingTables.output`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.CompatibleBlockFrequency`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.CompatibleOldFrequency`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.HomogeneousRestrictionBound`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.ambientPrimalEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.codomainTransport`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.compatibleBlockFrequencyEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.component`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.dependentRowEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.fixedFrequencyEnergy`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.frequencyProdEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.hyperplaneExtensionEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.mapFintype`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.pointAppend`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.pointLift`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.pointPad`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.pointRestrict`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.rankComponent`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.smallCoeff`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.smallComponent`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.synthesis`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.ProductMixedSliceBound`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.UniformMixedBound`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.adaptedFiberCoefficient`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.coordinateOfData`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.extensionEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.frequencyBlockEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.imageAmbientEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.imagePullback`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.imageTranslate`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.leftRangeEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.primalA`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.primalD`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.primalW`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.productFiberCoefficient`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.productFrequencyEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.quotientRightEquiv`, `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.submoduleFintype`, `OAI.UniqueGamesTheorem.Inverse.KMSBasisInvariant.IsBasisInvariant`, `OAI.UniqueGamesTheorem.Inverse.KMSBasisInvariant.primalChange` and 25 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Inverse_KMSAffineRestrictionPresentationLemmas`, `UniqueGames_Inverse_KMSAnalyticBlockFrequenciesLemmas`, `UniqueGames_Inverse_KMSAnalyticCharacterInduction`, `UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportCoreLemmas`, `UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportLemmas`, `UniqueGames_Inverse_KMSAnalyticHybridEnergyLemmas`, `UniqueGames_Inverse_KMSFourthMomentMixedBaseLemmas`, `UniqueGames_Inverse_KMSFourthMomentMixedEnergyLemmas`, `UniqueGames_Inverse_KMSFourthMomentZoomInAlgebraLemmas`, `UniqueGames_Inverse_KMSKernelOrbitsFourierLemmas`, `UniqueGames_Inverse_KMSLowLevelLemmas`, `UniqueGames_Inverse_RowErasureMatrixLemmas`, `UniqueGames_Inverse_ShortcodeFiberLemmas`, `UniqueGames_Inverse_ShortcodeFromGrassmannLemmas`, `UniqueGames_Inverse_ShortcodeInterfaceLemmas`, `UniqueGames_PCP_Clone100`, `UniqueGames_PCP_FoldedEquationLemmas`, `UniqueGames_PCP_PreprocessingTablesLemmas`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_TableGapReductionLemmas`, `UniqueGames_Reduction_IncidenceProbabilityLemmas`, `UniqueGames_Soundness_ConditionalSimulationLemmas`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`; the bundles `OAIQ086U003`, `OAIQ086U004` and `OAIQ086U005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ086U011` and `OAIQ086U013`; the statements `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound`, `OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid` and `OAI.UniqueGamesTheorem.Inverse.ShortcodeTheorem.inversePrinciple`; the proofs of `OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.uniformMixedBound_of_affineDensityBound`, `OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid` and `OAI.UniqueGamesTheorem.Inverse.ShortcodeTheorem.inversePrinciple`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U003
import Definitions.Def_OAIQ086U004
import Definitions.Def_OAIQ086U005

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAffineRestrictionPresentationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The actual parameter space of an affine matrix restriction splits along a
complementary domain decomposition. The constrained coordinate is a map out of
`U / D`, while the complementary coordinate is an unrestricted map into `W`.
The equivalence transports the full uniform law to independent uniform factors.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

instance freeFintype [Finite E] [Finite F] (E₀ : Submodule F2 E)
    (W : Submodule F2 F) : Fintype (E₀ →ₗ[F2] W) := by
  classical
  letI : Fintype E₀ := Fintype.ofFinite E₀
  letI : Fintype W := Fintype.ofFinite W
  exact Fintype.ofInjective (fun C : E₀ →ₗ[F2] W => (C : E₀ → W))
    DFunLike.coe_injective

end
end UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit

end

section

/-!
# Actual Fourier components for the KMS analytic argument

All coefficients use normalized expectation on the primal matrix space; sums
over frequencies are unnormalized. These identities use only the common
trace-character Fourier infrastructure, not the legacy rank-level inequality.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Fourier synthesis in the actual trace-character orthonormal basis. -/
def synthesis (a : (F →ₗ[F2] E) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  ∑ S, a S • (fun X => (linearTraceCharacter S X).re)

/-- The component formed by retaining precisely the actual frequencies in P. -/
def component (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F) → ℝ :=
  synthesis fun T => if P T then linearCoeff f T else 0

/-- The rank-level component uses actual image dimension. -/
def rankComponent (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  component (fun T => Module.finrank F2 T.range = i) f

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
# Actual Hybrid derivative energy in product coordinates

Parseval and affine restriction merge the selected Fourier coefficients over
each actual compressed frequency. For a product splitting, explicit linear
equivalences identify the quotient by the first factor with the second factor,
and the first-factor subspace with its original space. Reindexing the frequency
sum therefore introduces no multiplicity or normalization factor.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Appendix.Derivatives

section ProductEquivalences

variable {R A U B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup U] [Module R U]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

/-- The first factor, regarded as its actual coordinate subspace. -/
def leftRangeEquiv : B ≃ₗ[R] LinearMap.range (LinearMap.inl R B C) where
  toFun b := ⟨(b, 0), ⟨b, rfl⟩⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := hx
    rfl
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

@[simp] theorem leftRangeEquiv_coe (b : B) :
    (leftRangeEquiv (R := R) (C := C) b : B × C) = (b, 0) := rfl

@[simp] theorem quotientRightMap_mkQ (x : A × U) :
    quotientRightMap (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

/-- The quotient by the first coordinate has the second coordinate as a
canonical linear presentation. -/
def quotientRightEquiv :
    ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U)) ≃ₗ[R] U where
  toLinearMap := quotientRightMap
  invFun u := (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u)
  left_inv := by
    intro q
    obtain ⟨⟨a, u⟩, rfl⟩ := (LinearMap.range (LinearMap.inl R A U)).mkQ_surjective q
    change (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) =
      (LinearMap.range (LinearMap.inl R A U)).mkQ (a, u)
    have hz : (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
    calc
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ (a, 0) +
          (LinearMap.range (LinearMap.inl R A U)).mkQ (0, u) := by rw [hz, zero_add]
      _ = (LinearMap.range (LinearMap.inl R A U)).mkQ ((a, 0) + (0, u)) :=
        (map_add _ _ _).symm
      _ = _ := by simp
  right_inv _ := rfl

@[simp] theorem quotientRightEquiv_mkQ (x : A × U) :
    quotientRightEquiv (R := R)
      ((LinearMap.range (LinearMap.inl R A U)).mkQ x) = x.2 := rfl

/-- The exact change of frequency coordinates for a product restriction. -/
def productFrequencyEquiv :
    ((LinearMap.range (LinearMap.inl R B C)) →ₗ[R]
      ((A × U) ⧸ LinearMap.range (LinearMap.inl R A U))) ≃ (B →ₗ[R] U) where
  toFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).toLinearMap)
  invFun Z := (quotientRightEquiv (R := R) (A := A) (U := U)).symm.toLinearMap.comp
    (Z.comp (leftRangeEquiv (R := R) (B := B) (C := C)).symm.toLinearMap)
  left_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  right_inv Z := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

end ProductEquivalences

section ProductEnergy

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C] in
/-- Actual quotient compression becomes the block compression. -/
@[simp] theorem productFrequencyEquiv_compressFrequency
    (S : (B × C) →ₗ[F2] (A × U)) :
    productFrequencyEquiv (Restriction.compressFrequency
      (LinearMap.range (LinearMap.inl F2 A U))
      (LinearMap.range (LinearMap.inl F2 B C)) S) =
      (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) := by
  apply LinearMap.ext
  intro b
  rfl

end ProductEnergy
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportCoreLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Transport of a prescribed compressed image to adapted coordinates

The complement is an arbitrary actual complement to the image subspace.
The resulting coordinate change carries each original Fourier fiber to the
adapted fiber, preserving coefficients, phases, and the actual selector.
-/

noncomputable section
namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter linearTraceCharacter_apply linearTracePair)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]

/-- Keep the selected first factor and split the remaining space along its
prescribed compressed image. -/
def imageAmbientEquiv (W D : Submodule F2 U) (h : IsCompl W D) :
    (A × (W × D)) ≃ₗ[F2] (A × U) :=
  (LinearEquiv.refl F2 A).prodCongr (imageCoordinates W D h).symm

/-- The original function expressed in the adapted primal coordinates. -/
def imagePullback (W D : Submodule F2 U) (h : IsCompl W D)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (X : (A × (W × D)) →ₗ[F2] (B × C)) : ℝ :=
  f (X.comp (imageAmbientEquiv (A := A) W D h).symm.toLinearMap)

/-- The same affine translate expressed in adapted coordinates. -/
def imageTranslate (W D : Submodule F2 U) (h : IsCompl W D)
    (T : (A × U) →ₗ[F2] (B × C)) :
    (A × (W × D)) →ₗ[F2] (B × C) :=
  T.comp (imageAmbientEquiv W D h).toLinearMap

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

section

/-!
# The actual small-space Fourier component

An injection from the small domain into the large domain lifts dual
frequencies by composition. Only surjective small-space frequencies are
retained. The identities below use the actual trace-character coefficients
and normalized primal expectation; no fourth-moment estimate is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

/-- The Fourier array of the small full-rank component. -/
def smallCoeff (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (T : F →ₗ[F2] I) : ℝ :=
  if Function.Surjective T then linearCoeff f (ι.comp T) else 0

/-- A genuine function on the small primal matrix space, synthesized in its
own orthonormal trace-character basis. -/
def smallComponent (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ) :
    (I →ₗ[F2] F) → ℝ := synthesis (smallCoeff ι f)

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

namespace UniqueGamesTheorem.Inverse.KMSBasisInvariant
noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- The invertible change of the ordered domain basis. -/
def primalChange (g : E ≃ₗ[F2] E) : (E →ₗ[F2] F) ≃ (E →ₗ[F2] F) where
  toFun X := X.comp g.toLinearMap
  invFun X := X.comp g.symm.toLinearMap
  left_inv X := by ext x; simp
  right_inv X := by ext x; simp

def IsBasisInvariant (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (g : E ≃ₗ[F2] E) X, f (X.comp g.toLinearMap) = f X

end
end UniqueGamesTheorem.Inverse.KMSBasisInvariant

end

section

/-!
# Homogeneous restriction bounds for the KMS character induction

The restriction below samples linear maps into an actual subspace of the
output. Quantifying over injective presentations makes the bound invariant
under a choice of coordinates. This is a transparent squared-density
hypothesis, not a Fourier, inverse, or fourth-moment estimate.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

universe u v
variable {E : Type u} {F B : Type v}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup B] [Module F2 B]

/-- Every homogeneous output restriction of codimension at most `r` has the
stated actual normalized squared norm. The dimension inequality avoids
truncated subtraction in the restriction-composition step. -/
def HomogeneousRestrictionBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (E →ₗ[F2] C)],
    ∀ J : C →ₗ[F2] F, Function.Injective J →
      Module.finrank F2 F ≤ Module.finrank F2 C + r →
        (𝔼 X : E →ₗ[F2] C, f (J.comp X) ^ 2) ≤ ε

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFourthMomentZoomInAlgebraLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The frequency dichotomy behind the KMS point-restriction recursion.
A row appended to a surjective frequency is either independent, or is the
unique pullback of a functional on the smaller frequency space.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters

variable {E F J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup J] [Module F2 J]

/-- Append the primal value at the last coordinate. -/
def pointAppend (X : E →ₗ[F2] F) (a : F) : (E × F2) →ₗ[F2] F :=
  X.coprod (LinearMap.toSpanSingleton F2 F a)

@[simp] theorem pointAppend_apply (X : E →ₗ[F2] F) (a : F) (x : E) (c : F2) :
    pointAppend X a (x, c) = X x + c • a := rfl

/-- Fix one primal column, with no averaging or normalization. -/
def pointRestrict (f : ((E × F2) →ₗ[F2] F) → ℝ) (a : F) :
    (E →ₗ[F2] F) → ℝ := fun X => f (pointAppend X a)

/-- Extend an injection while retaining the newly fixed coordinate. -/
def pointLift (ι : J →ₗ[F2] E) : (J × F2) →ₗ[F2] (E × F2) :=
  ι.prodMap LinearMap.id

/-- The lower-dimensional embedding into the old coordinates. -/
def pointPad (ι : J →ₗ[F2] E) : J →ₗ[F2] (E × F2) :=
  ι.prod 0

/-- A non-surjective appended row vanishes on the kernel of a surjective
base frequency; the proof explicitly constructs a preimage otherwise. -/
theorem ker_le_of_not_surjective_prod (T : F →ₗ[F2] J)
    (hT : Function.Surjective T) (ell : F →ₗ[F2] F2)
    (h : ¬ Function.Surjective (T.prod ell)) : T.ker ≤ ell.ker := by
  intro w hw
  change ell w = 0
  by_contra hn
  have hwT : T w = 0 := hw
  have hwell : ell w = 1 :=
    (UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases (ell w)).resolve_left hn
  apply h
  rintro ⟨y, c⟩
  obtain ⟨x, hx⟩ := hT y
  refine ⟨x + (c - ell x) • w, ?_⟩
  apply Prod.ext
  · change T (x + (c - ell x) • w) = y
    simp [hx, hwT]
  · change ell (x + (c - ell x) • w) = c
    simp [hwell]

/-- Exact factorization, including uniqueness, of every dependent row. -/
theorem not_surjective_prod_iff (T : F →ₗ[F2] J)
    (hT : Function.Surjective T) (ell : F →ₗ[F2] F2) :
    ¬ Function.Surjective (T.prod ell) ↔
      ∃! φ : J →ₗ[F2] F2, φ.comp T = ell := by
  constructor
  · intro h
    let φ := (T.ker.liftQ ell (ker_le_of_not_surjective_prod T hT ell h)).comp
      (T.quotKerEquivOfSurjective hT).symm.toLinearMap
    have hφ : φ.comp T = ell := by
      ext x
      simp [φ]
    refine ⟨φ, hφ, ?_⟩
    intro ψ hψ
    ext y
    obtain ⟨x, rfl⟩ := hT y
    exact (congrArg (fun L : F →ₗ[F2] F2 => L x) hψ).trans
      (congrArg (fun L : F →ₗ[F2] F2 => L x) hφ).symm
  · rintro ⟨φ, hφ, _⟩ hsurj
    obtain ⟨x, hx⟩ := hsurj (0, 1)
    have hTx : T x = 0 := congrArg Prod.fst hx
    have hellx : ell x = 1 := congrArg Prod.snd hx
    have he := congrArg (fun L : F →ₗ[F2] F2 => L x) hφ
    simp only [LinearMap.comp_apply, hTx, map_zero, hellx] at he
    exact zero_ne_one he

/-- Pullback along a surjection parametrizes the dependent rows exactly. -/
def dependentRowEquiv (T : F →ₗ[F2] J) (hT : Function.Surjective T) :
    (J →ₗ[F2] F2) ≃ {ell : F →ₗ[F2] F2 // ¬ Function.Surjective (T.prod ell)} where
  toFun φ := ⟨φ.comp T, (not_surjective_prod_iff T hT _).mpr
    ⟨φ, rfl, fun ψ hψ => by
      ext y
      obtain ⟨x, rfl⟩ := hT y
      exact congrArg (fun L : F →ₗ[F2] F2 => L x) hψ⟩⟩
  invFun ell := Classical.choose ((not_surjective_prod_iff T hT ell.val).mp ell.property)
  left_inv φ := by
    exact (Classical.choose_spec ((not_surjective_prod_iff T hT (φ.comp T)).mp
      ((not_surjective_prod_iff T hT _).mpr
        ⟨φ, rfl, fun ψ hψ => by
          ext y
          obtain ⟨x, rfl⟩ := hT y
          exact congrArg (fun L : F →ₗ[F2] F2 => L x) hψ⟩))).2 φ rfl |>.symm
  right_inv ell := by
    apply Subtype.ext
    exact (Classical.choose_spec
      ((not_surjective_prod_iff T hT ell.val).mp ell.property)).1

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
Exact Fourier merging when one primal column is fixed. All frequency sums
are unnormalized; the primal Fourier coefficient uses normalized expectation.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- Splitting the last frequency row is an exact bijection. -/
def frequencyProdEquiv : ((F →ₗ[F2] E) × (F →ₗ[F2] F2)) ≃
    (F →ₗ[F2] (E × F2)) where
  toFun p := p.1.prod p.2
  invFun S := ((LinearMap.fst F2 E F2).comp S,
    (LinearMap.snd F2 E F2).comp S)
  left_inv _ := rfl
  right_inv _ := rfl

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
A transparent local squared-density hypothesis for the new KMS point and
character inductions. The sampled maps are actual affine restrictions,
presented by a surjective domain quotient and an injective codomain map.
No Fourier, hybrid-derivative, rank-level, or inverse estimate is included.
The Grassmann application discharges this predicate from its actual local
density bounds; the analytic induction must still be proved separately.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic

universe u v
variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- All affine restrictions with at most r prescribed input/output dimensions
have normalized squared density at most ε. The dimension sum avoids any
truncated-subtraction ambiguity. -/
def AffineDensityBound (r : ℕ) (ε : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (D : Type u) [AddCommGroup D] [Module F2 D] [FiniteDimensional F2 D]
    (C : Type v) [AddCommGroup C] [Module F2 C] [FiniteDimensional F2 C]
    [Fintype (D →ₗ[F2] C)],
    ∀ L : E →ₗ[F2] D, Function.Surjective L →
    ∀ J : C →ₗ[F2] F, Function.Injective J →
    ∀ T : E →ₗ[F2] F,
      Module.finrank F2 E + Module.finrank F2 F ≤
        Module.finrank F2 D + Module.finrank F2 C + r →
      (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L)) ^ 2) ≤ ε

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
Transport of actual small components when the ambient domain changes by a
linear equivalence. The coefficient and component identities hold for every
real function; basis invariance is separately transported when available.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E E' F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup E'] [Module F2 E']
  [AddCommGroup F] [Module F2 F] [AddCommGroup I] [Module F2 I]

/-- Reindex primal matrices by changing the ambient domain. -/
def ambientPrimalEquiv (h : E ≃ₗ[F2] E') :
    (E' →ₗ[F2] F) ≃ (E →ₗ[F2] F) where
  toFun X := X.comp h.toLinearMap
  invFun X := X.comp h.symm.toLinearMap
  left_inv X := by ext x; simp
  right_inv X := by ext x; simp

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSKernelOrbitsFourierLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Extension fibers for a dual hyperplane

Extending a linear frequency from `B` to `B × F2` amounts to choosing one
vector. Outside the old range every extension has the same kernel. Actual
basis invariance therefore makes all these Fourier coefficients equal.
The resulting exact counting identity is the algebraic part of the
hyperplane recursion; no analytic estimate is assumed here.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E B : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup B] [Module F2 B]

/-- Recover a linear map from its old coordinates and its new-coordinate value. -/
theorem hyperplaneExtend_recover (S : (B × F2) →ₗ[F2] E) :
    hyperplaneExtend (S.comp (LinearMap.inl F2 B F2)) (S (0, 1)) = S := by
  have h : LinearMap.toSpanSingleton F2 E (S (0, 1)) =
      S.comp (LinearMap.inr F2 B F2) := by
    ext
    simp
  rw [hyperplaneExtend, h, LinearMap.coprod_comp_inl_inr]

/-- Exact parametrization of a restriction fiber, including dependent extensions. -/
def hyperplaneExtensionEquiv (z : B →ₗ[F2] E) :
    E ≃ {S : (B × F2) →ₗ[F2] E // S.comp (LinearMap.inl F2 B F2) = z} where
  toFun v := ⟨hyperplaneExtend z v, hyperplaneExtend_comp_inl z v⟩
  invFun S := S.1 (0, 1)
  left_inv v := hyperplaneExtend_new_coordinate z v
  right_inv S := by
    apply Subtype.ext
    change hyperplaneExtend z (S.1 (0, 1)) = S.1
    simpa only [S.2] using hyperplaneExtend_recover S.1

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! Exact coefficient arrays in an adapted hybrid fiber. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalyticHybridCoordinates KMSAnalytic

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- Specifying the value on the complementary block gives every extension
exactly once. This will give the cardinality factor `|Hom(C,W)|`. -/
def extensionEquiv (z : B →ₗ[R] W) : Extension (C := C) z ≃ (C →ₗ[R] W) where
  toFun ψ := ψ.val.comp (LinearMap.inr R B C)
  invFun u := ⟨z.coprod u, by ext b; simp⟩
  left_inv ψ := by
    apply Subtype.ext
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : ψ.val (b, 0) = z b :=
      congrArg (fun t : B →ₗ[R] W => t b) ψ.property
    change z b + ψ.val (0, c) = ψ.val (b, c)
    rw [← hb, ← map_add]
    simp
  right_inv u := by ext c; simp

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-!
# Restricted Fourier sums on the small space

A prescribed partial frequency is encoded by an actual linear projection of
the small codomain. This gives a coordinate-free index for the fixed-character
induction in KMS Lemma 3.19. The statements below establish its exact base
normalization and remove impossible partial frequencies.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

variable {E F I J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

/-- Squared small Fourier coefficients whose image under a prescribed linear
projection is the fixed partial frequency. -/
def fixedFrequencyEnergy (ι : I →ₗ[F2] E) (f : (E →ₗ[F2] F) → ℝ)
    (π : I →ₗ[F2] J) (A : F →ₗ[F2] J) : ℝ :=
  ∑ T with π.comp T = A, smallCoeff ι f T ^ 2

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticBlockFrequenciesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Compatible block frequencies

A compatible surjection on `B × F2` has a unique old surjection and a new
vector in the kernel of the partial projection. The new vector does not
change its kernel. Consequently actual basis-invariant Fourier coefficients
are constant along this fiber, yielding its exact energy multiplicity.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {B J K E : Type*}
  [AddCommGroup B] [Module F2 B] [AddCommGroup J] [Module F2 J]
  [AddCommGroup K] [Module F2 K] [AddCommGroup E] [Module F2 E]

theorem blockFrequency_surjective_iff (z : B →ₗ[F2] J) (w : J) :
    Function.Surjective (blockFrequency z w) ↔ Function.Surjective z := by
  constructor
  · intro h y
    obtain ⟨⟨b, c⟩, hx⟩ := h (y, 0)
    have hc : c = 0 := congrArg Prod.snd hx
    refine ⟨b, ?_⟩
    simpa only [blockFrequency_apply, hc, zero_smul, add_zero] using congrArg Prod.fst hx
  · intro h x
    obtain ⟨b, hb⟩ := h (x.1 - x.2 • w)
    refine ⟨(b, x.2), ?_⟩
    simp only [blockFrequency_apply, hb, sub_add_cancel, Prod.eta]

theorem blockFrequency_compatible_iff (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (z : B →ₗ[F2] J) (w : J) :
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp (blockFrequency z w) =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2) ↔ π.comp z = A ∧ π w = 0 := by
  constructor
  · intro h
    constructor
    · apply LinearMap.ext
      intro b
      simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (b, 0)).1) h
    · simpa using congrArg (fun T : (B × F2) →ₗ[F2] (K × F2) => (T (0, 1)).1) h
  · rintro ⟨hz, hw⟩
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : π (z b) = A b := congrArg (fun T : B →ₗ[F2] K => T b) hz
    simp [hb, hw]

theorem blockFrequency_recover (π : J →ₗ[F2] K) (A : B →ₗ[F2] K)
    (T : (B × F2) →ₗ[F2] (J × F2))
    (hT : (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)) :
    blockFrequency (blockOld T) (blockNew T) = T := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun R : (B × F2) →ₗ[F2] J => R x)
      (hyperplaneExtend_recover ((LinearMap.fst F2 J F2).comp T))
  · have h := congrArg (fun R : (B × F2) →ₗ[F2] (K × F2) => (R x).2) hT
    exact h.symm

abbrev CompatibleBlockFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {T : (B × F2) →ₗ[F2] (J × F2) // Function.Surjective T ∧
    (π.prodMap (LinearMap.id : F2 →ₗ[F2] F2)).comp T =
      A.prodMap (LinearMap.id : F2 →ₗ[F2] F2)}

abbrev CompatibleOldFrequency (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :=
  {z : B →ₗ[F2] J // Function.Surjective z ∧ π.comp z = A}

/-- The actual compatible frequency fiber, with its exact kernel-vector parameter. -/
def compatibleBlockFrequencyEquiv (π : J →ₗ[F2] K) (A : B →ₗ[F2] K) :
    CompatibleBlockFrequency π A ≃ CompatibleOldFrequency π A × π.ker where
  toFun T := by
    have hr := blockFrequency_recover π A T.val T.property.2
    have hc : π.comp (blockOld T.val) = A ∧ π (blockNew T.val) = 0 :=
      (blockFrequency_compatible_iff π A _ _).mp (by rw [hr]; exact T.property.2)
    refine (⟨blockOld T.val, ?_, hc.1⟩, ⟨blockNew T.val, hc.2⟩)
    apply (blockFrequency_surjective_iff (blockOld T.val) (blockNew T.val)).mp
    rw [hr]
    exact T.property.1
  invFun p := ⟨blockFrequency p.1.val p.2.val,
    (blockFrequency_surjective_iff _ _).mpr p.1.property.1,
    (blockFrequency_compatible_iff π A _ _).mpr ⟨p.1.property.2, p.2.property⟩⟩
  left_inv T := by
    apply Subtype.ext
    exact blockFrequency_recover π A T.val T.property.2
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact blockOld_blockFrequency _ _
    · apply Subtype.ext
      exact blockNew_blockFrequency _ _

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
# Transport of the primal codomain

An equivalence of primal codomains gives a unique frequency in the Fourier
pullback fiber. The resulting exact coefficient identity transports both
the small component and its prescribed-frequency energy. No invariance or
analytic estimate is needed for these identities.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F F' I J : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [AddCommGroup F'] [Module F2 F']
  [AddCommGroup I] [Module F2 I] [AddCommGroup J] [Module F2 J]

def codomainTransport (e : F ≃ₗ[F2] F') (f : (E →ₗ[F2] F) → ℝ) :
    (E →ₗ[F2] F') → ℝ := fun X => f (e.symm.toLinearMap.comp X)

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFourthMomentMixedEnergyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact Fourier slice energies and their one-point KMS recurrence. The energy
is an unnormalized sum of actual squared coefficients. Translation changes
only a unit sign, so the dependent graph terms in the point recursion have
identical slice energies, without an ambient-cardinality loss.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- An arbitrary actual Fourier slice; in the mixed estimate P fixes selected
frequency coordinates. -/
def sliceEnergy (P : (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  ∑ T with P T, linearCoeff f T ^ 2

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
Exact partial restrictions in product coordinates. Translating the full map
shifts both the fixed and free coordinates. The latter shift preserves every
actual Fourier slice energy, so finite differences of translated functions
cost only the finite Cauchy factor already present before restriction.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- Fix the first product block, leaving the second block free. -/
def partialRestrict (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F) :
    (I →ₗ[F2] F) → ℝ := fun X => f (a.coprod X)

@[simp] theorem partialRestrict_apply
    (f : ((A × I) →ₗ[F2] F) → ℝ) (a : A →ₗ[F2] F)
    (X : I →ₗ[F2] F) : partialRestrict f a X = f (a.coprod X) := rfl

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
Exact Fourier merging after fixing a primal product block. The coefficient
uses normalized expectation, while the merged frequency sum is unnormalized.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSFourthMoment

variable {A I F : Type*}
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- Splitting the fixed and free frequency blocks is an exact bijection. -/
def frequencyBlockEquiv : ((F →ₗ[F2] A) × (F →ₗ[F2] I)) ≃
    (F →ₗ[F2] (A × I)) where
  toFun p := p.1.prod p.2
  invFun S := ((LinearMap.fst F2 A I).comp S,
    (LinearMap.snd F2 A I).comp S)
  left_inv _ := rfl
  right_inv _ := rfl

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-! The actual Fourier coefficient of an adapted hybrid fiber factors into
the complementary-block phase and a mixed partial-restriction coefficient. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates
open KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]

def coordinateOfData (z : B →ₗ[F2] W) (α : (B × C) →ₗ[F2] A)
    (ψ : Extension (C := C) z) (v : C →ₗ[F2] D) :
    Coordinates (A := A) (D := D) (C := C) z :=
  ⟨α, ψ.val, ψ.property, v⟩

def primalA (T : (A × (W × D)) →ₗ[F2] (B × C)) : A →ₗ[F2] (B × C) :=
  T.comp (LinearMap.inl F2 A (W × D))

def primalW (T : (A × (W × D)) →ₗ[F2] (B × C)) : W →ₗ[F2] (B × C) :=
  (T.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inl F2 W D)

def primalD (T : (A × (W × D)) →ₗ[F2] (B × C)) : D →ₗ[F2] (B × C) :=
  (T.comp (LinearMap.inr F2 A (W × D))).comp (LinearMap.inr F2 W D)

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

section

/-! A single compressed-image contribution is controlled by an actual mixed
slice energy. The only losses are the explicit finite coordinate counts. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix
open KMSAnalytic KMSAnalyticHybridCoordinates KMSFourthMoment

variable {A W D B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup W] [Module F2 W]
  [AddCommGroup D] [Module F2 D] [AddCommGroup B] [Module F2 B]
  [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 W]
  [FiniteDimensional F2 D] [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype ((B × C) →ₗ[F2] A)] [Fintype ((B × C) →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] C)]
  [Fintype (C →ₗ[F2] D)] [Fintype (C →ₗ[F2] W)] [Fintype (B →ₗ[F2] W)]
  [Fintype ((B × C) →ₗ[F2] (A × (W × D)))]
  [Fintype ((A × (W × D)) →ₗ[F2] (B × C))]
  [Fintype ((A × (W × C)) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (A × (W × C)))]
  [Fintype ((W × C) →ₗ[F2] (B × C))]
  [Fintype ((B × C) →ₗ[F2] (W × C))]

def adaptedFiberCoefficient (z : B →ₗ[F2] W)
    (f : ((A × (W × D)) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × (W × D)) →ₗ[F2] (B × C)) : ℝ :=
  ∑ S : {S : (B × C) →ₗ[F2] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[F2] D)},
    (if LinearIdentities.Hybrid S.val
        (LinearMap.range (LinearMap.inl F2 A (W × D)))
        (LinearMap.range (LinearMap.inl F2 B C)) then
      linearCoeff (rankComponent (Module.finrank F2 (A × (W × C))) f) S.val else 0) *
      (linearTraceCharacter S.val T).re

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSFourthMomentMixedBaseLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
With no fixed points, the mixed energy is exactly the fixed-character energy
of the actual small component. This is the base interface between the two
KMS inductions; no norm estimate is assumed or altered by the identification.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {A I : Type*} [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I] [Subsingleton A]

/-- The free block is the entire product when the fixed block is zero. -/
def zeroFixedEquiv : I ≃ₗ[F2] (A × I) :=
  { LinearMap.inr F2 A I with
    invFun := Prod.snd
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨a, x⟩
      exact Prod.ext (Subsingleton.elim _ _) rfl }

@[simp] theorem zeroFixedEquiv_apply (x : I) :
    zeroFixedEquiv (A := A) x = (0, x) := rfl

@[simp] theorem zeroFixedEquiv_symm_apply (a : A) (x : I) :
    (zeroFixedEquiv (A := A) (I := I)).symm (a, x) = x := rfl

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
Move one fixed coordinate to the last position while preserving the free
block. These are identities of actual linear maps and restricted functions;
no Fourier support or analytic estimate is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment

noncomputable section
open scoped Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {A0 A I F : Type*}
  [AddCommGroup A0] [Module F2 A0]
  [AddCommGroup A] [Module F2 A]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]

/-- Put the last coordinate into the fixed block through `e`, keeping the
free block unchanged. -/
def pointShuffle (e : (A0 × F2) ≃ₗ[F2] A) :
    ((A0 × I) × F2) ≃ₗ[F2] (A × I) where
  toFun p := (e (p.1.1, p.2), p.1.2)
  invFun p := (((e.symm p.1).1, p.2), (e.symm p.1).2)
  left_inv p := by
    rcases p with ⟨⟨u, v⟩, c⟩
    simp
  right_inv p := by
    rcases p with ⟨u, v⟩
    simp
  map_add' p q := by
    apply Prod.ext
    · change e (p.1.1 + q.1.1, p.2 + q.2) =
        e (p.1.1, p.2) + e (q.1.1, q.2)
      exact map_add e (p.1.1, p.2) (q.1.1, q.2)
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · change e (c • p.1.1, c • p.2) = c • e (p.1.1, p.2)
      exact map_smul e c (p.1.1, p.2)
    · rfl

@[simp] theorem pointShuffle_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A0) (v : I) (c : F2) :
    pointShuffle (I := I) e ((u, v), c) = (e (u, c), v) := rfl

@[simp] theorem pointShuffle_symm_apply (e : (A0 × F2) ≃ₗ[F2] A)
    (u : A) (v : I) :
    (pointShuffle (I := I) e).symm (u, v) =
      (((e.symm u).1, v), (e.symm u).2) := rfl

/-- Express a function in the shuffled coordinates. -/
def pointShuffleTransport (e : (A0 × F2) ≃ₗ[F2] A)
    (f : ((A × I) →ₗ[F2] F) → ℝ) :
    (((A0 × I) × F2) →ₗ[F2] F) → ℝ :=
  fun Y => f (Y.comp (pointShuffle e).symm.toLinearMap)

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticCharacterInduction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full fixed-character induction for the actual KMS small component.
The only local hypothesis bounds squared norms of homogeneous restrictions;
all Fourier recursions, multiplicities and coordinate changes are proved.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

universe u v w x

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Product Hybrid energy from actual mixed slices

The derivative's exact rank support is partitioned by its actual compressed
image. Each image is put in complement coordinates, and the proved coefficient
factorization bounds that contribution by an actual mixed slice. The finite
image, extension, and complementary-map counts fit the mixed denominator.
The sole analytic premise is the displayed uniform bound on actual slices.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Appendix.Derivatives
open KMSAnalytic KMSFourthMoment

local instance (priority := 2000) classicalSurjective_rf72c05_1 {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)
attribute [local instance] OAI.UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy.mapFintype
local instance submoduleFintype {V : Type*}
    [AddCommGroup V] [Module F2 V] [Fintype V] : Fintype (Submodule F2 V) :=
  Fintype.ofInjective (fun W : Submodule F2 V => (W : Set V)) SetLike.coe_injective

variable {A U B C : Type*}
  [AddCommGroup A] [Module F2 A] [AddCommGroup U] [Module F2 U]
  [AddCommGroup B] [Module F2 B] [AddCommGroup C] [Module F2 C]
  [FiniteDimensional F2 A] [FiniteDimensional F2 U]
  [FiniteDimensional F2 B] [FiniteDimensional F2 C]
  [Fintype A] [Fintype U] [Fintype B] [Fintype C]

/-- The actual mixed-slice hypothesis in all coordinates adapted to the
compressed image. It is a bound on `smallComponent`, with the original
function and translate transported by the explicit product equivalence. -/
def ProductMixedSliceBound (i : ℕ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (L : ℝ) : Prop :=
  ∀ (W D : Submodule F2 U),
    Module.finrank F2 W = i - (Module.finrank F2 A + Module.finrank F2 C) →
    ∀ (hD : IsCompl W D)
      (κ : (A × (W × C)) →ₗ[F2] (A × (W × D))),
      Function.Injective κ →
      sliceEnergy (fun V : (B × C) →ₗ[F2] (W × C) =>
        (LinearMap.snd F2 W C).comp V = LinearMap.snd F2 B C)
        (partialRestrict (smallComponent κ (imagePullback W D hD f))
          (primalA (imageTranslate W D hD T))) ≤
        L / (2 : ℝ) ^ ((2 * Module.finrank F2 C +
          (i - (Module.finrank F2 A + Module.finrank F2 C))) *
            Module.finrank F2 (A × U))

/-- The selected coefficient at one ordinary product-compressed frequency. -/
def productFiberCoefficient (i : ℕ)
    (f : ((A × U) →ₗ[F2] (B × C)) → ℝ)
    (T : (A × U) →ₗ[F2] (B × C)) (Z : B →ₗ[F2] U) : ℝ :=
  ∑ S : (B × C) →ₗ[F2] (A × U),
    if LinearIdentities.Hybrid S (LinearMap.range (LinearMap.inl F2 A U))
        (LinearMap.range (LinearMap.inl F2 B C)) ∧
        (LinearMap.snd F2 A U).comp (S.comp (LinearMap.inl F2 B C)) = Z
    then linearCoeff (rankComponent i f) S * (linearTraceCharacter S T).re else 0

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSLowLevelLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The spectral cutoff step of KMS on the actual full uniform rank-one noise.
The low-level fourth-moment estimate remains an explicit input to the last
combining lemma; none of these statements asserts that estimate or expansion.
The multiplier is reused from the proved uniform-subspace kernel count.
-/

namespace UniqueGamesTheorem.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixNoise
open UniqueGamesTheorem.Decoder.PositiveMultiplier
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSMomentScalar

section ActualFourier
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual operator samples both rank-one factors uniformly, including zero. -/
def uniformNoise (f : (E →ₗ[F2] F) → ℝ) : (E →ₗ[F2] F) → ℝ :=
  linearRealNoiseOperator (subspaceLaw (LinearMap.id : F →ₗ[F2] F)) f

end ActualFourier

end
end UniqueGamesTheorem.Inverse.KMSLowLevel

end

section

/-!
The complete fixed-point induction from the fixed-character base estimate.
The base is kept as a named mathematical input here so its separate character
induction can be assembled independently. This intermediate theorem is not
the final KMS endpoint: its base must be discharged by the proved homogeneous
character estimate. All point-recursion, basis transport and local-density
steps are established within this theorem's proof.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Inverse.KMSAnalytic

universe u v

local instance mapFintype {V : Type*} {W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
A uniform formulation of the genuine KMS mixed estimate. Every instance is
the actual Fourier slice of a partially restricted small component. The
property is preserved by coordinate pullback and follows from the proved
mixed estimate under the affine squared-density hypothesis.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Inverse.KMSFourthMoment

universe u v w

attribute [local instance] mixedMapFintype

variable {E : Type u} {F : Type v}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F]

/-- All mixed small-component slices of total degree at most `r`, with their
exact ambient normalization weight. No Hybrid derivative bound is included
in this property. Fixed primal points and prescribed frequencies are arbitrary. -/
def UniformMixedBound (r : ℕ) (L : ℝ) (f : (E →ₗ[F2] F) → ℝ) : Prop :=
  ∀ (A I J : Type u)
    [AddCommGroup A] [Module F2 A] [FiniteDimensional F2 A] [Fintype A]
    [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I] [Fintype I]
    [AddCommGroup J] [Module F2 J] [FiniteDimensional F2 J] [Fintype J],
    ∀ (ι : (A × I) →ₗ[F2] E), Function.Injective ι →
    ∀ (a : A →ₗ[F2] F) (π : I →ₗ[F2] J), Function.Surjective π →
    ∀ (ν : F →ₗ[F2] J), Module.finrank F2 A + Module.finrank F2 I ≤ r →
      (2 : ℝ) ^ ((Module.finrank F2 I + Module.finrank F2 J) * Module.finrank F2 E) *
        sliceEnergy (fun T => π.comp T = ν)
          (partialRestrict (smallComponent ι f) a) ≤ L

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeInterfaceLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The shortcode inverse principle uses an arbitrary table function, full uniform
factor sampling, and an affine intercept.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

def Slice.constantAgreement {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (u : Vector ell) : ℝ :=
  S.points.expect fun M => if f M = u then 1 else 0

/-- Dimension-uniform inverse statement. The constants `α,r` depend only
on `η`; only the final input dimension threshold may depend on `ell`. There is
no folding assumption, and no inverse-theorem certificate is hidden in `f`. -/
def InversePrinciple : Prop :=
  ∀ η : ℝ, 0 < η → η < 1 →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∃ r : ℕ, 1 ≤ r ∧
      ∃ ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
          ∀ f : Mat ell m → Vector ell,
            η ≤ equalityAcceptance f → HasAffineSlice f α r

end
end UniqueGamesTheorem.Inverse.Shortcode

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureMatrixLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact uniform parametrization of the concrete row/column slice.  The quotient
parameter describes every point, not only a lower-bounding subfamily.  Affine
targets retain the base-point contribution and their original intercept.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode.Slice

noncomputable section
open scoped BigOperators Matrix

variable {ell m : ℕ}

instance directionsFintype (S : Slice ell m) : Fintype S.Directions := by
  classical
  letI : Fintype (Vector m ⧸ S.columnSpan) := Fintype.ofFinite _
  letI : Fintype S.rowMap.ker := Fintype.ofFinite _
  exact Fintype.ofInjective
    (fun N : S.Directions => (N : (Vector m ⧸ S.columnSpan) → S.rowMap.ker))
    DFunLike.coe_injective

end
end UniqueGamesTheorem.Inverse.Shortcode.Slice

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The actual finite matrix column event occupies at least `2^(-ell*r)` of its
row-advice fiber. This connects the intrinsic quotient-map count to the padded
descriptions used by the selector, without assuming independent equations.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass

noncomputable section
open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open UniqueGamesTheorem.Inverse.RowErasureMatrix
open scoped BigOperators Classical

/-- Forget only the column equations of a slice. -/
def rowOnly {ell m : ℕ} (S : Slice ell m) : Slice ell m where
  rows := S.rows
  columns := 0
  rowCoefficient := S.rowCoefficient
  rowValue := S.rowValue
  columnCoefficient := Fin.elim0
  columnValue := Fin.elim0

end
end UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass

end

section

/-!
The selected column event under the actual uniform matrix and row-map samples.
The witness is fixed by visible row advice before testing the hidden matrix.
Fiber sizes are retained explicitly; no uniformity of row values is assumed.
The final averaging lemmas also allow arbitrary nonnegative context weights.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

noncomputable section
open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass
open scoped BigOperators

variable {ell m r : ℕ}

def selectedEventMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedEvent f α A)

def selectedMatchMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedMatch f α A)

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeFiberLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual uniform matrix test supplies a positive-mass output fiber with
large retention. The transition kernel averages independent full vectors,
including zero. -/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Information

def matrixWeight {ell m : ℕ} (_ : Mat ell m) : ℝ :=
  (Fintype.card (Mat ell m) : ℝ)⁻¹

def matrixKernel {ell m : ℕ} (M N : Mat ell m) : ℝ :=
  𝔼 a : Vector ell, 𝔼 l : Vector m,
    if N = M + rankOne a l then 1 else 0

end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

def matrixFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (Mat ell m) := Finset.univ.filter fun M => f M = y

def liftedFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (KMS.Vertex (ell + m) ell) := (matrixFiber f y).image matrixVertex

@[simp] theorem matrixVertex_mem_liftedFiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    matrixVertex M ∈ liftedFiber f y ↔ f M = y := by
  constructor
  · intro h
    obtain ⟨N, hN, hNM⟩ := Finset.mem_image.mp h
    have : N = M := matrixVertex_injective hNM
    subst N
    exact (Finset.mem_filter.mp hN).2
  · intro h
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

section

/-! Exact finite output-fiber sampling identities. These connect the weighted
kernel extraction to uniform sampling of a matrix in the actual output fiber.
-/

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode UniqueGamesTheorem.Foundations.Information

def fiberFactorRetention {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) (a : Vector ell) (l : Vector m) : ℝ :=
  (matrixFiber f y).expect fun M => if f (M + rankOne a l) = y then 1 else 0

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeFromGrassmannLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open Shortcode MatrixChart

/-- OPEN finite sampling bridge, stated on the actual equality test, actual
lifted output fibers, and actual Grassmann retention. The positive dimensions
exclude the degenerate empty-neighbor cases. No KMS or inverse principle is
part of this proposition. -/
def ChartFiberRetention : Prop :=
  ∀ {ell m : ℕ}, 1 ≤ ell → 1 ≤ m →
    ∀ η : ℝ, 0 < η → η < 1 → zeroFactorMass ell m ≤ η / 2 →
      ∀ f : Mat ell m → Vector ell, η ≤ equalityAcceptance f →
        ∃ y : Vector ell, (liftedFiber f y).Nonempty ∧
          η / 4 ≤ KMS.retention (liftedFiber f y)

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FoldedEquationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Outer.Clone100Counting

open scoped BigOperators

theorem majority_aligned_nonneg (f : Index → Bool) :
    0 ≤ sign (majorityBit f) * bias f := by
  by_cases h : bias f < 0
  · simp [majorityBit, h, sign]
    exact le_of_lt h
  · simpa [majorityBit, h, sign] using le_of_not_gt h

theorem parityIndicator_nonneg (a b c rhs : Bool) :
    0 ≤ parityIndicator a b c rhs := by
  unfold parityIndicator
  split <;> norm_num

theorem parityIndicator_le_one (a b c rhs : Bool) :
    parityIndicator a b c rhs ≤ 1 := by
  unfold parityIndicator
  split <;> norm_num

theorem parityIndicator_eq (a b c rhs : Bool) :
    parityIndicator a b c rhs =
      (1 + sign rhs * sign a * sign b * sign c) / 2 := by
  cases a <;> cases b <;> cases c <;> cases rhs <;>
    norm_num [parityIndicator, sign]

theorem unconditionedScore_eq (p q r : Index → Bool) (rhs : Bool) :
    unconditionedScore p q r rhs =
      (1 + sign rhs * bias p * bias q * bias r) / 2 := by
  have hp := independent_product_sum
    (fun i => sign (p i)) (fun i => sign (q i)) (fun i => sign (r i))
  have hs : (∑ t : Triple, sign rhs * sign (p t.1) * sign (q t.2.1) * sign (r t.2.2)) =
      sign rhs * ((∑ i, sign (p i)) * (∑ j, sign (q j)) * (∑ k, sign (r k))) := by
    rw [← hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  unfold unconditionedScore
  simp_rw [parityIndicator_eq, div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  unfold bias
  norm_num
  ring

theorem unconditionedScore_le_one (p q r : Index → Bool) (rhs : Bool) :
    unconditionedScore p q r rhs ≤ 1 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset Triple))
    (fun t _ => parityIndicator_le_one (p t.1) (q t.2.1) (r t.2.2) rhs)
  norm_num [Fintype.card_prod, Fintype.card_fin] at h
  unfold unconditionedScore
  linarith

theorem signed_product_of_failure (a b c rhs : Bool) (x y z : ℚ)
    (h : (xor (xor a b) c == rhs) = false) :
    sign rhs * x * y * z = -((sign a * x) * (sign b * y) * (sign c * z)) := by
  cases a <;> cases b <;> cases c <;> cases rhs <;>
    simp_all [sign]

/-- An equation violated by the majority assignment is satisfied by independent
clone labels with probability at most one half. This also allows repeated
original variable names: independence belongs to the sampled clone indices. -/
theorem unconditionedScore_le_half_of_failure (p q r : Index → Bool) (rhs : Bool)
    (h : (xor (xor (majorityBit p) (majorityBit q)) (majorityBit r) == rhs) = false) :
    unconditionedScore p q r rhs ≤ 1 / 2 := by
  have hn := mul_nonneg
    (mul_nonneg (majority_aligned_nonneg p) (majority_aligned_nonneg q))
    (majority_aligned_nonneg r)
  rw [unconditionedScore_eq,
    signed_product_of_failure (majorityBit p) (majorityBit q) (majorityBit r)
      rhs (bias p) (bias q) (bias r) h]
  linarith

theorem unconditionedScore_le (p q r : Index → Bool) (rhs : Bool) :
    unconditionedScore p q r rhs ≤
      (1 + parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs) / 2 := by
  cases h : (xor (xor (majorityBit p) (majorityBit q)) (majorityBit r) == rhs) with
  | false =>
    have hi : parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs = 0 := by
      unfold parityIndicator
      rw [h]
      rfl
    rw [hi, add_zero]
    exact unconditionedScore_le_half_of_failure p q r rhs h
  | true =>
    have hi : parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs = 1 := by
      unfold parityIndicator
      rw [h]
      rfl
    rw [hi]
    norm_num
    exact unconditionedScore_le_one p q r rhs

/-- Conditioning a bounded function onto 970200 of one million outcomes
changes its upper expectation by at most 3/100. The exact loss is 298/10000.
Only finite sums and the actual accepted sample cardinality are needed. -/
theorem condition_970200_le {T : Type*} [Fintype T]
    (good : T → Prop) [DecidablePred good]
    (_hT : Fintype.card T = 1000000)
    (hgood : Fintype.card {t : T // good t} = 970200)
    (f : T → ℚ) (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) :
    (∑ t : {t : T // good t}, f t.val) / 970200 ≤
      (∑ t : T, f t) / 1000000 + 3 / 100 := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype good f
  have hn : 0 ≤ ∑ t : {t : T // ¬good t}, f t.val :=
    Finset.sum_nonneg (fun t _ => hf0 t.val)
  have hle : (∑ t : {t : T // good t}, f t.val) ≤ ∑ t : T, f t := by
    linarith
  have hcap := Finset.sum_le_sum (s := (Finset.univ : Finset {t : T // good t}))
    (fun t _ => hf1 t.val)
  simp only [Finset.sum_const, Finset.card_univ, hgood, nsmul_eq_mul] at hcap
  norm_num at hcap
  linarith

theorem conditionedScore_le (good : Triple → Prop) [DecidablePred good]
    (hgood : Fintype.card {t : Triple // good t} = 970200)
    (p q r : Index → Bool) (rhs : Bool) :
    conditionedScore good p q r rhs ≤
      (1 + parityIndicator (majorityBit p) (majorityBit q) (majorityBit r) rhs) / 2 + 3 / 100 := by
  have hcond := condition_970200_le good
    (by norm_num [Fintype.card_prod, Fintype.card_fin]) hgood
    (fun t => parityIndicator (p t.1) (q t.2.1) (r t.2.2) rhs)
    (fun t => parityIndicator_nonneg _ _ _ _)
    (fun t => parityIndicator_le_one _ _ _ _)
  have hmaj := unconditionedScore_le p q r rhs
  change conditionedScore good p q r rhs ≤ unconditionedScore p q r rhs + 3 / 100 at hcond
  linarith

end UniqueGamesTheorem.Outer.Clone100Counting

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Clone100
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Outer.Clone100

open UniqueGamesTheorem.Reduction CloneGap ActualSource
open Clone100Triples Clone100Counting
open scoped BigOperators

noncomputable section

def clone {N : Type} (e : Equation N) (t : GoodTriple) : Equation (N × Fin 100) :=
  ⟨(e.first, t.val.1), (e.second, t.val.2.1), (e.third, t.val.2.2), e.rhs⟩

theorem clone_distinct {N : Type} (e : Equation N) (t : GoodTriple) :
    (clone e t).first ≠ (clone e t).second ∧
      (clone e t).first ≠ (clone e t).third ∧
      (clone e t).second ≠ (clone e t).third := by
  exact ⟨fun h => t.property.1 (congrArg Prod.snd h),
    fun h => t.property.2.1 (congrArg Prod.snd h),
    fun h => t.property.2.2 (congrArg Prod.snd h)⟩

theorem equation_distinct {n : Nat} (e : Equation (Fin n)) (t : GoodTriple) :
    (equation e t).first ≠ (equation e t).second ∧
      (equation e t).first ≠ (equation e t).third ∧
      (equation e t).second ≠ (equation e t).third := by
  obtain ⟨h12, h13, h23⟩ := clone_distinct e t
  exact ⟨fun h => h12 ((nameEquiv n).injective h),
    fun h => h13 ((nameEquiv n).injective h),
    fun h => h23 ((nameEquiv n).injective h)⟩

def clonedSource (input : SourceEncoding.Input) : Source :=
  Source.ofList (clonedInput input).equations (clonedInput input).nonempty

theorem clonedSource_distinct (input : SourceEncoding.Input) :
    (clonedSource input).DistinctNames := by
  intro i
  have hm : (clonedInput input).equations[i.val] ∈ equations input.equations :=
    List.getElem_mem i.isLt
  obtain ⟨e, _, ht⟩ := List.mem_flatMap.mp hm
  obtain ⟨t, _, he⟩ := List.mem_map.mp ht
  change ((clonedInput input).equations[i.val]).first ≠
      ((clonedInput input).equations[i.val]).second ∧
    ((clonedInput input).equations[i.val]).first ≠
      ((clonedInput input).equations[i.val]).third ∧
    ((clonedInput input).equations[i.val]).second ≠
      ((clonedInput input).equations[i.val]).third
  rw [← he]
  exact equation_distinct e t

theorem equation_lift {n : Nat} (e : Equation (Fin n)) (t : GoodTriple)
    (a : Fin n → Bool) : satisfied (equation e t) (lift a) = satisfied e a := by
  simp [equation, lift, satisfied]

theorem completeness_count {n : Nat} (es : List (Equation (Fin n)))
    (a : Fin n → Bool) :
    (equations es).countP (fun e => satisfied e (lift a)) =
      es.countP (fun e => satisfied e a) * 970200 := by
  induction es with
  | nil => simp [equations]
  | cons e es ih =>
    simp only [equations, List.flatMap_cons, List.countP_append, List.countP_map,
      Function.comp_def] at *
    simp_rw [equation_lift]
    rw [CloneGap.count_const, triples_length, ih]
    cases h : satisfied e a <;> simp [h, Nat.add_mul, Nat.add_comm]

def success {n : Nat} (es : List (Equation (Fin n))) (a : Fin n → Bool) : ℚ :=
  (es.countP (fun e => satisfied e a) : ℚ) / es.length

theorem completeness (input : SourceEncoding.Input)
    (a : Fin input.variables → Bool) :
    success (clonedInput input).equations (lift a) = success input.equations a := by
  simp only [success, clonedInput, completeness_count, equations_length, Nat.cast_mul]
  have hn : (input.equations.length : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (List.length_pos_iff.mpr input.nonempty)
  field_simp

theorem equation_count_le {n : Nat} (e : Equation (Fin n))
    (a : Fin (n * 100) → Bool) :
    ((triples.map (equation e)).countP (fun e => satisfied e a) : ℚ) ≤
      970200 * ((1 + if satisfied e (majority a) then (1 : ℚ) else 0) / 2 + 3 / 100) := by
  have bound := conditionedScore_le good card_goodTriple
    (fun i => a (nameEquiv n (e.first, i)))
    (fun i => a (nameEquiv n (e.second, i)))
    (fun i => a (nameEquiv n (e.third, i))) e.rhs
  have he : ((triples.map (equation e)).countP (fun e => satisfied e a) : ℚ) =
      ∑ t : GoodTriple, parityIndicator (a (nameEquiv n (e.first, t.val.1)))
        (a (nameEquiv n (e.second, t.val.2.1)))
        (a (nameEquiv n (e.third, t.val.2.2))) e.rhs := by
    rw [List.countP_map, count_as_sum]
    exact (Finset.sum_map_toList (Finset.univ : Finset GoodTriple)
        (fun t => parityIndicator (a (nameEquiv n (e.first, t.val.1)))
          (a (nameEquiv n (e.second, t.val.2.1)))
          (a (nameEquiv n (e.third, t.val.2.2))) e.rhs))
  rw [he]
  unfold conditionedScore at bound
  have hb := (div_le_iff₀ (show (0 : ℚ) < 970200 by norm_num)).mp bound
  rw [mul_comm _ (970200 : ℚ)] at hb
  exact hb

theorem soundness_count {n : Nat} (es : List (Equation (Fin n)))
    (a : Fin (n * 100) → Bool) :
    ((equations es).countP (fun e => satisfied e a) : ℚ) ≤
      970200 * ((53 / 100 : ℚ) * es.length +
        (es.countP (fun e => satisfied e (majority a)) : ℚ) / 2) := by
  induction es with
  | nil => simp [equations]
  | cons e es ih =>
    have he := equation_count_le e a
    simp only [equations, List.flatMap_cons, List.countP_append, Nat.cast_add,
      List.length_cons] at *
    cases h : satisfied e (majority a) <;>
      simp [h] at * <;> linarith

theorem soundness (input : SourceEncoding.Input)
    (a : Fin (clonedInput input).variables → Bool) :
    success (clonedInput input).equations a ≤
      (1 + success input.equations (majority a)) / 2 + 3 / 100 := by
  have h := soundness_count input.equations a
  have hn : (0 : ℚ) < input.equations.length := by
    exact_mod_cast List.length_pos_iff.mpr input.nonempty
  change (_ : ℚ) / _ ≤ _
  simp only [clonedInput, equations_length, Nat.cast_mul]
  rw [div_le_iff₀ (mul_pos hn (by norm_num))]
  calc
    _ ≤ 970200 * ((53 / 100 : ℚ) * input.equations.length +
        (input.equations.countP (fun e => satisfied e (majority a)) : ℚ) / 2) := h
    _ = _ := by
      unfold success
      field_simp
      ring

theorem soundness_four_fifths (input : SourceEncoding.Input) (ξ : ℚ)
    (hξ : ξ < 1 / 100)
    (hsource : ∀ a, success input.equations a ≤ (1 + ξ) / 2)
    (a : Fin (clonedInput input).variables → Bool) :
    success (clonedInput input).equations a ≤ 4 / 5 := by
  have h := soundness input a
  have hs := hsource (majority a)
  linarith

end
end UniqueGamesTheorem.Outer.Clone100

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_PreprocessingTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def output (H : BaseTable) (t : GraphTables.Table) : PortTables.Input degree :=
  ⟨vertices t, preprocess H t⟩

end UniqueGamesTheorem.Foundations.PCP.PreprocessingTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

theorem alphabet_positive : 0 < alphabet := by
  unfold alphabet PoweringTables.labelCount
  exact Nat.pow_pos (by decide)

end UniqueGamesTheorem.Foundations.PCP.RoundTables

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_IncidenceProbabilityLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.SourceProbability

open ActualSource

theorem Source_failure_eq_count (S : Source) (A : Fin S.variables → Bool) :
    S.failure A =
      (S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) / S.occurrences := by
  have hp := IncidenceProbability.expect_bool_indicator_eq_count_ofFn
    (fun i : Fin S.occurrences => !S.satisfied A i)
  have he : Finset.univ.expect
      (fun i : Fin S.occurrences => if !S.satisfied A i then (1 : ℚ) else 0) =
      S.failure A := by
    unfold Source.failure
    congr 1
    funext i
    cases S.satisfied A i <;> rfl
  rw [he] at hp
  rw [hp]
  congr 2
  have hmap : List.ofFn (fun i : Fin S.occurrences => !S.satisfied A i) =
      S.sourceList.map (fun e => !CloneGap.satisfied e A) := by
    simp only [Source.sourceList, List.map_ofFn, Source.satisfied, Function.comp_def]
  rw [hmap, List.countP_map]
  rfl

theorem failure_add_satisfaction (S : Source) (A : Fin S.variables → Bool) :
    S.failure A +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) / S.occurrences = 1 := by
  rw [Source_failure_eq_count, ← add_div]
  have h := count_complement S.sourceList (fun e => CloneGap.satisfied e A)
  have hc : ((S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ)) = S.occurrences := by
    exact_mod_cast (h.trans S.sourceList_length)
  rw [hc, div_self]
  exact_mod_cast Nat.ne_of_gt S.nonempty

end UniqueGamesTheorem.Reduction.SourceProbability

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_TableGapReductionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map admits a polynomial-time machine. -/



namespace UniqueGamesTheorem.Outer.HastadSource

open UniqueGamesTheorem.Foundations Target Complexity PCP
open UniqueGamesTheorem.Reduction ActualSource
open MachineFiniteAlphabet


def asSource (input : SourceEncoding.Input) : Source :=
  Source.ofList input.equations input.nonempty

end UniqueGamesTheorem.Outer.HastadSource

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ConditionalSimulationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The actual local simulation in Lemma 6.8 after fixing H. These reconstruction
maps consume only the first player's occurrence tuple or the second player's
name tuple. Its winning-event containment is proved from the concrete equation
and named-projection predicates.
-/

namespace UniqueGamesTheorem.Soundness.ConditionalSimulation

open Foundations.Games ConditionalIncidences IncidenceExtraction
open RepeatedGameBounds

noncomputable section

def incidenceGame {O N : Type} [Fintype O] [Fintype N]
    (g : Incidence O N) (mu : FiniteDistribution (O × N)) :
    Foundations.Games.Game O N Triple Bool :=
  Simulation.weightedGame ⟨g.namedAccepts⟩ mu

def actualLocalSimulation
    {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (mu : FiniteDistribution (O × N))
    (enumerate : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma)) :
    IncidenceExtraction.LocalSimulation
      (Simulation.predicateGame ((incidenceGame g mu).repetition (zeroSet J gamma).card))
      (ActualProjection.predicateGame (R := R) g (membershipBool J)) where
  questionA qa := localFirstFromH J g.name gamma observed reference
    (fun j => qa (enumerate.symm j))
  questionB qb := localSecondFromH J g.name gamma observed reference
    (fun j => qb (enumerate.symm j))
  answerA _ answer i := answer.2 (enumerate i).val
  answerB _ answer i := answer.2.2 (enumerate i).val
  sound := by
    classical
    intro qa qb answerA answerB haccept
    change ((incidenceGame g mu).repetition (zeroSet J gamma).card).accepts _ _ _ _ = true
    rw [Foundations.Games.Game.repetition_accepts_iff]
    intro i
    change decide (g.namedAccepts (qa i) (qb i)
      (answerA.2 (enumerate i).val) (answerB.2.2 (enumerate i).val)) = true
    rw [decide_eq_true_eq]
    have hj : (enumerate i).val ∈ J := zeroSet_subset J gamma (enumerate i).property
    have hsingle : membershipBool J (enumerate i).val = true := by
      simp [membershipBool, hj]
    have hname : (localSecondFromH J g.name gamma observed reference
        (fun j => qb (enumerate.symm j))).question (enumerate i).val = Sum.inr (qb i) := by
      simpa using localSecondFromH_question_inside J g.name gamma observed reference
        (fun j => qb (enumerate.symm j)) (enumerate i)
    have h := ActualProjection.accepts_implies_named_incidence g (membershipBool J)
      _ _ answerA answerB haccept (enumerate i).val hsingle (qb i) hname
    simpa only [localFirstFromH_question_inside, Equiv.symm_apply_apply] using h

end
end UniqueGamesTheorem.Soundness.ConditionalSimulation

end

end OAI
end


