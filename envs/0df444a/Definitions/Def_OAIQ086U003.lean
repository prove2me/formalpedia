-- Prove2me | Definitions.Def_OAIQ086U003
-- name    : OAIQ086U003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:15:23.741742+00:00
-- url     : https://prove2.me/theorems/9fb7f4ee-c195-4977-a554-c06e5ee4e2c6
-- title:
--   Definitions bundle OAIQ086U003 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1106 declarations of OpenAI's Lean: 544 definitions, 10 inductive types or structures, 9 instances and 543 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Clean.StochasticBound.actualGame`, `OAI.UniqueGamesTheorem.Clean.StochasticBound.nativeStochasticSuccess`, `OAI.UniqueGamesTheorem.Decoder.ActualAdviceSampling.sampledAgreement`, `OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.Visible`, `OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.actualDraw`, `OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.complementMap`, `OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.fullInput`, `OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.policies`, `OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.projectedInput`, `OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.rowMap`, `OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.sourceIncidence`, `OAI.UniqueGamesTheorem.Decoder.ActualConditionalLaw.datumAgreement`, `OAI.UniqueGamesTheorem.Decoder.ActualConditionalLaw.homFintype`, `OAI.UniqueGamesTheorem.Decoder.ActualEvents.Context`, `OAI.UniqueGamesTheorem.Decoder.ActualEvents.FullTableSample`, `OAI.UniqueGamesTheorem.Decoder.ActualEvents.Sample`, `OAI.UniqueGamesTheorem.Decoder.ActualEvents.fullTableEquiv`, `OAI.UniqueGamesTheorem.Decoder.ActualEvents.homFintype`, `OAI.UniqueGamesTheorem.Decoder.ActualEvents.sliceEvent`, `OAI.UniqueGamesTheorem.Decoder.ActualEvents.targetHit`, `OAI.UniqueGamesTheorem.Decoder.ActualEvents.unrestricted`, `OAI.UniqueGamesTheorem.Decoder.ActualGoodRows.adviceMass`, `OAI.UniqueGamesTheorem.Decoder.ActualGoodRows.homFintype`, `OAI.UniqueGamesTheorem.Decoder.ActualGoodRows.table`, `OAI.UniqueGamesTheorem.Decoder.ActualProjectedTransfer.slopeVariation`, `OAI.UniqueGamesTheorem.Decoder.ActualSeedEvents.Datum`, `OAI.UniqueGamesTheorem.Decoder.ActualSeedEvents.Seed`, `OAI.UniqueGamesTheorem.Decoder.ActualSeedEvents.draw`, `OAI.UniqueGamesTheorem.Decoder.ActualSeedEvents.law`, `OAI.UniqueGamesTheorem.Decoder.ActualSeedEvents.pad`, `OAI.UniqueGamesTheorem.Decoder.ActualSeedEvents.slice`, `OAI.UniqueGamesTheorem.Decoder.ActualSeedEvents.targetHit`, `OAI.UniqueGamesTheorem.Decoder.ActualSeedSampling.drawAgreement`, `OAI.UniqueGamesTheorem.Decoder.ActualSeedVariation.homFintype`, `OAI.UniqueGamesTheorem.Decoder.ActualSpectral.fiberAcceptance`, `OAI.UniqueGamesTheorem.Decoder.ActualSpectral.homFintype`, `OAI.UniqueGamesTheorem.Decoder.AdviceExperiment.Draw`, `OAI.UniqueGamesTheorem.Decoder.AdviceExperiment.FullAdvice`, `OAI.UniqueGamesTheorem.Decoder.AdviceExperiment.ProjectedAdvice`, `OAI.UniqueGamesTheorem.Decoder.AdviceExperiment.leftObservation` and 514 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Analysis_MatrixCharactersLemmas`, `UniqueGames_Decoding_ActualAdviceStochasticBridgeLemmas`, `UniqueGames_Decoding_ActualAdviceUpperLemmas`, `UniqueGames_Decoding_ActualProjectedTransfer`, `UniqueGames_Decoding_ActualSeedSamplingLemmas`, `UniqueGames_Decoding_ActualSpectralLemmas`, `UniqueGames_Decoding_AdviceFibersLemmas`, `UniqueGames_Decoding_MaskMomentLemmas`, `UniqueGames_Decoding_MatrixCoordinates`, `UniqueGames_Decoding_PaddedLaw`, `UniqueGames_Decoding_PrivateStrategyLemmas`, `UniqueGames_Decoding_SelectedFiberLaw`, `UniqueGames_Decoding_StochasticBound`, `UniqueGames_Decoding_TableKeysAddressGameLemmas`, `UniqueGames_Decoding_TableKeysCompletenessLemmas`, `UniqueGames_Decoding_TableKeysGame`, `UniqueGames_Decoding_TableKeysLemmas`, `UniqueGames_Decoding_VisiblePoliciesLemmas`, `UniqueGames_Decoding_VisibleTransferLemmas`, `UniqueGames_Foundations_FiniteTrialsLemmas`, `UniqueGames_Foundations_SamplingLemmas`, `UniqueGames_Foundations_ValueLemmas`, `UniqueGames_Games_FinishBoundsLemmas`, `UniqueGames_Games_ProductLemmas`, `UniqueGames_Games_ProductMachineSemantics`, `UniqueGames_Games_ProductTarget`, `UniqueGames_Inverse_KMSAffineRestrictionPresentationLemmas`, `UniqueGames_Inverse_KMSAnalyticBlockFrequenciesLemmas`, `UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportLemmas`, `UniqueGames_Inverse_KMSAnalyticHybridEnergyLemmas`, `UniqueGames_Inverse_KMSKernelOrbitsFourierLemmas`, `UniqueGames_Inverse_KMSLowLevelLemmas`, `UniqueGames_Inverse_RowErasureMatrixLemmas`, `UniqueGames_Inverse_ShortcodeInterfaceLemmas`, `UniqueGames_Machines_GraphCounterStartLemmas`, `UniqueGames_Machines_MachineBinaryInputReductionLemmas`, `UniqueGames_Machines_MachineClone100`, `UniqueGames_Machines_MachineClone100Certified`, `UniqueGames_Machines_MachineClone100Headers`, `UniqueGames_Machines_MachineClone100Loop`, `UniqueGames_Machines_MachineClone100Run`, `UniqueGames_Machines_MachineClone100TableLemmas`, `UniqueGames_Machines_MachineClone100Triples`, `UniqueGames_Machines_MachineCompositionLemmas`, `UniqueGames_Machines_MachineDrainManyLemmas`, `UniqueGames_Machines_MachineLemmas`, `UniqueGames_Machines_MachineLookupCore`, `UniqueGames_Machines_MachineLookupDiscard`, `UniqueGames_Machines_MachineLookupLemmas`, `UniqueGames_Machines_MachineProductFieldLemmas`, `UniqueGames_Machines_MachineProductGatherBoundsLemmas`, `UniqueGames_Machines_MachineProductHeadersFrameLemmas`, `UniqueGames_Machines_MachineProductProgram`, `UniqueGames_Machines_MachineProductSeed`, `UniqueGames_Machines_MachineRadixStepLemmas`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineSubroutineLemmas`, `UniqueGames_Machines_MachineTransducerCopy`, `UniqueGames_Machines_MachineTupleOdometer`, `UniqueGames_Machines_MachineUnaryAddAt`, `UniqueGames_Machines_MachineUnaryAffineAt`, `UniqueGames_Machines_MachineUnaryMultiply`, `UniqueGames_PCP_ClauseVerifierLemmas`, `UniqueGames_PCP_Clone100`, `UniqueGames_PCP_FoldedEquationLemmas`, `UniqueGames_PCP_HonestTestLemmas`, `UniqueGames_PCP_SourceContextLoad`, `UniqueGames_PCP_SourceDescriptorEmissionLemmas`, `UniqueGames_PCP_SourceFieldArrayLemmas`, `UniqueGames_PCP_SourceHonestLemmas`, `UniqueGames_PCP_SourceLoopInitLemmas`, `UniqueGames_PCP_SourceMachine`, `UniqueGames_PCP_SourceOccurrences`, `UniqueGames_PCP_SourceQueryLoopLemmas`, `UniqueGames_Reduction_ActualCanonicalLemmas`, `UniqueGames_Reduction_ActualCompleteness`, `UniqueGames_Reduction_ActualGame`, `UniqueGames_Reduction_ActualSourceLemmas`, `UniqueGames_Reduction_CanonicalBodyTemplateLemmas`, `UniqueGames_Reduction_EncodingLemmas`, `UniqueGames_Reduction_ExplicitLemmas`, `UniqueGames_Reduction_GapSemanticsLemmas`, `UniqueGames_Reduction_NoiseEnumerationLemmas`, `UniqueGames_Reduction_RealTargetLemmas`, `UniqueGames_Reduction_TableReduction`, `UniqueGames_Soundness_ConditionalSimulationLemmas`, `UniqueGames_Soundness_RawPrivateTable`, `UniqueGames_Soundness_RawTargetLawLemmas`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`; the bundles `OAIQ086U000`, `OAIQ086U001` and `OAIQ086U002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ086U006`, `OAIQ086U007`, `OAIQ086U008` and `OAIQ086U009`; the statements `OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.contradiction` and `OAI_UniqueGamesTheorem_Gadget_exists_split_gadget`; the proof of `OAI_UniqueGamesTheorem_Gadget_exists_split_gadget`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U000
import Definitions.Def_OAIQ086U001
import Definitions.Def_OAIQ086U002

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixCharacters

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear

theorem tracePair_ext_right {n m : Nat} {S T : Matrix (Fin m) (Fin n) F2}
    (h : ∀ X, tracePair X S = tracePair X T) : S = T :=
  Matrix.ext_iff_trace_mul_left.mpr h

theorem binarySign_injective : Function.Injective binarySign := by
  intro a b h
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl
  · rfl
  · have hf : (1 : ℂ) = -1 := by simpa using h
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · have hf : (1 : ℂ) = -1 := by simpa using h.symm
    exact False.elim (one_ne_zero ((CharZero.eq_neg_self_iff).mp hf))
  · rfl

theorem binarySign_real (a : F2) : ((binarySign a).re : ℂ) = binarySign a := by
  unfold binarySign
  split <;> simp

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_eq_matrix_tracePair {n m : Nat}
    (bE : Module.Basis (Fin m) F2 E) (bF : Module.Basis (Fin n) F2 F)
    (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S =
      tracePair (LinearMap.toMatrix bE bF X) (LinearMap.toMatrix bF bE S) := by
  change LinearMap.trace F2 F (X.comp S) =
    Matrix.trace (LinearMap.toMatrix bE bF X * LinearMap.toMatrix bF bE S)
  rw [LinearMap.trace_eq_matrix_trace F2 bF, LinearMap.toMatrix_comp bF bE bF]

theorem linearTraceCharacter_real (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    ((linearTraceCharacter S X).re : ℂ) = linearTraceCharacter S X := binarySign_real _

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

theorem linearTracePair_swap (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair X S = linearTracePair S X :=
  LinearMap.trace_comp_comm' S X

theorem linearTraceCharacter_swap (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X = linearTraceCharacter X S := by
  simp only [linearTraceCharacter_apply, linearTracePair_swap X S]

/-- The actual trace pairing is nondegenerate in its dual-map argument. -/
theorem linearTracePair_ext_right {S T : F →ₗ[F2] E}
    (h : ∀ X, linearTracePair X S = linearTracePair X T) : S = T := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  apply (LinearMap.toMatrix bF bE).injective
  apply tracePair_ext_right
  intro X
  obtain ⟨X', rfl⟩ := (LinearMap.toMatrix bE bF).surjective X
  exact (linearTracePair_eq_matrix_tracePair bE bF X' S).symm.trans
    ((h X').trans (linearTracePair_eq_matrix_tracePair bE bF X' T))

theorem linearTraceCharacter_injective :
    Function.Injective (linearTraceCharacter (E := E) (F := F)) := by
  intro S T h
  apply linearTracePair_ext_right
  intro X
  apply binarySign_injective
  exact congrArg (fun ψ : AddChar (E →ₗ[F2] F) ℂ => ψ X) h

theorem linearTraceCharacter_eq_zero_iff (S : F →ₗ[F2] E) :
    linearTraceCharacter S = 0 ↔ S = 0 := by
  rw [← linearTraceCharacter_zero, linearTraceCharacter_injective.eq_iff]

theorem sum_linearTraceCharacter [Fintype (E →ₗ[F2] F)] (S : F →ₗ[F2] E) :
    ∑ X, linearTraceCharacter S X =
      if S = 0 then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  rw [AddChar.sum_eq_ite]
  simp only [linearTraceCharacter_eq_zero_iff]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixCharacters

end

end

section

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open UniqueGamesTheorem.Fourier.MatrixCharacters

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [AddCommGroup G] in
theorem star_expect (f : G → ℂ) :
    star (𝔼 x, f x) = 𝔼 x, star (f x) := by
  simp [Fintype.expect_eq_sum_div_card]

theorem star_fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) :
    star (fourierCoeff f ψ) = 𝔼 x, star (f x) * ψ x := by
  rw [fourierCoeff, star_expect]
  simp [star_mul, mul_comm]

end FiniteGroup

section LinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem card_linearMap_reverse :
    Fintype.card (F →ₗ[F2] E) = Fintype.card (E →ₗ[F2] F) := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  calc
    Fintype.card (F →ₗ[F2] E) =
        Fintype.card (Matrix (Fin (Module.finrank F2 E))
          (Fin (Module.finrank F2 F)) F2) :=
      Fintype.card_congr (LinearMap.toMatrix bF bE).toEquiv
    _ = Fintype.card (Matrix (Fin (Module.finrank F2 F))
          (Fin (Module.finrank F2 E)) F2) := by
      exact Fintype.card_congr
        { toFun := Matrix.transpose
          invFun := Matrix.transpose
          left_inv := Matrix.transpose_transpose
          right_inv := Matrix.transpose_transpose }
    _ = Fintype.card (E →ₗ[F2] F) :=
      (Fintype.card_congr (LinearMap.toMatrix bE bF).toEquiv).symm

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearTraceCharacter_star (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    star (linearTraceCharacter S X) = linearTraceCharacter S X := by
  calc
    _ = star (((linearTraceCharacter S X).re : ℝ) : ℂ) :=
      congrArg star (linearTraceCharacter_real S X).symm
    _ = ((linearTraceCharacter S X).re : ℂ) := by simp
    _ = linearTraceCharacter S X := linearTraceCharacter_real S X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearMap_add_eq_zero_iff (X Y : E →ₗ[F2] F) :
    X + Y = 0 ↔ X = Y := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hself : Y + Y = 0 := by
    have h := congrArg (fun c : F2 => c • Y) htwo
    simpa only [add_smul, one_smul, zero_smul] using h
  have hneg : -Y = Y := neg_eq_iff_add_eq_zero.mpr hself
  rw [add_eq_zero_iff_eq_neg, hneg]

/-- Exact trace-character orthogonality with the frequency sum unnormalized. -/
theorem linear_character_kernel (X Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, star (linearTraceCharacter S X) * linearTraceCharacter S Y =
      if X = Y then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  calc
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter S (X + Y) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [linearTraceCharacter_star, AddChar.map_add_eq_mul]
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter (X + Y) S := by
      apply Finset.sum_congr rfl
      intro S _
      exact linearTraceCharacter_swap S (X + Y)
    _ = if X + Y = 0 then (Fintype.card (F →ₗ[F2] E) : ℂ) else 0 :=
      sum_linearTraceCharacter (X + Y)
    _ = _ := by rw [linearMap_add_eq_zero_iff, card_linearMap_reverse]

/-- Fourier inversion obtained directly from the finite trace orthogonality sum. -/
theorem linear_complex_inversion (f : (E →ₗ[F2] F) → ℂ) (Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, fourierCoeff f (linearTraceCharacter S) *
      linearTraceCharacter S Y = f Y := by
  classical
  simp only [fourierCoeff]
  simp_rw [Finset.expect_mul, mul_assoc]
  rw [← Finset.expect_sum_comm]
  simp_rw [← Finset.mul_sum, linear_character_kernel]
  rw [Finset.expect_eq_sum_div_card]
  simp [mul_ite]

/-- Mixed Parseval with normalized primal expectation and unnormalized frequency sum. -/
theorem linear_complex_parseval (f g : (E →ₗ[F2] F) → ℂ) :
    ∑ S : F →ₗ[F2] E, star (fourierCoeff f (linearTraceCharacter S)) *
      fourierCoeff g (linearTraceCharacter S) = 𝔼 X, star (f X) * g X := by
  simp_rw [star_fourierCoeff, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro X _
  calc
    (∑ S : F →ₗ[F2] E, (star (f X) * linearTraceCharacter S X) *
        fourierCoeff g (linearTraceCharacter S)) =
        star (f X) * ∑ S : F →ₗ[F2] E,
          fourierCoeff g (linearTraceCharacter S) * linearTraceCharacter S X := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl
    _ = star (f X) * g X := by rw [linear_complex_inversion]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_complex (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    (linearCoeff f S : ℂ) =
      fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S) := by
  rw [linearCoeff, complex_ofReal_expect, fourierCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [Complex.ofReal_mul, linearTraceCharacter_real, linearTraceCharacter_star]

/-- Parseval for real functions and the real binary trace coefficients. -/
theorem linear_parseval_inner (f g : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S =
      𝔼 X, f X * g X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          star (fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S)) *
            fourierCoeff (fun X => (g X : ℂ)) (linearTraceCharacter S) := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [← linearCoeff_complex, ← linearCoeff_complex]
      simp
    _ = 𝔼 X, star (f X : ℂ) * (g X : ℂ) := linear_complex_parseval _ _
    _ = ((𝔼 X, f X * g X : ℝ) : ℂ) := by
      rw [complex_ofReal_expect]
      simp

theorem linear_parseval (f : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S ^ 2 = 𝔼 X, f X ^ 2 := by
  simpa only [pow_two] using linear_parseval_inner f f

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixFourier

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCompositionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

open Turing MachineComposition

variable {Command : Type} (LocalLabel : Command → Type)

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

variable [DecidableEq K]

/-- This generic composition lemma retains the local execution obligations.
Concrete callers discharge them with the rotor, comparison and row programs. -/
theorem trace (program : Λ → TM2.Stmt Γ Λ σ)
    (invariant : Data → Prop) (state : Data → σ) (tapes : Data → ∀ k, List (Γ k))
    (commands : List Command)
    (localInvariant : ∀ command ∈ commands, ∀ data, invariant data →
      invariant (result command data))
    (localTrace : ∀ command ∈ commands, ∀ (labels : LocalLabel command → Λ) (exit : Option Λ),
      (∀ l, program (labels l) = localInstruction command labels exit l) →
      ∀ data, invariant data →
      (advance (TM2.step program))^[cost command data]
        (some ⟨some (labels (main command)), state data, tapes data⟩) =
      some ⟨exit, state (result command data), tapes (result command data)⟩)
    (labels : Label LocalLabel commands → Λ) (exit : Option Λ)
    (atLabels : ∀ l, program (labels l) =
      instruction LocalLabel main localInstruction commands labels exit l)
    (data : Data) (valid : invariant data) :
    (advance (TM2.step program))^[steps result cost commands data]
      (some ⟨entry LocalLabel main commands labels exit, state data, tapes data⟩) =
    some ⟨exit, state (resultOf result commands data), tapes (resultOf result commands data)⟩ := by
  induction commands generalizing data with
  | nil => rfl
  | cons command commands ih =>
      have firstRun := localTrace command (by simp)
        (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit)
        (fun l => atLabels (.inl l)) data valid
      have nextValid := localInvariant command (by simp) data valid
      have tailRun := ih
        (fun c hc d hd => localInvariant c (by simp [hc]) d hd)
        (fun c hc => localTrace c (by simp [hc]))
        (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
        (result command data) nextValid
      rw [steps, Nat.add_comm, Function.iterate_add_apply]
      change (advance (TM2.step program))^[steps result cost commands (result command data)]
        ((advance (TM2.step program))^[cost command data]
          (some ⟨some (labels (.inl (main command))), state data, tapes data⟩)) = _
      rw [firstRun]
      exact tailRun

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteSequence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_FiniteTrialsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite two-player games with actual joint question distributions.

An answer function receives only its own player's question. In a repeated game,
that question is the entire tuple, so a repeated strategy need not act separately
on coordinates. The predicate may reject invalid answers depending on questions.
All probabilities below are actual finite sums of real weights.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem probability_nonnegative (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    0 ≤ μ.probability event := by
  apply Finset.sum_nonneg
  intro x _
  split
  · exact μ.nonnegative x
  · exact le_rfl

theorem probability_le_one (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    μ.probability event ≤ 1 := by
  rw [← μ.normalized]
  apply Finset.sum_le_sum
  intro x _
  split
  · exact le_rfl
  · exact μ.nonnegative x

theorem probability_pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ)
    (event : Γ → Bool) :
    (μ.pushforward f).probability event = μ.probability (fun x => event (f x)) := by
  classical
  simp only [probability, pushforward]
  calc
    _ = ∑ y, ∑ x, if f x = y then (if event y then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : event y = true <;> simp [hy]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem probability_transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ)
    (event : Γ → Bool) :
    (μ.transport equiv).probability event = μ.probability (fun x => event (equiv x)) := by
  unfold probability transport
  exact Fintype.sum_equiv equiv.symm _ _ (fun _ => by simp)

theorem probability_iid_all (μ : FiniteDistribution Ω) (event : Ω → Bool) (n : Nat) :
    (μ.iid n).probability (fun x => decide (∀ i, event (x i) = true)) =
      μ.probability event ^ n := by
  classical
  unfold probability iid
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq]
  by_cases h : ∀ i, event (x i) = true
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def wins (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂)
    (questions : Q₁ × Q₂) : Bool :=
  G.accepts questions.1 questions.2 (strategy.1 questions.1) (strategy.2 questions.2)

def success (G : Game Q₁ Q₂ A₁ A₂) (strategy : Strategy Q₁ Q₂ A₁ A₂) : ℝ :=
  G.questions.probability (G.wins strategy)

theorem success_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : 0 ≤ G.success strategy :=
  G.questions.probability_nonnegative _

theorem success_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ 1 :=
  G.questions.probability_le_one _

/-- Playing a fixed base strategy separately in each coordinate is one
permitted repeated strategy, though repeated strategies are more general. -/
def repeatStrategy (strategy : Strategy Q₁ Q₂ A₁ A₂) (n : Nat) :
    Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) :=
  (fun x i => strategy.1 (x i), fun y i => strategy.2 (y i))

theorem success_repeatStrategy (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) (n : Nat) :
    (G.repetition n).success (repeatStrategy strategy n) = G.success strategy ^ n := by
  unfold success
  change ((G.questions.iid n).transport (tupleQuestionEquiv n)).probability _ = _
  rw [FiniteDistribution.probability_transport]
  exact G.questions.probability_iid_all (G.wins strategy) n

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

/-- A maximum of the finitely many actual deterministic success probabilities. -/
def value (G : Game Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty G.success

theorem success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ G.value := by
  classical
  exact Finset.le_sup' G.success (Finset.mem_univ strategy)

theorem value_le_iff (G : Game Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    G.value ≤ bound ↔ ∀ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy ≤ bound := by
  classical
  simp [value, Finset.sup'_le_iff]

theorem exists_optimal_strategy (G : Game Q₁ Q₂ A₁ A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy = G.value := by
  classical
  obtain ⟨strategy, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Strategy Q₁ Q₂ A₁ A₂))) Finset.univ_nonempty G.success
  exact ⟨strategy, h.symm⟩

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

section

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

namespace UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem eq_of_weight_eq {μ ν : FiniteDistribution Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk w' hw' hs' =>
      have he : w = w' := funext h
      cases he
      rfl

end FiniteDistribution

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

def stochasticSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) : ℝ :=
  G.questions.expectation (fun q =>
    (responses₁ q.1).expectation (fun a =>
      (responses₂ q.2).expectation (fun b =>
        if G.accepts q.1 q.2 a b then 1 else 0)))

end Game
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Foundations_SamplingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact finite sampling laws used to identify verifier distributions with repeated
game question laws. These are finite sum/product identities, not independence
assumptions about an unspecified distribution.
-/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

theorem iid_pushforward {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f : Ω → Γ) (n : Nat) :
    (μ.pushforward f).iid n =
      (μ.iid n).pushforward (fun answers i => f (answers i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [iid, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f (x i)) = y
  · have hp : ∀ i, f (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, f (x i) = y i := fun hp => h (funext hp)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem iid_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (n : Nat) :
    (uniform Ω).iid n = uniform (Fin n → Ω) := by
  classical
  apply eq_of_weight_eq
  intro x
  simp [iid, uniform, Nat.cast_pow, one_div]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineSubroutineLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineSubroutine

open Turing

variable {K Λ Λ' σ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem trace (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (steps : Nat) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration labels exit a)) = some (configuration labels exit b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) steps a b run

end UniqueGamesTheorem.Foundations.Complexity.MachineSubroutine

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

/-- Literal split at the selected word. -/
theorem encoded_selected_split (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    encodeWords values = encodeWords (values.take i) ++ encodeWord value ++
      encodeWords (values.drop (i + 1)) := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  have hs : values = values.take i ++ value :: values.drop (i + 1) := by
    calc
      values = values.take i ++ values.drop i := (List.take_append_drop i values).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hv]
  simpa only [encodeWords_append, encodeWords, List.append_assoc] using
    congrArg encodeWords hs

/-- This counts the bits through the selected word, capped at the whole table
when the index is invalid. It is not a machine step count. -/
def scannedBits (values : List Nat) (i : Nat) : Nat :=
  (encodeWords (values.take (i + 1))).length

theorem encoded_prefix_length_le (values : List Nat) (i : Nat) :
    (encodeWords (values.take i)).length ≤ (encodeWords values).length := by
  have hs : encodeWords (values.take i) ++ encodeWords (values.drop i) =
      encodeWords values := by
    rw [← encodeWords_append, List.take_append_drop]
  have hl := congrArg List.length hs
  simp only [List.length_append] at hl
  omega

theorem scannedBits_le (values : List Nat) (i : Nat) :
    scannedBits values i ≤ (encodeWords values).length :=
  encoded_prefix_length_le values (i + 1)

theorem scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    scannedBits values i = (encodeWords (values.take i)).length + value + 1 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  simp [scannedBits, List.take_succ_eq_append_getElem hi, hv, encodeWords,
    Nat.add_assoc]

theorem selected_scan_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWords (values.take i)).length + value + 1 ≤
      (encodeWords values).length := by
  rw [← scannedBits_of_some values i value h]
  exact scannedBits_le values i

theorem output_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord value).length ≤ (encodeWords values).length := by
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

theorem index_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord i).length ≤ (encodeWords values).length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  have hp : i ≤ (encodeWords (values.take i)).length := by
    simp only [encodeWords_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

/-! Bounds on the proposed lookup recurrence. A separate machine proof must
identify these counts with actual transition traces. -/

/-- A uniform bound, including indices beyond the end of the table. -/
theorem steps_le_encoded_length_strong (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero =>
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega
    | succ i =>
      have ht := ih i
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega

/-- Successful lookup uses exactly the consumed table prefix, one guard per
skipped word, and the two final control steps. -/
theorem steps_eq_scannedBits_of_lt (values : List Nat) (i : Nat)
    (h : i < values.length) :
    steps values i = scannedBits values i + i + 2 := by
  induction values generalizing i with
  | nil => simp at h
  | cons n ns ih =>
    cases i with
    | zero => simp [steps, scannedBits, encodeWords, Nat.add_assoc]
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [scannedBits] at ht
      simp only [steps, scannedBits, List.take_succ_cons, encodeWords,
        List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    steps values i = scannedBits values i + i + 2 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  exact steps_eq_scannedBits_of_lt values i hi

/-- Linear in the combined encoded tape lengths. This is a bound for `steps`,
not yet a theorem about a concrete machine's execution. -/
theorem steps_le_input_encoding_size (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * (encodeWord i).length := by
  have h := steps_le_encoded_length_strong values i
  rw [encodeWord_length]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

end

section

/-!
One actual TM2 transition tests and decrements a zero-delimited unary counter.
The guard peeks before branching: a true bit is popped, while a false delimiter
is retained. Both branches clear the one-bit register and preserve the ambient
state. There is no assumed execution trace or input-dependent finite program.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem counterTapes_other (counter other : K) (hne : other ≠ counter)
    (base : K → List Bool) (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix other = base other := by
  simp [counterTapes, hne]

/-- Positive counters lose exactly one true bit; the delimiter and suffix
remain. Ambient state, unrelated tapes, and labels are accounted for explicitly. -/
theorem stepAux_succ (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base (n + 1) suffix) =
      ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord, List.replicate_succ]

/-- A zero counter is inspected without removing its delimiter. -/
theorem stepAux_zero (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base 0 suffix) =
      ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord]

theorem guardStep_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩ =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base (n + 1) suffix)) = _
  rw [atGuard, stepAux_succ]

theorem guardStep_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩ =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base 0 suffix)) = _
  rw [atGuard, stepAux_zero]

/-- The positive branch executes in exactly one transition of the ambient program. -/
theorem guardTrace_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register),
        counterTapes counter base (n + 1) suffix⟩) =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register

theorem guardTrace_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩) =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register

def guardInTime_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩
      (some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register
  steps_le_m := Nat.le_refl _

def guardInTime_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩
      (some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

end

section

/-!
Counted loops in one actual TM2 program. A unary guard is executed once before
each caller body and once more at zero. The caller supplies only individual
body traces, each returning to the guard with the same counter remainder.

Schedules are indexed by the remaining count: body `r` takes ambient state
`r + 1` to ambient state `r`. Consequently the run starts at index `n` and
ends at index zero. Bodies may change the ambient state and unprotected tapes.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCountedLoop

open Turing
open scoped BigOperators
open MachineUnaryCounter

variable {K Λ σ : Type} [DecidableEq K]

def guardConfiguration (counter : K) (guardLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some guardLabel, (ambient n, register n), counterTapes counter (base n) n suffix⟩

def bodyConfiguration (counter : K) (bodyLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (n + 1), none), counterTapes counter (base (n + 1)) n suffix⟩

def exitConfiguration (counter : K) (exitLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none), counterTapes counter (base 0) 0 suffix⟩

/-- The hypotheses are actual traces of the caller's body in the same program.
Both endpoints have the same unary remainder and unread suffix. -/
def BodyTraces (counter : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n →
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some (bodyConfiguration counter bodyLabel suffix ambient base r)) =
      some (guardConfiguration counter guardLabel suffix ambient register base r)

/-- The loop trace is derived by composing each actual unary guard transition
with one supplied body trace. No whole-loop execution is assumed. -/
theorem loopTrace (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodyTraces : BodyTraces counter guardLabel bodyLabel program suffix
      ambient register base cost n) :
    (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
      (some (guardConfiguration counter guardLabel suffix ambient register base n)) =
      some (exitConfiguration counter exitLabel suffix ambient base) := by
  revert bodyTraces
  induction n with
  | zero =>
      intro _
      simpa only [totalSteps_zero, guardConfiguration, exitConfiguration] using
        guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
          (base 0) suffix (ambient 0) (register 0)
  | succ n ih =>
      intro bodyTraces
      rw [totalSteps_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n + cost n]
        (TM2.step program
          ⟨some guardLabel, (ambient (n + 1), register (n + 1)),
            counterTapes counter (base (n + 1)) (n + 1) suffix⟩) = _
      rw [guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
        (base (n + 1)) n suffix (ambient (n + 1)) (register (n + 1)),
        Function.iterate_add_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
        ((MachineComposition.advance (TM2.step program))^[cost n]
          (some (bodyConfiguration counter bodyLabel suffix ambient base n))) = _
      rw [bodyTraces n (Nat.lt_succ_self n)]
      exact ih (fun r hr => bodyTraces r (Nat.lt_trans hr (Nat.lt_succ_self n)))

end UniqueGamesTheorem.Foundations.Complexity.MachineCountedLoop

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_GapSemanticsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Changing finite encodings preserves the actual Unique Games instance gaps.
Vertex names may be permuted and constraint occurrences may be reordered. -/

namespace UniqueGamesTheorem.Integration.InstanceEquivalences

open UniqueGamesTheorem.Foundations.Target
open GapSemantics

theorem rename_count {n m q : Nat} (e : Fin n ≃ Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (renameConstraint e)) =
      countSatisfied (labeling ∘ e) constraints := by
  induction constraints with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c.satisfied (labeling ∘ e) = true <;> simp [countSatisfied, ih, hc]

theorem countSatisfied_perm {n q : Nat} (labeling : Fin n → Fin q)
    {constraints constraints' : List (Constraint n q)}
    (h : constraints.Perm constraints') :
    countSatisfied labeling constraints = countSatisfied labeling constraints' := by
  rw [countSatisfied_eq_sum, countSatisfied_eq_sum]
  exact (h.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum_eq

/-- This statement is directly usable by an executable adapter: only its
vertex equivalence and its permutation of the explicit edge list are needed. -/
theorem satisfactionRate_eq_of_rename_perm {q : Nat} (g h : Instance q)
    (e : Fin g.vertices ≃ Fin h.vertices)
    (hp : h.constraints.Perm (g.constraints.map (renameConstraint e)))
    (labeling : Fin h.vertices → Fin q) :
    satisfactionRate h labeling = satisfactionRate g (labeling ∘ e) := by
  have hcount := countSatisfied_perm labeling hp
  rw [rename_count] at hcount
  have hlength := hp.length_eq
  simp only [List.length_map] at hlength
  unfold satisfactionRate
  rw [hcount, hlength]

end UniqueGamesTheorem.Integration.InstanceEquivalences

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_RealTargetLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The value of the actual finite Unique Games instance is its maximum satisfied
constraint fraction. Maximization ranges over every finite vertex labeling;
the denominator counts stored constraint occurrences, including repetitions.
The natural-number maximum totalizes an empty labeling type at zero. The
attainment and threshold equivalences require a positive alphabet.
-/

namespace UniqueGamesTheorem.Integration.InstanceValue

open UniqueGamesTheorem.Foundations
open Target

/-- The usual instance value: the largest satisfied fraction of its stored
constraint list. The denominator is positive by the `Instance` invariant. -/
noncomputable def value {q : Nat} (g : Instance q) : ℝ :=
  (maxSatisfied g : ℝ) / g.constraints.length

theorem labeling_rate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ value g := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast countSatisfied_le_maxSatisfied g labeling
  · exact Nat.cast_nonneg _

/-- This value uses the same rate already defined for the encoded gap target. -/
theorem satisfactionRate_le_value {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    (GapSemantics.satisfactionRate g labeling : ℝ) ≤ value g := by
  simpa [GapSemantics.satisfactionRate] using labeling_rate_le_value g labeling

end UniqueGamesTheorem.Integration.InstanceValue

end

section

/-! Injective vertex addresses may leave unused output vertices. The actual
instance is obtained by mapping endpoints in the original constraint list;
constraint order, multiplicity, and permutation tables are retained exactly. -/

namespace UniqueGamesTheorem.Integration.VertexEmbedding

open UniqueGamesTheorem.Foundations.Target
open GapSemantics TranslationTarget

theorem count_map {n m q : Nat} (f : Fin n → Fin m)
    (constraints : List (Constraint n q)) (labeling : Fin m → Fin q) :
    countSatisfied labeling (constraints.map (embedConstraint f)) =
      countSatisfied (labeling ∘ f) constraints := by
  induction constraints with
  | nil => rfl
  | cons c cs ih =>
      by_cases hc : c.satisfied (labeling ∘ f) = true <;> simp [countSatisfied, ih, hc]

@[simp] theorem embedInstance_length {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).constraints.length = g.constraints.length := List.length_map _

@[simp] theorem extendLabeling_apply {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q)
    (defaultLabel : Fin q) (v : Fin n) :
    extendLabeling f labeling defaultLabel (f v) = labeling v := by
  classical
  have hx : ∃ u, f u = f v := ⟨v, rfl⟩
  rw [extendLabeling, dite_eq_left hx]
  exact congrArg labeling (hf (Classical.choose_spec hx))

theorem extendLabeling_comp {n m q : Nat} (f : Fin n → Fin m)
    (hf : Function.Injective f) (labeling : Fin n → Fin q) (defaultLabel : Fin q) :
    extendLabeling f labeling defaultLabel ∘ f = labeling := by
  funext v
  exact extendLabeling_apply f hf labeling defaultLabel v

end UniqueGamesTheorem.Integration.VertexEmbedding

end

section

namespace UniqueGamesTheorem.Reduction.ActualHomogeneous

open Integration.BinaryLinear
open scoped BigOperators

variable {dimension : Nat}

theorem pair_fst_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).1 = if p then a.1 else b.1 := by split_ifs <;> rfl
theorem pair_snd_ite (p : Prop) [Decidable p] (a b : F2 × F2) :
    (if p then a else b).2 = if p then a.2 else b.2 := by split_ifs <;> rfl

theorem coordinate_decomposition (x : E dimension) :
    x = x.1 • hBasis dimension + ∑ j : Fin dimension,
      ((x.2 j).1 • firstBasis j + (x.2 j).2 • secondBasis j) := by
  apply Prod.ext
  · simp [hBasis, firstBasis, secondBasis, Prod.fst_sum]
  · funext j
    apply Prod.ext <;>
      simp [hBasis, firstBasis, secondBasis, Pi.single_apply,
        Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, pair_fst_ite, pair_snd_ite]

theorem linearMap_expansion {R : Type*} [AddCommGroup R] [Module F2 R]
    (X : E dimension →ₗ[F2] R) (x : E dimension) :
    X x = x.1 • X (hBasis dimension) + ∑ j : Fin dimension,
      ((x.2 j).1 • X (firstBasis j) + (x.2 j).2 • X (secondBasis j)) := by
  conv_lhs => rw [coordinate_decomposition x]
  simp

theorem finrank_E (k : Nat) : Module.finrank F2 (E k) = 1 + 2 * k := by
  simp [E, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]

end UniqueGamesTheorem.Reduction.ActualHomogeneous

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualCanonicalLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualCanonical

open Integration.BinaryLinear ActualHomogeneous
open scoped BigOperators

universe u v w
variable {Name : Type u} {Id : Type v} {R : Type w}
variable {k : Nat}
variable [AddCommGroup R] [Module F2 R] [DecidableEq R]

omit [DecidableEq R] in
theorem add_self (x : R) : x + x = 0 := by
  calc
    x + x = (1 + 1 : F2) • x := by simp [add_smul]
    _ = 0 := by rw [show (1 + 1 : F2) = 0 by decide, zero_smul]

end UniqueGamesTheorem.Reduction.ActualCanonical

end

section

namespace UniqueGamesTheorem.Reduction.CloneGap

variable {α : Type*} {β : Type*} {Name : Type}

def satisfied (e : Equation Name) (g : Name → Bool) : Bool :=
  (xor (xor (g e.first) (g e.second)) (g e.third)) == e.rhs

end UniqueGamesTheorem.Reduction.CloneGap

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_RawPrivateTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The private Fourier table is defined from displayed data alone. Compatibility
with every hidden extension follows from the proved canonical locality theorem. -/

namespace UniqueGamesTheorem.Soundness.RawPrivateTable
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open PartnerProjection RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Id Name : Type}

def representative {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    (V : SupportedV J names) : Extension k Id := Classical.choose V.property

variable (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
  {R D C Label : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]
  [DecidableEq Id] [DecidableEq Name]

def projection (occ : Fin k → Id) (slot : Fin k → Slot) :
    ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  rawProjection (fun j => toBit (rhs (occ j))) J slot

end
end UniqueGamesTheorem.Soundness.RawPrivateTable

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_FinishBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The four-edge subdivision.
Every input occurrence has its own three interior vertices, even when
the original endpoints coincide or another occurrence has the same endpoints.
The left/right presentation inverts the permutation on the fourth edge.
-/

namespace UniqueGamesTheorem.Explicit

open scoped BigOperators

namespace BipartiteGame

variable {L R E A : Type*} [Fintype E] [DecidableEq A]

theorem satisfiedCount_eq_sum_satisfied (g : BipartiteGame L R E A)
    (a : L → A) (b : R → A) :
    satisfiedCount g a b = ∑ e, if g.Satisfied a b e then 1 else 0 := by
  classical
  unfold satisfiedCount
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : g.Satisfied a b e
  · have h' : g.permutation e (a (g.left e)) = b (g.right e) := Eq.symm h
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ g.permutation e (a (g.left e)) = b (g.right e) :=
      fun he => h he.symm
    rw [ite_eq_right h', ite_eq_right h]

end BipartiteGame

end UniqueGamesTheorem.Explicit

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualSourceLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualSource

open UniqueGamesTheorem.Integration.BinaryLinear

instance sourceIndexNonempty (S : Source) : Nonempty (Fin S.occurrences) :=
  ⟨⟨0, S.nonempty⟩⟩

def Source.satisfied (S : Source) (A : Fin S.variables → Bool)
    (i : Fin S.occurrences) : Bool := CloneGap.satisfied (S.equation i) A

def Source.failure (S : Source) (A : Fin S.variables → Bool) : ℚ :=
  Finset.univ.expect (fun i => if S.satisfied A i then (0 : ℚ) else 1)

def Source.DistinctNames (S : Source) : Prop :=
  ∀ i, (S.equation i).first ≠ (S.equation i).second ∧
    (S.equation i).first ≠ (S.equation i).third ∧
    (S.equation i).second ≠ (S.equation i).third

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

def SplitGadget.stabilityError {s d : Nat} (g : SplitGadget s d) : ℚ :=
  Finset.univ.expect (fun xv : Ambient s d × g.NoiseIndex =>
    if g.f (xv.1 + g.noise xv.2) = g.f xv.1 then (0 : ℚ) else 1)

end UniqueGamesTheorem.Reduction.ActualSource

end

section

/-! Transport of actual gadgets to the split coordinate model used by the reduction. -/

namespace UniqueGamesTheorem.Integration.SplitGadget

open BinaryLinear

variable {R : Type} [AddCommGroup R] [Module F2 R] [FiniteDimensional F2 R]

open UniqueGamesTheorem.Gadget.ActualGadget (Data stabilityError failureIndicator kernelError Satisfies)
open UniqueGamesTheorem.Reduction.ActualSource

noncomputable def kernelProbability {s d : Nat} (g : SplitGadget s d)
    {P : Type} [AddCommGroup P] [Module F2 P]
    (S : Ambient s d →ₗ[F2] P) : ℚ := by
  classical
  exact Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℚ) else 0)

end UniqueGamesTheorem.Integration.SplitGadget

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_RawTargetLawLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Concrete finite averaging for the projection upper bound

The coefficient samples here are actual functions `Fin t → (Fin m → ZMod 2)`.
Their law is the normalized finite uniform sum over all such functions. The
binomial moment formula is proved from this sum, without an independence or
binomial-distribution premise.
-/

namespace UniqueGamesTheorem.Soundness.RepeatedGameBounds

open scoped BigOperators

noncomputable section

/-! ## Actual weighted winning probabilities under a local simulation -/

open Foundations.Games

namespace Simulation

variable {QA QB A B OA OB X Y : Type}
  [Fintype QA] [Fintype QB] [Fintype A] [Fintype B]
  [Fintype OA] [Fintype OB] [Fintype X] [Fintype Y]

/-- Interpret a concrete predicate and a normalized finite question law as a
game with the common foundation interface. -/
def weightedGame (G : PredicateGame QA QB A B)
    (questions : FiniteDistribution (QA × QB)) : Game QA QB A B := by
  classical
  exact ⟨questions, fun qa qb a b => decide (G.accepts qa qb a b)⟩

end Simulation

/-! ## The actual named projection predicate -/

end
end UniqueGamesTheorem.Soundness.RepeatedGameBounds

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_MaskMomentLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Clean

open Foundations.Games
open scoped BigOperators

noncomputable section

variable {E : Type*} [Fintype E] [Nonempty E]

omit [Nonempty E] in
theorem cleanProbability_nonneg {β : ℝ} (hβ₀ : 0 ≤ β) :
    0 ≤ cleanProbability β E :=
  div_nonneg hβ₀ (Nat.cast_nonneg _)

theorem cleanProbability_le_one {β : ℝ} (hβ₁ : β ≤ 1) :
    cleanProbability β E ≤ 1 := by
  have hc : (1 : ℝ) ≤ Fintype.card E := by
    exact_mod_cast Fintype.card_pos (α := E)
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hc)).mpr
  simpa using hβ₁.trans hc

end
end UniqueGamesTheorem.Clean

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Soundness_ConditionalSimulationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
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

instance secondInputFintype {P R O N : Type}
    [Fintype P] [Fintype R] [Fintype O] [Fintype N] :
    Fintype (ZeroInformation.SecondInput P R O N) := by
  classical
  exact Fintype.ofEquiv ((P → Sum O N) × ZeroInformation.SecondRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

end
end UniqueGamesTheorem.Soundness.ConditionalSimulation

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_EncodingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Computable binary alphabet indexing and full translation permutation tables.
The labels are actual `Fin (2^s)` entries in the target instance format.
-/

namespace UniqueGamesTheorem.Reduction.Encoding

open Integration.BinaryLinear
open Foundations.Target

theorem translationTable_satisfied_iff {s : Nat}
    (a b cLeft cRight : Integration.BinaryLinear.Vector s) :
    (translationTable a b).images[alphabetEquiv s cLeft] = alphabetEquiv s cRight ↔
      cLeft + a + b = cRight := by
  rw [translationTable_images]
  exact (alphabetEquiv s).injective.eq_iff

end UniqueGamesTheorem.Reduction.Encoding

end

section

/-! The finite set of realizable orbit records.  Vertices are the image of the
actual canonical-data map, so equal retained data from different questions
become one vertex.  The two sides remain distinct. -/

namespace UniqueGamesTheorem.Reduction.ActualOrbit

open UniqueGamesTheorem.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

theorem vertex_surjective (can : Q → Ambient s d × T) :
    Function.Surjective (vertex can) := by
  rintro ⟨o, q, hq⟩
  exact ⟨q, Subtype.ext hq⟩

noncomputable instance vertexFintype [Fintype Q] (can : Q → Ambient s d × T) :
    Fintype (Vertex can) := by
  classical
  exact Fintype.ofSurjective (vertex can) (vertex_surjective can)

/-- `false` is the left copy and `true` is the right copy. -/
abbrev TwoSidedVertex (can : Q → Ambient s d × T) := Bool × Vertex can

noncomputable def vertexEquiv [Fintype Q] (can : Q → Ambient s d × T) :
    TwoSidedVertex can ≃ Fin (Fintype.card (TwoSidedVertex can)) :=
  Fintype.equivFin _

/-- Executable vertex numbering from an exhaustive list, preserving the same
realizable-body subtype used in the semantic statements. -/
def explicitVertexEquiv [DecidableEq (Vector d × T)]
    (can : Q → Ambient s d × T) (queries : List Q) (full : ∀ q, q ∈ queries) :
    Vertex can ≃ Fin (Encoding.imageVertices queries (body can)).length :=
  let e : Vertex can ≃ Encoding.ImageVertex queries (body can) :=
    { toFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mpr
        v.property⟩
      invFun v := ⟨v.val, (Encoding.imageVertices_range queries (body can) full v.val).mp
        v.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  e.trans (Encoding.imageEquiv queries (body can))

def unfold (can : Q → Ambient s d × T) (label : Vertex can → Vector s) (q : Q) :
    Vector s := label (vertex can q) + offset can q

theorem add_self_vector (c : Vector s) : c + c = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (c i)

theorem add_cancel_vector (a b : Vector s) : (a + b) + b = a := by
  rw [add_assoc, add_self_vector, add_zero]

/-- The precise orientation used by the generated edge. -/
theorem constraint_iff_unfolded (can : Q → Ambient s d × T)
    (labelL labelR : Vertex can → Vector s) (q r : Q) :
    (labelL (vertex can q) + offset can q) + offset can r = labelR (vertex can r) ↔
      unfold can labelL q = unfold can labelR r := by
  constructor
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'

end UniqueGamesTheorem.Reduction.ActualOrbit

end

section

/-! Internal serialization of canonical orbit bodies. Each record occupies nine
natural-number words, so record boundaries are independent of the tag. The
outer complement coordinate occupies one leading word. These are injectivity,
deduplication, and output-size statements, not machine running-time claims. -/

namespace UniqueGamesTheorem.Reduction.CanonicalEncoding

open Integration.BinaryLinear
open Foundations.Complexity

abbrev Ambient (s d : Nat) := Integration.BinaryLinear.Vector s × Integration.BinaryLinear.Vector d
abbrev Record (n m s d : Nat) := ActualCanonical.Record (Fin n) (Fin m) (Ambient s d)
abbrev Body (n m k s d : Nat) := Integration.BinaryLinear.Vector d × (Fin k → Record n m s d)

theorem vectorWord_lt {s : Nat} (v : Integration.BinaryLinear.Vector s) :
    vectorWord v < 2^s := (Encoding.alphabetEquiv s v).isLt

/-- Words: tag, name, occurrence, followed by three split coefficient pairs.
Padding is zero. A single record uses only the first coefficient pair. -/
def recordWords {n m s d : Nat} : Record n m s d → List Nat
  | .blank => [0, 0, 0, 0, 0, 0, 0, 0, 0]
  | .single name coefficient =>
      [1, name.val, 0, vectorWord coefficient.1, vectorWord coefficient.2, 0, 0, 0, 0]
  | .full occurrence coefficients =>
      [2, 0, occurrence.val,
        vectorWord (coefficients 0).1, vectorWord (coefficients 0).2,
        vectorWord (coefficients 1).1, vectorWord (coefficients 1).2,
        vectorWord (coefficients 2).1, vectorWord (coefficients 2).2]

@[simp] theorem recordWords_length {n m s d : Nat} (r : Record n m s d) :
    (recordWords r).length = 9 := by
  cases r <;> rfl

theorem recordWords_injective {n m s d : Nat} :
    Function.Injective (recordWords (n := n) (m := m) (s := s) (d := d)) := by
  intro r t h
  cases r with
  | blank => cases t <;> simp_all [recordWords]
  | single name coefficient =>
    cases t with
    | blank => simp [recordWords] at h
    | single name' coefficient' =>
      simp [recordWords] at h
      rcases h with ⟨hn, hc, hd⟩
      have hp : coefficient = coefficient' := Prod.ext hc hd
      have hn' : name = name' := Fin.ext hn
      cases hn'
      cases hp
      rfl
    | full occurrence coefficients => simp [recordWords] at h
  | full occurrence coefficients =>
    cases t with
    | blank => simp [recordWords] at h
    | single name coefficient => simp [recordWords] at h
    | full occurrence' coefficients' =>
      simp [recordWords] at h
      rcases h with ⟨hi, h0c, h0d, h1c, h1d, h2c, h2d⟩
      have hp : coefficients = coefficients' := by
        funext i
        fin_cases i
        · exact Prod.ext h0c h0d
        · exact Prod.ext h1c h1d
        · exact Prod.ext h2c h2d
      have hi' : occurrence = occurrence' := Fin.ext hi
      cases hi'
      cases hp
      rfl

def recordsWords {n m s d : Nat} (rs : List (Record n m s d)) : List Nat :=
  rs.flatMap recordWords

@[simp] theorem recordsWords_nil {n m s d : Nat} :
    recordsWords ([] : List (Record n m s d)) = [] := rfl

@[simp] theorem recordsWords_cons {n m s d : Nat} (r : Record n m s d)
    (rs : List (Record n m s d)) :
    recordsWords (r :: rs) = recordWords r ++ recordsWords rs := rfl

@[simp] theorem recordsWords_length {n m s d : Nat} (rs : List (Record n m s d)) :
    (recordsWords rs).length = 9 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem recordsWords_take_head {n m s d : Nat} (r : Record n m s d)
    (rs : List (Record n m s d)) :
    (recordsWords (r :: rs)).take 9 = recordWords r := by
  change (recordWords r ++ recordsWords rs).take 9 = recordWords r
  simpa only [recordWords_length] using
    (List.take_append_length (l₁ := recordWords r) (l₂ := recordsWords rs))

theorem recordsWords_injective {n m s d : Nat} :
    Function.Injective (recordsWords (n := n) (m := m) (s := s) (d := d)) := by
  intro rs
  induction rs with
  | nil =>
    intro ts h
    cases ts with
    | nil => rfl
    | cons t ts =>
      have hl := congrArg List.length h
      simp only [recordsWords_length, List.length_nil, List.length_cons] at hl
      omega
  | cons r rs ih =>
    intro ts h
    cases ts with
    | nil =>
      have hl := congrArg List.length h
      simp only [recordsWords_length, List.length_nil, List.length_cons] at hl
      omega
    | cons t ts =>
      have hh := congrArg (List.take 9) h
      simp only [recordsWords_take_head] at hh
      have hr := recordWords_injective hh
      subst t
      apply congrArg (List.cons r)
      apply ih
      exact List.append_cancel_left (by simpa only [recordsWords_cons] using h)

def bodyWords {n m k s d : Nat} (body : Body n m k s d) : List Nat :=
  vectorWord body.1 :: recordsWords (List.ofFn body.2)

@[simp] theorem bodyWords_length {n m k s d : Nat} (body : Body n m k s d) :
    (bodyWords body).length = 1 + 9*k := by
  simp [bodyWords, Nat.add_comm]

theorem bodyWords_injective {n m k s d : Nat} :
    Function.Injective (bodyWords (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  have hh := List.cons.inj h
  apply Prod.ext
  · exact vectorWord_injective hh.1
  · exact List.ofFn_injective (recordsWords_injective hh.2)

@[simp] theorem bodyWords_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyWords x = bodyWords y ↔ x = y := bodyWords_injective.eq_iff

theorem recordWords_bounded {n m s d : Nat} (r : Record n m s d)
    (w : Nat) (hw : w ∈ recordWords r) : w ≤ wordBound n m s d := by
  unfold wordBound
  cases r with
  | blank =>
    simp [recordWords] at hw
    subst w
    exact Nat.zero_le _
  | single name coefficient =>
    have hn := name.isLt
    have hc := vectorWord_lt coefficient.1
    have hd := vectorWord_lt coefficient.2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega
  | full occurrence coefficients =>
    have hi := occurrence.isLt
    have h0c := vectorWord_lt (coefficients 0).1
    have h0d := vectorWord_lt (coefficients 0).2
    have h1c := vectorWord_lt (coefficients 1).1
    have h1d := vectorWord_lt (coefficients 1).2
    have h2c := vectorWord_lt (coefficients 2).1
    have h2d := vectorWord_lt (coefficients 2).2
    simp only [recordWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h | h | h | h | h | h <;> omega

theorem bodyWords_bounded {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w ≤ wordBound n m s d := by
  rcases List.mem_cons.mp hw with h | h
  · subst w
    have hv := vectorWord_lt body.1
    have hs : 0 < (2 : Nat)^s := pow_pos (by decide) _
    unfold wordBound
    omega
  · obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp h
    exact recordWords_bounded r w hr

end UniqueGamesTheorem.Reduction.CanonicalEncoding

end

section

/-! Direct canonical-body addresses. The fixed list of canonical words is
interpreted in big-endian order, matching forward Horner steps `B*acc+digit`.
Unused addresses represent isolated vertices. These are semantic encoding and
polynomial-size results, not an assumed machine implementation. -/

namespace UniqueGamesTheorem.Reduction.CanonicalAddress

open CanonicalEncoding

@[simp] theorem radix_nil (B : Nat) : radix B [] = 0 := rfl

theorem radix_lt_pow_length {B : Nat} (hB : 1 < B) (words : List Nat)
    (bounded : ∀ w ∈ words, w < B) : radix B words < B ^ words.length := by
  unfold radix
  simpa only [List.length_reverse] using
    Nat.ofDigits_lt_base_pow_length hB
      (fun w hw => bounded w (List.mem_reverse.mp hw))

/-- Fixed width makes leading zero words unambiguous. -/
theorem radix_injective_of_length_eq {B : Nat} (hB : 1 < B)
    {xs ys : List Nat} (sameLength : xs.length = ys.length)
    (xsBounded : ∀ w ∈ xs, w < B) (ysBounded : ∀ w ∈ ys, w < B)
    (sameAddress : radix B xs = radix B ys) : xs = ys := by
  have reversed : xs.reverse = ys.reverse :=
    Nat.ofDigits_inj_of_len_eq hB (by simpa only [List.length_reverse] using sameLength)
      (fun w hw => xsBounded w (List.mem_reverse.mp hw))
      (fun w hw => ysBounded w (List.mem_reverse.mp hw)) sameAddress
  have h := congrArg List.reverse reversed
  simpa only [List.reverse_reverse] using h

@[simp] theorem base_eq (n m s d : Nat) :
    base n m s d = n + m + 2^s + 2^d + 4 := by
  simp [base, wordBound, Nat.add_assoc]

theorem one_lt_base (n m s d : Nat) : 1 < base n m s d := by
  have h : 3 ≤ wordBound n m s d := by
    unfold wordBound
    exact Nat.le_add_left 3 _
  unfold base
  omega

theorem bodyWords_lt_base {n m k s d : Nat} (body : Body n m k s d)
    (w : Nat) (hw : w ∈ bodyWords body) : w < base n m s d :=
  Nat.lt_succ_of_le (bodyWords_bounded body w hw)

def capacity (n m k s d : Nat) : Nat := (base n m s d) ^ (1 + 9*k)

def bodyAddress {n m k s d : Nat} (body : Body n m k s d) :
    Fin (capacity n m k s d) :=
  ⟨radix (base n m s d) (bodyWords body), by
    simpa only [capacity, bodyWords_length] using
      radix_lt_pow_length (one_lt_base n m s d) (bodyWords body) (bodyWords_lt_base body)⟩

@[simp] theorem bodyAddress_val {n m k s d : Nat} (body : Body n m k s d) :
    (bodyAddress body).val = radix (base n m s d) (bodyWords body) := rfl

theorem bodyAddress_injective {n m k s d : Nat} :
    Function.Injective (bodyAddress (n := n) (m := m) (k := k) (s := s) (d := d)) := by
  intro x y h
  apply bodyWords_injective
  exact radix_injective_of_length_eq (one_lt_base n m s d)
    (by simp only [bodyWords_length]) (bodyWords_lt_base x) (bodyWords_lt_base y)
    (congrArg Fin.val h)

@[simp] theorem bodyAddress_eq_iff {n m k s d : Nat} (x y : Body n m k s d) :
    bodyAddress x = bodyAddress y ↔ x = y := bodyAddress_injective.eq_iff

end UniqueGamesTheorem.Reduction.CanonicalAddress

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ExplicitLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite linear-map enumeration for the free homogeneous coordinates.
The lists contain linear maps themselves, constructed by finite coordinate sums.
Their exhaustiveness and lack of repetitions identify the list with the uniform
map experiment. No machine running-time claim follows just from their lengths.
-/

namespace UniqueGamesTheorem.Reduction.ActualEnumeration

open Integration.BinaryLinear
open ActualHomogeneous
open UniqueGamesTheorem.Reduction.Explicit
open scoped BigOperators

variable {α β N : Type*} {m n k s d noiseCount : Nat}

section Coefficients

variable (k : Nat) (R : Type*) [AddCommGroup R] [Module F2 R]

def fromCoefficients (a : Coefficients k R) : E k →ₗ[F2] R where
  toFun x := x.1 • a.1 + ∑ j : Fin k,
    ((x.2 j).1 • (a.2 j).1 + (x.2 j).2 • (a.2 j).2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul]
    simp only [add_add_add_comm, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      mul_smul, smul_add, Finset.smul_sum, RingHom.id_apply]

def toCoefficients (X : E k →ₗ[F2] R) : Coefficients k R :=
  (X (hBasis k), fun j => (X (firstBasis j), X (secondBasis j)))

theorem to_fromCoefficients (a : Coefficients k R) :
    toCoefficients k R (fromCoefficients k R a) = a := by
  apply Prod.ext
  · simp [toCoefficients, fromCoefficients, hBasis]
  · funext j
    apply Prod.ext <;>
      simp [toCoefficients, fromCoefficients, firstBasis, secondBasis, Pi.single_apply,
        apply_ite]

theorem from_toCoefficients (X : E k →ₗ[F2] R) :
    fromCoefficients k R (toCoefficients k R X) = X := by
  apply LinearMap.ext
  intro x
  exact (linearMap_expansion X x).symm

/-- Actual matrix-coefficient equivalence, rather than just a count model. -/
def coefficientEquiv : Coefficients k R ≃ (E k →ₗ[F2] R) where
  toFun := fromCoefficients k R
  invFun := toCoefficients k R
  left_inv := to_fromCoefficients k R
  right_inv := from_toCoefficients k R

def allLinearMaps (values : List R) : List (E k →ₗ[F2] R) :=
  (pairs values (functions (pairs values values) k)).map (coefficientEquiv k R)

theorem length_allLinearMaps (values : List R) :
    (allLinearMaps k R values).length = values.length^(2*k+1) := by
  simp only [allLinearMaps, List.length_map, length_pairs, length_functions]
  rw [show values.length * values.length = values.length^2 by simp [pow_two],
    ← pow_mul, pow_succ]
  exact Nat.mul_comm _ _

theorem mem_allLinearMaps {values : List R} (full : ∀ a, a ∈ values)
    (X : E k →ₗ[F2] R) : X ∈ allLinearMaps k R values := by
  apply List.mem_map.mpr
  refine ⟨toCoefficients k R X, ?_, from_toCoefficients k R X⟩
  apply mem_pairs.mpr
  exact ⟨full _, mem_functions (fun a => mem_pairs.mpr ⟨full _, full _⟩) _⟩

theorem nodup_allLinearMaps {values : List R} (distinct : values.Nodup) :
    (allLinearMaps k R values).Nodup :=
  (nodup_pairs distinct (nodup_functions (nodup_pairs distinct distinct) k)).map
    (coefficientEquiv k R).injective

end Coefficients

def vectors (s : Nat) : List (Integration.BinaryLinear.Vector s) :=
  (List.finRange (2^s)).map (Encoding.alphabetEquiv s).symm

theorem length_vectors (s : Nat) : (vectors s).length = 2^s := by
  simp [vectors]

theorem mem_vectors (v : Integration.BinaryLinear.Vector s) : v ∈ vectors s := by
  exact List.mem_map.mpr ⟨Encoding.alphabetEquiv s v, List.mem_finRange _,
    (Encoding.alphabetEquiv s).symm_apply_apply v⟩

theorem nodup_vectors (s : Nat) : (vectors s).Nodup :=
  (List.nodup_finRange _).map (Encoding.alphabetEquiv s).symm.injective

abbrev Ambient (s d : Nat) :=
  Integration.BinaryLinear.Vector s × Integration.BinaryLinear.Vector d

def ambientVectors (s d : Nat) : List (Ambient s d) := pairs (vectors s) (vectors d)

theorem length_ambientVectors (s d : Nat) : (ambientVectors s d).length = 2^(s+d) := by
  simp [ambientVectors, length_pairs, length_vectors, pow_add]

theorem mem_ambientVectors (v : Ambient s d) : v ∈ ambientVectors s d :=
  mem_pairs.mpr ⟨mem_vectors v.1, mem_vectors v.2⟩

theorem nodup_ambientVectors (s d : Nat) : (ambientVectors s d).Nodup :=
  nodup_pairs (nodup_vectors s) (nodup_vectors d)

abbrev Query (m k s d : Nat) := (Fin k → Fin m) × (E k →ₗ[F2] Ambient s d)

def queries (m k s d : Nat) : List (Query m k s d) :=
  pairs (functions (List.finRange m) k) (allLinearMaps k _ (ambientVectors s d))

theorem mem_queries (q : Query m k s d) : q ∈ queries m k s d :=
  mem_pairs.mpr ⟨mem_functions (fun i => List.mem_finRange i) _,
    mem_allLinearMaps k _ mem_ambientVectors _⟩

theorem nodup_queries (m k s d : Nat) : (queries m k s d).Nodup :=
  nodup_pairs (nodup_functions (List.nodup_finRange _) _)
    (nodup_allLinearMaps k _ (nodup_ambientVectors s d))

abbrev Outcome (m k s d noiseCount : Nat) :=
  Query m k s d ×
    (Fin noiseCount × (E k →ₗ[F2] F2))

def outcomes (m k s d noiseCount : Nat) : List (Outcome m k s d noiseCount) :=
  pairs
    (queries m k s d)
    (pairs (List.finRange noiseCount) (allLinearMaps k F2 [0, 1]))

theorem length_outcomes (m k s d noiseCount : Nat) :
    (outcomes m k s d noiseCount).length = edgeCount m k (s+d) noiseCount := by
  simp only [outcomes, queries, length_pairs, length_functions, List.length_finRange,
    length_allLinearMaps, length_ambientVectors, List.length_cons, List.length_nil,
    edgeCount, ← pow_mul]
  change m^k * 2^((s+d)*(2*k+1)) * (noiseCount * 2^(2*k+1)) =
    m^k * 2^((2*k+1)*(s+d+1)) * noiseCount
  rw [show (2*k+1)*(s+d+1) = (s+d)*(2*k+1)+(2*k+1) by ring, pow_add]
  ring

/-- The executable edge experiment for an arbitrary explicitly ordered noise
index type. Equal noise vectors still have separate indices and entries. -/
def indexedOutcomes (m k s d : Nat) (indices : List N) :
    List (Query m k s d × (N × (E k →ₗ[F2] F2))) :=
  pairs (queries m k s d) (pairs indices (allLinearMaps k F2 [0, 1]))

theorem length_indexedOutcomes (m k s d : Nat) (indices : List N) :
    (indexedOutcomes m k s d indices).length = edgeCount m k (s+d) indices.length := by
  rw [← length_outcomes m k s d indices.length]
  simp only [indexedOutcomes, outcomes, length_pairs, List.length_finRange]

theorem mem_indexedOutcomes {indices : List N} (full : ∀ i, i ∈ indices)
    (ω : Query m k s d × (N × (E k →ₗ[F2] F2))) :
    ω ∈ indexedOutcomes m k s d indices := by
  apply mem_pairs.mpr
  exact ⟨mem_queries _, mem_pairs.mpr ⟨full _, mem_allLinearMaps k F2
    (fun a => by rcases scalar_cases a with rfl | rfl <;> simp) _⟩⟩

theorem nodup_indexedOutcomes {indices : List N} (distinct : indices.Nodup)
    (m k s d : Nat) : (indexedOutcomes m k s d indices).Nodup :=
  nodup_pairs (nodup_queries m k s d)
    (nodup_pairs distinct (nodup_allLinearMaps k F2 (by simp)))

end UniqueGamesTheorem.Reduction.ActualEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_PaddedLaw
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual linear-map realization of the sparse padded-table experiment.
The finite sample has one independent full pair or singleton coefficient at
each occurrence position and one independent homogeneous intercept. Its map
is formed by composing a genuine map on the raw projected target with the
actual parity projection. The third position contributes its parity-dependent
intercept; it is not treated as a homogeneous two-coordinate projection.
-/

namespace UniqueGamesTheorem.Decoder.PaddedLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget RawMapLaw
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

def decodeSlot (i : Fin 3) : Slot :=
  if i = 0 then .first else if i = 1 then .second else .third

def blockThird (d : BlockDraw V) : V := blockAmbient d 2

def singletonPositions (d : Fin k → BlockDraw V) : Finset (Fin k) :=
  Finset.univ.filter fun j => (d j).isRight

def drawSlots (d : Fin k → BlockDraw V) (j : Fin k) : Slot :=
  match d j with
  | .inl _ => .first
  | .inr ia => decodeSlot ia.1

def drawCoefficients (d : Fin k → BlockDraw V) (z : V) :
    RawCoefficients (singletonPositions d) V
  | none => z
  | some (.inl (j, i)) =>
      match d j.val with
      | .inl ab => if i = 0 then ab.1 else ab.2
      | .inr _ => 0
  | some (.inr j) =>
      match d j.val with
      | .inl _ => 0
      | .inr ia => ia.2

def paddedMap (rhs : Fin k → Bool) (d : Fin k → BlockDraw V) (z : V) :
    ActualHomogeneous.E k →ₗ[F2] V :=
  (rawMap (singletonPositions d) V (drawCoefficients d z)).comp
    (rawProjection rhs (singletonPositions d) (drawSlots d))

def interceptShift (rhs : Fin k → Bool) (d : Fin k → BlockDraw V) : V :=
  ∑ j, ofBit (rhs j) • blockThird (d j)

/-- The conditional coefficient sample, with full pairs and singleton values
kept at their occurrence-local positions. -/
abbrev RawTuple (J : Finset (Fin k)) (V : Type) :=
  V × ((PositionOutside J → V × V) × (PositionInside J → V))

def rawTupleEquiv (J : Finset (Fin k)) : RawTuple J V ≃ RawCoefficients J V where
  toFun a
    | none => a.1
    | some (.inl (j, i)) => if i = 0 then (a.2.1 j).1 else (a.2.1 j).2
    | some (.inr j) => a.2.2 j
  invFun gamma := ⟨gamma none,
    ⟨(fun j => (gamma (some (.inl (j, 0))), gamma (some (.inl (j, 1))))),
      (fun j => gamma (some (.inr j)))⟩⟩
  left_inv a := by
    apply Prod.ext rfl
    apply Prod.ext
    · funext j
      rfl
    · rfl
  right_inv gamma := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl

def tupleDraw (J : Finset (Fin k)) (slot : Fin k → Slot) (a : RawTuple J V)
    (j : Fin k) : BlockDraw V :=
  if hj : j ∈ J then .inr (ConcreteExtraction.slotIndex (slot j), a.2.2 ⟨j, hj⟩)
  else .inl (a.2.1 ⟨j, hj⟩)

section Law

variable [Fintype V]

/-- Retain a full pair with probability `1-beta`, or choose one of three
singleton positions with probability `beta/3` and its uniform slope. -/
def blockWeights (β : ℝ) : BlockDraw V → ℝ
  | .inl ab => (1 - β) * uniformWeights (V × V) ab
  | .inr ia => (β / 3) * uniformWeights V ia.2

omit [Module F2 V] in
theorem blockWeights_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    UniqueGamesTheorem.Foundations.Information.IsProbability (blockWeights (V := V) β) := by
  constructor
  · intro d
    cases d with
    | inl ab => exact mul_nonneg (sub_nonneg.mpr hβ') (uniformWeights_pos ab).le
    | inr ia => exact mul_nonneg (div_nonneg hβ (by norm_num)) (uniformWeights_pos ia.2).le
  · rw [Fintype.sum_sum_type]
    simp only [blockWeights, ← Finset.mul_sum,
      (uniformWeights_isProbability (α := V × V)).2, mul_one, Fintype.sum_prod_type,
      (uniformWeights_isProbability (α := V)).2]
    simp

def drawWeights (β : ℝ) (k : ℕ) : ((Fin k → BlockDraw V) × V) → ℝ :=
  fun dz => independentWeights (blockWeights β) k dz.1 * uniformWeights V dz.2

def paddedWeights (rhs : Fin k → Bool) (β : ℝ) : ActualEnumeration.Coefficients k V → ℝ :=
  pushforwardWeight (drawWeights β k)
    (fun dz => ActualEnumeration.toCoefficients k V (paddedMap rhs dz.1 dz.2))

def choiceWeight (β : ℝ) : ProjectionChoice → ℝ
  | none => 1 - β
  | some _ => β / 3

theorem choiceWeight_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    UniqueGamesTheorem.Foundations.Information.IsProbability (choiceWeight β) := by
  constructor
  · intro c
    cases c with
    | none => exact sub_nonneg.mpr hβ'
    | some i => exact div_nonneg hβ (by norm_num)
  · rw [Fintype.sum_option]
    simp [choiceWeight]
    ring

def blockKernel : ProjectionChoice → BlockDraw V → ℝ
  | none, .inl ab => uniformWeights (V × V) ab
  | some i, .inr ja => if i = ja.1 then uniformWeights V ja.2 else 0
  | _, _ => 0

def choiceTupleWeight (β : ℝ) (c : Fin k → ProjectionChoice) : ℝ :=
  ∏ j, choiceWeight β (c j)

theorem choiceTupleWeight_isProbability (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    UniqueGamesTheorem.Foundations.Information.IsProbability (choiceTupleWeight (k := k) β) := by
  exact independentWeights_isProbability (choiceWeight β)
    (choiceWeight_isProbability β hβ hβ') k

def kernelTupleWeight (c : Fin k → ProjectionChoice) (d : Fin k → BlockDraw V) : ℝ :=
  ∏ j, blockKernel (c j) (d j)

/-- The actual coefficient type after a choice has been fixed. -/
def ChoiceValue (V : Type) : ProjectionChoice → Type
  | none => V × V
  | some _ => V

instance choiceValueFintype (c : ProjectionChoice) : Fintype (ChoiceValue V c) := by
  cases c <;> dsimp [ChoiceValue] <;> infer_instance

def choiceEmbed : (c : ProjectionChoice) → ChoiceValue V c → BlockDraw V
  | none, ab => .inl ab
  | some i, a => .inr (i, a)

def choiceMask (c : Fin k → ProjectionChoice) : Finset (Fin k) :=
  Finset.univ.filter fun j => (c j).isSome

def choiceSlot : ProjectionChoice → Slot
  | none => .first
  | some i => decodeSlot i

def choiceSlots (c : Fin k → ProjectionChoice) (j : Fin k) : Slot :=
  choiceSlot (c j)

theorem not_mem_choiceMask (c : Fin k → ProjectionChoice) (j : Fin k) :
    j ∉ choiceMask c ↔ c j = none := by
  cases h : c j <;> simp [choiceMask, h]

def fullChoiceValue : (c : ProjectionChoice) → ChoiceValue V c → V × V
  | none, x => x
  | some _, _ => (0, 0)

def singleChoiceValue : (c : ProjectionChoice) → ChoiceValue V c → V
  | none, _ => 0
  | some _, x => x

def readChoiceValue (q : ProjectionChoice) (full : q = none → V × V)
    (single : q.isSome = true → V) : ChoiceValue V q := by
  cases q with
  | none => exact full rfl
  | some i => exact single rfl

omit [Module F2 V] [Fintype V] in
theorem readChoiceValue_roundtrip (q : ProjectionChoice) (v : ChoiceValue V q) :
    readChoiceValue q (fun _ => fullChoiceValue q v)
      (fun _ => singleChoiceValue q v) = v := by
  cases q <;> rfl

omit [Module F2 V] [Fintype V] in
theorem readChoiceValue_full (q : ProjectionChoice) (full : q = none → V × V)
    (single : q.isSome = true → V) (h : q = none) :
    fullChoiceValue q (readChoiceValue q full single) = full h := by
  subst q
  rfl

omit [Module F2 V] [Fintype V] in
theorem readChoiceValue_single (q : ProjectionChoice) (full : q = none → V × V)
    (single : q.isSome = true → V) (h : q.isSome = true) :
    singleChoiceValue q (readChoiceValue q full single) = single h := by
  cases q with
  | none => simp at h
  | some i => rfl

def choiceValuesToRawTuple (c : Fin k → ProjectionChoice)
    (fz : (∀ j, ChoiceValue V (c j)) × V) : RawTuple (choiceMask c) V :=
  (fz.2,
    (fun j => fullChoiceValue (c j.val) (fz.1 j.val)),
      fun j => singleChoiceValue (c j.val) (fz.1 j.val))

def rawTupleToChoiceValues (c : Fin k → ProjectionChoice)
    (a : RawTuple (choiceMask c) V) (j : Fin k) : ChoiceValue V (c j) :=
  readChoiceValue (c j)
    (fun h => a.2.1 ⟨j, (not_mem_choiceMask c j).mpr h⟩)
    (fun h => a.2.2 ⟨j, by simpa [choiceMask] using h⟩)

/-- Choice fibers and the RawTuple model contain exactly the
same coefficients, with no unused coordinate and no multiplicity. -/
def choiceValuesRawTupleEquiv (c : Fin k → ProjectionChoice) :
    ((∀ j, ChoiceValue V (c j)) × V) ≃ RawTuple (choiceMask c) V where
  toFun := choiceValuesToRawTuple c
  invFun a := (rawTupleToChoiceValues c a, a.1)
  left_inv fz := by
    apply Prod.ext
    · funext j
      exact readChoiceValue_roundtrip (c j) (fz.1 j)
    · rfl
  right_inv a := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        have hc : c j.val = none := (not_mem_choiceMask c j.val).mp j.property
        exact readChoiceValue_full (c j.val) _ _ hc
      · funext j
        have hc : (c j.val).isSome = true := by
          simpa [choiceMask] using j.property
        exact readChoiceValue_single (c j.val) _ _ hc

section MapSpace

variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

def paddedMapWeights (rhs : Fin k → Bool) (β : ℝ) :
    (ActualHomogeneous.E k →ₗ[F2] V) → ℝ :=
  pushforwardWeight (drawWeights β k) (fun dz => paddedMap rhs dz.1 dz.2)

end MapSpace

end Law

end
end UniqueGamesTheorem.Decoder.PaddedLaw

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_StochasticBound
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Local randomized advice responses are bounded using complete independently
sampled response tables. The verifier questions are the actual weighted
pushforward of the occurrence/position draw, with the complete private row
input retained on each side. No response sees the opposite private question.

The outer mask and coefficient tuple may be fixed before selecting either
response kernel. Revealing these data only strengthens this upper bound; they
contain no clean question or agreement event. The quantitative game-repetition
rate is a separate input to the final averaging lemma.
-/

namespace UniqueGamesTheorem.Clean.StochasticBound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds
open scoped BigOperators

noncomputable section

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

/-- The common weighted-game interface for the actual fixed-advice experiment. -/
def actualGame (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) :
    Game (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P) :=
  Simulation.weightedGame (ActualProjection.predicateGame (R := R) g (membershipBool J))
    ((FiniteDistribution.table (fun _ : P => μ)).pushforward fun draw =>
      (actualFirst J gamma draw, actualSecond J g.name gamma draw))

/-- The native experiment samples a mask, then the actual coefficient tuple.
The kernels may depend on these public choices but not on an opposite input. -/
def nativeStochasticSuccess (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      (RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R))).expectation
      fun gamma => (actualGame μ (NativeExperiment.maskSet mask) g gamma).stochasticSuccess
        (responses mask gamma).1 (responses mask gamma).2

end
end UniqueGamesTheorem.Clean.StochasticBound

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_AdviceFibersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier
open MatrixCharacters MatrixFourier MatrixNoise MatrixEnergy

namespace UniqueGamesTheorem.Decoder.PositiveMultiplier

section ActualMatrixTest

variable {Q C E V : Type*} [Fintype Q] [Fintype C]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
  [Fintype V] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)]

/-- The actual equality test, including zero perturbation factors. -/
def equalityAcceptance (ν : V → ℝ) (label : (E →ₗ[F2] V) → C) : ℝ := by
  classical
  exact 𝔼 X, ∑ v, ν v * (𝔼 l : E →ₗ[F2] F2,
    if label X = label (X + l.smulRight v) then (1 : ℝ) else 0)

end ActualMatrixTest

section UniformSubspace

variable {K V E : Type*}
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup V] [Module F2 V] [Fintype V]
  [AddCommGroup E] [Module F2 E]

/-- Pushforward of uniform sampling in `K`.  For a subspace inclusion this
is uniform sampling in that subspace; the definition also permits a linear
map with nontrivial fibers without accidentally conditioning on nonzero vectors. -/
def subspaceLaw (ι : K →ₗ[F2] V) (v : V) : ℝ := by
  classical
  exact ∑ k, if ι k = v then (Fintype.card K : ℝ)⁻¹ else 0

end UniformSubspace

end UniqueGamesTheorem.Decoder.PositiveMultiplier

end

end

section

noncomputable section

namespace UniqueGamesTheorem.Decoder.PrivateFourier

open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixFourier
open scoped BigOperators Classical

section Signs

/-- A real-valued binary character, with the uniform Fourier normalization. -/
def sign (a : F2) : ℝ := (binarySign a).re

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

theorem sign_sq (a : F2) : sign a ^ 2 = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

@[simp] theorem sign_abs (a : F2) : |sign a| = 1 := by
  rcases Integration.BinaryLinear.scalar_cases a with rfl | rfl <;> simp

end Signs

section ActualFourier

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]

/-- The private sign function, formed from the table on one visible row fiber. -/
def tableSign (F : (E →ₗ[F2] H) → K) (σ : K →ₗ[F2] F2)
    (N : E →ₗ[F2] H) : ℝ := sign (σ (F N))

/-- The actual probability assigned to a reverse-map frequency. -/
def frequencyWeight (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) : ℝ :=
  linearCoeff f Φ ^ 2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 H] [Fintype (H →ₗ[F2] E)] in
theorem frequencyWeight_nonneg (f : (E →ₗ[F2] H) → ℝ) (Φ : H →ₗ[F2] E) :
    0 ≤ frequencyWeight f Φ := sq_nonneg _

/-- Squared Fourier coefficients of the private sign form a probability law. -/
theorem tableSign_frequencyWeight_sum (F : (E →ₗ[F2] H) → K)
    (σ : K →ₗ[F2] F2) :
    ∑ Φ : H →ₗ[F2] E, frequencyWeight (tableSign F σ) Φ = 1 := by
  simp only [frequencyWeight, linear_parseval, tableSign, sign_sq]
  exact Fintype.expect_const 1

end ActualFourier

section AffineSlice

variable {E H V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)]

/-- Frequencies in the affine target's annihilator coset.  With `q = Q.mkQ`,
this is exactly `θ + Hom(H,Q)` in the ambient reverse-map space. -/
def frequencyCoset (q : E →ₗ[F2] V) (θ : H →ₗ[F2] E) :
    Finset (H →ₗ[F2] E) := Finset.univ.filter fun Φ => q.comp (Φ + θ) = 0

/-- Correlation on a genuine affine slice.  `N₀` is retained: its phase cannot
be discarded when the witness has a nonzero affine intercept. -/
def sliceCorrelation (q : E →ₗ[F2] V) (N₀ : E →ₗ[F2] H)
    (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) : ℝ :=
  𝔼 A : V →ₗ[F2] H,
    f (N₀ + A.comp q) * (linearTraceCharacter θ (N₀ + A.comp q)).re

end AffineSlice

end UniqueGamesTheorem.Decoder.PrivateFourier

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_PrivateStrategyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual private response laws for Fourier decoding

The right response law has only its row-fiber table, the inclusion of its hidden
kernel, a first-bit map, and an actual fallback answer as arguments.  In
particular it has no column slice or witness.  Zero-mass invalid frequencies
are repaired to the fallback so that the response type always consists of
actual answers.  Witness data occur only in the success analysis.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.PrivateStrategy

attribute [local instance] Classical.propDecidable

open PrivateFourier
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

section Candidates

variable {E E' : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup E'] [Module F2 E'] [Fintype E]

def candidates (Z : Submodule F2 E) (z : E) (τ : E →ₗ[F2] F2) : Finset E :=
  Finset.univ.filter fun v => v - z ∈ Z ∧ τ v = 1

theorem mem_candidates (Z : Submodule F2 E) (z v : E) (τ : E →ₗ[F2] F2) :
    v ∈ candidates Z z τ ↔ v - z ∈ Z ∧ τ v = 1 := by simp [candidates]

end Candidates

section RightRule

variable {E H K : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

omit [FiniteDimensional F2 H] in
theorem exists_unit (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) : ∃ h, σ h = 1 := by
  have hn : ∃ h, σ h ≠ 0 := by
    by_contra hh
    apply hne
    ext h
    by_contra hh'
    exact hh ⟨h, hh'⟩
  obtain ⟨h, hh⟩ := hn
  exact ⟨h, (UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases _).resolve_left hh⟩

def chooseUnit (σ : H →ₗ[F2] F2) (hne : σ ≠ 0) : H :=
  Classical.choose (exists_unit σ hne)

abbrev ActualAnswer (τ : E →ₗ[F2] F2) := {v : E // τ v = 1}

/-- The uniform output character followed by its actual Fourier frequency. -/
def privateSeedLaw (F : (E →ₗ[F2] H) → K) :
    FiniteDistribution ((K →ₗ[F2] F2) × (H →ₗ[F2] E)) where
  weight p := frequencyWeight (tableSign F p.1) p.2 /
    (Fintype.card (K →ₗ[F2] F2) : ℝ)
  nonnegative p := div_nonneg (frequencyWeight_nonneg _ _) (Nat.cast_nonneg _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.sum_div, tableSign_frequencyWeight_sum]
    simp [Fintype.card_ne_zero]

/-- The decoder receives no left witness.  The first-bit repair affects only
zero-mass frequencies when the table is folded. -/
def privateOutput (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2)
    (fallback : ActualAnswer τ) (p : (K →ₗ[F2] F2) × (H →ₗ[F2] E)) :
    ActualAnswer τ :=
  if hn : p.1.comp ι = 0 then fallback else
    let v := p.2 (chooseUnit (p.1.comp ι) hn)
    if hv : τ v = 1 then ⟨v, hv⟩ else fallback

/-- This is an actual finite distribution on actual answers, for every visible
row table.  The sampler's normalization is Parseval, not a hypothesis. -/
def privateLaw [Fintype E] (F : (E →ₗ[F2] H) → K)
    (ι : H →ₗ[F2] K) (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) :
    FiniteDistribution (ActualAnswer τ) :=
  (privateSeedLaw F).pushforward (privateOutput ι τ fallback)

end RightRule

section LeftRule

variable {E : Type*} [AddCommGroup E] [Module F2 E] [Fintype E]

/-- The left rule is uniform on its own chosen affine-answer candidates. -/
def candidateLaw (Z : Submodule F2 E) (z : E) (τ : E →ₗ[F2] F2)
    (hz : τ z = 1) : FiniteDistribution (ActualAnswer τ) := by
  letI : Nonempty {v // v ∈ candidates Z z τ} :=
    ⟨⟨z, (mem_candidates Z z z τ).2 ⟨by simp, hz⟩⟩⟩
  exact (FiniteDistribution.uniform {v // v ∈ candidates Z z τ}).pushforward
    (fun v => ⟨v.1, ((mem_candidates Z z v.1 τ).1 v.2).2⟩)

end LeftRule

section ConditionalAgreement

variable {U E H K : Type*}
variable [AddCommGroup U] [Module F2 U] [Fintype U]
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

/-- Actual independent response-law success, with the literal projection test. -/
def conditionalAgreement (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) : ℝ :=
  ((candidateLaw Z z τU hz).product (privateLaw F ι τ fallback)).probability
    (fun a => decide (π a.1.1 = a.2.1))

/-- The exact good Fourier mass in a witness coset; unlike the response law,
this analysis-only quantity is allowed to mention the witness. -/
def goodCosetMass (Q : Submodule F2 E) (z' : E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K) : ℝ :=
  𝔼 σ : K →ₗ[F2] F2, if σ.comp ι ≠ 0 then
    ∑ Φ ∈ frequencyCoset Q.mkQ ((σ.comp ι).smulRight z'),
      frequencyWeight (tableSign F σ) Φ else 0

end ConditionalAgreement

end UniqueGamesTheorem.Decoder.PrivateStrategy

end

end

section

/-!
The surrogate perturbation fixes the complementary table exactly. Splitting
the actual uniform matrix law therefore expresses surrogate acceptance as the
mean of the uniform shortcode tests on the `(U,T)` fibers, including zero
perturbation factors. This supplies the sampling identification needed before
applying the inverse theorem to the many useful fibers.
-/

namespace UniqueGamesTheorem.Decoder.SurrogateFibers

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier
open PositiveMultiplier
open scoped BigOperators

noncomputable section

variable {E K W C : Type*}
variable [AddCommGroup E] [Module F2 E]
variable [AddCommGroup K] [Module F2 K] [Fintype K]
variable [AddCommGroup W] [Module F2 W] [Fintype W]
variable [Fintype (E →ₗ[F2] F2)]
variable [Fintype (E →ₗ[F2] K)] [Fintype (E →ₗ[F2] W)]
variable [Fintype (E →ₗ[F2] K × W)]

/-- Uniform shortcode sampling; neither nonzero-factor conditioning nor
rank-one-matrix-uniform sampling is substituted for its two independent factors. -/
def shortcodeAcceptance (f : (E →ₗ[F2] K) → C) : ℝ := by
  classical
  exact 𝔼 M, 𝔼 a : K, 𝔼 l : E →ₗ[F2] F2,
    if f M = f (M + l.smulRight a) then (1 : ℝ) else 0

end
end UniqueGamesTheorem.Decoder.SurrogateFibers

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_NoiseEnumerationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Finite noise tables for the executable outer reduction. Positions, including
positions containing equal vectors, remain distinct sample outcomes. -/

namespace UniqueGamesTheorem.Integration.NoiseTables

open BinaryLinear UniqueGamesTheorem.Reduction.ActualSource

variable {s d : Nat}

namespace Table

def gadget (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : SplitGadget s d where
  f := f
  equivariant := hf
  NoiseIndex := Fin T.vectors.length
  noiseFintype := inferInstance
  noiseNonempty := ⟨⟨0, List.length_pos_iff.mpr T.nonempty⟩⟩
  noise := T.vectors.get

end Table
end UniqueGamesTheorem.Integration.NoiseTables

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualGame
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite translation game of Definition 4.6.  All questions, linear
maps, noise indices and linear functionals occur once in the outcome list.
Equal noise vectors retain their index multiplicity. -/

namespace UniqueGamesTheorem.Reduction.ActualGame

open UniqueGamesTheorem.Integration.BinaryLinear
open ActualSource
open Foundations.Target
open scoped BigOperators

abbrev Dual (k : Nat) := ActualHomogeneous.E k →ₗ[F2] F2

noncomputable instance mapFintype (k s d : Nat) : Fintype (Map k s d) :=
  Fintype.ofInjective (fun X : Map k s d => (X : ActualHomogeneous.E k →
    ActualSource.Ambient s d)) DFunLike.coe_injective

noncomputable instance dualFintype (k : Nat) : Fintype (Dual k) :=
  Fintype.ofInjective (fun X : Dual k => (X : ActualHomogeneous.E k → F2))
    DFunLike.coe_injective

abbrev TwoSidedVertex (S : Source) (k s d : Nat) := Bool × Vertex S k s d

noncomputable def vertexCount (S : Source) (k s d : Nat) : Nat :=
  Fintype.card (TwoSidedVertex S k s d)

noncomputable def vertexEncoding (S : Source) (k s d : Nat) :
    TwoSidedVertex S k s d ≃ Fin (vertexCount S k s d) :=
  ActualOrbit.vertexEquiv (canonical S k s d)

/-- Each product element is a separate edge occurrence. -/
abbrev Outcome (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  Query S k s d × g.NoiseIndex × Dual k

def leftQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Query S k s d := ω.1

def rightQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Query S k s d :=
  (ω.1.1, ω.1.2 + ω.2.2.smulRight (g.noise ω.2.1))

noncomputable def edge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := vertexEncoding S k s d (false, vertex S k s d (leftQuery S k g ω))
  target := vertexEncoding S k s d (true, vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

noncomputable def outcomes (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    List (Outcome S k g) := Finset.univ.toList

@[simp] theorem mem_outcomes (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : Outcome S k g) : ω ∈ outcomes S k g := by
  simp [outcomes]

theorem outcomes_nodup (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    (outcomes S k g).Nodup := Finset.nodup_toList _

@[simp] theorem outcomes_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) : (outcomes S k g).length = Fintype.card (Outcome S k g) := by
  simp [outcomes]

noncomputable def sideLabel (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (side : Bool) :
    Vertex S k s d → Alphabet s := fun v =>
  (Encoding.alphabetEquiv s).symm (labeling (vertexEncoding S k s d (side, v)))

noncomputable def labelingOf (S : Source) (k s d : Nat)
    (labels : Bool → Vertex S k s d → Alphabet s) :
    Fin (vertexCount S k s d) → Fin (2^s) := fun i =>
  let v := (vertexEncoding S k s d).symm i
  Encoding.alphabetEquiv s (labels v.1 v.2)

@[simp] theorem sideLabel_labelingOf (S : Source) (k s d : Nat)
    (labels : Bool → Vertex S k s d → Alphabet s) (side : Bool) :
    sideLabel S k s d (labelingOf S k s d labels) side = labels side := by
  funext v
  simp [sideLabel, labelingOf]

noncomputable def unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (side : Bool)
    (q : Query S k s d) : Alphabet s :=
  ActualOrbit.unfold (canonical S k s d) (sideLabel S k s d labeling side) q

theorem edge_satisfied_iff (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (ω : Outcome S k g) :
    (edge S k g ω).satisfied labeling = true ↔
      unfolded S k s d labeling false (leftQuery S k g ω) =
      unfolded S k s d labeling true (rightQuery S k g ω) := by
  rw [Constraint.satisfied, decide_eq_true_eq]
  have h := Encoding.translationTable_satisfied_iff
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))
    (sideLabel S k s d labeling false (vertex S k s d (leftQuery S k g ω)))
    (sideLabel S k s d labeling true (vertex S k s d (rightQuery S k g ω)))
  simp only [sideLabel, Encoding.alphabetEquiv_apply_symm_apply] at h
  exact h.trans (ActualOrbit.constraint_iff_unfolded (canonical S k s d)
    (sideLabel S k s d labeling false) (sideLabel S k s d labeling true) _ _)

noncomputable def acceptanceProbability (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) : ℚ :=
  Finset.univ.expect (fun ω : Outcome S k g =>
    if (edge S k g ω).satisfied labeling then (1 : ℚ) else 0)

theorem acceptanceProbability_eq_test (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      Finset.univ.expect (fun ω : Outcome S k g =>
        if unfolded S k s d labeling false (leftQuery S k g ω) =
            unfolded S k s d labeling true (rightQuery S k g ω)
        then (1 : ℚ) else 0) := by
  unfold acceptanceProbability
  apply Finset.expect_congr rfl
  intro ω _
  simp only [edge_satisfied_iff]

/-! ## Executable enumeration and vertex numbering -/

def orbitBodyDecidableEq (S : Source) (k s d : Nat) :
    DecidableEq (Vector d × (Fin k → ActualCanonical.Record
      (Fin S.variables) (Fin S.occurrences) (ActualSource.Ambient s d))) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

def explicitBodies (S : Source) (k s d : Nat) := by
  letI := orbitBodyDecidableEq S k s d
  exact Encoding.imageVertices (ActualEnumeration.queries S.occurrences k s d)
    (ActualOrbit.body (canonical S k s d))

def explicitVertexCount (S : Source) (k s d : Nat) : Nat :=
  2 * (explicitBodies S k s d).length

def explicitVertexEncoding (S : Source) (k s d : Nat) :
    TwoSidedVertex S k s d ≃ Fin (explicitVertexCount S k s d) := by
  letI := orbitBodyDecidableEq S k s d
  exact (Equiv.prodCongr (Equiv.refl Bool)
    (ActualOrbit.explicitVertexEquiv (canonical S k s d)
      (ActualEnumeration.queries S.occurrences k s d) ActualEnumeration.mem_queries)).trans
    (Encoding.sideEquiv _)

def explicitEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (explicitVertexCount S k s d) (2^s) where
  source := explicitVertexEncoding S k s d (false, vertex S k s d (leftQuery S k g ω))
  target := explicitVertexEncoding S k s d (true, vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

def explicitOutcomes (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : List (Outcome S k g) :=
  ActualEnumeration.indexedOutcomes S.occurrences k s d en.indices

theorem explicitOutcomes_nodup (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (explicitOutcomes S k g en).Nodup :=
  ActualEnumeration.nodup_indexedOutcomes en.nodup _ _ _ _

@[simp] theorem mem_explicitOutcomes (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) (ω : Outcome S k g) :
    ω ∈ explicitOutcomes S k g en :=
  ActualEnumeration.mem_indexedOutcomes en.complete ω

theorem explicitOutcomes_perm_outcomes (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (explicitOutcomes S k g en).Perm (outcomes S k g) := by
  apply (List.perm_ext_iff_of_nodup (explicitOutcomes_nodup S k g en)
    (outcomes_nodup S k g)).2
  intro ω
  simp

/-- This construction computes its vertex numbering, all outcomes, and every
forward/inverse permutation entry from the explicitly supplied finite data. -/
def outputInstanceWithEnumeration (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) : Foundations.Target.Instance (2^s) where
  vertices := explicitVertexCount S k s d
  constraints := (explicitOutcomes S k g en).map (explicitEdge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : explicitEdge S k g ω ∈
        (explicitOutcomes S k g en).map (explicitEdge S k g) :=
      List.mem_map.mpr ⟨ω, mem_explicitOutcomes S k g en ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstanceWithEnumeration_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstanceWithEnumeration, List.length_map, explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

end UniqueGamesTheorem.Reduction.ActualGame

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_TableKeysGame
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.TableKeysGame

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction
open ActualSource Foundations.Target
open scoped BigOperators

abbrev Question (S : Source) (k : Nat) := ActualGame.Question S k
abbrev Map (k s d : Nat) := ActualGame.Map k s d
abbrev Dual (k : Nat) := ActualGame.Dual k
abbrev Query (S : Source) (k s d : Nat) := ActualGame.Query S k s d
abbrev canonical (S : Source) (k s d : Nat) := ActualGame.canonical S k s d

/-- One realized key orbit, with no prover-side copy. -/
abbrev Vertex (S : Source) (k s d : Nat) := ActualGame.Vertex S k s d
abbrev vertex (S : Source) (k s d : Nat) := ActualGame.vertex S k s d
abbrev offset (S : Source) (k s d : Nat) := ActualGame.offset S k s d
abbrev shiftQuery (S : Source) (k s d : Nat) := ActualGame.shiftQuery S k s d

noncomputable def vertexCount (S : Source) (k s d : Nat) : Nat :=
  Fintype.card (Vertex S k s d)

noncomputable def vertexEncoding (S : Source) (k s d : Nat) :
    Vertex S k s d ≃ Fin (vertexCount S k s d) := Fintype.equivFin _

/-- All four sampling choices remain separate occurrence indices. -/
abbrev Outcome (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  Query S k s d × g.NoiseIndex × Dual k

abbrev leftQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  ActualGame.leftQuery S k g
abbrev rightQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  ActualGame.rightQuery S k g

noncomputable def edge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := vertexEncoding S k s d (vertex S k s d (leftQuery S k g ω))
  target := vertexEncoding S k s d (vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

noncomputable def outcomes (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  ActualGame.outcomes S k g

noncomputable def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (outcomes S k g).map (edge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : edge S k g ω ∈ (outcomes S k g).map (edge S k g) :=
      List.mem_map.mpr ⟨ω, ActualGame.mem_outcomes S k g ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstance_constraints_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) :
    (outputInstance S k g).constraints.length = Fintype.card (Outcome S k g) := by
  simp [outputInstance, outcomes]

noncomputable def vertexLabel (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    Vertex S k s d → Alphabet s := fun v =>
  (Encoding.alphabetEquiv s).symm (labeling (vertexEncoding S k s d v))

noncomputable def labelingOf (S : Source) (k s d : Nat)
    (labels : Vertex S k s d → Alphabet s) :
    Fin (vertexCount S k s d) → Fin (2^s) := fun i =>
  Encoding.alphabetEquiv s (labels ((vertexEncoding S k s d).symm i))

@[simp] theorem vertexLabel_labelingOf (S : Source) (k s d : Nat)
    (labels : Vertex S k s d → Alphabet s) :
    vertexLabel S k s d (labelingOf S k s d labels) = labels := by
  funext v
  simp [vertexLabel, labelingOf]

/-- Restore the removed alphabet component of the affine intercept. -/
noncomputable def unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (q : Query S k s d) : Alphabet s :=
  ActualOrbit.unfold (canonical S k s d) (vertexLabel S k s d labeling) q

theorem unfolded_equivariant (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (q : Query S k s d) (c : Alphabet s) :
    unfolded S k s d labeling (shiftQuery S k s d c q) =
      unfolded S k s d labeling q + c := by
  change vertexLabel S k s d labeling
      (ActualGame.vertex S k s d (ActualGame.shiftQuery S k s d c q)) +
    ActualGame.offset S k s d (ActualGame.shiftQuery S k s d c q) = _
  rw [ActualGame.vertex_shiftQuery, ActualGame.offset_shiftQuery]
  exact (add_assoc _ _ _).symm

theorem edge_satisfied_iff (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (ω : Outcome S k g) :
    (edge S k g ω).satisfied labeling = true ↔
      unfolded S k s d labeling (leftQuery S k g ω) =
        unfolded S k s d labeling (rightQuery S k g ω) := by
  rw [Constraint.satisfied, decide_eq_true_eq]
  have h := Encoding.translationTable_satisfied_iff
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))
    (vertexLabel S k s d labeling (vertex S k s d (leftQuery S k g ω)))
    (vertexLabel S k s d labeling (vertex S k s d (rightQuery S k g ω)))
  simp only [vertexLabel, Encoding.alphabetEquiv_apply_symm_apply] at h
  exact h.trans (ActualOrbit.constraint_iff_unfolded (canonical S k s d)
    (vertexLabel S k s d labeling) (vertexLabel S k s d labeling) _ _)

noncomputable def acceptanceProbability (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) : ℚ :=
  𝔼 ω : Outcome S k g, if (edge S k g ω).satisfied labeling then (1 : ℚ) else 0

theorem acceptanceProbability_eq_test (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      𝔼 ω : Outcome S k g,
        if unfolded S k s d labeling (leftQuery S k g ω) =
            unfolded S k s d labeling (rightQuery S k g ω)
        then (1 : ℚ) else 0 := by
  unfold acceptanceProbability
  apply Finset.expect_congr rfl
  intro ω _
  simp only [edge_satisfied_iff]

theorem countSatisfied_map {n q : Nat} {I : Type*}
    (labeling : Fin n → Fin q) (edges : I → Constraint n q) (xs : List I) :
    countSatisfied labeling (xs.map edges) =
      (xs.map (fun x => if (edges x).satisfied labeling then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, countSatisfied, List.sum_cons, ih]

theorem countSatisfied_eq_sum (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    countSatisfied labeling (outputInstance S k g).constraints =
      ∑ ω : Outcome S k g, if (edge S k g ω).satisfied labeling then 1 else 0 := by
  change countSatisfied labeling ((outcomes S k g).map (edge S k g)) = _
  rw [countSatisfied_map]
  exact Finset.sum_map_toList _ _

/-- The test probability is the satisfied fraction of the actual occurrence list. -/
theorem acceptanceProbability_eq_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      (countSatisfied labeling (outputInstance S k g).constraints : ℚ) /
        (outputInstance S k g).constraints.length := by
  rw [acceptanceProbability, Fintype.expect_eq_sum_div_card,
    outputInstance_constraints_length, countSatisfied_eq_sum]
  congr 1
  simp

/-- Exhaustive numbering of the same single-orbit vertex type. -/
def explicitVertexCount (S : Source) (k s d : Nat) : Nat :=
  (ActualGame.explicitBodies S k s d).length

def explicitVertexEncoding (S : Source) (k s d : Nat) :
    Vertex S k s d ≃ Fin (explicitVertexCount S k s d) := by
  letI := ActualGame.orbitBodyDecidableEq S k s d
  exact ActualOrbit.explicitVertexEquiv (canonical S k s d)
    (ActualEnumeration.queries S.occurrences k s d) ActualEnumeration.mem_queries

noncomputable def semanticToExplicitVertices (S : Source) (k s d : Nat) :
    Fin (vertexCount S k s d) ≃ Fin (explicitVertexCount S k s d) :=
  (vertexEncoding S k s d).symm.trans (explicitVertexEncoding S k s d)

@[simp] theorem semanticToExplicitVertices_apply (S : Source) (k s d : Nat)
    (v : Vertex S k s d) :
    semanticToExplicitVertices S k s d (vertexEncoding S k s d v) =
      explicitVertexEncoding S k s d v := by
  simp [semanticToExplicitVertices]

def explicitEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (explicitVertexCount S k s d) (2^s) where
  source := explicitVertexEncoding S k s d (vertex S k s d (leftQuery S k g ω))
  target := explicitVertexEncoding S k s d (vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

theorem explicitEdge_eq_rename (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : Outcome S k g) :
    explicitEdge S k g ω = Integration.InstanceEquivalences.renameConstraint
      (semanticToExplicitVertices S k s d) (edge S k g ω) := by
  simp only [explicitEdge, Integration.InstanceEquivalences.renameConstraint, edge,
    semanticToExplicitVertices_apply]

/-- Executable finite output, still allowing loops and parallel occurrences. -/
def outputInstanceWithEnumeration (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := explicitVertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (explicitEdge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : explicitEdge S k g ω ∈
        (ActualGame.explicitOutcomes S k g en).map (explicitEdge S k g) :=
      List.mem_map.mpr ⟨ω, ActualGame.mem_explicitOutcomes S k g en ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstanceWithEnumeration_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstanceWithEnumeration, List.length_map,
    ActualGame.explicitOutcomes, ActualEnumeration.length_indexedOutcomes]

theorem explicitConstraints_perm_renamed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.Perm
      ((outputInstance S k g).constraints.map
        (Integration.InstanceEquivalences.renameConstraint (semanticToExplicitVertices S k s d))) := by
  simpa only [outputInstanceWithEnumeration, outputInstance, List.map_map,
    Function.comp_def, ← explicitEdge_eq_rename, outcomes] using
    (ActualGame.explicitOutcomes_perm_outcomes S k g en).map (explicitEdge S k g)

end UniqueGamesTheorem.Decoder.TableKeysGame

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_TableKeysLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact affine-table keys for outer questions

The retained data has one entry at every original block position.  A full entry
contains the equation *occurrence ID*, a singleton entry contains the actual
variable ID, and the first component is the entire reduced affine intercept.
The common coefficient-normalization implementation below is independent of
every latent-gadget existence or inverse theorem.

The explicit binary slope cases justify its use for the rank-zero, rank-one,
and rank-two rule.  In particular, the third-position pullback adds the parity
intercept twice, so exact sharing preserves the intercept as well as the slopes.
-/

namespace UniqueGamesTheorem.Decoder.TableKeys

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open scoped BigOperators

universe u v w

section ExactKeys

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
variable {k : Nat}

abbrev Key (k : Nat) (Name Id R : Type) := ActualCanonical.Data k Name Id R

def key (occ : Fin k → Id) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (P : ActualHomogeneous.E k →ₗ[F2] R) : Key k Name Id R :=
  ActualCanonical.canonical occ names rhs P

variable [DecidableEq Name] [DecidableEq Id]

/-- The reduced table attached to visible data is independent of the compatible
full question used to realize it.  This is equality of the entire key. -/
noncomputable def projectedKey (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
    (Q : RawPrivateTable.SupportedV J names) (Y : RawPartnerTarget.RawPoint J →ₗ[F2] R) :
    Key k Name Id R :=
  key (RawPrivateTable.representative Q).1 names rhs
    (Y.comp (RawPrivateTable.projection J rhs (RawPrivateTable.representative Q).1
      (RawPrivateTable.representative Q).2))

end ExactKeys

end UniqueGamesTheorem.Decoder.TableKeys

end

section

namespace UniqueGamesTheorem.Decoder.TableKeys

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness

variable {Name Id R : Type} [AddCommGroup R] [Module F2 R]
variable {k : Nat}

/-- Read the shared homogeneous coordinate in the visible coordinate system. -/
def visibleTau (J : Finset (Fin k)) : RawPartnerTarget.RawPoint J →ₗ[F2] F2 :=
  LinearMap.proj none

end UniqueGamesTheorem.Decoder.TableKeys

end

section

/-!
The concrete observation maps of the projected-advice experiment.

The full hidden draw contains the equation occurrence IDs, singleton positions,
projection choices, public row map, and the two sampled tables. The observations
are precisely `(U,A,Tπ,AMπ)` and `(O,A,T,AM)`. The hidden matrix is absent from
both observation types. Changing its kernel-valued part preserves both inputs
and hence every deterministic witness or strategy chosen from those inputs.
-/

namespace UniqueGamesTheorem.Decoder.AdviceExperiment

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness

noncomputable section

variable (k : Nat) (Id K W R : Type)
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup W] [Module F2 W]
variable [AddCommGroup R] [Module F2 R]

/-- The first prover's entire information; no singleton-choice or private
matrix field is present. -/
structure FullAdvice where
  occurrences : Fin k → Id
  rowMap : K →ₗ[F2] R
  complement : ActualHomogeneous.E k →ₗ[F2] W
  rows : ActualHomogeneous.E k →ₗ[F2] R

/-- The actual draw before forgetting the hidden projection and private map. -/
structure Draw where
  singletons : Finset (Fin k)
  occurrences : Fin k → Id
  positions : Fin k → PartnerProjection.Slot
  rowMap : K →ₗ[F2] R
  hiddenMatrix : RawPartnerTarget.RawPoint singletons →ₗ[F2] K
  complement : RawPartnerTarget.RawPoint singletons →ₗ[F2] W

variable {k Id K W R}

variable {Name : Type} (names : Id → Fin 3 → Name)

/-- The second prover sees actual equation/variable tags, retaining ordered
block positions but omitting every hidden singleton occurrence ID. -/
structure ProjectedAdvice (J : Finset (Fin k)) where
  question : RawPrivateTable.SupportedV J names
  rowMap : K →ₗ[F2] R
  complement : RawPartnerTarget.RawPoint J →ₗ[F2] W
  rows : RawPartnerTarget.RawPoint J →ₗ[F2] R

variable (rhs : Id → F2)

def projection (d : Draw k Id K W R) :
    ActualHomogeneous.E k →ₗ[F2] RawPartnerTarget.RawPoint d.singletons :=
  RawPrivateTable.projection d.singletons rhs d.occurrences d.positions

def leftObservation (d : Draw k Id K W R) : FullAdvice k Id K W R where
  occurrences := d.occurrences
  rowMap := d.rowMap
  complement := d.complement.comp (projection rhs d)
  rows := (d.rowMap.comp d.hiddenMatrix).comp (projection rhs d)

def rightObservation (d : Draw k Id K W R) :
    (J : Finset (Fin k)) × ProjectedAdvice (K := K) (W := W) (R := R) names J :=
  ⟨d.singletons, {
    question := RawPrivateTable.supported d.singletons names d.occurrences d.positions
    rowMap := d.rowMap
    complement := d.complement
    rows := d.rowMap.comp d.hiddenMatrix }⟩

/-- The same full sampled table used in the unconditional variation comparison.
Its projection choices have not been supplied as extra compared coordinates. -/
def paddedMatrix (d : Draw k Id K W R) : ActualHomogeneous.E k →ₗ[F2] K :=
  d.hiddenMatrix.comp (projection rhs d)

end
end UniqueGamesTheorem.Decoder.AdviceExperiment

end

section

/-!
Restore actual orbit labels as a total function of the entire reduced key.
The arbitrary value at unrealized orbit bodies is used only to make this
function total; every table queried by the verifier and by the sparse
experiment is proved to be an actual realization.  Folding holds even for
the total extension, because the removed intercept is always restored.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysRestoration

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

section OrbitExtension

variable {Q T : Type} {s d : Nat}

def extendedLabel (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (body : Vector d × T) : Alphabet s :=
  if h : ∃ q, ActualOrbit.body can q = body then label ⟨body, h⟩ else 0

/-- Restore the full affine intercept after labeling the orbit body. -/
def restoredData (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (D : Ambient s d × T) : Alphabet s :=
  extendedLabel can label (D.1.2, D.2) + D.1.1

end OrbitExtension

/-- The actual verifier labeling, viewed as a function of exact affine keys. -/
def keyAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (D : TableKeys.Key k (Fin S.variables) (Fin S.occurrences) (Ambient s d)) : Alphabet s :=
  restoredData (TableKeysGame.canonical S k s d)
    (TableKeysGame.vertexLabel S k s d labeling) D

def projectedAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) : Alphabet s :=
  keyAnswer S k s d labeling
    (TableKeys.projectedKey J (ActualGame.names S) (ActualGame.rhs S) O Y)

end

end UniqueGamesTheorem.Decoder.TableKeysRestoration

end

section

/-!
The private row table obtained from an actual single-orbit labeling.  Its
parameters are only the visible question, public row map, visible row value,
and complement table.  Neither a hidden full question nor a selected affine
witness is supplied to its definition.  Affine target intercepts remain
explicit when the matrix is expressed in private kernel coordinates.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysPrivateRow

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ActualSource

noncomputable section

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

/-- The right player's actual private table, formed from visible row advice. -/
def rowAnswer (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker) : Alphabet s :=
  TableKeysRestoration.projectedAnswer S k s d labeling J Q
    ((AdviceFibers.assemble A (AdviceFibers.observedBase A rows) N).prod T)

/-- This intercept is determined once the visible base and affine witness are
fixed; it is not silently erased when decoding from a row fiber. -/
def targetIntercept (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (z : RawPartnerTarget.RawPoint J) (u : Alphabet s) : Alphabet s :=
  AdviceFibers.observedBase A rows z + u

end

end UniqueGamesTheorem.Decoder.TableKeysPrivateRow

end

section

/-!
# Decoding an actual transferred column slice

The point `Mstar` used to parametrize a transferred slice is distinct from the
canonical visible row base `observedBase A rows`.  The right strategy uses only
the latter.  Their kernel-valued difference appears solely in the analysis.
The exact quotient equivalence transports uniform slice agreement, including
the affine offset, to the conditional private-decoder theorem.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.TransferredDecoding

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open ActualSource
open PrivateFourier PrivateStrategy
open scoped BigOperators Classical

open UniqueGamesTheorem.Inverse

attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

section Rebase

variable {E K R : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup K] [Module F2 K] [AddCommGroup R] [Module F2 R]

/-- The slice origin, expressed relative to the fixed visible row base. -/
def privateOrigin (A : K →ₗ[F2] R) (rows : AdviceFibers.ObservedRow (E := E) A)
    (Mstar : E →ₗ[F2] K) (hstar : A.comp Mstar = rows.val) : E →ₗ[F2] A.ker :=
  AdviceFibers.kernelDifference A rows.val (AdviceFibers.observedBase A rows)
    (AdviceFibers.observedBase_property A rows) ⟨Mstar, hstar⟩

end Rebase

section ActualSlice

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

/-- A default actual projected answer depends only on the displayed positions. -/
def visibleFallback (J : Finset (Fin k)) : ActualAnswer (TableKeys.visibleTau J) :=
  ⟨Pi.single none 1, by simp [TableKeys.visibleTau]⟩

end ActualSlice

end UniqueGamesTheorem.Decoder.TransferredDecoding

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualAdviceStochasticBridgeLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

/-! Actual randomized point policies are transported locally into Boolean
answer kernels. Complete response tables are selected only after public advice
is fixed and before the remaining questions. No global deterministic policy
independent of public advice is asserted or needed for this upper bound. -/

/-! Section 5's clean bound for actual local linear-advice policies. The
sampling correspondence, private response conversion, weighted conditional
product law, and alphabet-independent repetition estimate are all invoked as
proved theorems. No sampler or repeated-game bound is an input hypothesis. -/

/-!
The actual finite advice law. Uniform independent hidden/complement maps induce
the exact uniform visible-map law, including for rank-deficient public maps.
The whole-table comparison retains an arbitrary common occurrence/public-data
law, so weighted occurrence sampling is not replaced by uniform IDs.
-/

namespace Decoder.AdviceLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open ConditionalIncidences RawPartnerTarget RawMapLaw
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Clean

attribute [local instance] Classical.propDecidable

section VisibleMap

variable {k : ℕ} {K W R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup W] [Module F2 W] [Fintype W]
  [AddCommGroup R] [Module F2 R] [Fintype R]

/-- The precise visible table `(T,A M)`, with the second component in its
actual attainable range. The argument order is complement, hidden matrix. -/
def visibleMap (A : K →ₗ[F2] R) {J : Finset (Fin k)}
    (T : RawPoint J →ₗ[F2] W) (M : RawPoint J →ₗ[F2] K) :
    RawPoint J →ₗ[F2] (W × A.range) :=
  T.prod (A.rangeRestrict.comp M)

def rawMapPairCoefficientsEquiv (J : Finset (Fin k)) :
    ((RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K)) ≃
      (RawSlot J → W × K) :=
  (Equiv.prodCongr (rawMapEquiv J W).symm (rawMapEquiv J K).symm).trans
    (Equiv.arrowProdEquivProdArrow (RawSlot J) (fun _ => W) (fun _ => K)).symm

variable {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

/-- Actual success starts with genuinely sampled hidden and complement maps.
The iid incidence law includes every slot choice, including unused choices at
full positions. Policies receive only their respective visible table. -/
def actualSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (A : K →ₗ[F2] R)
    (policy : ActualAdviceStochasticBridge.Policies k g (W × A.range))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      ((RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] W) ×
        (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] K))).expectation fun TM =>
      ActualAdviceStochasticBridge.fixedMapSuccess μ g policy
        (NativeExperiment.maskSet mask) (visibleMap A TM.1 TM.2)

end VisibleMap

section WholeTable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
  [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

def drawDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution ((Fin k → PaddedLaw.BlockDraw V) × V) where
  weight := PaddedLaw.drawWeights β k
  nonnegative dz := mul_nonneg
    ((SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).1 dz.1)
    (SparseLaw.uniformWeights_pos dz.2).le
  normalized := by
    rw [Fintype.sum_prod_type]
    simp only [PaddedLaw.drawWeights, ← Finset.mul_sum,
      (SparseLaw.uniformWeights_isProbability (α := V)).2, mul_one]
    exact (SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).2

def paddedDistribution (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ActualHomogeneous.E k →ₗ[F2] V) :=
  (drawDistribution β hβ hβ').pushforward (fun dz => PaddedLaw.paddedMap rhs dz.1 dz.2)

end WholeTable

section CommonLaw

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

/-- Keep the common outer datum while sampling its conditional table law. -/
def withKernel (μ : FiniteDistribution Ω) (p : Ω → FiniteDistribution Y) :
    FiniteDistribution (Ω × Y) where
  weight xy := μ.weight xy.1 * (p xy.1).weight xy.2
  nonnegative xy := mul_nonneg (μ.nonnegative _) ((p _).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact μ.normalized

end CommonLaw

section HiddenRows

variable {k : ℕ} {K R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup R] [Module F2 R] [Fintype R]

instance observedRowsFintype (J : Finset (Fin k)) (A : K →ₗ[F2] R) :
    Fintype (AdviceFibers.ObservedRow (E := RawPoint J) A) := Fintype.ofFinite _

end HiddenRows

section ProjectionSeeds

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]

/-- The actual two-stage sampler retains both its projection choices and its
uniform map on that projected target. Thus target advice is not forgotten. -/
abbrev ProjectionSeed (k : ℕ) (V : Type) [AddCommGroup V] [Module F2 V] :=
  Σ c : Fin k → PaddedLaw.ProjectionChoice,
    RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V

def projectionSeedDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ProjectionSeed k V) where
  weight s := PaddedLaw.choiceTupleWeight β s.1 * SparseLaw.uniformWeights _ s.2
  nonnegative s := mul_nonneg
    ((PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').1 s.1)
    (SparseLaw.uniformWeights_pos s.2).le
  normalized := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (SparseLaw.uniformWeights_isProbability).2, mul_one]
    exact (PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').2

def projectSeedMap (rhs : Fin k → Bool) (s : ProjectionSeed k V) :
    ActualHomogeneous.E k →ₗ[F2] V :=
  s.2.comp (rawProjection rhs (PaddedLaw.choiceMask s.1) (PaddedLaw.choiceSlots s.1))

end ProjectionSeeds

section ActualDraw

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

/-- Convert the actual two-stage seed into the full hidden experiment. The
second summand of the seed remains available for the target-side observation. -/
def seedToActualDraw (occ : Fin k → Id) (A : K →ₗ[F2] R)
    (s : ProjectionSeed k (K × W)) : AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask s.1
  occurrences := occ
  positions := PaddedLaw.choiceSlots s.1
  rowMap := A
  hiddenMatrix := (LinearMap.fst F2 K W).comp s.2
  complement := (LinearMap.snd F2 K W).comp s.2

end ActualDraw

section MaskSlots

def choiceDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution PaddedLaw.ProjectionChoice where
  weight := PaddedLaw.choiceWeight β
  nonnegative := (PaddedLaw.choiceWeight_isProbability β hβ hβ').1
  normalized := (PaddedLaw.choiceWeight_isProbability β hβ hβ').2

/-- Full positions discard their auxiliary slot; singleton positions retain it. -/
def maskSlotChoice (p : Bool × Fin 3) : PaddedLaw.ProjectionChoice :=
  if p.1 then some p.2 else none

def choicesOfMaskSlots {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    Fin k → PaddedLaw.ProjectionChoice :=
  fun j => maskSlotChoice (mask j, slots j)

end MaskSlots

/-- A finite hidden sample whose actual Draw is `seedToActualDraw`. -/
def fullSeedLaw {k : ℕ} {Id A V : Type} [Fintype Id] [Fintype A]
    [AddCommGroup V] [Module F2 V] [Fintype V]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :=
  (occurrences.product publicLaw).product (projectionSeedDistribution (k := k) (V := V) β hβ hβ')

def fullSeedPad {k : ℕ} {Id A V : Type} [AddCommGroup V] [Module F2 V]
    (rhs : Id → Bool) (s : ((Fin k → Id) × A) × ProjectionSeed k V) :
    ((Fin k → Id) × A) × (ActualHomogeneous.E k →ₗ[F2] V) :=
  (s.1, projectSeedMap (fun j => rhs (s.1.1 j)) s.2)

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

abbrev FullSeed (k : ℕ) (Id K W R : Type)
    [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
    [AddCommGroup R] [Module F2 R] :=
  ((Fin k → Id) × (K →ₗ[F2] R)) × ProjectionSeed k (K × W)

/-- Complete visible conditioning data: occurrences, public map, projection
choices, the entire complement map, and precisely the attainable rows. -/
abbrev CompleteData (k : ℕ) (Id K W R : Type)
    [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
    [AddCommGroup R] [Module F2 R] :=
  Σ ua : (Fin k → Id) × (K →ₗ[F2] R),
    Σ c : Fin k → PaddedLaw.ProjectionChoice,
      (RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] W) ×
        AdviceFibers.ObservedRow (E := RawPoint (PaddedLaw.choiceMask c)) ua.2

abbrev PrivateMap (d : CompleteData k Id K W R) :=
  RawPoint (PaddedLaw.choiceMask d.2.1) →ₗ[F2] d.1.2.ker

def targetObservationEquiv (J : Finset (Fin k)) (A : K →ₗ[F2] R) :
    (RawPoint J →ₗ[F2] (K × W)) ≃
      ((RawPoint J →ₗ[F2] W) × AdviceFibers.ObservedRow (E := RawPoint J) A) ×
        (RawPoint J →ₗ[F2] A.ker) :=
  (LinearMap.prodEquiv F2).toEquiv.symm |>.trans
    (Equiv.prodComm _ _) |>.trans
    (Equiv.prodCongr (Equiv.refl _) (AdviceFibers.observationEquiv A)) |>.trans
    (Equiv.prodAssoc _ _ _).symm

/-- A global bijection retains all actual visible data, with exactly one
uniform kernel-valued matrix left after conditioning. -/
def fullSeedCoordinatesEquiv :
    FullSeed k Id K W R ≃ Σ d : CompleteData k Id K W R, PrivateMap d :=
  ((Equiv.sigmaEquivProd ((Fin k → Id) × (K →ₗ[F2] R))
      (ProjectionSeed k (K × W))).symm.trans
    (Equiv.sigmaCongrRight fun (ua : (Fin k → Id) × (K →ₗ[F2] R)) =>
      Equiv.sigmaCongrRight fun c => targetObservationEquiv (PaddedLaw.choiceMask c) ua.2)).trans
    { toFun := fun p => ⟨⟨p.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩
      invFun := fun p => ⟨p.1.1, p.1.2.1, p.1.2.2, p.2⟩
      left_inv := fun p => by rcases p with ⟨ua, c, ⟨T, S⟩, N⟩; rfl
      right_inv := fun p => by rcases p with ⟨⟨ua, c, T, S⟩, N⟩; rfl }

def completeObserve (s : FullSeed k Id K W R) : CompleteData k Id K W R :=
  (fullSeedCoordinatesEquiv s).1

def completeAssemble (d : CompleteData k Id K W R) (N : PrivateMap d) :
    FullSeed k Id K W R :=
  fullSeedCoordinatesEquiv.symm ⟨d, N⟩

@[simp] theorem completeObserve_assemble (d : CompleteData k Id K W R)
    (N : PrivateMap d) : completeObserve (completeAssemble d N) = d :=
  congrArg Sigma.fst (fullSeedCoordinatesEquiv.apply_symm_apply ⟨d, N⟩)

/-- Exact equivalence for a fiber of the complete observation, not just the
marginal row observation. This is the input for finite conditioning. -/
def completeFiberEquiv (d : CompleteData k Id K W R) :
    PrivateMap d ≃ {s : FullSeed k Id K W R // completeObserve s = d} :=
  ((Equiv.subtypeEquiv fullSeedCoordinatesEquiv (fun _ => Iff.rfl)).trans
    (Equiv.sigmaSubtype d)).symm

@[simp] theorem completeFiberEquiv_val (d : CompleteData k Id K W R) (N : PrivateMap d) :
    (completeFiberEquiv d N).val = completeAssemble d N := rfl

/-- The actual Draw obtained from the complete-data fiber coordinates. -/
def completeDraw (d : CompleteData k Id K W R) (N : PrivateMap d) :
    AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask d.2.1
  occurrences := d.1.1
  positions := PaddedLaw.choiceSlots d.2.1
  rowMap := d.1.2
  hiddenMatrix := AdviceFibers.assemble d.1.2 (AdviceFibers.observedBase d.1.2 d.2.2.2) N
  complement := d.2.2.1

theorem completeDraw_rows (d : CompleteData k Id K W R) (N : PrivateMap d) :
    (completeDraw d N).rowMap.comp (completeDraw d N).hiddenMatrix = d.2.2.2.val := by
  exact (AdviceFibers.observed_assemble _ _ N).trans
    (AdviceFibers.observedBase_property _ _)

theorem completeDraw_left (rhs : Id → F2) (d : CompleteData k Id K W R)
    (N : PrivateMap d) :
    AdviceExperiment.leftObservation rhs (completeDraw d N) = {
      occurrences := d.1.1, rowMap := d.1.2,
      complement := d.2.2.1.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)),
      rows := d.2.2.2.val.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)) } := by
  simp only [AdviceExperiment.leftObservation, completeDraw_rows]
  rfl

variable [Fintype Id] [Fintype K] [Fintype W] [Fintype R] [Fintype (K →ₗ[F2] R)]

def completeWeight (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (d : CompleteData k Id K W R) : ℝ :=
  (occurrences.weight d.1.1 * publicLaw.weight d.1.2) *
    (PaddedLaw.choiceTupleWeight β d.2.1 *
      (1 / (Fintype.card (RawPoint (PaddedLaw.choiceMask d.2.1) →ₗ[F2] (K × W)) : ℝ)))

end Decoder.AdviceLaw

end UniqueGamesTheorem

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_ShortcodeInterfaceLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
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

abbrev Vector (n : ℕ) := Fin n → F2
abbrev Mat (ell m : ℕ) := Matrix (Fin ell) (Fin m) F2

def rankOne {ell m : ℕ} (a : Vector ell) (l : Vector m) : Mat ell m :=
  fun i j => a i * l j

def evaluate {ell m : ℕ} (M : Mat ell m) (z : Vector m) : Vector ell :=
  fun i => ∑ j, M i j * z j

@[simp] theorem evaluate_zero {ell m : ℕ} (M : Mat ell m) : evaluate M 0 = 0 := by
  ext i
  simp [evaluate]

@[simp] theorem rankOne_zero_left {ell m : ℕ} (l : Vector m) :
    rankOne (0 : Vector ell) l = 0 := by
  ext i j
  simp [rankOne]

@[simp] theorem rankOne_zero_right {ell m : ℕ} (a : Vector ell) :
    rankOne a (0 : Vector m) = 0 := by
  ext i j
  simp [rankOne]

/-- Both perturbation factors are independent uniform vectors, including zero.
The matrix is sampled independently as well. -/
def equalityAcceptance {ell m : ℕ} (f : Mat ell m → Vector ell) : ℝ :=
  𝔼 M, 𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0

/-- A description includes possibly dependent equations; the row and column
counts need not equal their ranks. -/
structure Slice (ell m : ℕ) where
  rows : ℕ
  columns : ℕ
  rowCoefficient : Fin rows → Vector ell
  rowValue : Fin rows → Vector m
  columnCoefficient : Fin columns → Vector m
  columnValue : Fin columns → Vector ell

def Slice.Contains {ell m : ℕ} (S : Slice ell m) (M : Mat ell m) : Prop :=
  (∀ i j, (∑ a, S.rowCoefficient i a * M a j) = S.rowValue i j) ∧
    ∀ i, evaluate M (S.columnCoefficient i) = S.columnValue i

def Slice.points {ell m : ℕ} (S : Slice ell m) : Finset (Mat ell m) :=
  Finset.univ.filter S.Contains

def Slice.affineAgreement {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) : ℝ :=
  S.points.expect fun M => if f M = evaluate M z + u then 1 else 0

def HasAffineSlice {ell m : ℕ} (f : Mat ell m → Vector ell) (α : ℝ) (r : ℕ) : Prop :=
  ∃ S : Slice ell m, S.rows ≤ r ∧ S.columns ≤ r ∧ S.points.Nonempty ∧
    ∃ z : Vector m, ∃ u : Vector ell, α ≤ S.affineAgreement f z u

end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-!
The exact sampling bridge from the vector factors in the shortcode test
to actual KMS Grassmann vertices. Every nonzero vector pair is sent to the
matrix `M + rankOne a l`, and this is a bijection onto the chart neighbors.
-/

namespace UniqueGamesTheorem.Inverse.MatrixChart

open Matrix
open Shortcode (Vector Mat rankOne)

variable {ell m : ℕ}

@[simp] theorem dotFunctional_zero_binary :
    dotFunctional (0 : Vector ell) = 0 := by
  apply LinearMap.ext
  intro x
  change (0 : Vector ell) ⬝ᵥ x = 0
  simp

theorem dotFunctional_ne_zero {a : Vector ell} (ha : a ≠ 0) :
    dotFunctional a ≠ 0 := by
  intro h
  exact ha (dotFunctional_injective (h.trans dotFunctional_zero_binary.symm))

/-- The shortcode outer product is precisely the rank-one chart map. -/
theorem vecMulLinear_rankOne (a : Vector ell) (l : Vector m) :
    (rankOne a l).vecMulLinear = (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* Matrix.vecMulVec a l = (a ⬝ᵥ x) • l
  rw [Matrix.vecMul_vecMulVec, dotProduct_comm x a]

/-- This is the exact perturbation, including its functional/vector order. -/
theorem vecMulLinear_add_rankOne (M : Mat ell m) (a : Vector ell) (l : Vector m) :
    (M + rankOne a l).vecMulLinear = M.vecMulLinear + (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* (M + rankOne a l) = M.vecMulLinear x +
    ((dotFunctional a).smulRight l) x
  rw [Matrix.vecMul_add]
  exact congrArg (fun y => M.vecMulLinear x + y)
    (LinearMap.congr_fun (vecMulLinear_rankOne a l) x)

theorem adjacent_matrixVertex_add_rankOne (M : Mat ell m)
    (a : Vector ell) (l : Vector m) (ha : a ≠ 0) (hl : l ≠ 0) :
    KMS.Adjacent (matrixVertex M) (matrixVertex (M + rankOne a l)) := by
  apply (adjacent_matrixVertex_iff M (M + rankOne a l)).mpr
  apply (adjacent_iff_rank_one M.vecMulLinear (M + rankOne a l).vecMulLinear).mp
  rw [vecMulLinear_add_rankOne]
  exact adjacent_rank_one_step M.vecMulLinear (dotFunctional a) l
    (dotFunctional_ne_zero ha) hl

abbrev NonzeroVectorFactors (ell m : ℕ) :=
  {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0}

/-- Actual Grassmann vertices adjacent to `matrixVertex M` and remaining
inside the finite matrix chart. -/
abbrev MatrixVertexChartNeighbors (M : Mat ell m) :=
  {L : KMS.Vertex (ell + m) ell //
    KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m}

def vectorFactorMatrixNeighbor (M : Mat ell m) (p : NonzeroVectorFactors ell m) :
    MatrixVertexChartNeighbors M :=
  ⟨matrixVertex (M + rankOne p.1.val p.2.val),
    adjacent_matrixVertex_add_rankOne M p.1.val p.2.val p.1.property p.2.property,
    (mem_matrixChart _).mpr ⟨M + rankOne p.1.val p.2.val, rfl⟩⟩

theorem vectorFactorMatrixNeighbor_injective (M : Mat ell m) :
    Function.Injective (vectorFactorMatrixNeighbor M) := by
  intro p q h
  have hM : M + rankOne p.1.val p.2.val = M + rankOne q.1.val q.2.val :=
    matrixVertex_injective (congrArg Subtype.val h)
  have hrank := congrArg Matrix.vecMulLinear (add_left_cancel hM)
  rw [vecMulLinear_rankOne, vecMulLinear_rankOne] at hrank
  obtain ⟨ha, hl⟩ := binary_smulRight_unique (dotFunctional_ne_zero p.1.property)
    p.2.property hrank
  exact Prod.ext (Subtype.ext (dotFunctional_injective ha)) (Subtype.ext hl)

theorem vectorFactorMatrixNeighbor_surjective (M : Mat ell m) :
    Function.Surjective (vectorFactorMatrixNeighbor M) := by
  intro L
  obtain ⟨N, hN⟩ := (mem_matrixChart L.val).mp L.property.2
  have hMN : KMS.Adjacent (matrixVertex M) (matrixVertex N) := by
    rw [hN]
    exact L.property.1
  have hNM : KMS.Adjacent (matrixVertex N) (matrixVertex M) :=
    ⟨hMN.1.symm, by rw [inf_comm]; exact hMN.2⟩
  obtain ⟨a, l, ha, hl, hfactor⟩ := exists_smulRight_of_rank_one
    (N.vecMulLinear - M.vecMulLinear) ((adjacent_matrixVertex_iff N M).mp hNM)
  obtain ⟨v, hv⟩ := dotFunctional_surjective a
  have hv0 : v ≠ 0 := by
    intro h
    apply ha
    rw [← hv, h, dotFunctional_zero_binary]
  have hmatrix : M + rankOne v l = N := by
    apply (LinearMap.toMatrixRight' (R := ZMod 2)).symm.injective
    change (M + rankOne v l).vecMulLinear = N.vecMulLinear
    rw [vecMulLinear_add_rankOne, hv]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hfactor).symm
  refine ⟨(⟨v, hv0⟩, ⟨l, hl⟩), ?_⟩
  apply Subtype.ext
  change matrixVertex (M + rankOne v l) = L.val
  rw [hmatrix]
  exact hN

/-- Uniform independent nonzero vector factors induce exactly uniform
neighbors of the actual Grassmann vertex within the matrix chart. -/
noncomputable def vectorFactorsEquivMatrixVertexChartNeighbors (M : Mat ell m) :
    NonzeroVectorFactors ell m ≃ MatrixVertexChartNeighbors M :=
  Equiv.ofBijective (vectorFactorMatrixNeighbor M)
    ⟨vectorFactorMatrixNeighbor_injective M, vectorFactorMatrixNeighbor_surjective M⟩

@[simp] theorem vectorFactorsEquivMatrixVertexChartNeighbors_apply (M : Mat ell m)
    (p : NonzeroVectorFactors ell m) :
    (vectorFactorsEquivMatrixVertexChartNeighbors M p).val =
      matrixVertex (M + rankOne p.1.val p.2.val) := rfl

end UniqueGamesTheorem.Inverse.MatrixChart

end

section

/-!
The size bound for simultaneous row/column slices.
Starting at any point of a nonempty slice, maps from the quotient by its column
span into the common row kernel give distinct points of that same affine slice.
Rank-nullity gives the dimension lower bound even when equations are dependent.
This argument uses only finite-dimensional linear algebra.
-/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Matrix

namespace Slice

variable {ell m : ℕ}

/-- The simultaneous row functionals, allowing dependent and zero rows. -/
def rowMap (S : Slice ell m) : Vector ell →ₗ[F2] Vector S.rows :=
  Matrix.mulVecLin S.rowCoefficient

/-- Column specifications fix the matrix on this entire subspace. -/
def columnSpan (S : Slice ell m) : Submodule F2 (Vector m) :=
  Submodule.span F2 (Set.range S.columnCoefficient)

/-- Free directions of a row/column slice, intrinsically as quotient maps. -/
abbrev Directions (S : Slice ell m) :=
  (Vector m ⧸ S.columnSpan) →ₗ[F2] S.rowMap.ker

def directionMap (S : Slice ell m) (N : S.Directions) :
    Vector m →ₗ[F2] Vector ell :=
  S.rowMap.ker.subtype.comp (N.comp S.columnSpan.mkQ)

def directionMatrix (S : Slice ell m) (N : S.Directions) : Mat ell m :=
  LinearMap.toMatrix' (S.directionMap N)

theorem directionMatrix_injective (S : Slice ell m) :
    Function.Injective S.directionMatrix := by
  intro N P h
  have hmap : S.directionMap N = S.directionMap P :=
    LinearMap.toMatrix'.injective h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := S.columnSpan.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : Vector m →ₗ[F2] Vector ell => f v) hmap

theorem directionMatrix_row (S : Slice ell m) (N : S.Directions)
    (i : Fin S.rows) (j : Fin m) :
    (∑ a, S.rowCoefficient i a * S.directionMatrix N a j) = 0 := by
  have h := (N (S.columnSpan.mkQ (Pi.single j 1))).property
  have hi := congrFun h i
  change (∑ a, S.rowCoefficient i a *
    (N (S.columnSpan.mkQ (Pi.single j 1)) : Vector ell) a) = 0 at hi
  exact hi

theorem directionMatrix_column (S : Slice ell m) (N : S.Directions)
    (i : Fin S.columns) :
    evaluate (S.directionMatrix N) (S.columnCoefficient i) = 0 := by
  have hq : S.columnSpan.mkQ (S.columnCoefficient i) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero S.columnSpan).mpr
    exact Submodule.subset_span ⟨i, rfl⟩
  change (S.directionMatrix N) *ᵥ (S.columnCoefficient i) = 0
  rw [directionMatrix, LinearMap.toMatrix'_mulVec]
  simp [directionMap, hq]

theorem contains_add_direction (S : Slice ell m) (M : Mat ell m)
    (hM : S.Contains M) (N : S.Directions) :
    S.Contains (M + S.directionMatrix N) := by
  constructor
  · intro i j
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hM.1 i j, S.directionMatrix_row N i j, add_zero]
  · intro i
    have hd := S.directionMatrix_column N i
    change evaluate (M + S.directionMatrix N) (S.columnCoefficient i) = _
    have he : evaluate (M + S.directionMatrix N) (S.columnCoefficient i) =
        evaluate M (S.columnCoefficient i) +
          evaluate (S.directionMatrix N) (S.columnCoefficient i) := by
      ext a
      simp [evaluate, add_mul, Finset.sum_add_distrib]
    rw [he, hM.2 i, hd, add_zero]

def directionEmbedding (S : Slice ell m) (M : Mat ell m) (hM : S.Contains M) :
    S.Directions ↪ S.points where
  toFun N := ⟨M + S.directionMatrix N, by
    simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.contains_add_direction M hM N⟩
  inj' := by
    intro N P h
    apply S.directionMatrix_injective
    exact add_left_cancel (congrArg Subtype.val h)

end Slice
end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-! Exact connection between the finite-array shortcode slices and the
linear-map slices used by affine witness normalization. -/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical Matrix

namespace Slice

variable {ell m : ℕ}

theorem row_equations_iff (S : Slice ell m) (M : Mat ell m) :
    (∀ i j, (∑ a, S.rowCoefficient i a * M a j) = S.rowValue i j) ↔
      S.rowMap.comp (Matrix.toLin' M) = Matrix.toLin' S.rowValue := by
  let A : Matrix (Fin S.rows) (Fin ell) F2 := S.rowCoefficient
  let B : Matrix (Fin S.rows) (Fin m) F2 := S.rowValue
  change (∀ i j, (∑ a, A i a * M a j) = B i j) ↔
    (Matrix.toLin' A).comp (Matrix.toLin' M) = Matrix.toLin' B
  constructor
  · intro h
    have hm : A * M = B := by
      ext i j
      exact h i j
    rw [← Matrix.toLin'_mul, hm]
  · intro h
    have hm : A * M = B := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul]
      exact h
    intro i j
    exact congrFun (congrFun hm i) j

/-- This is an equivalence of the actual equations, not merely a cardinality
comparison or a homogeneous approximation of the affine slice. -/
theorem contains_iff_inSlice (S : Slice ell m) (M₀ : Mat ell m)
    (hM₀ : S.Contains M₀) (M : Mat ell m) :
    S.Contains M ↔
      AffineWitness.InSlice S.rowMap S.columnSpan
        (Matrix.toLin' M₀) (Matrix.toLin' M) := by
  have hrow₀ := (S.row_equations_iff M₀).mp hM₀.1
  have hcol₀ : ∀ i, Matrix.toLin' M₀ (S.columnCoefficient i) =
      S.columnValue i := hM₀.2
  have heq := AffineWitness.explicit_slice_iff S.rowMap
    (Matrix.toLin' S.rowValue) S.columnCoefficient S.columnValue
    (Matrix.toLin' M₀) (Matrix.toLin' M) hrow₀ hcol₀
  constructor
  · intro hM
    exact heq.mp ⟨(S.row_equations_iff M).mp hM.1, hM.2⟩
  · intro hM
    have h := heq.mpr hM
    exact ⟨(S.row_equations_iff M).mpr h.1, h.2⟩

/-- Exact finite sample-space equivalence between the matrix representation
and the linear-map representation of a nonempty affine slice. -/
def linearSliceEquiv (S : Slice ell m) (M₀ : Mat ell m)
    (hM₀ : S.Contains M₀) :
    S.points ≃ AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀) where
  toFun M := ⟨Matrix.toLin' M.val,
    (S.contains_iff_inSlice M₀ hM₀ M.val).mp (by
      simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using M.property)⟩
  invFun N := ⟨LinearMap.toMatrix' N.val, by
    simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]
    apply (S.contains_iff_inSlice M₀ hM₀ _).mpr
    simpa only [Matrix.toLin'_toMatrix'] using N.property⟩
  left_inv M := by
    apply Subtype.ext
    exact LinearMap.toMatrix'_toLin' M.val
  right_inv N := by
    apply Subtype.ext
    exact Matrix.toLin'_toMatrix' N.val

/-- Pointwise preservation on the genuine slice preserves its exact uniform
affine agreement, including the empty-slice convention. -/
theorem affineAgreement_eq_of_target_eq (S : Slice ell m)
    (f : Mat ell m → Vector ell) (z z' : Vector m) (u u' : Vector ell)
    (htarget : ∀ M, S.Contains M → evaluate M z' + u' = evaluate M z + u) :
    S.affineAgreement f z' u' = S.affineAgreement f z u := by
  unfold affineAgreement
  apply Finset.expect_congr rfl
  intro M hM
  have hcontains : S.Contains M := by
    simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using hM
  rw [htarget M hcontains]

theorem affineAgreement_eq_of_linear_target_eq (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z z' : Vector m) (u u' : Vector ell)
    (htarget : ∀ M, AffineWitness.InSlice S.rowMap S.columnSpan
      (Matrix.toLin' M₀) M → M z' + u' = M z + u) :
    S.affineAgreement f z' u' = S.affineAgreement f z u := by
  apply S.affineAgreement_eq_of_target_eq f z z' u u'
  intro M hM
  exact htarget (Matrix.toLin' M) ((S.contains_iff_inSlice M₀ hM₀ M).mp hM)

end Slice
end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-! First-bit normalization in the actual finite-array shortcode API. The
sample space, event count, affine intercept, and folding law are transported
exactly; no inverse result is assumed by the representation bridge. -/

namespace UniqueGamesTheorem.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

variable {ell m : ℕ}

/-- The coordinate row of a binary linear functional. -/
def functionalRow (e : Vector m →ₗ[F2] F2) : Vector m :=
  fun j => e (Pi.single j 1)

theorem toMatrix_shift (e : Vector m →ₗ[F2] F2) (h : Vector ell)
    (M : Mat ell m) :
    LinearMap.toMatrix' (AffineWitness.shift e h (Matrix.toLin' M)) =
      M + rankOne h (functionalRow e) := by
  rw [AffineWitness.shift, map_add, LinearMap.toMatrix'_toLin']
  congr 1
  ext i j
  simp only [LinearMap.toMatrix'_apply, LinearMap.smulRight_apply,
    Pi.smul_apply, smul_eq_mul, rankOne, functionalRow, mul_comm]

namespace Slice

/-- Exact density identity on the complete nonempty affine slice, with no
lost conditioning factor in the change from matrices to linear maps. -/
theorem affineAgreement_eq_linear_ratio (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) :
    S.affineAgreement f z u =
      (Nat.card {N : AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀) //
        f (LinearMap.toMatrix' N.val) = N.val z + u} : ℝ) /
      (Nat.card (AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀)) : ℝ) := by
  unfold affineAgreement
  apply finset_expect_indicator_eq_card_ratio_of_equiv S.points
    (fun M => f M = evaluate M z + u) (S.linearSliceEquiv M₀ hM₀)
    (fun N => f (LinearMap.toMatrix' N.val) = N.val z + u)
  intro M
  change (f M.val = evaluate M.val z + u) ↔
    (f (LinearMap.toMatrix' (Matrix.toLin' M.val)) = Matrix.toLin' M.val z + u)
  rw [LinearMap.toMatrix'_toLin']
  rfl

/-- First-bit normalization for the exact selected shortcode slice.
The original affine agreement is preserved, not merely bounded below. -/
theorem first_bit_normalization (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (e : Vector m →ₗ[F2] F2)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell)
    (hfold : ∀ (h : S.rowMap.ker) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (α : ℝ) (hα : 0 < α) (hgood : α / 2 ≤ S.affineAgreement f z u)
    (hsmall : 1 / (2 : ℝ) ^ (ell - S.rows) < α / 8) :
    ∃ z' : Vector m, ∃ u' : Vector ell, e z' = 1 ∧
      S.affineAgreement f z' u' = S.affineAgreement f z u ∧
      ∀ M, S.Contains M → evaluate M z' + u' = evaluate M z + u := by
  let F : (Vector m →ₗ[F2] Vector ell) → Vector ell :=
    fun N => f (LinearMap.toMatrix' N)
  have hfold' : ∀ (h : S.rowMap.ker) N,
      F (AffineWitness.shift e h N) = F N + h := by
    intro h N
    have hs : LinearMap.toMatrix' (AffineWitness.shift e h N) =
        LinearMap.toMatrix' N + rankOne h (functionalRow e) := by
      simpa only [Matrix.toLin'_toMatrix'] using toMatrix_shift e h (LinearMap.toMatrix' N)
    exact (congrArg f hs).trans (hfold h (LinearMap.toMatrix' N))
  have hgood' := hgood
  rw [S.affineAgreement_eq_linear_ratio M₀ hM₀ f z u] at hgood'
  obtain ⟨z', u', he, ht⟩ := AffineWitness.first_bit_witness e S.rowMap S.columnSpan
    (Matrix.toLin' M₀) z u F hfold' α hα hgood' hsmall
  refine ⟨z', u', he, S.affineAgreement_eq_of_linear_target_eq M₀ hM₀ f z z' u u' ht, ?_⟩
  intro M hM
  exact ht (Matrix.toLin' M) ((S.contains_iff_inSlice M₀ hM₀ M).mp hM)

end Slice
end
end UniqueGamesTheorem.Inverse.Shortcode

end

section

/-!
Fixed-length descriptions for the row-erasure union bound. Row and column
equation lists are padded with zero equations. Targets retain both the linear
coefficient and the affine intercept. Thus the finite description count is
exactly `2^((2r+1)(ell+m))`, including descriptions with empty solution sets.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureDescriptions

open UniqueGamesTheorem.Inverse.Shortcode
open scoped BigOperators

noncomputable section

/-- A row map is represented by all its binary matrix coefficients. -/
abbrev RowMap (ell r : ℕ) := Fin r → Vector ell

/-- Ordered padded row coefficients, row values, column coefficients, column
values, affine coefficient, and affine intercept. Redundant descriptions are
intentional: counting descriptions provides an upper bound on distinct slices. -/
abbrev Description (ell m r : ℕ) :=
  (Fin r → Vector ell) × (Fin r → Vector m) ×
    (Fin r → Vector m) × (Fin r → Vector ell) × Vector m × Vector ell

def Description.toSlice {ell m r : ℕ} (d : Description ell m r) : Slice ell m where
  rows := r
  columns := r
  rowCoefficient := d.1
  rowValue := d.2.1
  columnCoefficient := d.2.2.1
  columnValue := d.2.2.2.1

def Description.coefficient {ell m r : ℕ} (d : Description ell m r) : Vector m :=
  d.2.2.2.2.1

def Description.intercept {ell m r : ℕ} (d : Description ell m r) : Vector ell :=
  d.2.2.2.2.2

def padSlice {ell m : ℕ} (S : Slice ell m) (r : ℕ) : Slice ell m where
  rows := r
  columns := r
  rowCoefficient := padZero S.rowCoefficient
  rowValue := padZero S.rowValue
  columnCoefficient := padZero S.columnCoefficient
  columnValue := padZero S.columnValue

def describe {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (padZero S.rowCoefficient, padZero S.rowValue,
    padZero S.columnCoefficient, padZero S.columnValue, z, u)

@[simp] theorem describe_toSlice {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) :
    (describe (r := r) S z u).toSlice = padSlice S r := rfl

@[simp] theorem describe_coefficient {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : (describe (r := r) S z u).coefficient = z := rfl

@[simp] theorem describe_intercept {ell m r : ℕ} (S : Slice ell m)
    (z : Vector m) (u : Vector ell) : (describe (r := r) S z u).intercept = u := rfl

end
end UniqueGamesTheorem.Inverse.RowErasureDescriptions

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_RowErasureMatrixLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions
open scoped BigOperators Classical

noncomputable section

def rowAdvice {ell m r : ℕ} (A : RowMap ell r) (M : Mat ell m) : Mat r m :=
  fun i j => ∑ a, A i a * M a j

def family (ell m r : ℕ) :
    SliceFamily (Mat ell m) (Vector ell) (RowMap ell r) (Mat r m)
      (Description ell m r) where
  advice := rowAdvice
  rowMap := fun d => d.1
  rowValue := fun d => d.2.1
  points := fun d => d.toSlice.points
  target := fun d M => evaluate M d.coefficient + d.intercept
  points_row := by
    intro d M hM
    have h : d.toSlice.Contains M := (Finset.mem_filter.mp hM).2
    funext i j
    exact h.1 i j

theorem family_agreement {ell m r : ℕ} (d : Description ell m r)
    (f : Mat ell m → Vector ell) :
    (family ell m r).agreement f d =
      d.toSlice.affineAgreement f d.coefficient d.intercept := by
  unfold SliceFamily.agreement Slice.affineAgreement
  apply Finset.expect_congr rfl
  intro M _
  change indicator (f M = evaluate M d.coefficient + d.intercept) = _
  by_cases h : f M = evaluate M d.coefficient + d.intercept
  · simp [indicator, h]
  · simp [indicator, h]

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

section

/-!
Visible selection of a row-erasure witness. The selected description depends
only on the fixed table function, the row map, and the observed row value.
The full sampled matrix enters only the later event testing its membership in
the already selected slice. Classical choice fixes one witness once and for all;
proof irrelevance makes the choice independent of the goodness proof.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure

noncomputable section

variable {X Y A S D : Type*}

theorem SliceFamily.selectedDescription_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.selectedDescription f α a s = some (F.chosenDescription f α a s hgood) := by
  simp only [SliceFamily.selectedDescription, dite_eq_left hgood]

theorem SliceFamily.selectedEvent_iff_of_advice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) (hx : F.advice a x = s) :
    F.selectedEvent f α a x ↔ x ∈ F.points (F.chosenDescription f α a s hgood) := by
  unfold SliceFamily.selectedEvent
  rw [hx, F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hmem⟩
    have he := Option.some.inj hd
    simpa only [he] using hmem
  · intro hmem
    exact ⟨_, rfl, hmem⟩

end
end UniqueGamesTheorem.Inverse.RowErasure

end

section

/-!
Normalize the affine target chosen from visible row advice. The selected row
and column equations are unchanged. Only the target coefficient and intercept
are replaced, with exact target equality on the entire selected slice.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureDescriptions

open UniqueGamesTheorem.Inverse.Shortcode

/-- Replace the affine target while retaining all row and column data. -/
def Description.withTarget {ell m r : ℕ} (d : Description ell m r)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (d.1, d.2.1, d.2.2.1, d.2.2.2.1, z, u)

@[simp] theorem Description.withTarget_toSlice {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).toSlice = d.toSlice := rfl

@[simp] theorem Description.withTarget_coefficient {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).coefficient = z := rfl

@[simp] theorem Description.withTarget_intercept {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).intercept = u := rfl

end UniqueGamesTheorem.Inverse.RowErasureDescriptions

namespace UniqueGamesTheorem.Inverse.RowErasureMatrix

open UniqueGamesTheorem.Inverse.Shortcode
open UniqueGamesTheorem.Inverse.RowErasure
open UniqueGamesTheorem.Inverse.RowErasureDescriptions

noncomputable section

variable {ell m r : ℕ}

/-- Normalization of the already chosen description. The sampled matrix is
absent from the selector's inputs; pointwise target equality holds afterward
for every matrix in the selected slice. -/
theorem exists_normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    ∃ d : Description ell m r,
      (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M := by
  classical
  let d₀ := (family ell m r).chosenDescription f α A S hgood
  obtain ⟨hrow, hvalue, hnonempty, hagree⟩ :=
    (family ell m r).chosenDescription_spec f α A S hgood
  obtain ⟨M₀, hM₀⟩ := hnonempty
  have hcontains : d₀.toSlice.Contains M₀ := by
    exact (Finset.mem_filter.mp hM₀).2
  have hagree' : α / 2 ≤ d₀.toSlice.affineAgreement f d₀.coefficient d₀.intercept := by
    exact (family_agreement d₀ f) ▸ hagree
  obtain ⟨z, u, hfirst, heq, htarget⟩ :=
    d₀.toSlice.first_bit_normalization M₀ hcontains e f d₀.coefficient d₀.intercept
      (fun h M => hfold h M) α hα hagree' hsmall
  have heq' : (family ell m r).agreement f (d₀.withTarget z u) =
      (family ell m r).agreement f d₀ := by
    rw [family_agreement, family_agreement]
    exact heq
  refine ⟨d₀.withTarget z u, hrow, hvalue, ⟨M₀, hM₀⟩, ?_, hfirst, rfl, heq', ?_⟩
  · exact heq'.symm ▸ hagree
  · intro M hM
    exact htarget M (Finset.mem_filter.mp hM).2

/-- A fixed normalized witness determined by the visible table and row advice.
All remaining inputs are the fixed normalization functional and proofs. -/
def normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    Description ell m r :=
  Classical.choose (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

theorem normalizedChosenDescription_spec
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    let d := normalizedChosenDescription f α A S hgood e hfold hα hsmall
    (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M :=
  Classical.choose_spec
    (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

end
end UniqueGamesTheorem.Inverse.RowErasureMatrix

end

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

theorem difference_row_zero (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.rowMap.comp (Matrix.toLin' (M - M₀)) = 0 := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have hrow : LinearMap.toMatrix' S.rowMap = S.rowCoefficient :=
    LinearMap.toMatrix'_toLin' S.rowCoefficient
  rw [hrow]
  ext i j
  change (∑ a, S.rowCoefficient i a * (M - M₀) a j) = 0
  simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hM.1 i j, h₀.1 i j, sub_self]

theorem difference_range_le (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    LinearMap.range (Matrix.toLin' (M - M₀)) ≤ S.rowMap.ker := by
  rintro _ ⟨v, rfl⟩
  have h := LinearMap.congr_fun (S.difference_row_zero hM h₀) v
  exact h

theorem difference_vanishes_columns (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.columnSpan ≤ LinearMap.ker (Matrix.toLin' (M - M₀)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change Matrix.toLin' (M - M₀) (S.columnCoefficient i) = 0
  have he : Matrix.toLin' (M - M₀) (S.columnCoefficient i) =
      evaluate M (S.columnCoefficient i) - evaluate M₀ (S.columnCoefficient i) := by
    rw [map_sub, LinearMap.sub_apply]
    rfl
  rw [he, hM.2 i, h₀.2 i, sub_self]

/-- Every actual slice point differs from the base by a unique quotient map. -/
theorem directionEmbedding_surjective (S : Slice ell m)
    (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    Function.Surjective (S.directionEmbedding M₀ h₀) := by
  intro M
  have hM : S.Contains M.val := by
    simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using M.property
  obtain ⟨N, hN⟩ :=
    RowErasureSliceQuotient.exists_direction_of_row_and_column
      S.rowMap S.columnSpan (Matrix.toLin' (M.val - M₀))
      (S.difference_vanishes_columns hM h₀) (S.difference_range_le hM h₀)
  have hdir : S.directionMap N = Matrix.toLin' (M.val - M₀) := hN
  have hmat : S.directionMatrix N = M.val - M₀ := by
    unfold directionMatrix
    rw [hdir, LinearMap.toMatrix'_toLin']
  refine ⟨N, ?_⟩
  apply Subtype.ext
  change M₀ + S.directionMatrix N = M.val
  rw [hmat]
  abel

/-- The concrete simultaneous slice is exactly an affine copy of
`Hom(domain / columnSpan, commonRowKernel)`. -/
def directionEquiv (S : Slice ell m) (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    S.Directions ≃ S.points :=
  Equiv.ofBijective (S.directionEmbedding M₀ h₀)
    ⟨(S.directionEmbedding M₀ h₀).injective, S.directionEmbedding_surjective M₀ h₀⟩

@[simp] theorem directionEquiv_val (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) (N : S.Directions) :
    (S.directionEquiv M₀ h₀ N).val = M₀ + S.directionMatrix N := rfl

end
end UniqueGamesTheorem.Inverse.Shortcode.Slice

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_MatrixCoordinates
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

def domainCoordinates (k : ℕ) :
    ActualHomogeneous.E k ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [ActualHomogeneous.finrank_E, Module.finrank_fin_fun])

def changeDomain {D E K : Type*} [AddCommGroup D] [Module F2 D]
    [AddCommGroup E] [Module F2 E] [AddCommGroup K] [Module F2 K]
    (e : D ≃ₗ[F2] E) : (D →ₗ[F2] K) ≃ₗ[F2] (E →ₗ[F2] K) where
  toFun M := M.comp e.symm.toLinearMap
  invFun M := M.comp e.toLinearMap
  left_inv M := by ext x; simp
  right_inv M := by ext x; simp
  map_add' M N := by ext x; rfl
  map_smul' c M := by ext x; rfl

def mapEquiv (k ell : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) ≃ₗ[F2]
      Inverse.Shortcode.Mat ell (1 + 2 * k) :=
  (changeDomain (domainCoordinates k)).trans LinearMap.toMatrix'

@[simp] theorem mapEquiv_apply (k ell : ℕ)
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k ell M = LinearMap.toMatrix' (M.comp (domainCoordinates k).symm.toLinearMap) :=
  rfl

@[simp] theorem mapEquiv_symm_apply (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) :
    (mapEquiv k ell).symm M = (Matrix.toLin' M).comp (domainCoordinates k).toLinearMap :=
  rfl

def functionalEquiv (k : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] F2) ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  (changeDomain (domainCoordinates k)).trans ((Pi.basisFun F2 (Fin (1 + 2 * k))).constr F2).symm

@[simp] theorem functionalEquiv_apply (k : ℕ)
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (j : Fin (1 + 2 * k)) :
    functionalEquiv k l j = l ((domainCoordinates k).symm (Pi.single j 1)) := by
  simp [functionalEquiv, changeDomain, Module.Basis.constr_symm_apply, Pi.basisFun_apply]

theorem mapEquiv_rankOne (k ell : ℕ) (l : ActualHomogeneous.E k →ₗ[F2] F2)
    (a : Fin ell → F2) :
    mapEquiv k ell (l.smulRight a) = Inverse.Shortcode.rankOne a (functionalEquiv k l) := by
  ext i j
  simp [Inverse.Shortcode.rankOne, mul_comm]

theorem mapEquiv_symm_add_rankOne (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k))
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (a : Fin ell → F2) :
    (mapEquiv k ell).symm (M + Inverse.Shortcode.rankOne a (functionalEquiv k l)) =
      (mapEquiv k ell).symm M + l.smulRight a := by
  apply (mapEquiv k ell).injective
  rw [LinearEquiv.apply_symm_apply, map_add, LinearEquiv.apply_symm_apply, mapEquiv_rankOne]

def coordinateTau (k : ℕ) : (Fin (1 + 2 * k) → F2) →ₗ[F2] F2 :=
  ActualHomogeneous.tau.comp (domainCoordinates k).symm.toLinearMap

theorem functionalEquiv_tau (k : ℕ) :
    functionalEquiv k ActualHomogeneous.tau =
      Inverse.Shortcode.functionalRow (coordinateTau k) := by
  ext j
  rw [functionalEquiv_apply]
  rfl

theorem mapEquiv_symm_firstBit_shift (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) (a : Fin ell → F2) :
    (mapEquiv k ell).symm
        (M + Inverse.Shortcode.rankOne a (Inverse.Shortcode.functionalRow (coordinateTau k))) =
      (mapEquiv k ell).symm M + ActualHomogeneous.tau.smulRight a := by
  rw [← functionalEquiv_tau]
  exact mapEquiv_symm_add_rankOne k ell M ActualHomogeneous.tau a

theorem mapEquiv_rowAdvice (k ell r : ℕ)
    (A : (Fin ell → F2) →ₗ[F2] (Fin r → F2))
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k r (A.comp M) =
      Inverse.RowErasureMatrix.rowAdvice (LinearMap.toMatrix' A) (mapEquiv k ell M) := by
  change LinearMap.toMatrix' (A.comp (M.comp (domainCoordinates k).symm.toLinearMap)) = _
  rw [LinearMap.toMatrix'_comp]
  rfl

end
end UniqueGamesTheorem.Decoder.MatrixCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAffineRestrictionPresentationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An affine map family presented by a surjective input map and an injective
output map is precisely the quotient-parameter family with vanishing subspace
the input kernel and target subspace the output range. Both its uniform law
and its dimension budget agree exactly with the intrinsic restriction data.
-/

namespace UniqueGamesTheorem.Inverse.KMSAffineRestrictionPresentation

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F D C : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]

/-- Change from surjective/injective presentation coordinates to the actual
quotient-domain and subspace-target parameter. -/
def parameterEquiv (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) :
    (D →ₗ[F2] C) ≃ₗ[F2] Parameter L.ker J.range :=
  LinearEquiv.arrowCongr (L.quotKerEquivOfSurjective hL).symm
    (LinearEquiv.ofInjective J hJ)

@[simp] theorem parameterEquiv_apply_mk (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (X : D →ₗ[F2] C) (x : E) :
    ((parameterEquiv L hL J hJ X) (L.ker.mkQ x) : F) = J (X (L x)) := rfl

/-- The embedded quotient parameter is the original two-sided composition. -/
@[simp] theorem embed_parameterEquiv (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (X : D →ₗ[F2] C) :
    embed L.ker J.range (parameterEquiv L hL J hJ X) = J.comp (X.comp L) := by
  apply LinearMap.ext
  intro x
  rfl

@[simp] theorem translate_parameterEquiv (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (T : E →ₗ[F2] F) (X : D →ₗ[F2] C) :
    translate L.ker J.range T (parameterEquiv L hL J hJ X) =
      T + J.comp (X.comp L) := by
  rw [Fourier.MatrixRestrictions.translate, embed_parameterEquiv]

end
end UniqueGamesTheorem.Inverse.KMSAffineRestrictionPresentation

end

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

/-- The original vanishing subspace viewed inside the chosen large summand. -/
abbrev localVanishing (D U : Submodule F2 E) : Submodule F2 U :=
  D.comap U.subtype

/-- The constrained component of an actual quotient parameter. -/
def splitLeft (D U : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) : Parameter (localVanishing D U) W :=
  (localVanishing D U).liftQ (A.comp (D.mkQ.comp U.subtype)) (by
    intro x hx
    change A (D.mkQ (x : E)) = 0
    have hz : D.mkQ (x : E) = 0 :=
      (Submodule.Quotient.mk_eq_zero D).mpr hx
    rw [hz, map_zero])

@[simp] theorem splitLeft_apply (D U : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) (x : U) :
    splitLeft D U W A ((localVanishing D U).mkQ x) =
      A (D.mkQ (x : E)) := rfl

/-- The free component of an actual quotient parameter. -/
def splitRight (D E₀ : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) : E₀ →ₗ[F2] W :=
  A.comp (D.mkQ.comp E₀.subtype)

@[simp] theorem splitRight_apply (D E₀ : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) (x : E₀) :
    splitRight D E₀ W A x = A (D.mkQ (x : E)) := rfl

/-- Assemble the two components before quotienting by `D`. -/
def joinMap (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hc : IsCompl U E₀) (B : Parameter (localVanishing D U) W)
    (C : E₀ →ₗ[F2] W) : E →ₗ[F2] W :=
  B.comp ((localVanishing D U).mkQ.comp (U.projectionOnto E₀ hc)) +
    C.comp (E₀.projectionOnto U hc.symm)

@[simp] theorem joinMap_apply_left (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : U) :
    joinMap D U E₀ W hc B C (x : E) = B ((localVanishing D U).mkQ x) := by
  simp [joinMap]

@[simp] theorem joinMap_apply_right (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E₀) :
    joinMap D U E₀ W hc B C (x : E) = C x := by
  simp [joinMap]

theorem joinMap_vanishes (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    D ≤ (joinMap D U E₀ W hc B C).ker := by
  intro x hx
  let u : U := ⟨x, hDU hx⟩
  change joinMap D U E₀ W hc B C (u : E) = 0
  rw [joinMap_apply_left]
  have hz : (localVanishing D U).mkQ u = 0 :=
    (Submodule.Quotient.mk_eq_zero (localVanishing D U)).mpr hx
  rw [hz, map_zero]

/-- The actual quotient parameter reconstructed from both independent pieces. -/
def join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) : Parameter D W :=
  D.liftQ (joinMap D U E₀ W hc B C) (joinMap_vanishes D U E₀ W hDU hc B C)

@[simp] theorem join_apply (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E) :
    join D U E₀ W hDU hc B C (D.mkQ x) = joinMap D U E₀ W hc B C x := rfl

@[simp] theorem join_embed_apply_left (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : U) :
    embed D W (join D U E₀ W hDU hc B C) (x : E) =
      (B ((localVanishing D U).mkQ x) : F) := by
  rw [embed_apply, join_apply, joinMap_apply_left]

@[simp] theorem join_embed_apply_right (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E₀) :
    embed D W (join D U E₀ W hDU hc B C) (x : E) = (C x : F) := by
  rw [embed_apply, join_apply, joinMap_apply_right]

theorem splitLeft_join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    splitLeft D U W (join D U E₀ W hDU hc B C) = B := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
  rw [splitLeft_apply, join_apply, joinMap_apply_left]

theorem splitRight_join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    splitRight D E₀ W (join D U E₀ W hDU hc B C) = C := by
  apply LinearMap.ext
  intro x
  rw [splitRight_apply, join_apply, joinMap_apply_right]

theorem join_split (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (A : Parameter D W) :
    join D U E₀ W hDU hc (splitLeft D U W A) (splitRight D E₀ W A) = A := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := D.mkQ_surjective q
  obtain ⟨⟨u, v⟩, hx⟩ := (Submodule.prodEquivOfIsCompl U E₀ hc).surjective x
  change (u : E) + (v : E) = x at hx
  rw [← hx]
  simp only [map_add, join_apply, joinMap_apply_left, joinMap_apply_right,
    splitLeft_apply, splitRight_apply]

/-- Linear equivalence of the full restriction domain with the constrained
component and the free complementary component. -/
def splitEquiv (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) :
    Parameter D W ≃ₗ[F2]
      (Parameter (localVanishing D U) W × (E₀ →ₗ[F2] W)) where
  toFun A := (splitLeft D U W A, splitRight D E₀ W A)
  invFun P := join D U E₀ W hDU hc P.1 P.2
  left_inv := join_split D U E₀ W hDU hc
  right_inv P := Prod.ext (splitLeft_join D U E₀ W hDU hc P.1 P.2)
    (splitRight_join D U E₀ W hDU hc P.1 P.2)
  map_add' A B := by
    apply Prod.ext
    · apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
      rfl
    · rfl
  map_smul' a A := by
    apply Prod.ext
    · apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
      rfl
    · rfl

@[simp] theorem splitEquiv_symm_apply (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    (splitEquiv D U E₀ W hDU hc).symm (B, C) = join D U E₀ W hDU hc B C := rfl

end
end UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSKernelOrbitsFourierLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
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

/-- Extend a frequency by specifying its value on the new coordinate. -/
def hyperplaneExtend (z : B →ₗ[F2] E) (v : E) : (B × F2) →ₗ[F2] E :=
  z.coprod (LinearMap.toSpanSingleton F2 E v)

@[simp] theorem hyperplaneExtend_apply (z : B →ₗ[F2] E) (v : E) (b : B) (c : F2) :
    hyperplaneExtend z v (b, c) = z b + c • v := rfl

@[simp] theorem hyperplaneExtend_comp_inl (z : B →ₗ[F2] E) (v : E) :
    (hyperplaneExtend z v).comp (LinearMap.inl F2 B F2) = z :=
  LinearMap.coprod_inl _ _

@[simp] theorem hyperplaneExtend_new_coordinate (z : B →ₗ[F2] E) (v : E) :
    hyperplaneExtend z v (0, 1) = v := by simp

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! Exact images and dependent-extension sums after embedding a smaller
frequency space. These identities align the genuine zoom-out recurrence with
the small-component Fourier coefficients. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {E B J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup B] [Module F2 B]
  [AddCommGroup J] [Module F2 J]

def leftEmbedding (ι : (J × F2) →ₗ[F2] E) : J →ₗ[F2] E :=
  ι.comp (LinearMap.inl F2 J F2)

theorem leftEmbedding_injective (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) : Function.Injective (leftEmbedding ι) := by
  intro x y h
  have hxy : (x, (0 : F2)) = (y, 0) := hι h
  exact congrArg Prod.fst hxy

theorem range_left_comp_of_surjective (ι : (J × F2) →ₗ[F2] E)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    ((leftEmbedding ι).comp z).range = (leftEmbedding ι).range := by
  ext v
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨z b, rfl⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨b, rfl⟩ := hz j
    exact ⟨b, rfl⟩

/-- The dependent extensions are enumerated exactly once by the small space. -/
def liftedRangeEquiv (ι : (J × F2) →ₗ[F2] E) (hι : Function.Injective ι)
    (z : B →ₗ[F2] J) (hz : Function.Surjective z) :
    J ≃ ((leftEmbedding ι).comp z).range :=
  Equiv.ofBijective
    (fun j => ⟨leftEmbedding ι j, by
      rw [range_left_comp_of_surjective ι z hz]
      exact ⟨j, rfl⟩⟩)
    ⟨by
      intro x y h
      exact leftEmbedding_injective ι hι (congrArg Subtype.val h),
      by
      rintro ⟨v, b, rfl⟩
      exact ⟨z b, rfl⟩⟩

@[simp] theorem liftedRangeEquiv_val (ι : (J × F2) →ₗ[F2] E)
    (hι : Function.Injective ι) (z : B →ₗ[F2] J) (hz : Function.Surjective z) (j : J) :
    (liftedRangeEquiv ι hι z hz j).val = leftEmbedding ι j := rfl

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticBlockFrequenciesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
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

/-- Adjoin a new identity coordinate and an arbitrary off-diagonal vector. -/
def blockFrequency (z : B →ₗ[F2] J) (w : J) : (B × F2) →ₗ[F2] (J × F2) :=
  (hyperplaneExtend z w).prod (LinearMap.snd F2 B F2)

@[simp] theorem blockFrequency_apply (z : B →ₗ[F2] J) (w : J) (b : B) (c : F2) :
    blockFrequency z w (b, c) = (z b + c • w, c) := rfl

def blockOld (T : (B × F2) →ₗ[F2] (J × F2)) : B →ₗ[F2] J :=
  ((LinearMap.fst F2 J F2).comp T).comp (LinearMap.inl F2 B F2)

def blockNew (T : (B × F2) →ₗ[F2] (J × F2)) : J := (T (0, 1)).1

@[simp] theorem blockOld_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockOld (blockFrequency z w) = z := by
  ext b
  simp [blockOld]

@[simp] theorem blockNew_blockFrequency (z : B →ₗ[F2] J) (w : J) :
    blockNew (blockFrequency z w) = w := by simp [blockNew]

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

/-- Actual dual frequencies are reindexed by precomposition with the inverse. -/
def codomainFrequencyEquiv (e : F ≃ₗ[F2] F') : (F →ₗ[F2] I) ≃ (F' →ₗ[F2] I) where
  toFun T := T.comp e.symm.toLinearMap
  invFun T := T.comp e.toLinearMap
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem codomainFrequencyEquiv_apply (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    codomainFrequencyEquiv e T = T.comp e.symm.toLinearMap := rfl

@[simp] theorem codomainFrequency_cancel (e : F ≃ₗ[F2] F') (T : F →ₗ[F2] I) :
    (T.comp e.symm.toLinearMap).comp e.toLinearMap = T := by ext x; simp

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-!
# Transport of the small component between equivalent coordinate spaces

The embedding and partial projection are transported together. Thus the
lifted frequency and its prescribed partial value remain literally the same.
Finite reindexing proves exact coefficient, function, and restricted-energy
identities without requiring basis invariance of the original function.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters
  (linearTraceCharacter linearTraceCharacter_apply linearTracePair)

variable {E F I I' J : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I] [AddCommGroup I'] [Module F2 I']
  [AddCommGroup J] [Module F2 J]

/-- Reindex the actual dual frequency maps by an equivalence of their targets. -/
def smallFrequencyEquiv (e : I ≃ₗ[F2] I') : (F →ₗ[F2] I) ≃ (F →ₗ[F2] I') where
  toFun T := e.toLinearMap.comp T
  invFun T := e.symm.toLinearMap.comp T
  left_inv T := by ext x; simp
  right_inv T := by ext x; simp

@[simp] theorem smallFrequencyEquiv_apply (e : I ≃ₗ[F2] I') (T : F →ₗ[F2] I) :
    smallFrequencyEquiv e T = e.toLinearMap.comp T := rfl

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
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

local instance (priority := 2000) classicalSurjective_re79100_1 {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)
local instance mapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSLowLevelLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Coordinates adapted to an injected distinguished point. The complementary
subspace contains all old injected directions, so that the original injection
becomes exactly `pointLift` in the constructed coordinates.
-/

namespace UniqueGamesTheorem.Inverse.KMSPointComplement

noncomputable section
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {E I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

/-- The coordinates supplied by a complement to a nonzero point. -/
def pointEquivOfIsCompl (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) : (U × F2) ≃ₗ[F2] E :=
  ((LinearEquiv.refl F2 U).prodCongr
    (LinearEquiv.toSpanNonzeroSingleton F2 E v hv)).trans
      (Submodule.prodEquivOfIsCompl U (Submodule.span F2 {v}) hc)

@[simp] theorem pointEquivOfIsCompl_apply (U : Submodule F2 E) (v : E) (hv : v ≠ 0)
    (hc : IsCompl U (Submodule.span F2 {v})) (x : U) (c : F2) :
    pointEquivOfIsCompl U v hv hc (x, c) = (x : E) + c • v := rfl

end
end UniqueGamesTheorem.Inverse.KMSPointComplement

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

/-- A consistent finite enumeration of actual binary linear maps, built from
the finite vertex spaces. This is the enumeration used by the mixed theorem. -/
@[instance_reducible] def mixedMapFintype {V W : Type*}
    [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]
    [Fintype V] [Fintype W] : Fintype (V →ₗ[F2] W) :=
  Fintype.ofInjective (fun L : V →ₗ[F2] W => (L : V → W)) DFunLike.coe_injective

attribute [local instance] mixedMapFintype

end
end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
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

def rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m) :
    Finset (Mat ell m) :=
  Finset.univ.filter fun M => rowAdvice A M = s

@[simp] theorem mem_rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m)
    (M : Mat ell m) : M ∈ rowFiber A s ↔ rowAdvice A M = s := by
  simp [rowFiber]

end
end UniqueGamesTheorem.Inverse.RowErasureDescriptionColumnMass

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualSpectralLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Reduction.ActualSource
open UniqueGamesTheorem.Fourier.MatrixNoise

namespace UniqueGamesTheorem.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

def fiberAcceptance (S : Source) (k s d : Nat)
    (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (U : Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) : ℝ :=
  shortcodeAcceptance (fun M : ActualHomogeneous.E k →ₗ[F2] Alphabet s =>
    unfolded S k s d label (U, M.prod T))

end UniqueGamesTheorem.Decoder.ActualSpectral

end

end

section

namespace UniqueGamesTheorem.Decoder.ActualGoodRows

open Integration.BinaryLinear Reduction ActualSource
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

def table (S : Source) (k s d : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (U : ActualGame.Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (M : Mat s (1 + 2 * k)) : Vector s :=
  TableKeysGame.unfolded S k s d labeling
    (U, ((MatrixCoordinates.mapEquiv k s).symm M).prod T)

/-- The row-advice probability in actual matrix coordinates. In particular,
dependent rows of `A` are sampled with their full multiplicity. -/
def adviceMass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) : ℝ :=
  𝔼 U : ActualGame.Question S k,
    𝔼 T : ActualHomogeneous.E k →ₗ[F2] Vector d,
      RowErasure.adviceMass
        ((RowErasureMatrix.family s (1 + 2 * k) r).goodAt (table S k s d labeling U T) α)

end
end UniqueGamesTheorem.Decoder.ActualGoodRows

end

section

/-! The two full-table events used in the projected-witness transfer. Their
sample space contains actual occurrence tuples and complete affine tables,
but no projection choice. The selected witness depends on row advice only.
-/

namespace UniqueGamesTheorem.Decoder.ActualEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat)
open scoped BigOperators Classical

noncomputable section

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

abbrev Context (S : Source) (k d : ℕ) :=
  ActualGame.Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)

abbrev Sample (S : Source) (k s d r : ℕ) :=
  Context S k d × (RowErasureDescriptions.RowMap s r × Mat s (1 + 2 * k))

abbrev FullTableSample (S : Source) (k s d r : ℕ) :=
  (ActualGame.Question S k × (Alphabet s →ₗ[F2] Vector r)) × ActualGame.Map k s d

/-- A bijection merely rearranges the full sampled table and changes its
matrix coordinates. It never appends the hidden projection to this law. -/
def fullTableEquiv (S : Source) (k s d r : ℕ) :
    FullTableSample S k s d r ≃ Sample S k s d r where
  toFun p := ((p.1.1, (LinearMap.snd F2 (Alphabet s) (Vector d)).comp p.2),
    (LinearMap.toMatrix' p.1.2,
      MatrixCoordinates.mapEquiv k s ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp p.2)))
  invFun q := ((q.1.1, Matrix.toLin' q.2.1),
    ((MatrixCoordinates.mapEquiv k s).symm q.2.2).prod q.1.2)
  left_inv p := by
    rcases p with ⟨⟨U, A⟩, P⟩
    apply Prod.ext
    · simp
    · apply LinearMap.ext
      intro x
      simp only [LinearEquiv.symm_apply_apply, LinearMap.prod_apply]
      rfl
  right_inv q := by
    rcases q with ⟨⟨U, T⟩, A, M⟩
    apply Prod.ext
    · apply Prod.ext rfl
      apply LinearMap.ext
      intro x
      rfl
    · apply Prod.ext
      · exact LinearMap.toMatrix'_toLin' A
      · change MatrixCoordinates.mapEquiv k s
          ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp
            (((MatrixCoordinates.mapEquiv k s).symm M).prod T)) = M
        have hf : (LinearMap.fst F2 (Alphabet s) (Vector d)).comp
            (((MatrixCoordinates.mapEquiv k s).symm M).prod T) =
              (MatrixCoordinates.mapEquiv k s).symm M := by
          apply LinearMap.ext
          intro x
          rfl
        rw [hf, LinearEquiv.apply_symm_apply]

def unrestricted (S : Source) (k s d r : ℕ) : FiniteDistribution (Sample S k s d r) :=
  FiniteDistribution.uniform _

def sliceEvent (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r) : Bool :=
  decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
    (ActualGoodRows.table S k s d labeling p.1.1 p.1.2) α p.2.1 p.2.2)

def targetHit (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r) : Bool :=
  decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
    (ActualGoodRows.table S k s d labeling p.1.1 p.1.2) α p.2.1 p.2.2)

end
end UniqueGamesTheorem.Decoder.ActualEvents

end

section

namespace UniqueGamesTheorem.Decoder.MatrixGapChoice

open Integration.BinaryLinear Reduction ActualSource
open Inverse.Shortcode (Mat HasAffineSlice equalityAcceptance)

noncomputable section

/-- Fixed dimensions, density and sparse mask for one logical alphabet.
The remaining gadget codimension may be arbitrary when choosing the cube. -/
structure InverseParameters (rstar : ℕ) where
  α : ℝ
  positive : 0 < α
  bounded : α ≤ 1
  r : ℕ
  s : ℕ
  s_large : rstar ≤ s
  r_small : r < s
  trivial_small : 1 / (2 : ℝ) ^ (s - r) < α / 8
  tupleThreshold : ℕ
  inverse : ∀ k : ℕ, tupleThreshold ≤ k →
    ∀ f : Mat s (1 + 2 * k) → Vector s,
      ActualSpectral.eta rstar ≤ equalityAcceptance f → HasAffineSlice f α r
  advice : ∀ k : ℕ, tupleThreshold ≤ k →
    ∀ (S : Source) (d : ℕ) (g : SplitGadget s d)
      (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)),
      (∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
        rstar ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
        Integration.SplitGadget.kernelProbability g L ≤ 7 / 8) →
      (99 : ℚ) / 100 ≤ TableKeysGame.acceptanceProbability S k g labeling →
      ActualGoodRows.goodRowMass rstar s r ≤ ActualGoodRows.adviceMass S k s d r labeling α

end
end UniqueGamesTheorem.Decoder.MatrixGapChoice

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_VisiblePoliciesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Decoder.VisiblePolicies

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource PrivateStrategy
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- The part of a normalized affine witness needed by the left sampler. -/
structure ResponseWitness (k : ℕ) where
  columns : Submodule F2 (ActualHomogeneous.E k)
  coefficient : ActualHomogeneous.E k
  firstBit : ActualHomogeneous.tau coefficient = 1

def defaultWitness (k : ℕ) : ResponseWitness k :=
  ⟨⊥, ActualHomogeneous.hBasis k, ActualHomogeneous.tau_hBasis⟩

variable {k s d : ℕ} {R : Type} [AddCommGroup R] [Module F2 R]

abbrev LeftInput (S : Source) (k s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.FullAdvice k (Fin S.occurrences) (Alphabet s) (Vector d) R

abbrev RightInput (S : Source) (J : Finset (Fin k)) (s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.ProjectedAdvice (K := Alphabet s) (W := Vector d) (R := R)
    (ActualGame.names S) J

/-- The witness choice has only the left observation as its variable input. -/
def chosenWitness {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) : ResponseWitness k :=
  if h : ∃ w, good q w then Classical.choose h else defaultWitness k

def leftPolicy {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) :
    FiniteDistribution (ActualAnswer (ActualHomogeneous.tau (dimension := k))) :=
  let w := chosenWitness good q
  candidateLaw w.columns w.coefficient ActualHomogeneous.tau w.firstBit

/-- A fixed valid fallback gives a total policy even on impossible row inputs. -/
def pointLaw {X : Type*} [Fintype X] (x : X) : FiniteDistribution X where
  weight y := if y = x then 1 else 0
  nonnegative y := by split <;> norm_num
  normalized := by simp

/-- The right kernel consumes its own complete visible observation only. -/
def rightPolicy (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (q : RightInput S J s d R) :
    FiniteDistribution (ActualAnswer (TableKeys.visibleTau J)) :=
  if h : ∃ M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s,
      q.rowMap.comp M = q.rows then
    privateLaw
      (TableKeysPrivateRow.rowAnswer S labeling J q.question q.rowMap ⟨q.rows, h⟩ q.complement)
      q.rowMap.ker.subtype (TableKeys.visibleTau J) (TransferredDecoding.visibleFallback J)
  else pointLaw (TransferredDecoding.visibleFallback J)

/-- The literal product of the two observation-local stochastic responses. -/
def observedAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) : ℝ :=
  ((leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)).product
    (rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2)).probability
    (fun answers => decide
      (AdviceExperiment.projection (ActualGame.rhs S) draw answers.1.1 = answers.2.1))

end UniqueGamesTheorem.Decoder.VisiblePolicies

end

end

section

/-!
# The actual visible selector used by the stochastic decoder

At fixed labeling, the matrix table depends only on the occurrence question and
complement map. Its normalized row/column witness is selected from the observed
row map and row value. Transporting this witness through the actual homogeneous
coordinates supplies `VisiblePolicies.ResponseWitness`; the selected target's
affine intercept is retained separately, including exact equality on the slice.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.SelectedPolicies

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Inverse
open ActualSource VisiblePolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

/-- The table at a fixed actual occurrence question and complement map. -/
def matrixTable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (occ : ActualGame.Question S k)
    (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (M : Shortcode.Mat s (1 + 2 * k)) : Alphabet s :=
  TableKeysGame.unfolded S k s d labeling
    (occ, ((mapEquiv k s).symm M).prod T)

/-- No hidden matrix is an input to this fixed table function. -/
def fullTable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (q : LeftInput S k s d (Vector r)) : Shortcode.Mat s (1 + 2 * k) → Alphabet s :=
  matrixTable S labeling q.occurrences q.complement

theorem matrixTable_fold (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (occ : ActualGame.Question S k)
    (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (h : Alphabet s) (M : Shortcode.Mat s (1 + 2 * k)) :
    matrixTable S labeling occ T
        (M + Shortcode.rankOne h (Shortcode.functionalRow (coordinateTau k))) =
      matrixTable S labeling occ T M + h := by
  unfold matrixTable
  rw [mapEquiv_symm_firstBit_shift]
  have hprod : (((mapEquiv k s).symm M + ActualHomogeneous.tau.smulRight h).prod T) =
      ((mapEquiv k s).symm M).prod T +
        ActualHomogeneous.tau.smulRight (h, (0 : Vector d)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · simp
  rw [hprod]
  exact TableKeysGame.unfolded_equivariant S k s d labeling
    (occ, ((mapEquiv k s).symm M).prod T) h

def GoodAdvice (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (q : LeftInput S k s d (Vector r)) : Prop :=
  (RowErasureMatrix.family s (1 + 2 * k) r).GoodAdvice (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows)

/-- The actual normalized description, chosen using only the left observation. -/
def normalizedDescription (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    RowErasureDescriptions.Description s (1 + 2 * k) r :=
  RowErasureMatrix.normalizedChosenDescription (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood (coordinateTau k)
    (matrixTable_fold S labeling q.occurrences q.complement) hα hsmall

theorem normalizedDescription_spec (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    let F := RowErasureMatrix.family s (1 + 2 * k) r
    let D := normalizedDescription S labeling α hα hsmall q hgood
    let D₀ := F.chosenDescription (fullTable S labeling q) α
      (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood
    F.rowMap D = LinearMap.toMatrix' q.rowMap ∧
      F.rowValue D = mapEquiv k r q.rows ∧
      (F.points D).Nonempty ∧
      α / 2 ≤ F.agreement (fullTable S labeling q) D ∧
      coordinateTau k D.coefficient = 1 ∧
      D.toSlice = D₀.toSlice ∧
      F.agreement (fullTable S labeling q) D = F.agreement (fullTable S labeling q) D₀ ∧
      ∀ M, M ∈ F.points D₀ → F.target D M = F.target D₀ M :=
  RowErasureMatrix.normalizedChosenDescription_spec (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood (coordinateTau k)
    (matrixTable_fold S labeling q.occurrences q.complement) hα hsmall

/-- The response coefficient and columns in the actual homogeneous space. -/
def normalizedResponse (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    ResponseWitness k where
  columns := (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan.map
    (domainCoordinates k).symm.toLinearMap
  coefficient := (domainCoordinates k).symm
    (normalizedDescription S labeling α hα hsmall q hgood).coefficient
  firstBit := (normalizedDescription_spec S labeling α hα hsmall q hgood).2.2.2.2.1

/-- The generic selector predicate is now the graph of the actual normalized
row-advice selector, rather than an unspecified class of candidate witnesses. -/
def goodPredicate (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (w : ResponseWitness k) : Prop :=
  ∃ hgood : GoodAdvice S labeling α q,
    w = normalizedResponse S labeling α hα hsmall q hgood

end UniqueGamesTheorem.Decoder.SelectedPolicies

end

end

section

/-!
# Conditional success of the actual selected policies

This endpoint uses the normalized witness chosen from the left observation and
the private Fourier kernel chosen from the right observation. The hypothesis is
literal uniform agreement on a transferred affine column slice. Deriving that
hypothesis from the actual visible conditional law is the separate transfer
step; it is not assumed as an inverse theorem or as extra prover information.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.SelectedDecoding

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- The affine slice is a subtype of a finite linear-map space. -/
instance affineSliceFintype {E K L : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup K] [Module F2 K]
    [AddCommGroup L] [Module F2 L] [Fintype (E →ₗ[F2] K)]
    (A : K →ₗ[F2] L) (Q : Submodule F2 E) (Mstar : E →ₗ[F2] K) :
    Fintype (RowErasureSliceQuotient.AffineSlice A Q Mstar) := by
  unfold RowErasureSliceQuotient.AffineSlice
  infer_instance

variable {k s d r : ℕ}

/-- Normalizing the target preserves the actual selected event, point by point. -/
theorem selectedEvent_iff_normalized (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k))
    (hrow : RowErasureMatrix.rowAdvice (LinearMap.toMatrix' q.rowMap) M =
      mapEquiv k r q.rows) :
    (RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
        (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap) M ↔
      M ∈ (RowErasureMatrix.family s (1 + 2 * k) r).points
        (normalizedDescription S labeling α hα hsmall q hgood) := by
  have he := (RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent_iff_of_advice
    (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap)
    (mapEquiv k r q.rows) hgood M hrow
  obtain ⟨_, _, _, _, _, hslice, _, _⟩ :=
    normalizedDescription_spec S labeling α hα hsmall q hgood
  rw [show (RowErasureMatrix.family s (1 + 2 * k) r).points
      (normalizedDescription S labeling α hα hsmall q hgood) =
      (RowErasureMatrix.family s (1 + 2 * k) r).points
        ((RowErasureMatrix.family s (1 + 2 * k) r).chosenDescription
          (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap)
          (mapEquiv k r q.rows) hgood) from congrArg Shortcode.Slice.points hslice]
  exact he

/-- Literal uniform target agreement on the projected affine slice. The slice
origin is an analysis witness, independent of the canonical visible row base. -/
def transferredAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (w : ResponseWitness k) (u : Alphabet s)
    (Mstar : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s) : ℝ :=
  𝔼 M : RowErasureSliceQuotient.AffineSlice draw.rowMap
      (w.columns.map (AdviceExperiment.projection (ActualGame.rhs S) draw)) Mstar,
    if TableKeysRestoration.projectedAnswer S k s d labeling draw.singletons
        (RawPrivateTable.supported draw.singletons (ActualGame.names S)
          draw.occurrences draw.positions) (M.val.prod draw.complement) =
      M.val (AdviceExperiment.projection (ActualGame.rhs S) draw w.coefficient) + u
    then (1 : ℝ) else 0

end UniqueGamesTheorem.Decoder.SelectedDecoding

end

end

section

/-!
# The selected padded slice is the actual projected affine slice

After fixing row advice, the selected full-domain column equations on `Mπ` are
exactly the equations fixing `M` on the image of the selected column span under
`π`. The equivalence keeps the same maps, so both uniform sampling and affine
target equality transport without changing the chosen intercept.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.ProjectedColumnSlice

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

section Algebra

variable {V : Type*} [AddCommGroup V] [Module F2 V]

/-- Two successive images of a column subspace express the same pointwise
agreement as composition with the coordinate change and projection. -/
theorem column_agreement_iff (Q : Submodule F2 (Vector (1 + 2 * k)))
    (π : ActualHomogeneous.E k →ₗ[F2] V) (M Mstar : V →ₗ[F2] Alphabet s) :
    (∀ x ∈ Q, M (π ((domainCoordinates k).symm x)) =
      Mstar (π ((domainCoordinates k).symm x))) ↔
      ∀ v ∈ (Q.map (domainCoordinates k).symm.toLinearMap).map π, M v = Mstar v := by
  constructor
  · intro h v hv
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
    exact h x hx
  · intro h x hx
    apply h
    exact Submodule.mem_map.mpr ⟨(domainCoordinates k).symm x,
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- A simultaneous matrix slice pulls back to the projected column equations
once the actual row equation is fixed. -/
theorem contains_padded_iff
    (D : RowErasureDescriptions.Description s (1 + 2 * k) r)
    (A : Alphabet s →ₗ[F2] Vector r)
    (hDrow : (RowErasureMatrix.family s (1 + 2 * k) r).rowMap D = LinearMap.toMatrix' A)
    (π : ActualHomogeneous.E k →ₗ[F2] V) (Mstar : V →ₗ[F2] Alphabet s)
    (hstar : mapEquiv k s (Mstar.comp π) ∈ D.toSlice.points)
    (M : V →ₗ[F2] Alphabet s) (hrow : A.comp M = A.comp Mstar) :
    mapEquiv k s (M.comp π) ∈ D.toSlice.points ↔
      ∀ v ∈ (D.toSlice.columnSpan.map (domainCoordinates k).symm.toLinearMap).map π,
        M v = Mstar v := by
  have hr : D.toSlice.rowMap = A := by
    change Matrix.toLin' D.1 = A
    change D.1 = LinearMap.toMatrix' A at hDrow
    rw [hDrow, Matrix.toLin'_toMatrix']
  have hc (N : V →ₗ[F2] Alphabet s) :
      Matrix.toLin' (mapEquiv k s (N.comp π)) =
        (N.comp π).comp (domainCoordinates k).symm.toLinearMap := by
    rw [mapEquiv_apply, Matrix.toLin'_toMatrix']
  have hs : D.toSlice.Contains (mapEquiv k s (Mstar.comp π)) :=
    (Finset.mem_filter.mp hstar).2
  have he := D.toSlice.contains_iff_inSlice (mapEquiv k s (Mstar.comp π)) hs
    (mapEquiv k s (M.comp π))
  rw [AffineWitness.InSlice, hr, hc, hc] at he
  have hrows : A.comp ((M.comp π).comp (domainCoordinates k).symm.toLinearMap) =
      A.comp ((Mstar.comp π).comp (domainCoordinates k).symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hrow (π ((domainCoordinates k).symm x))
  constructor
  · intro h
    have hh := he.mp (Finset.mem_filter.mp h).2
    exact (column_agreement_iff D.toSlice.columnSpan π M Mstar).mp hh.2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, he.mpr ⟨hrows,
      (column_agreement_iff D.toSlice.columnSpan π M Mstar).mpr h⟩⟩

end Algebra

end UniqueGamesTheorem.Decoder.ProjectedColumnSlice

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_VisibleTransferLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Decoder.VisibleTransfer

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Ω D : Type*} [Fintype Ω] [Fintype D]

def fiberMass (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) (event : Ω → Bool) : ℝ :=
  μ.probability (fiberEvent observe d event)

/-- Positive projected column-slice mass and sufficient conditional target
agreement. Both quantities are computed after fixing actual visible data. -/
def visibleWitness (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (d : D) : Bool := by
  classical
  exact decide (0 < fiberMass μ observe d slice ∧
    threshold * fiberMass μ observe d slice ≤
      fiberMass μ observe d (fun x => slice x && targetHit x))

end
end UniqueGamesTheorem.Decoder.VisibleTransfer

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualAdviceUpperLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The clean-coordinate upper bound for the actual private-decoding policies.
At every fixed public map `A`, the visible coefficient space is
`Vector d × A.range`.  Its cardinality is at most `2^(d+rs)`, including when
`A` is rank deficient.  The true independent uniform maps `T,M`, the
Bernoulli mask, and all iid occurrence/position draws are retained by the
proved sampling equality, before averaging over the uniform public map.
-/

namespace UniqueGamesTheorem.Decoder.ActualAdviceUpper

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

instance (priority := high) publicMapFintype (s rs : Nat) : Fintype (Alphabet s →ₗ[F2] Vector rs) :=
  Fintype.ofInjective (fun A : Alphabet s →ₗ[F2] Vector rs => (A : Alphabet s → Vector rs))
    DFunLike.coe_injective

/-- The ordinary game uses actual occurrence IDs and actual variable names. -/
def sourceIncidence (S : Source) :
    IncidenceExtraction.Incidence (Fin S.occurrences) (Fin S.variables) where
  name := ActualGame.names S
  rhs e := (S.equation e).rhs

abbrev Visible (d : Nat) (A : Alphabet s →ₗ[F2] Vector rs) := Vector d × A.range

def complementMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector d :=
  (LinearMap.fst F2 (Vector d) A.range).comp Y

def rowMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector rs :=
  A.range.subtype.comp ((LinearMap.snd F2 (Vector d) A.range).comp Y)

/-- Decode only the data visible to the first player. -/
def fullInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (occ : Fin k → Fin S.occurrences)
    (Y : ActualHomogeneous.E k →ₗ[F2] Visible d A) :
    VisiblePolicies.LeftInput S k s d (Vector rs) where
  occurrences := occ
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

/-- Decode only the displayed question and the visible row/complement maps. -/
def projectedInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Visible d A) :
    VisiblePolicies.RightInput S J s d (Vector rs) where
  question := O
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

/-- Actual observation-local stochastic policies, in the exact advice space
used by the clean-coordinate experiment.  Public `A` is fixed before questions. -/
def policies (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) :
    Clean.ActualAdviceStochasticBridge.Policies k (sourceIncidence S) (Visible d A) where
  first _ occ Y := VisiblePolicies.leftPolicy good (fullInput S A occ Y)
  second J O Y := VisiblePolicies.rightPolicy S labeling J (projectedInput S A J O Y)

/-- The real draw corresponding to a fixed mask and the independently sampled
complement and hidden matrices. -/
def actualDraw (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector rs) where
  singletons := J
  occurrences := occ
  positions := slot
  rowMap := A
  hiddenMatrix := M
  complement := T

end

end UniqueGamesTheorem.Decoder.ActualAdviceUpper

end

section

/-!
The stochastic clean upper bound applies to the literal agreement of the two
actual local decoders.  The equality below retains every sampled mask, all
occurrence/position draws, and both independently uniform target maps.
-/

namespace UniqueGamesTheorem.Decoder.ActualAdviceSampling

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource ActualAdviceUpper

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

/-- The actual experiment, before identifying its visible-map marginal with
the clean-coordinate law. The two private answer draws are already averaged
inside `observedAgreement`. -/
def sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
        (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
      fun TM => (FiniteDistribution.table (fun _ : Fin k => μ)).expectation fun draw =>
        VisiblePolicies.observedAgreement S labeling good
          (actualDraw S A (Clean.NativeExperiment.maskSet mask) (fun j => (draw j).1)
            (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) TM.1 TM.2)

end

end UniqueGamesTheorem.Decoder.ActualAdviceSampling

end

section

/-! The complete-data conditional law of the actual projected experiment.
The residual private matrix is uniform even when the occurrence law is
weighted and the public row map has deficient rank. -/

namespace UniqueGamesTheorem.Decoder.ActualConditionalLaw

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

section Policy

variable {k s d r : ℕ}

def datumAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector r) → VisiblePolicies.ResponseWitness k → Prop)
    (data : AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)) : ℝ :=
  VisiblePolicies.observedAgreement S labeling good (AdviceLaw.completeDraw data 0)

end Policy
end
end UniqueGamesTheorem.Decoder.ActualConditionalLaw

end

section

/-! The selected full-table events pulled back to the genuine projected
experiment. The comparison space forgets the projection, while complete data
retains it only for the subsequent finite conditional-law argument. -/

namespace UniqueGamesTheorem.Decoder.ActualSeedEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype_re79100_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
abbrev Seed (S : Source) (k s d r : ℕ) :=
  AdviceLaw.FullSeed k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)

abbrev Datum (S : Source) (k s d r : ℕ) :=
  AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)

def law (S : Source) (k s d r : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (Seed S k s d r) :=
  AdviceLaw.fullSeedLaw (V := Ambient s d)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ'

def draw {S : Source} {k s d r : ℕ} (x : Seed S k s d r) :=
  AdviceLaw.seedToActualDraw x.1.1 x.1.2 x.2

def pad (S : Source) (k s d r : ℕ) (x : Seed S k s d r) : ActualEvents.Sample S k s d r :=
  ActualEvents.fullTableEquiv S k s d r
    (AdviceLaw.fullSeedPad (fun i => toBit (ActualGame.rhs S i)) x)

def slice (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    Seed S k s d r → Bool :=
  fun x => ActualEvents.sliceEvent S k s d r labeling α (pad S k s d r x)

def targetHit (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    Seed S k s d r → Bool :=
  fun x => ActualEvents.targetHit S k s d r labeling α (pad S k s d r x)

theorem slice_eq_selectedEvent (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ)
    (x : Seed S k s d r) :
    slice S k s d r labeling α x = decide
      ((Inverse.RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
        (SelectedPolicies.fullTable S labeling
          (AdviceExperiment.leftObservation (ActualGame.rhs S) (draw x))) α
        (LinearMap.toMatrix' (draw x).rowMap)
        (MatrixCoordinates.mapEquiv k s (AdviceExperiment.paddedMatrix (ActualGame.rhs S) (draw x)))) :=
  rfl

end
end UniqueGamesTheorem.Decoder.ActualSeedEvents

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_TableReduction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Integration.TableReduction

open BinaryLinear NoiseTables UniqueGamesTheorem.Reduction.ActualSource
open UniqueGamesTheorem.Reduction.ActualGame UniqueGamesTheorem.Foundations.Target

variable {s d : Nat}

def tableEnumeration (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : NoiseEnumeration (T.gadget f hf) where
  indices := List.finRange T.vectors.length
  nodup := List.nodup_finRange _
  complete i := List.mem_finRange i

/-- The projection is used only to fill an erased witness field. It is never
used when generating constraints or evaluating their permutation tables. -/
def tableSkeleton (T : Table s d) : SplitGadget s d :=
  T.gadget Prod.fst (fun _ _ => rfl)

end UniqueGamesTheorem.Integration.TableReduction

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_TableKeysAddressGameLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Direct addresses for the v2 single-orbit matrix game. There is one canonical
body address space, with no side bit and no extra right-endpoint offset.
Unused addresses are isolated. Runtime construction uses canonical words and
radix arithmetic, not deduplication or inverse vertex enumeration.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysAddressGame

open UniqueGamesTheorem.Reduction
open ActualSource Foundations.Target
open Integration.VertexEmbedding

abbrev vertexCount (S : Source) (k s d : Nat) : Nat :=
  CanonicalAddress.capacity S.variables S.occurrences k s d

def vertexAddress (S : Source) (k s d : Nat) (v : TableKeysGame.Vertex S k s d) :
    Fin (vertexCount S k s d) := CanonicalAddress.bodyAddress v.val

theorem vertexAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (vertexAddress S k s d) := by
  intro v w h
  apply Subtype.ext
  exact CanonicalAddress.bodyAddress_injective h

/-- Both endpoints use this same routine and this same address block. -/
def queryAddress (S : Source) (k s d : Nat) (q : TableKeysGame.Query S k s d) :
    Fin (vertexCount S k s d) :=
  CanonicalAddress.bodyAddress (ActualOrbit.body (TableKeysGame.canonical S k s d) q)

@[simp] theorem vertexAddress_query (S : Source) (k s d : Nat)
    (q : TableKeysGame.Query S k s d) :
    vertexAddress S k s d (TableKeysGame.vertex S k s d q) =
      queryAddress S k s d q := rfl

/-- This inverse is a proof adapter only; the output constructor never calls it. -/
def explicitToAddress (S : Source) (k s d : Nat) :
    Fin (TableKeysGame.explicitVertexCount S k s d) → Fin (vertexCount S k s d) :=
  fun i => vertexAddress S k s d ((TableKeysGame.explicitVertexEncoding S k s d).symm i)

theorem explicitToAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (explicitToAddress S k s d) :=
  (vertexAddress_injective S k s d).comp
    (TableKeysGame.explicitVertexEncoding S k s d).symm.injective

@[simp] theorem explicitToAddress_apply (S : Source) (k s d : Nat)
    (v : TableKeysGame.Vertex S k s d) :
    explicitToAddress S k s d (TableKeysGame.explicitVertexEncoding S k s d v) =
      vertexAddress S k s d v := by
  simp only [explicitToAddress, Equiv.symm_apply_apply]

def addressEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : TableKeysGame.Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := queryAddress S k s d (TableKeysGame.leftQuery S k g ω)
  target := queryAddress S k s d (TableKeysGame.rightQuery S k g ω)
  permutation := Encoding.translationTable
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))

theorem addressEdge_eq_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : TableKeysGame.Outcome S k g) :
    addressEdge S k g ω = embedConstraint (explicitToAddress S k s d)
      (TableKeysGame.explicitEdge S k g ω) := by
  simp only [addressEdge, embedConstraint, TableKeysGame.explicitEdge,
    explicitToAddress_apply, vertexAddress_query]

/-- The correcting function is not evaluated when producing an edge list. -/
def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (addressEdge S k g)
  nonempty h := by
    have hempty := List.map_eq_nil_iff.mp h
    apply (TableKeysGame.outputInstanceWithEnumeration S k g en).nonempty
    change (ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g) = []
    rw [hempty]
    rfl

@[simp] theorem outputInstance_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstance S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstance, List.length_map, ActualGame.explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

theorem outputInstance_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    countSatisfied labeling (outputInstance S k g en).constraints =
      countSatisfied (labeling ∘ explicitToAddress S k s d)
        (TableKeysGame.outputInstanceWithEnumeration S k g en).constraints := by
  simpa only [outputInstance, TableKeysGame.outputInstanceWithEnumeration, List.map_map,
    Function.comp_def, ← addressEdge_eq_embed] using
    count_map (explicitToAddress S k s d)
      ((ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g)) labeling

theorem outputInstance_translations (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (outputInstance S k g en) := by
  intro constraint hconstraint
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hconstraint
  refine ⟨TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω) +
    TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω), ?_⟩
  intro label
  have h := Encoding.translationTable_images
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))
    ((Encoding.alphabetEquiv s).symm label)
  simpa only [addressEdge, Encoding.alphabetEquiv_apply_symm_apply,
    Encoding.alphabetEquiv_symm_apply_apply, add_assoc] using
    congrArg (Encoding.alphabetEquiv s).symm h

/-- Fixed finite noise data suffice for executable output. -/
def tableOutput (S : Source) (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    Instance (2^s) :=
  outputInstance S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

/-- The nonlinear correctness witness is erased from the output program. -/
theorem tableOutput_eq_with_witness (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    tableOutput S k T = outputInstance S k (T.gadget f hf)
      (Integration.TableReduction.tableEnumeration T f hf) := by
  rfl

theorem tableOutput_translations (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (tableOutput S k T) := outputInstance_translations S k _ _

end UniqueGamesTheorem.Decoder.TableKeysAddressGame

end

section

/-! Transport the matrix-test bound to the actual direct-address edge list.
Every address labeling restricts to a semantic orbit labeling, with exactly
the same satisfied fraction and the same occurrence multiplicities. -/

namespace UniqueGamesTheorem.Decoder.MatrixGap

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Integration
open ActualSource

noncomputable section

theorem address_rate_eq_semantic_acceptance (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysAddressGame.vertexCount S k s d) → Fin (2 ^ s)) :
    GapSemantics.satisfactionRate (TableKeysAddressGame.outputInstance S k g en) labeling =
      TableKeysGame.acceptanceProbability S k g
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) := by
  calc
    _ = GapSemantics.satisfactionRate
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) := by
      unfold GapSemantics.satisfactionRate
      exact congrArg₂ (fun a b : Nat => (a : ℚ) / b)
        (TableKeysAddressGame.outputInstance_count S k g en labeling)
        (by simp only [TableKeysAddressGame.outputInstance,
          TableKeysGame.outputInstanceWithEnumeration, List.length_map])
    _ = GapSemantics.satisfactionRate (TableKeysGame.outputInstance S k g)
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) :=
      InstanceEquivalences.satisfactionRate_eq_of_rename_perm
        (TableKeysGame.outputInstance S k g)
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (TableKeysGame.semanticToExplicitVertices S k s d)
        (TableKeysGame.explicitConstraints_perm_renamed S k g en) _
    _ = _ := (TableKeysGame.acceptanceProbability_eq_count S k g _).symm

end

end UniqueGamesTheorem.Decoder.MatrixGap

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_ActualCompleteness
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual finite-distribution identities for completeness. -/
namespace UniqueGamesTheorem.Reduction.ActualCompleteness

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

section Evaluation
variable {E R : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup R] [Module F2 R] [Fintype R] [Fintype (E →ₗ[F2] R)]

/-- Evaluation at a point on the homogeneous `h = 1` slice sends the uniform
law on all linear maps to the uniform law on the target vector space. -/
theorem expect_linear_eval (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1)
    (g : R → ℚ) :
    (𝔼 X : E →ₗ[F2] R, g (X x)) = 𝔼 r : R, g r := by
  classical
  have hinv (r : R) : (𝔼 X : E →ₗ[F2] R, g (X x + r)) =
      𝔼 X : E →ₗ[F2] R, g (X x) := by
    let e : (E →ₗ[F2] R) ≃ (E →ₗ[F2] R) := Equiv.addRight (τ.smulRight r)
    apply Fintype.expect_equiv e
    intro X
    simp [e, hx]
  calc
    (𝔼 X : E →ₗ[F2] R, g (X x)) =
        𝔼 r : R, 𝔼 X : E →ₗ[F2] R, g (X x + r) := by simp only [hinv, Fintype.expect_const]
    _ = 𝔼 X : E →ₗ[F2] R, 𝔼 r : R, g (X x + r) := Finset.expect_comm _ _ _
    _ = 𝔼 r : R, g r := by
      have hshift (a : R) : (𝔼 r : R, g (a + r)) = 𝔼 r : R, g r := by
        apply Fintype.expect_equiv (Equiv.addLeft a)
        intro r
        rfl
      simp only [hshift, Fintype.expect_const]

end Evaluation

open ActualSource

section Noise
variable {E : Type*} [AddCommGroup E] [Module F2 E] {s d : Nat}
  [Fintype (E →ₗ[F2] Ambient s d)] [Fintype (E →ₗ[F2] F2)]

/-- The actual honest noise test on a fixed valid homogeneous point. -/
noncomputable def localNoiseFailure (g : SplitGadget s d) (x : E) : ℚ :=
  𝔼 X : E →ₗ[F2] Ambient s d, 𝔼 i : g.NoiseIndex, 𝔼 ell : E →ₗ[F2] F2,
    if g.f (X x + ell x • g.noise i) = g.f (X x) then 0 else 1

/-- The independent random functional makes the conditional noise failure
exactly half the gadget's stability error, including indexed noise repetitions. -/
theorem localNoiseFailure_eq_half (g : SplitGadget s d)
    (τ : E →ₗ[F2] F2) (x : E) (hx : τ x = 1) :
    localNoiseFailure g x = g.stabilityError / 2 := by
  classical
  have hbit (r v : Ambient s d) :
      (𝔼 b : F2, if g.f (r + b • v) = g.f r then (0 : ℚ) else 1) =
        (if g.f (r + v) = g.f r then (0 : ℚ) else 1) / 2 := by
    have huniv : (Finset.univ : Finset F2) = {0, 1} := by decide
    by_cases h : g.f (r + v) = g.f r <;> simp [Finset.expect, huniv, h]
  have hinner (X : E →ₗ[F2] Ambient s d) (i : g.NoiseIndex) :
      (𝔼 ell : E →ₗ[F2] F2,
        if g.f (X x + ell x • g.noise i) = g.f (X x) then (0 : ℚ) else 1) =
      (if g.f (X x + g.noise i) = g.f (X x) then (0 : ℚ) else 1) / 2 := by
    exact (expect_linear_eval τ x hx
      (fun b => if g.f (X x + b • g.noise i) = g.f (X x) then (0 : ℚ) else 1)).trans
      (hbit (X x) (g.noise i))
  unfold localNoiseFailure
  simp_rw [hinner]
  rw [expect_linear_eval τ x hx (fun r => 𝔼 i : g.NoiseIndex,
    (if g.f (r + g.noise i) = g.f r then (0 : ℚ) else 1) / 2)]
  have hstab : g.stabilityError = 𝔼 r : Ambient s d, 𝔼 i : g.NoiseIndex,
      if g.f (r + g.noise i) = g.f r then (0 : ℚ) else 1 := by
    exact (Finset.expect_product Finset.univ Finset.univ
      (fun ri : Ambient s d × g.NoiseIndex =>
        if g.f (ri.1 + g.noise ri.2) = g.f ri.1 then (0 : ℚ) else 1))
  rw [hstab]
  simp only [div_eq_mul_inv]
  simp_rw [Finset.expect_mul]

end Noise

section Source

noncomputable def tupleFailure (S : Source) (A : Fin S.variables → Bool) (k : Nat) : ℚ :=
  𝔼 U : Fin k → Fin S.occurrences,
    if ∀ j, S.satisfied A (U j) = true then 0 else 1

theorem tupleFailure_le (S : Source) (A : Fin S.variables → Bool) (k : Nat) :
    tupleFailure S A k ≤ k * S.failure A := by
  classical
  have hpoint (U : Fin k → Fin S.occurrences) :
      (if ∀ j, S.satisfied A (U j) = true then (0 : ℚ) else 1) ≤
        ∑ j : Fin k, if S.satisfied A (U j) then (0 : ℚ) else 1 := by
    by_cases hgood : ∀ j, S.satisfied A (U j) = true
    · simp [hgood]
    · have hex : ∃ j, S.satisfied A (U j) ≠ true := not_forall.mp hgood
      obtain ⟨j, hj⟩ := hex
      have hsum := Finset.single_le_sum
        (f := fun j : Fin k => if S.satisfied A (U j) then (0 : ℚ) else 1)
        (s := Finset.univ) (a := j) (by intro i _; split <;> norm_num)
        (Finset.mem_univ j)
      simpa [hgood, hj] using hsum
  calc
    tupleFailure S A k ≤ 𝔼 U : Fin k → Fin S.occurrences,
        ∑ j : Fin k, if S.satisfied A (U j) then (0 : ℚ) else 1 :=
      Finset.expect_le_expect (fun U _ => hpoint U)
    _ = ∑ j : Fin k, 𝔼 U : Fin k → Fin S.occurrences,
        if S.satisfied A (U j) then (0 : ℚ) else 1 := Finset.expect_sum_comm _ _ _
    _ = k * S.failure A := by
      have hcoord (j : Fin k) :
          (𝔼 U : Fin k → Fin S.occurrences,
            if S.satisfied A (U j) then (0 : ℚ) else 1) = S.failure A :=
        expect_function_apply j (fun e => if S.satisfied A e then (0 : ℚ) else 1)
      simp_rw [hcoord]
      simp

end Source

section HonestEvaluation
open ActualCanonical ActualHomogeneous
variable {Name Id R : Type*} [AddCommGroup R] [Module F2 R] [DecidableEq R] {k : Nat}

def evalTriple (names : Id → Fin 3 → Name) (A : Name → F2) (e : Id)
    (a : Fin 3 → R) : R := ∑ i, A (names e i) • a i

def evalRecord (names : Id → Fin 3 → Name) (A : Name → F2) : Record Name Id R → R
  | .blank => 0
  | .single n c => A n • c
  | .full e a => evalTriple names A e a

/-- An assignment is evaluated from retained record data only. -/
def evaluate (names : Id → Fin 3 → Name) (A : Name → F2)
    (d : Data k Name Id R) : R := d.1 + ∑ j, evalRecord names A (d.2 j)

theorem record_eval_normalized (names : Id → Fin 3 → Name) (A : Name → F2)
    (e : Id) (a : Fin 3 → R) :
    evalRecord names A (record names e a) = evalTriple names A e (ActualCanonical.normalize a) := by
  classical
  by_cases h01 : a 0 = a 1
  · by_cases h02 : a 0 = a 2
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
  · by_cases h02 : a 0 = a 2
    · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
        Fin.sum_univ_three, ActualCanonical.add_self]
    · by_cases h12 : a 1 = a 2
      · simp_all [record, evalRecord, evalTriple, ActualCanonical.normalize, ActualCanonical.translate, pivot,
          Fin.sum_univ_three, ActualCanonical.add_self]
      · simp [record, h01, h02, h12, evalRecord]

theorem record_eval_adjustment (names : Id → Fin 3 → Name) (A : Name → F2)
    (rhs : Id → F2) (e : Id) (a : Fin 3 → R)
    (hvalid : ∑ i, A (names e i) = rhs e) :
    rhs e • pivot a + evalRecord names A (record names e a) = evalTriple names A e a := by
  rw [record_eval_normalized]
  simp only [evalTriple, ActualCanonical.normalize, ActualCanonical.translate, smul_add, Finset.sum_add_distrib,
    ← Finset.sum_smul, hvalid]
  calc
    _ = (∑ i, A (names e i) • a i) + (rhs e • pivot a + rhs e • pivot a) := by abel
    _ = _ := by rw [ActualCanonical.add_self, add_zero]

theorem evaluate_data (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (A : Name → F2) (z : R) (a : Fin k → Fin 3 → R)
    (hvalid : ∀ j, ∑ i, A (names (occ j) i) = rhs (occ j)) :
    evaluate names A (data occ names rhs z a) =
      z + ∑ j, evalTriple names A (occ j) (a j) := by
  simp only [evaluate, data]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => record_eval_adjustment names A rhs (occ j) (a j) (hvalid j))

/-- The free-coordinate local assignment always has homogeneous coordinate one. -/
def honestPoint (occ : Fin k → Id) (names : Id → Fin 3 → Name) (A : Name → F2) : E k :=
  (1, fun j => (A (names (occ j) 0), A (names (occ j) 1)))

@[simp] theorem honestPoint_tau (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (A : Name → F2) : tau (honestPoint occ names A) = 1 := rfl

/-- Actual canonical evaluation equals linear-map evaluation on every question
whose occurrences the assignment satisfies. -/
theorem canonical_evaluate (occ : Fin k → Id) (names : Id → Fin 3 → Name)
    (rhs : Id → F2) (A : Name → F2) (X : E k →ₗ[F2] R)
    (hvalid : ∀ j, ∑ i, A (names (occ j) i) = rhs (occ j)) :
    evaluate names A (canonical occ names rhs X) = X (honestPoint occ names A) := by
  rw [canonical, evaluate_data occ names rhs A _ _ hvalid]
  conv_rhs => rw [ActualHomogeneous.linearMap_expansion]
  simp [honestPoint, evalTriple, standardTriple, Fin.sum_univ_three]

end HonestEvaluation

section ActualLabeling
noncomputable section

def honestVertexLabel (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) (v : ActualGame.Vertex S k s d) : Alphabet s :=
  g.f ((0, v.val.1) + ∑ j, evalRecord (ActualGame.names S)
    (fun n => ofBit (A n)) (v.val.2 j))

def honestLabeling (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) :
    Fin (ActualGame.vertexCount S k s d) → Fin (2^s) :=
  ActualGame.labelingOf S k s d (fun _ => honestVertexLabel S k g A)

/-- Equivariance recovers the dropped alphabet component exactly. -/
theorem honest_unfolded (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) (side : Bool) (q : ActualGame.Query S k s d) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (evaluate (ActualGame.names S) (fun n => ofBit (A n))
        (ActualGame.canonical S k s d q)) := by
  simp only [honestLabeling, ActualGame.unfolded, ActualGame.sideLabel_labelingOf,
    ActualOrbit.unfold]
  let z := (ActualGame.canonical S k s d q).1
  let r := ∑ j, evalRecord (ActualGame.names S) (fun n => ofBit (A n))
    ((ActualGame.canonical S k s d q).2 j)
  change g.f ((0, z.2) + r) + z.1 = g.f (z + r)
  have hsplit : ((0, z.2) + r) + (z.1, 0) = z + r := by
    apply Prod.ext <;> simp [add_comm]
  have h := g.equivariant ((0, z.2) + r) z.1
  rw [hsplit] at h
  exact h.symm

def sourcePoint (S : Source) (k : Nat) (A : Fin S.variables → Bool)
    (U : ActualGame.Question S k) : ActualHomogeneous.E k :=
  honestPoint U (ActualGame.names S) (fun n => ofBit (A n))

@[simp] theorem sourcePoint_tau (S : Source) (k : Nat) (A : Fin S.variables → Bool)
    (U : ActualGame.Question S k) : ActualHomogeneous.tau (sourcePoint S k A U) = 1 := rfl

theorem satisfied_parity (S : Source) (A : Fin S.variables → Bool)
    (e : Fin S.occurrences) (h : S.satisfied A e = true) :
    ∑ i : Fin 3, ofBit (A (ActualGame.names S e i)) = ActualGame.rhs S e := by
  have hb : ((A (S.equation e).first ^^ A (S.equation e).second) ^^
      A (S.equation e).third) = (S.equation e).rhs := by
    simpa [Source.satisfied, CloneGap.satisfied] using h
  have hf := congrArg ofBit hb
  simpa [Fin.sum_univ_three, ActualGame.names, ActualGame.rhs, ofBit_xor, add_assoc]
    using hf

theorem honest_unfolded_valid (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) (side : Bool) (q : ActualGame.Query S k s d)
    (hgood : ∀ j, S.satisfied A (q.1 j) = true) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (q.2 (sourcePoint S k A q.1)) := by
  rw [honest_unfolded]
  apply congrArg g.f
  exact canonical_evaluate q.1 (ActualGame.names S) (ActualGame.rhs S)
    (fun n => ofBit (A n)) q.2 (fun j => satisfied_parity S A (q.1 j) (hgood j))

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      ActualGame.acceptanceProbability S k g (honestLabeling S k g A) := by
  classical
  let P (ω : ActualGame.Outcome S k g) : Prop :=
    ActualGame.unfolded S k s d (honestLabeling S k g A) false
        (ActualGame.leftQuery S k g ω) =
      ActualGame.unfolded S k s d (honestLabeling S k g A) true
        (ActualGame.rightQuery S k g ω)
  let bad (ω : ActualGame.Outcome S k g) : ℚ :=
    if ∀ j, S.satisfied A (ω.1.1 j) = true then 0 else 1
  let noiseBad (ω : ActualGame.Outcome S k g) : ℚ :=
    if g.f (ω.1.2 (sourcePoint S k A ω.1.1) +
        ω.2.2 (sourcePoint S k A ω.1.1) • g.noise ω.2.1) =
      g.f (ω.1.2 (sourcePoint S k A ω.1.1)) then 0 else 1
  have hpoint (ω : ActualGame.Outcome S k g) :
      (if P ω then (0 : ℚ) else 1) ≤ bad ω + noiseBad ω := by
    by_cases hgood : ∀ j, S.satisfied A (ω.1.1 j) = true
    · have hL := honest_unfolded_valid S k g A false (ActualGame.leftQuery S k g ω) hgood
      have hR := honest_unfolded_valid S k g A true (ActualGame.rightQuery S k g ω) hgood
      simp only [P, hL, hR, bad, ite_eq_left hgood, zero_add]
      simp [noiseBad, ActualGame.leftQuery, ActualGame.rightQuery,
        LinearMap.add_apply, LinearMap.smulRight_apply, eq_comm]
      exact le_rfl
    · have hn : 0 ≤ noiseBad ω := by dsimp [noiseBad]; split <;> norm_num
      have hf : (if P ω then (0 : ℚ) else 1) ≤ 1 := by split <;> norm_num
      simpa only [bad, ite_eq_right hgood] using hf.trans (le_add_of_nonneg_right hn)
  have hbad : (𝔼 ω : ActualGame.Outcome S k g, bad ω) = tupleFailure S A k := by
    simp only [expect_pair, bad]
    change (𝔼 U : ActualGame.Question S k, 𝔼 _X : ActualGame.Map k s d,
      𝔼 _i : g.NoiseIndex, 𝔼 _ell : ActualGame.Dual k,
      if ∀ j, S.satisfied A (U j) = true then (0 : ℚ) else 1) = _
    simp_rw [Fintype.expect_const]
    rfl
  have hnoise : (𝔼 ω : ActualGame.Outcome S k g, noiseBad ω) = g.stabilityError / 2 := by
    simp only [expect_pair]
    change (𝔼 U : ActualGame.Question S k, localNoiseFailure g (sourcePoint S k A U)) = _
    have hu (U : ActualGame.Question S k) := localNoiseFailure_eq_half g
      ActualHomogeneous.tau (sourcePoint S k A U) (sourcePoint_tau S k A U)
    simp only [hu, Fintype.expect_const]
  have hfailure : (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) ≤
      tupleFailure S A k + g.stabilityError / 2 := by
    calc
      _ ≤ 𝔼 ω : ActualGame.Outcome S k g, (bad ω + noiseBad ω) :=
        Finset.expect_le_expect (fun ω _ => hpoint ω)
      _ = _ := by rw [Finset.expect_add_distrib, hbad, hnoise]
  have hsum : ActualGame.acceptanceProbability S k g (honestLabeling S k g A) +
      (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) = 1 := by
    rw [ActualGame.acceptanceProbability_eq_test]
    change (𝔼 ω : ActualGame.Outcome S k g, if P ω then (1 : ℚ) else 0) + _ = _
    rw [← Finset.expect_add_distrib]
    have hp (ω : ActualGame.Outcome S k g) :
        (if P ω then (1 : ℚ) else 0) + (if P ω then (0 : ℚ) else 1) = 1 := by
      split <;> norm_num
    simp only [hp, Fintype.expect_const]
  have htuple := tupleFailure_le S A k
  linarith

end
end ActualLabeling

end UniqueGamesTheorem.Reduction.ActualCompleteness

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_TableKeysCompletenessLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Completeness of the v2 single-orbit matrix game. The generic finite-average
calculation is shared with the proved actual completeness calculation. Its
reuse is justified below by pointwise equality of restored answers under
diagonal labels; the output vertices themselves are never doubled.

No gadget existence, dispersion hypothesis, inverse theorem, or legacy
soundness theorem is a premise. The bound includes the exact fair-bit factor
`1 / 2`, and is a statement about the actual finite edge occurrence list.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysCompleteness

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction
open ActualSource Foundations.Target
open TableKeysGame
open scoped BigOperators

noncomputable section

/-- Use a single label function on both auxiliary sides, solely to share the
already proved finite-average calculation. This does not change the v2 game. -/
def diagonalLabeling (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    Fin (ActualGame.vertexCount S k s d) → Fin (2^s) :=
  ActualGame.labelingOf S k s d (fun _ => vertexLabel S k s d labeling)

theorem diagonal_unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (side : Bool) (q : Query S k s d) :
    ActualGame.unfolded S k s d (diagonalLabeling S k s d labeling) side q =
      unfolded S k s d labeling q := by
  simp only [diagonalLabeling, ActualGame.unfolded,
    ActualGame.sideLabel_labelingOf, unfolded, canonical]

/-- Pointwise-identical matrix tests have exactly the same acceptance average. -/
theorem acceptanceProbability_eq_diagonal (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      ActualGame.acceptanceProbability S k g (diagonalLabeling S k s d labeling) := by
  rw [acceptanceProbability_eq_test, ActualGame.acceptanceProbability_eq_test]
  simp only [diagonal_unfolded, leftQuery, rightQuery]

def honestLabeling (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) : Fin (vertexCount S k s d) → Fin (2^s) :=
  labelingOf S k s d (ActualCompleteness.honestVertexLabel S k g A)

theorem diagonal_honestLabeling (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) :
    diagonalLabeling S k s d (honestLabeling S k g A) =
      ActualCompleteness.honestLabeling S k g A := by
  simp only [diagonalLabeling, honestLabeling, vertexLabel_labelingOf,
    ActualCompleteness.honestLabeling]

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      acceptanceProbability S k g (honestLabeling S k g A) := by
  rw [acceptanceProbability_eq_diagonal, diagonal_honestLabeling]
  exact ActualCompleteness.honest_acceptance_bound S k g A

theorem honest_acceptance_of_bounds (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) (ξ p ε : ℚ)
    (hsource : S.failure A ≤ ξ) (hstable : g.stabilityError ≤ p)
    (hbudget : (k : ℚ) * ξ + p / 2 ≤ ε) :
    1 - ε ≤ acceptanceProbability S k g (honestLabeling S k g A) := by
  have hm := mul_le_mul_of_nonneg_left hsource (show (0 : ℚ) ≤ k by positivity)
  have hactual := honest_acceptance_bound S k g A
  linarith

end

end UniqueGamesTheorem.Decoder.TableKeysCompleteness

end

section

/-!
Completeness on the actual single-orbit address output. An honest semantic
labeling is extended over unused addresses, with its satisfied fraction
unchanged. The two rational error bounds need no packaged error parameter.
-/

namespace UniqueGamesTheorem.Decoder.MatrixGap

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Integration
open ActualSource

noncomputable section

/-- Every semantic labeling extends to a labeling of the padded address space.
The generated edge list retains its exact acceptance fraction. -/
theorem semantic_acceptance_le_address_value (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) :
    (TableKeysGame.acceptanceProbability S k g labeling : ℝ) ≤
      InstanceValue.value (TableKeysAddressGame.outputInstance S k g en) := by
  let e := TableKeysGame.semanticToExplicitVertices S k s d
  let addressLabel := VertexEmbedding.extendLabeling
    (TableKeysAddressGame.explicitToAddress S k s d) (labeling ∘ e.symm)
      (⟨0, by positivity⟩ : Fin (2 ^ s))
  have hrestrict : addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d =
      labeling ∘ e.symm :=
    VertexEmbedding.extendLabeling_comp _
      (TableKeysAddressGame.explicitToAddress_injective S k s d) _ _
  have hpullback : (addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
      TableKeysGame.semanticToExplicitVertices S k s d = labeling := by
    rw [hrestrict]
    funext v
    exact congrArg labeling (e.symm_apply_apply v)
  have hrate := address_rate_eq_semantic_acceptance S k g en addressLabel
  rw [hpullback] at hrate
  have hvalue := InstanceValue.satisfactionRate_le_value
    (TableKeysAddressGame.outputInstance S k g en) addressLabel
  rw [hrate] at hvalue
  exact hvalue

/-- The exact near-assignment loss and fair-bit factor one half, measured on
the generated address instance and then cast to its real optimum value. -/
theorem address_value_ge_of_near_assignment (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (assignment : Fin S.variables → Bool) (ξ p : ℚ)
    (hfailure : S.failure assignment ≤ ξ)
    (hstable : (T.gadget f hf).stabilityError ≤ p) :
    (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S k T) := by
  let g := T.gadget f hf
  have hrat := TableKeysCompleteness.honest_acceptance_of_bounds S k g assignment
    ξ p ((k : ℚ) * ξ + p / 2) hfailure hstable (le_refl _)
  have hreal : (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      (TableKeysGame.acceptanceProbability S k g
        (TableKeysCompleteness.honestLabeling S k g assignment) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 hrat
    simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_add, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] using h
  rw [TableKeysAddressGame.tableOutput_eq_with_witness S k T f hf]
  exact hreal.trans (semantic_acceptance_le_address_value S k g
    (TableReduction.tableEnumeration T f hf)
    (TableKeysCompleteness.honestLabeling S k g assignment))

end
end UniqueGamesTheorem.Decoder.MatrixGap

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualSeedSamplingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The complete seed used for the lower-bound conditioning argument and the
mask/slot/map experiment used for the clean upper bound have exactly the same
actual decoder success. Unused positions are removed only by the pointwise
observation equality; occurrence IDs and their ordered local copies remain.
-/

namespace UniqueGamesTheorem.Decoder.ActualSeedSampling

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource ActualAdviceUpper ActualAdviceSampling

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

/-- A named pointwise observable makes the finite expectation permutations
explicit without changing the actual sampled draw. -/
def drawAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) (mask : Fin k → Bool)
    (occ : Fin k → Fin S.occurrences) (slots : Fin k → Fin 3)
    (TM :
      (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
      (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s)) : ℝ :=
  VisiblePolicies.observedAgreement S labeling good
    (actualDraw S A (Clean.NativeExperiment.maskSet mask) occ
      (fun j => Clean.ActualAdviceBridge.indexSlot (slots j)) TM.1 TM.2)

end

end UniqueGamesTheorem.Decoder.ActualSeedSampling

end

section

/-! Whole-table variation for the exact projected seed law in the selected
event coordinates. The projection is averaged out before the comparison. -/

namespace UniqueGamesTheorem.Decoder.ActualSeedVariation

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end
end UniqueGamesTheorem.Decoder.ActualSeedVariation

end

section

namespace UniqueGamesTheorem.Decoder.MatrixGap

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Fixed matrix-test parameters, before the separate bipartite subdivision
and repetition. Existence is proved by the spectral/decoding argument. -/
structure Parameters (p : ℚ) where
  k : Nat
  s : Nat
  d : Nat
  k_pos : 1 ≤ k
  s_pos : 1 ≤ s
  T : NoiseTables.Table s d
  f : Ambient s d → Alphabet s
  equivariant : ∀ x c, f (x + (c, 0)) = f x + c
  stability : (T.gadget f equivariant).stabilityError ≤ p
  sound : ∀ S : Source, S.DistinctNames →
    Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5 →
    InstanceValue.value (TableKeysAddressGame.tableOutput S k T) ≤ (99 : ℝ) / 100

namespace Parameters

variable {p : ℚ}

/-- The actual output constructor depends only on finite tables, not on the
correcting map or its equivariance proof. -/
def output (P : Parameters p) (S : Source) : Instance (2 ^ P.s) :=
  TableKeysAddressGame.tableOutput S P.k P.T

theorem completeness (P : Parameters p) (S : Source)
    (assignment : Fin S.variables → Bool) (ξ : ℚ)
    (hfailure : S.failure assignment ≤ ξ) :
    (1 : ℝ) - ((P.k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S P.k P.T) :=
  address_value_ge_of_near_assignment S P.k P.T P.f P.equivariant assignment
    ξ p hfailure P.stability

theorem output_translations (P : Parameters p) (S : Source) :
    TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv P.s).symm
      (P.output S) :=
  TableKeysAddressGame.tableOutput_translations S P.k P.T

end Parameters

end

end UniqueGamesTheorem.Decoder.MatrixGap

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_SelectedFiberLaw
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual conditional selected-fiber agreement

The selected event is the full-table event used by the total-variation
comparison. On a positive complete-data fiber it becomes the uniform actual
affine row/column slice. The selector is fixed by the left observation; the
extra complete data and a supporting matrix occur only in this analysis.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.SelectedFiberLaw

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Inverse UniqueGamesTheorem.Foundations.Games
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates ActualSeedEvents
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

variable {k s d r : ℕ}

def datumLeft (S : Source) (data : Datum S k s d r) : LeftInput S k s d (Vector r) :=
  AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

def datumMatrix (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :=
  (AdviceLaw.completeDraw data N).hiddenMatrix

def datumProjection (S : Source) (data : Datum S k s d r) :=
  AdviceExperiment.projection (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

theorem datumLeft_eq (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data N) =
      datumLeft S data := by
  unfold datumLeft
  rw [AdviceLaw.completeDraw_left, AdviceLaw.completeDraw_left]

theorem datumMatrix_rows (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    data.1.2.comp (datumMatrix S data N) = data.2.2.2.val :=
  AdviceLaw.completeDraw_rows data N

theorem datumMatrix_rowAdvice (S : Source) (data : Datum S k s d r)
    (N : AdviceLaw.PrivateMap data) :
    RowErasureMatrix.rowAdvice (LinearMap.toMatrix' data.1.2)
        (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data))) =
      mapEquiv k r (datumLeft S data).rows := by
  rw [← mapEquiv_rowAdvice]
  change mapEquiv k r ((data.1.2.comp (datumMatrix S data N)).comp (datumProjection S data)) =
    mapEquiv k r ((data.1.2.comp (datumMatrix S data 0)).comp (datumProjection S data))
  rw [datumMatrix_rows, datumMatrix_rows]
  rfl

/-- Every event membership uses the same selected normalized witness on the
entire complete-data fiber. -/
theorem slice_assemble_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (N : AdviceLaw.PrivateMap data) :
    slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true ↔
      mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)) ∈
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).toSlice.points := by
  rw [slice_eq_selectedEvent]
  change decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
      (fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S)
        (AdviceLaw.completeDraw data N))) α (LinearMap.toMatrix' data.1.2)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)))) = true ↔ _
  rw [datumLeft_eq, decide_eq_true_eq]
  exact SelectedDecoding.selectedEvent_iff_normalized S labeling α hα hsmall
    (datumLeft S data) hgood _ (datumMatrix_rowAdvice S data N)

/-- The actual selected private coordinates are in bijection with the complete
projected affine slice. The supporting point is used only to state its column
equations; the canonical visible base still defines the private coordinates. -/
def selectedPrivateEquiv (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true) :
    {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true} ≃
      RowErasureSliceQuotient.AffineSlice data.1.2
        ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
          (datumProjection S data)) (datumMatrix S data Nstar) := by
  let D := normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood
  let e := AdviceFibers.rowFiberEquiv data.1.2 data.2.2.2.val
    (AdviceFibers.observedBase data.1.2 data.2.2.2)
    (AdviceFibers.observedBase_property data.1.2 data.2.2.2)
  have hs : mapEquiv k s ((datumMatrix S data Nstar).comp (datumProjection S data)) ∈ D.toSlice.points :=
    (slice_assemble_iff S labeling α hα hsmall data hgood Nstar).mp hstar
  have hrow (N : AdviceLaw.PrivateMap data) :
      data.1.2.comp (datumMatrix S data N) = data.1.2.comp (datumMatrix S data Nstar) := by
    rw [datumMatrix_rows, datumMatrix_rows]
  let lift := fun M : RowErasureSliceQuotient.AffineSlice data.1.2
      ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
        (datumProjection S data)) (datumMatrix S data Nstar) =>
    e.symm ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩
  have hlift (M) : datumMatrix S data (lift M) = M.val :=
    congrArg Subtype.val (e.apply_symm_apply ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩)
  refine {
    toFun := fun N => ⟨datumMatrix S data N.val, hrow N.val, ?_⟩
    invFun := fun M => ⟨lift M, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs
      (datumMatrix S data N.val) (hrow N.val)).mp
        ((slice_assemble_iff S labeling α hα hsmall data hgood N.val).mp N.property)
  · apply (slice_assemble_iff S labeling α hα hsmall data hgood (lift M)).mpr
    rw [hlift]
    exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs M.val M.property.1).mpr M.property.2
  · intro N
    apply Subtype.ext
    exact e.symm_apply_apply N.val
  · intro M
    apply Subtype.ext
    exact hlift M

@[simp] theorem selectedPrivateEquiv_val (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true)
    (N : {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true}) :
    (selectedPrivateEquiv S labeling α hα hsmall data hgood Nstar hstar N).val =
      datumMatrix S data N.val := rfl

end UniqueGamesTheorem.Decoder.SelectedFiberLaw

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Decoding_ActualProjectedTransfer
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The full selected-witness argument on the actual projected experiment.
The variation comparison precedes all conditioning. Its visible event then
pays the independent private decoder success on every selected datum. -/

namespace UniqueGamesTheorem.Decoder.ActualProjectedTransfer

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_re79100_2 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def slopeVariation (k s d : ℕ) (β : ℝ) : ℝ :=
  Foundations.Information.totalVariation
    (SparseLaw.independentWeights
      (SparseLaw.mixture β (SparseLaw.singletonPairWeights (Ambient s d))) k)
    (SparseLaw.uniformWeights (Fin k → Ambient s d × Ambient s d))

end
end UniqueGamesTheorem.Decoder.ActualProjectedTransfer

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_ClauseVerifierLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP

open Target

def honestAnswer {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : ClauseAnswer :=
  ⟨assignment clause[0].variableIndex, assignment clause[1].variableIndex,
   assignment clause[2].variableIndex⟩

abbrev RandomEvent (formula : Formula) := Fin formula.clauses.length × Slot

end UniqueGamesTheorem.Foundations.PCP

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContexts

open Target PCP

def pi (F : Formula) {u : ℕ} (c : ClauseContext F u) (v : VariableContext F u)
    (j : J u) : I u :=
  fun t => answerAt (j t) (canonicalSlot (clauseAt F (c t)) (v t))

def sampledVariables (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : VariableContext F u :=
  fun t => nameAt (clauseAt F (c t)) (s t)

def honestJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.variables → Bool) : J u :=
  fun t => honestAnswer (clauseAt F (c t)) assignment

def honestI (F : Formula) {u : ℕ} (v : VariableContext F u)
    (assignment : Fin F.variables → Bool) : I u :=
  fun t => assignment (v t)

end UniqueGamesTheorem.Foundations.Hastad.SourceContexts

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_GraphCounterStartLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOdometerInit
open Turing

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

/-- Place one of finitely many actual statements into an arbitrary ambient
Boolean-tape program, preserving the ambient state component. -/
def statement (tape : Tape k → K) (labels : Label k → Λ) (exit : Option Λ) :
    Label k → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .seed j => .push (tape (.current j)) (fun _ => false)
      (.goto (fun _ => labels (.copyOut j)))
  | .copyOut j => Reduction.MachineTransfer.loopAt (tape .radix) (tape .scratch)
      id false (labels (.copyOut j)) (some (labels (.copyBack j)))
  | .copyBack j => MachineCopy.forkLoop (tape .scratch) (tape .radix) (tape (.remaining j))
      false (labels (.copyBack j)) (some (labels (.trim j)))
  | .trim j => .pop (tape (.remaining j)) (fun state _ => state)
      (.goto (fun _ => labelAt labels (j.val+1)))
  | .done => .load (fun state => (state.1,none))
      (Reduction.MachineTransfer.exitAt (tape .radix) exit)

end UniqueGamesTheorem.Foundations.Complexity.MachineOdometerInit

/-!
A concrete sequential composition of two finite TM2 programs. The first output
is transferred to a temporary stack and then to the second input. Both loops
execute actual transitions and reset their shared register on exit. Static
renaming changes neither a stack word nor the number of executed transitions.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineBinaryInputReductionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The complete ordinary-binary input bridge. Arbitrary raw input bits are first
validated and retained, or replaced by a fixed contradictory encoded formula.
The checked occurrence-index renamer then emits the inherited dense 3CNF
codec. Both stages and their physical handoff have actual polynomial-time
finite-alphabet machine certificates.

This is a bridge for the explicit ordinary binary 3SAT language. It is not the
PCP construction, a proof of that construction's runtime, or an NP-hardness
assertion about the eventual 2-to-1 target.
-/

namespace UniqueGamesTheorem.Explicit.MachineOutputContract

open UniqueGamesTheorem.Foundations
open Target
open scoped BigOperators

/-! A canonical orientation from the false side to the true side. Injectivity
is on occurrence indices, so two distinct list entries cannot be parallel even
when their constraint tables are different. -/

/-- The full forward and inverse tables already prove the permutation laws. -/
def permutationEquiv {q : Nat} (table : PermutationTable q) : Equiv.Perm (Fin q) where
  toFun label := table.images[label]
  invFun label := table.inverseImages[label]
  left_inv := table.leftInverse
  right_inv := table.rightInverse

namespace SimpleBipartite

variable {q : Nat} {game : Instance q} (presentation : SimpleBipartite game)

/-- The list presentation yields exactly the bipartite occurrence abstraction
used by the subdivision proof, without quotienting or discarding occurrences. -/
def toBipartiteGame : BipartiteGame
    {v : Fin game.vertices // presentation.side v = false}
    {v : Fin game.vertices // presentation.side v = true}
    (Fin game.constraints.length) (Fin q) where
  left i := ⟨game.constraints[i].source, presentation.sourceSide i⟩
  right i := ⟨game.constraints[i].target, presentation.targetSide i⟩
  permutation i := permutationEquiv game.constraints[i].permutation
  simple := by
    intro i j same
    apply presentation.endpoints_injective
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst same)
    · exact congrArg Subtype.val (congrArg Prod.snd same)

/-- Two independently chosen side labelings give one total labeling because
every vertex has exactly one Boolean side. Isolated vertices cause no exception. -/
def mergeLabelings
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q) :
    Fin game.vertices → Fin q := fun v =>
  if h : presentation.side v = false then left ⟨v, h⟩
  else right ⟨v, by cases hs : presentation.side v <;> simp_all⟩

@[simp] theorem mergeLabelings_left
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q)
    (v : {v : Fin game.vertices // presentation.side v = false}) :
    presentation.mergeLabelings left right v.val = left v := by
  simp [mergeLabelings, v.property]

@[simp] theorem mergeLabelings_right
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q)
    (v : {v : Fin game.vertices // presentation.side v = true}) :
    presentation.mergeLabelings left right v.val = right v := by
  simp [mergeLabelings, v.property]

theorem toBipartiteGame_count (labeling : Fin game.vertices → Fin q) :
    presentation.toBipartiteGame.satisfiedCount
      (fun v => labeling v.val) (fun v => labeling v.val) =
      countSatisfied labeling game.constraints := by
  have count := Integration.GapSemantics.countSatisfied_ofFn labeling
    (fun i : Fin game.constraints.length => game.constraints[i])
  simp only [Fin.getElem_fin, List.ofFn_getElem] at count
  rw [count]
  unfold BipartiteGame.satisfiedCount
  apply Finset.sum_congr rfl
  intro e _
  simp [toBipartiteGame, permutationEquiv, Constraint.satisfied]
  rfl

theorem toBipartiteGame_count_merge
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q) :
    presentation.toBipartiteGame.satisfiedCount left right =
      countSatisfied (presentation.mergeLabelings left right) game.constraints := by
  simpa only [mergeLabelings_left, mergeLabelings_right] using
    presentation.toBipartiteGame_count (presentation.mergeLabelings left right)

theorem toBipartiteGame_maxSatisfied :
    presentation.toBipartiteGame.maxSatisfied =
      Integration.InstanceValue.maxSatisfied game := by
  classical
  apply Nat.le_antisymm
  · unfold BipartiteGame.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [presentation.toBipartiteGame_count_merge labeling.1 labeling.2]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied _ _
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [← presentation.toBipartiteGame_count labeling]
    exact BipartiteGame.satisfiedCount_le_maxSatisfied _ _ _

/-- The abstract bipartite game and the actual serialized list instance have
exactly the same value, including the same denominator of edge occurrences. -/
theorem toBipartiteGame_value :
    presentation.toBipartiteGame.value = Integration.InstanceValue.value game := by
  unfold BipartiteGame.value Integration.InstanceValue.value
  rw [presentation.toBipartiteGame_maxSatisfied]
  simp

end SimpleBipartite

/-! Every parameter, coordinate identification, program, and polynomial is
fixed before the input quantifier. The identity input encoding measures runtime
in the original raw bit length, including sparse binary variable names. -/

end UniqueGamesTheorem.Explicit.MachineOutputContract

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductTarget
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Explicit numbered permutation-table outputs for bipartite graphs and products.
All numbering maps are supplied as actual equivalences; the product uses the
computable radix equivalence with division/remainder inverse, never an arbitrary
finite-type enumeration. The value bridge preserves every list occurrence.
-/

namespace UniqueGamesTheorem.Explicit.ProductTarget

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

/-- Full forward and inverse tables of an explicit finite permutation. -/
def fullTable (p : Equiv.Perm (Fin q)) : PermutationTable q where
  images := Vector.ofFn p
  inverseImages := Vector.ofFn p.symm
  leftInverse a := by simp
  rightInverse a := by simp

@[simp] theorem fullTable_images (p : Equiv.Perm (Fin q)) (a : Fin q) :
    (fullTable p).images[a] = p a := by simp [fullTable]

@[simp] theorem permutationEquiv_fullTable (p : Equiv.Perm (Fin q)) :
    permutationEquiv (fullTable p) = p := by
  ext a
  simp [permutationEquiv, fullTable]

/-- One explicitly addressed row, with a separately supplied complete table. -/
def row (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ≃ Fin N)
    (edges : Fin M ≃ E) (tables : E → PermutationTable q) (i : Fin M) :
    Constraint N q where
  source := vertices (Sum.inl (G.left (edges i)))
  target := vertices (Sum.inr (G.right (edges i)))
  permutation := tables (edges i)

def render (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ≃ Fin N)
    (edges : Fin M ≃ E) (tables : E → PermutationTable q) (hM : 0 < M) :
    Instance q where
  vertices := N
  constraints := List.ofFn (row G vertices edges tables)
  nonempty := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp only [List.length_ofFn, List.length_nil] at hlength
    omega

@[simp] theorem render_length (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M) :
    (render G vertices edges tables hM).constraints.length = M := by
  simp [render]

end UniqueGamesTheorem.Explicit.ProductTarget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
The independent graph product in the last step of the reduction.

Edges are tuples of actual base edges.  The endpoint maps remain injective,
the edge law is exactly uniform, and the associated game agrees with ordinary
parallel repetition for every pair of local strategies, including strategies
depending on their whole question tuples.  Only the completeness lower bound
uses coordinatewise strategies; no repetition soundness bound is assumed here.
-/

namespace UniqueGamesTheorem.Explicit

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

namespace BipartiteGame

variable {L R E A : Type*}

/-- Independent tuples of edges and labels.  The two endpoint types keep the
two parts separate, even when the base sets happen to have the same type. -/
def product (G : BipartiteGame L R E A) (t : ℕ) :
    BipartiteGame (Fin t → L) (Fin t → R) (Fin t → E) (Fin t → A) where
  left e i := G.left (e i)
  right e i := G.right (e i)
  permutation e :=
    { toFun := fun a i => G.permutation (e i) (a i)
      invFun := fun a i => (G.permutation (e i)).symm (a i)
      left_inv := fun a => by funext i; exact (G.permutation (e i)).left_inv (a i)
      right_inv := fun a => by funext i; exact (G.permutation (e i)).right_inv (a i) }
  simple := by
    intro e f h
    funext i
    apply G.simple
    exact Prod.ext (congrFun (congrArg Prod.fst h) i)
      (congrFun (congrArg Prod.snd h) i)

@[simp] theorem product_left (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (i : Fin t) : (G.product t).left e i = G.left (e i) := rfl

@[simp] theorem product_right (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (i : Fin t) : (G.product t).right e i = G.right (e i) := rfl

@[simp] theorem product_permutation (G : BipartiteGame L R E A) (t : ℕ)
    (e : Fin t → E) (a : Fin t → A) (i : Fin t) :
    (G.product t).permutation e a i = G.permutation (e i) (a i) := rfl

section

variable [Fintype L] [Fintype R] [Fintype E] [Fintype A] [Nonempty E]

/-- Each actual edge has equal weight. Simplicity makes the acceptance
predicate at its endpoint pair exactly its permutation constraint. -/
def toGame (G : BipartiteGame L R E A) : Game L R A A := by
  classical
  exact
    { questions := (FiniteDistribution.uniform E).pushforward
        (fun e => (G.left e, G.right e))
      accepts := fun x y a b => decide
        (∃ e, G.left e = x ∧ G.right e = y ∧ b = G.permutation e a) }

@[simp] theorem toGame_accepts_on_edge (G : BipartiteGame L R E A)
    (e : E) (a b : A) :
    G.toGame.accepts (G.left e) (G.right e) a b = true ↔
      b = G.permutation e a := by
  classical
  simp only [toGame, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hleft, hright, h⟩
    have hf : f = e := G.simple (Prod.ext hleft hright)
    simpa [hf] using h
  · intro h
    exact ⟨e, rfl, rfl, h⟩

/-- At most one accepting right answer exists for each local question pair
and left answer, including question pairs with zero edge weight. -/
theorem toGame_isProjection (G : BipartiteGame L R E A) :
    UniqueGamesTheorem.Repetition.IsProjection G.toGame := by
  classical
  intro x y a b b' hb hb'
  simp only [toGame, decide_eq_true_eq] at hb hb'
  obtain ⟨e, heL, heR, he⟩ := hb
  obtain ⟨f, hfL, hfR, hf⟩ := hb'
  have hef : e = f := G.simple (Prod.ext (heL.trans hfL.symm) (heR.trans hfR.symm))
  subst f
  exact he.trans hf.symm

/-- Acceptance probability directly on the uniform occurrence set. -/
def occurrenceSuccess (G : BipartiteGame L R E A)
    (strategy : Strategy L R A A) : ℝ := by
  classical
  exact (FiniteDistribution.uniform E).probability
    (fun e => decide (G.Satisfied strategy.1 strategy.2 e))

theorem toGame_success (G : BipartiteGame L R E A)
    (strategy : Strategy L R A A) :
    G.toGame.success strategy = G.occurrenceSuccess strategy := by
  classical
  unfold Game.success occurrenceSuccess
  change ((FiniteDistribution.uniform E).pushforward _).probability _ = _
  rw [FiniteDistribution.probability_pushforward]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  change G.toGame.accepts (G.left e) (G.right e)
      (strategy.1 (G.left e)) (strategy.2 (G.right e)) = true ↔
    decide (G.Satisfied strategy.1 strategy.2 e) = true
  constructor
  · intro h
    exact decide_eq_true ((G.toGame_accepts_on_edge e _ _).mp h)
  · intro h
    exact (G.toGame_accepts_on_edge e _ _).mpr (of_decide_eq_true h)

/-- The probabilistic game evaluates the same unweighted edge fraction as
the explicit graph's integer occurrence counter. -/
theorem toGame_success_eq_satisfiedCount [DecidableEq A]
    (G : BipartiteGame L R E A) (strategy : Strategy L R A A) :
    G.toGame.success strategy =
      (G.satisfiedCount strategy.1 strategy.2 : ℝ) / Fintype.card E := by
  classical
  rw [toGame_success, satisfiedCount_eq_sum_satisfied]
  unfold occurrenceSuccess FiniteDistribution.probability FiniteDistribution.uniform
  simp only [decide_eq_true_eq, Nat.cast_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : G.Satisfied strategy.1 strategy.2 e <;> simp [h]

/-- The graph construction agrees with the ordinary independent repeated
game for arbitrary local tuple strategies. This is the soundness interface. -/
theorem product_success_eq_repetition (G : BipartiteGame L R E A) (t : ℕ)
    (strategy : Strategy (Fin t → L) (Fin t → R) (Fin t → A) (Fin t → A)) :
    (G.product t).toGame.success strategy = (G.toGame.repetition t).success strategy := by
  classical
  let : DecidableEq (Fin t → A) := fun a b => Classical.propDecidable (a = b)
  rw [toGame_success]
  unfold occurrenceSuccess Game.success
  change (FiniteDistribution.uniform (Fin t → E)).probability _ =
    ((G.toGame.questions.iid t).transport (Game.tupleQuestionEquiv t)).probability _
  rw [FiniteDistribution.probability_transport]
  change _ = (((FiniteDistribution.uniform E).pushforward
    (fun e => (G.left e, G.right e))).iid t).probability _
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.probability_pushforward,
    FiniteDistribution.iid_uniform]
  congr 1
  funext edges
  apply Bool.eq_iff_iff.mpr
  change _ ↔
    (G.toGame.repetition t).accepts (fun i => G.left (edges i))
      (fun i => G.right (edges i))
      (strategy.1 (fun i => G.left (edges i)))
      (strategy.2 (fun i => G.right (edges i))) = true
  rw [decide_eq_true_eq, Game.repetition_accepts_iff]
  constructor
  · intro h i
    apply (G.toGame_accepts_on_edge (edges i) _ _).mpr
    exact congrFun h i
  · intro h
    funext i
    exact (G.toGame_accepts_on_edge (edges i) _ _).mp (h i)

theorem product_coordinate_success (G : BipartiteGame L R E A) (t : ℕ)
    (strategy : Strategy L R A A) :
    (G.product t).toGame.success (Game.repeatStrategy strategy t) =
      G.toGame.success strategy ^ t := by
  rw [product_success_eq_repetition, Game.success_repeatStrategy]

/-- Scalar union bound, proved for the actual base success probability. -/
theorem one_sub_mul_one_sub_le_pow {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (t : ℕ) :
    1 - (t : ℝ) * (1 - p) ≤ p ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hmul := mul_le_mul_of_nonneg_right ih hp0
      have hnonneg : 0 ≤ (t : ℝ) * (1 - p) ^ 2 := by positivity
      rw [pow_succ]
      push_cast
      nlinarith

/-- The coordinatewise honest labeling loses at most `t` times the base
error. This does not restrict the strategies covered by the soundness bridge. -/
theorem product_coordinate_completeness (G : BipartiteGame L R E A) (t : ℕ)
    (strategy : Strategy L R A A) {error : ℝ}
    (hcomplete : 1 - error ≤ G.toGame.success strategy) :
    1 - (t : ℝ) * error ≤
      (G.product t).toGame.success (Game.repeatStrategy strategy t) := by
  rw [product_coordinate_success]
  have hbound := one_sub_mul_one_sub_le_pow
    (G.toGame.success_nonnegative strategy) (G.toGame.success_le_one strategy) t
  have hmul := mul_le_mul_of_nonneg_left hcomplete (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  linarith

variable [Nonempty A]

/-- The finite maximum over arbitrary local strategies is exactly the
explicit graph value used by the subdivision identity. -/
theorem toGame_value [DecidableEq A] (G : BipartiteGame L R E A) :
    G.toGame.value = G.value := by
  apply le_antisymm
  · apply (G.toGame.value_le_iff _).2
    intro strategy
    rw [toGame_success_eq_satisfiedCount, value]
    exact div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (G.satisfiedCount_le_maxSatisfied strategy.1 strategy.2))
      (Nat.cast_nonneg _)
  · obtain ⟨a, b, hab⟩ := G.maxSatisfied_attained
    have hs := G.toGame.success_le_value (a, b)
    rw [toGame_success_eq_satisfiedCount, hab] at hs
    exact hs

theorem product_value_eq_repetition (G : BipartiteGame L R E A) (t : ℕ) :
    (G.product t).toGame.value = (G.toGame.repetition t).value := by
  apply le_antisymm
  · apply ((G.product t).toGame.value_le_iff _).2
    intro strategy
    rw [product_success_eq_repetition]
    exact (G.toGame.repetition t).success_le_value strategy
  · apply ((G.toGame.repetition t).value_le_iff _).2
    intro strategy
    rw [← product_success_eq_repetition]
    exact (G.product t).toGame.success_le_value strategy

theorem product_completeness (G : BipartiteGame L R E A) (t : ℕ) {error : ℝ}
    (hcomplete : 1 - error ≤ G.toGame.value) :
    1 - (t : ℝ) * error ≤ (G.product t).toGame.value := by
  obtain ⟨strategy, hstrategy⟩ := G.toGame.exists_optimal_strategy
  have hs := G.product_coordinate_completeness t strategy (hstrategy.symm ▸ hcomplete)
  exact hs.trans ((G.product t).toGame.success_le_value _)

end

/-- A change of alphabet coordinates keeps endpoints and edge identities. -/
def relabel {B : Type*} (G : BipartiteGame L R E A) (e : A ≃ B) :
    BipartiteGame L R E B where
  left := G.left
  right := G.right
  permutation f := e.symm.trans ((G.permutation f).trans e)
  simple := G.simple

section

variable {B : Type*} [Fintype L] [Fintype R] [Fintype E]
  [Fintype A] [Fintype B] [Nonempty E]

/-- Alphabet coordinates are changed locally at each endpoint. -/
theorem relabel_success (G : BipartiteGame L R E A) (e : A ≃ B)
    (strategy : Strategy L R B B) :
    (G.relabel e).toGame.success strategy =
      G.toGame.success (fun x => e.symm (strategy.1 x), fun y => e.symm (strategy.2 y)) := by
  classical
  rw [toGame_success, toGame_success]
  unfold occurrenceSuccess
  congr 1
  funext f
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have h' := of_decide_eq_true h
    apply decide_eq_true
    apply e.injective
    simpa only [Satisfied, relabel, Equiv.trans_apply, Equiv.apply_symm_apply] using h'
  · intro h
    have h' := of_decide_eq_true h
    apply decide_eq_true
    simpa only [Satisfied, relabel, Equiv.trans_apply, Equiv.apply_symm_apply] using congrArg e h'

theorem relabel_success_forward (G : BipartiteGame L R E A) (e : A ≃ B)
    (strategy : Strategy L R A A) :
    (G.relabel e).toGame.success
      (fun x => e (strategy.1 x), fun y => e (strategy.2 y)) =
      G.toGame.success strategy := by
  rw [relabel_success]
  congr 1
  apply Prod.ext <;> funext x <;> simp

theorem relabel_value [Nonempty A] [Nonempty B]
    (G : BipartiteGame L R E A) (e : A ≃ B) :
    (G.relabel e).toGame.value = G.toGame.value := by
  apply le_antisymm
  · apply ((G.relabel e).toGame.value_le_iff _).2
    intro strategy
    rw [relabel_success]
    exact G.toGame.success_le_value _
  · apply (G.toGame.value_le_iff _).2
    intro strategy
    rw [← G.relabel_success_forward e strategy]
    exact (G.relabel e).toGame.success_le_value _

end

/-- The explicit binary vector coordinates of the final alphabet. The
coordinate order is `(base bit, repetition coordinate)`. -/
def binaryProductEquiv (ell t : ℕ) :
    (Fin t → Fin ell → ZMod 2) ≃+ (Fin (ell * t) → ZMod 2) where
  toFun a j := a ((finProdFinEquiv.symm j : Fin ell × Fin t).2)
    ((finProdFinEquiv.symm j : Fin ell × Fin t).1)
  invFun a i j := a (finProdFinEquiv (j, i))
  left_inv a := by funext i j; simp
  right_inv a := by
    funext j
    change a (finProdFinEquiv (finProdFinEquiv.symm j : Fin ell × Fin t)) = a j
    rw [Equiv.apply_symm_apply]
  map_add' _ _ := rfl

end BipartiteGame

end UniqueGamesTheorem.Explicit

/-!
The actual ordered full-table instance of the final independent product.
Caller-supplied coordinate numberings are used explicitly. Edges are emitted in
increasing mixed-radix address, with division/remainder decoding; the two vertex
blocks and the entire permutation table use the same coordinate convention.
-/

namespace UniqueGamesTheorem.Explicit.ProductOutput

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

variable {L R E : Type*} {l r m q : ℕ}

/-- Explicit tuple address, with coordinate zero the least significant digit. -/
def tupleCode {X : Type*} {n : ℕ} (code : X ≃ Fin n) (t : ℕ) :
    (Fin t → X) ≃ Fin (n ^ t) where
  toFun f := finFunctionFinEquiv (fun i => code (f i))
  invFun a i := code.symm (finFunctionFinEquiv.symm a i)
  left_inv f := by funext i; simp
  right_inv a := by simp

@[simp] theorem tupleCode_apply {X : Type*} {n : ℕ} (code : X ≃ Fin n)
    (t : ℕ) (f : Fin t → X) :
    tupleCode code t f = finFunctionFinEquiv (fun i => code (f i)) := rfl

@[simp] theorem tupleCode_symm_apply {X : Type*} {n : ℕ} (code : X ≃ Fin n)
    (t : ℕ) (a : Fin (n ^ t)) (i : Fin t) :
    (tupleCode code t).symm a i = code.symm (finFunctionFinEquiv.symm a i) := rfl

def vertexCode (leftCode : L ≃ Fin l) (rightCode : R ≃ Fin r) (t : ℕ) :
    ((Fin t → L) ⊕ (Fin t → R)) ≃ Fin (l ^ t + r ^ t) :=
  (Equiv.sumCongr (tupleCode leftCode t) (tupleCode rightCode t)).trans finSumFinEquiv

@[simp] theorem vertexCode_left (leftCode : L ≃ Fin l) (rightCode : R ≃ Fin r)
    (t : ℕ) (x : Fin t → L) :
    vertexCode leftCode rightCode t (Sum.inl x) =
      Fin.castAdd (r ^ t) (tupleCode leftCode t x) := rfl

@[simp] theorem vertexCode_right (leftCode : L ≃ Fin l) (rightCode : R ≃ Fin r)
    (t : ℕ) (y : Fin t → R) :
    vertexCode leftCode rightCode t (Sum.inr y) =
      Fin.natAdd (l ^ t) (tupleCode rightCode t y) := rfl

/-- The label tuple is numbered by its explicit base-q radix code. -/
def graph (G : BipartiteGame L R E (Fin q)) (t : ℕ) :
    BipartiteGame (Fin t → L) (Fin t → R) (Fin t → E) (Fin (q ^ t)) :=
  (G.product t).relabel finFunctionFinEquiv

def tables (G : BipartiteGame L R E (Fin q)) (t : ℕ)
    (edges : Fin t → E) : PermutationTable (q ^ t) :=
  fullTable ((graph G t).permutation edges)

/-- A row indexed by its actual place in the emitted edge list. -/
def outputRow (G : BipartiteGame L R E (Fin q))
    (leftCode : L ≃ Fin l) (rightCode : R ≃ Fin r) (edgeCode : E ≃ Fin m)
    (t : ℕ) (i : Fin (m ^ t)) : Constraint (l ^ t + r ^ t) (q ^ t) :=
  ProductTarget.row (graph G t) (vertexCode leftCode rightCode t)
    (tupleCode edgeCode t).symm (tables G t) i

/-- The executable output list has one row for each radix edge-tuple address. -/
def output (G : BipartiteGame L R E (Fin q))
    (leftCode : L ≃ Fin l) (rightCode : R ≃ Fin r) (edgeCode : E ≃ Fin m)
    (t : ℕ) (hm : 0 < m) : Instance (q ^ t) :=
  render (graph G t) (vertexCode leftCode rightCode t)
    (tupleCode edgeCode t).symm (tables G t) (pow_pos hm t)

@[simp] theorem output_constraints (G : BipartiteGame L R E (Fin q))
    (leftCode : L ≃ Fin l) (rightCode : R ≃ Fin r) (edgeCode : E ≃ Fin m)
    (t : ℕ) (hm : 0 < m) :
    (output G leftCode rightCode edgeCode t hm).constraints =
      List.ofFn (outputRow G leftCode rightCode edgeCode t) := rfl

@[simp] theorem output_length (G : BipartiteGame L R E (Fin q))
    (leftCode : L ≃ Fin l) (rightCode : R ≃ Fin r) (edgeCode : E ≃ Fin m)
    (t : ℕ) (hm : 0 < m) :
    (output G leftCode rightCode edgeCode t hm).constraints.length = m ^ t := by
  exact List.length_ofFn

end UniqueGamesTheorem.Explicit.ProductOutput

/-!
Machine-friendly product numbering on the common global vertex base.
Both endpoints use the same radix, so the machine needs neither a right-side
subtraction nor a final offset. Mixed-side tuples are isolated vertices. For a
positive repetition count the first coordinate supplies a total bipartition.
-/

namespace UniqueGamesTheorem.Explicit.ProductPaddedOutput

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

namespace Embedded

variable {L R E : Type*} {q N M : ℕ}

def row (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ↪ Fin N)
    (edges : Fin M ≃ E) (i : Fin M) : Constraint N q where
  source := vertices (Sum.inl (G.left (edges i)))
  target := vertices (Sum.inr (G.right (edges i)))
  permutation := fullTable (G.permutation (edges i))

def render (G : BipartiteGame L R E (Fin q)) (vertices : (L ⊕ R) ↪ Fin N)
    (edges : Fin M ≃ E) (hM : 0 < M) : Instance q where
  vertices := N
  constraints := List.ofFn (row G vertices edges)
  nonempty := by
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hlen
    omega

@[simp] theorem render_length (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    (render G vertices edges hM).constraints.length = M := by simp [render]

end Embedded

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

local instance instNonemptyFinLengthConstraintVerticesConstraints_re79100_1 : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
abbrev Left := {v : Fin H.vertices // presentation.side v = false}
abbrev Right := {v : Fin H.vertices // presentation.side v = true}

def graph (t : ℕ) : BipartiteGame
    (Fin t → Left H presentation) (Fin t → Right H presentation)
    (Fin t → Fin H.constraints.length) (Fin (q ^ t)) :=
  (presentation.toBipartiteGame.product t).relabel finFunctionFinEquiv

/-- The two genuine product vertex sets embed into the common global radix
space. Opposite sides cannot collide because the repetition count is positive. -/
def vertices (t : ℕ) (ht : 0 < t) :
    ((Fin t → Left H presentation) ⊕ (Fin t → Right H presentation)) ↪
      Fin (H.vertices ^ t) where
  toFun := Sum.elim
    (fun x => finFunctionFinEquiv (fun i => (x i).val))
    (fun y => finFunctionFinEquiv (fun i => (y i).val))
  inj' := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        funext i
        exact Subtype.ext (congrFun (finFunctionFinEquiv.injective h) i)
      | inr y =>
        have hfirst := congrFun (finFunctionFinEquiv.injective h) ⟨0, ht⟩
        have hs := congrArg presentation.side hfirst
        rw [(x ⟨0, ht⟩).property, (y ⟨0, ht⟩).property] at hs
        cases hs
    | inr x =>
      cases y with
      | inl y =>
        have hfirst := congrFun (finFunctionFinEquiv.injective h) ⟨0, ht⟩
        have hs := congrArg presentation.side hfirst
        rw [(x ⟨0, ht⟩).property, (y ⟨0, ht⟩).property] at hs
        cases hs
      | inr y =>
        apply congrArg Sum.inr
        funext i
        exact Subtype.ext (congrFun (finFunctionFinEquiv.injective h) i)

def outputRow (t : ℕ) (ht : 0 < t) (i : Fin (H.constraints.length ^ t)) :
    Constraint (H.vertices ^ t) (q ^ t) :=
  Embedded.row (graph H presentation t) (vertices H presentation t ht)
    finFunctionFinEquiv.symm i

def output (t : ℕ) (ht : 0 < t) : Instance (q ^ t) :=
  Embedded.render (graph H presentation t) (vertices H presentation t ht)
    finFunctionFinEquiv.symm (pow_pos H.constraintCount_positive t)

@[simp] theorem output_vertices (t : ℕ) (ht : 0 < t) :
    (output H presentation t ht).vertices = H.vertices ^ t := rfl

@[simp] theorem output_constraints (t : ℕ) (ht : 0 < t) :
    (output H presentation t ht).constraints = List.ofFn (outputRow H presentation t ht) := rfl

@[simp] theorem output_length (t : ℕ) (ht : 0 < t) :
    (output H presentation t ht).constraints.length = H.constraints.length ^ t := by simp

end UniqueGamesTheorem.Explicit.ProductPaddedOutput

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineDrainManyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def localInstruction (source : K) (labels : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineDrain.drain source (labels ()) exit

def instruction (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) :
    Label chosen → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction (LocalLabel (K := K)) (fun _ => ())
    localInstruction chosen labels exit

/-- Exact execution of all concrete drains in the supplied ambient program. -/
theorem trace (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps chosen base]
      (some ⟨entry chosen labels exit, (ambient, register), base⟩) =
    some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := LocalLabel (K := K)) (main := fun _ => ())
    (localInstruction := localInstruction (σ := σ)) (result := result) (cost := cost)
    program (fun _ : Data K => True) (fun data => (ambient, data.2)) (fun data => data.1)
    chosen (by intros; trivial)
    (by
      intro source _ localLabels localExit atLocal data _
      rcases data with ⟨tapes, reg⟩
      simpa only [cost, result, Function.update_eq_self] using
        MachineDrain.drainTrace source (localLabels ()) localExit program (atLocal ())
          tapes (tapes source) ambient reg)
    labels exit atLabels (base, register) trivial
  simpa only [sequence_steps, sequence_result, entry] using run

end UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceMachine
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

/-- Read one unary field, stopping at its zero delimiter. -/
def fieldLoop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.load (fun state => (state.1, none))
        (Reduction.MachineTransfer.exitAt destination exit)))

theorem fieldStep_delimiter (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), fieldTapes source destination base (false :: suffix) output⟩ =
      some ⟨exit, (ambient, none), fieldTapes source destination base suffix output⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (fieldTapes source destination base (false :: suffix) output)) = _
  rw [atLoop]
  cases exit <;>
    simp [fieldLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, hne, update_field_source]

theorem fieldStep_true (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), fieldTapes source destination base (true :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some true),
        fieldTapes source destination base input (true :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (fieldTapes source destination base (true :: input) output)) = _
  rw [atLoop]
  simp [fieldLoop, TM2.stepAux, hne, update_field_source, update_field_destination]

/-- Exactly one transition per unary bit, including its terminating delimiter. -/
theorem fieldLoopTrace (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        fieldTapes source destination base suffix (List.replicate n true ++ output)⟩ := by
  induction n generalizing output register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
      fieldStep_delimiter source destination hne loopLabel exit program atLoop
        base suffix output ambient register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base (true :: (encodeWord n ++ suffix)) output⟩) = _
    rw [fieldStep_true source destination hne loopLabel exit program atLoop, ih]
    have hrotate : List.replicate n true ++ true :: output =
        true :: (List.replicate n true ++ output) := by
      calc
        _ = (List.replicate n true ++ [true]) ++ output := by simp
        _ = List.replicate (n + 1) true ++ output := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ, List.cons_append]
    rw [hrotate]

def fieldInTime (source destination : K) (hne : source ≠ destination)
    (startLabel loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = fieldStart destination loopLabel)
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some startLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        fieldTapes source destination base suffix (encodeWord n ++ base destination)⟩)
      (n + 2) where
  steps := n + 2
  evals_in_steps := by
    have hbase : fieldTapes source destination base (encodeWord n ++ suffix)
        (base destination) = base := by rw [← hinput, fieldTapes_self]
    conv_lhs => rw [← hbase]
    change (MachineComposition.advance (TM2.step program))^[(n + 1) + 1]
      (some ⟨some startLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) (base destination)⟩) = _
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some startLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) (base destination)⟩) = _
    rw [fieldStartStep source destination startLabel loopLabel program atStart,
      fieldLoopTrace source destination hne loopLabel exit program atLoop]
    simp [encodeWord, List.append_assoc]
  steps_le_m := Nat.le_refl _

/-- Stack state after one completed field, retaining an arbitrary old destination. -/
def afterField (source destination : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) : K → List Bool :=
  fieldTapes source destination base suffix (encodeWord n ++ base destination)

def fourTapes (source : K) (destination : Fin 4 → K) (base : K → List Bool)
    (a b c d : Nat) (suffix : List Bool) : K → List Bool :=
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  afterField source (destination 3) t₂ d suffix

/-- Four fields are separated by actual finite-stack transitions. The stated
bound is exactly their serialized length plus four delimiter-seeding steps. -/
def fourFieldsInTime (source : K) (destination : Fin 4 → K)
    (hsep : ∀ j, source ≠ destination j)
    (start loopLabel : Fin 4 → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : ∀ j, program (start j) = fieldStart (destination j) (loopLabel j))
    (atLoop : ∀ j, program (loopLabel j) =
      fieldLoop source (destination j) (loopLabel j) (fieldNext start exit j))
    (base : K → List Bool) (a b c d : Nat) (suffix : List Bool)
    (hinput : base source = encodeWords [a, b, c, d] ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (start 0), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), fourTapes source destination base a b c d suffix⟩)
      (a + b + c + d + 8) := by
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  have h₀ : base source = encodeWord a ++ (encodeWords [b, c, d] ++ suffix) := by
    simpa only [encodeWords, List.append_assoc] using hinput
  have h₁ : t₀ source = encodeWord b ++ (encodeWords [c, d] ++ suffix) := by
    simp [t₀, afterField, hsep, encodeWords, List.append_assoc]
  have h₂ : t₁ source = encodeWord c ++ (encodeWords [d] ++ suffix) := by
    simp [t₁, afterField, hsep, encodeWords, List.append_assoc]
  have h₃ : t₂ source = encodeWord d ++ suffix := by
    simp [t₂, afterField, hsep, encodeWords]
  have p₀ := fieldInTime source (destination 0) (hsep 0) (start 0) (loopLabel 0)
    (some (start 1)) program (atStart 0) (atLoop 0) base a
    (encodeWords [b, c, d] ++ suffix) h₀ ambient register
  have p₁ := fieldInTime source (destination 1) (hsep 1) (start 1) (loopLabel 1)
    (some (start 2)) program (atStart 1) (atLoop 1) t₀ b
    (encodeWords [c, d] ++ suffix) h₁ ambient none
  have p₂ := fieldInTime source (destination 2) (hsep 2) (start 2) (loopLabel 2)
    (some (start 3)) program (atStart 2) (atLoop 2) t₁ c
    (encodeWords [d] ++ suffix) h₂ ambient none
  have p₃ := fieldInTime source (destination 3) (hsep 3) (start 3) (loopLabel 3)
    exit program (atStart 3) (atLoop 3) t₂ d suffix h₃ ambient none
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by have h := p.steps_le_m; omega
  }

end UniqueGamesTheorem.Foundations.Hastad.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLookupCore
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control for destructive unary-indexed table lookup. The guard decreases
the index even when the table is exhausted. Selection tests for an empty table
before writing the destination. All tests inspect just one finite head register.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

/-- Six fixed labels and a single optional-bit register, independent of input. -/
def program (index source destination : K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard index .skip .select
  | .skip => discard source .skip .guard
  | .select => select source destination .copy .rejected
  | .copy => Hastad.SourceMachine.fieldLoop source destination .copy (some .accepted)
  | .accepted => .halt
  | .rejected => .halt

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLookupDiscard
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

/-- A normalized tape form for the field-discard trace. -/
theorem discardTrace_update (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register),
        Function.update base source (encodeWord n ++ suffix)⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  induction n generalizing register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
      discardStep_delimiter source loopLabel returnLabel program atLoop
        base suffix ambient register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        Function.update base source (true :: (encodeWord n ++ suffix))⟩) = _
    rw [discardStep_true source loopLabel returnLabel program atLoop, ih]

/-- Discard exactly the first encoded field, in one transition per payload bit
plus one transition for its delimiter. No condition is imposed on other tapes. -/
theorem discardTrace (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  have hbase : Function.update base source (encodeWord n ++ suffix) = base := by
    funext p
    by_cases hp : p = source
    · subst p; simp [hinput]
    · simp [hp]
  have h := discardTrace_update source loopLabel returnLabel program atLoop
    base n suffix ambient register
  rw [hbase] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUnaryAffineAt
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def scan (source scratch destination : K) (coefficient : Nat) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun s head => (s.1,head))
    (.branch (fun s => s.2.getD false)
      (.push scratch (fun _ => true)
        (pushWord destination (List.replicate coefficient true) (.goto (fun _ => scanLabel))))
      (.branch (fun s => s.2.isSome)
        (.push source (fun _ => false) (finish restoreLabel))
        (finish restoreLabel)))

def seed (destination : K) (offset : Nat) (scanLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (encodeWord offset).reverse (.goto (fun _ => scanLabel))

def tapes (source scratch destination : K) (base : K → List Bool)
    (input saved output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input saved output

@[simp] theorem tapes_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output source = input :=
  MachineCopy.forkTapes_source source scratch destination hs hd base input saved output

@[simp] theorem tapes_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output scratch = saved :=
  MachineCopy.forkTapes_left source scratch destination hsd base input saved output

@[simp] theorem tapes_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output destination = output :=
  MachineCopy.forkTapes_right source scratch destination base input saved output

theorem update_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) source replacement =
      tapes source scratch destination base replacement saved output := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, h₀, hsd]
    · by_cases h₂ : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, h₀]
      · simp [tapes, MachineCopy.forkTapes, h₀, h₁, h₂]

theorem update_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) scratch replacement =
      tapes source scratch destination base input replacement output := by
  funext k
  by_cases h : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, hsd]
  · by_cases h' : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, h]
    · simp [tapes, MachineCopy.forkTapes, h, h']

theorem update_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) destination replacement =
      tapes source scratch destination base input saved replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem prepend_replicate_word (c b : Nat) (suffix : List Bool) :
    List.replicate c true ++ (encodeWord b ++ suffix) =
      encodeWord (c + b) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

theorem scan_step_succ (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord (a + 1) ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some scanLabel, (ambient,some true), tapes source scratch destination base
        (encodeWord a ++ suffix) (true :: saved) (encodeWord (coefficient + b) ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord (a + 1) ++ suffix = true :: (encodeWord a ++ suffix) by
    simp [encodeWord, List.replicate_succ]]
  simp [scan, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source source scratch destination hs hd hsd, tapes_scratch _ _ _ hsd,
    update_scratch _ _ _ hsd, stepAux_pushWord, tapes_destination,
    prepend_replicate_word, update_destination]

theorem scan_step_zero (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord 0 ++ suffix = false :: suffix from rfl]
  simp [scan, finish, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source source scratch destination hs hd hsd]

theorem scanTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[a + 1]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) saved (encodeWord b ++ output)⟩) =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) (List.replicate a true ++ saved)
        (encodeWord (coefficient * a + b) ++ output)⟩ := by
  induction a generalizing b saved register with
  | zero =>
      simpa using scan_step_zero source scratch destination hs hd hsd coefficient scanLabel
        restoreLabel program atScan base b suffix saved output ambient register
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ source scratch destination hs hd hsd coefficient scanLabel restoreLabel
        program atScan]
      rw [ih]
      have hval : coefficient * a + (coefficient + b) = coefficient * (a + 1) + b := by
        rw [Nat.mul_succ]; omega
      rw [hval]
      have hsave : List.replicate a true ++ true :: saved = List.replicate (a + 1) true ++ saved := by
        simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
      rw [hsave]

theorem restoreTapes (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (a value : Nat) (suffix output : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base (encodeWord 0 ++ suffix)
        (List.replicate a true) (encodeWord value ++ output))
      [] (encodeWord a ++ suffix) =
      tapes source scratch destination base (encodeWord a ++ suffix) [] (encodeWord value ++ output) := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k
      simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hs, hsd]
    · by_cases h₂ : k = destination
      · subst k
        simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hd, Ne.symm hsd]
      · simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, h₀, h₁, h₂]

theorem affineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1)]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩) =
      some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩ := by
  have hscan := scanTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    program atScan base a b suffix [] output ambient register
  simp only [List.append_nil] at hscan
  let mid := tapes source scratch destination base (encodeWord 0 ++ suffix)
    (List.replicate a true) (encodeWord (coefficient * a + b) ++ output)
  have hrestore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm hs)
    id false restoreLabel exit program atRestore mid ambient none
  change (advance (TM2.step program))^[(mid scratch).length + 1]
    (some ⟨some restoreLabel,(ambient,none),mid⟩) = _ at hrestore
  have hsaved : mid scratch = List.replicate a true := by
    simp [mid, tapes, hsd]
  have hsource : mid source = encodeWord 0 ++ suffix := by
    simp [mid, tapes, hs, hd]
  rw [hsaved, hsource] at hrestore
  simp only [List.length_replicate, List.reverse_replicate, List.map_id] at hrestore
  have hword : List.replicate a true ++ (encodeWord 0 ++ suffix) = encodeWord a ++ suffix := by
    simp [encodeWord, List.append_assoc]
  rw [hword] at hrestore
  simp only [mid, restoreTapes source scratch destination hs hd hsd] at hrestore
  rw [show 2 * (a + 1) = (a + 1) + (a + 1) by omega, Function.iterate_add_apply, hscan]
  exact hrestore

/-- Include the literal offset prefix. The caller supplies an arbitrary output
suffix, not a precomputed address; all runtime arithmetic occurs on the tapes. -/
theorem seededAffineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient offset : Nat) (seedLabel scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program seedLabel = seed destination offset scanLabel)
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord a ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1) + 1]
      (some ⟨some seedLabel, (ambient,register), base⟩) =
      some ⟨exit, (ambient,none),
        Function.update base destination (encodeWord (coefficient * a + offset) ++ base destination)⟩ := by
  have hseed : TM2.step program ⟨some seedLabel,(ambient,register),base⟩ =
      some ⟨some scanLabel,(ambient,register),
        Function.update base destination (encodeWord offset ++ base destination)⟩ := by
    change some (TM2.stepAux (program seedLabel) _ _) = _
    rw [atSeed, seed, stepAux_pushWord]
    simp only [List.reverse_reverse, TM2.stepAux]
  have hrun := affineTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    exit program atScan atRestore base a offset suffix (base destination) ambient register
  have hframe (word : List Bool) :
      tapes source scratch destination base (encodeWord a ++ suffix) [] word =
        Function.update base destination word := by
    rw [← sourceWord, ← scratchEmpty]
    simp only [tapes, MachineCopy.forkTapes, Function.update_eq_self]
  rw [hframe, hframe] at hrun
  rw [Function.iterate_succ_apply]
  simp only [advance_some]
  rw [hseed]
  exact hrun

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLookupLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing
open MachineComposition

variable {K σ : Type} [DecidableEq K]

theorem guard_step_succ (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) input output⟩ =
      some ⟨some .skip, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord, List.replicate_succ, update_index]

theorem guard_step_zero (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ =
      some ⟨some .select, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord]

theorem select_step_nonempty (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) (hinput : input ≠ [])
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .select, (ambient, register),
        tapes index source destination base counter input output⟩ =
      some ⟨some .copy, (ambient, input.head?),
        tapes index source destination base counter input (false :: output)⟩ := by
  change some (TM2.stepAux (program index source destination .select) _ _) = _
  cases input with
  | nil => exact (hinput rfl).elim
  | cons head tail =>
    simp [program, select, Hastad.SourceMachine.fieldStart, TM2.stepAux,
      tapes_source, hsd, update_destination]

theorem copyTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 1]
      (some ⟨some .copy, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) (false :: output)⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  have h := Hastad.SourceMachine.fieldLoopTrace source destination hsd
    Label.copy (some Label.accepted) (program index source destination) rfl
    (Function.update base index counter) n suffix (false :: output) ambient register
  simpa only [Hastad.SourceMachine.fieldTapes, tapes, encodeWord,
    List.append_assoc, List.singleton_append] using h

theorem selectTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .select, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [select_step_nonempty index source destination hsd base counter
    (encodeWord n ++ suffix) output (by simp [encodeWord]) ambient register]
  exact copyTrace index source destination hsd base counter n suffix output ambient _

theorem skipCycleTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i n : Nat) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) (encodeWord n ++ suffix) output⟩) =
      some ⟨some .guard, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) suffix output⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [guard_step_succ index source destination his hid]
  have h := discardTrace source Label.skip Label.guard
    (program index source destination) rfl
    (tapes index source destination base (encodeWord i ++ indexSuffix)
      (encodeWord n ++ suffix) output) n suffix (by simp [hsd]) ambient none
  simpa only [update_source index source destination hsd] using h

/-- A successful positional lookup scans precisely its prior and selected
field. The suffix is arbitrary and is retained byte for byte. -/
theorem successPrefixTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List Nat) (value : Nat)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[
        (encodeWords prior).length + prior.length + value + 3]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord prior.length ++ indexSuffix)
        (encodeWords prior ++ (encodeWord value ++ suffix)) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) suffix (encodeWord value ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [encodeWords, List.length_nil, Nat.zero_add, List.nil_append]
    rw [show value + 3 = (value + 2) + 1 by omega, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [guard_step_zero index source destination his hid]
    exact selectTrace index source destination hsd base _ value suffix output ambient none
  | cons n prior ih =>
    simp only [encodeWords, List.length_cons, List.length_append, encodeWord_length]
    rw [show n + 1 + (encodeWords prior).length + (prior.length + 1) + value + 3 =
      ((encodeWords prior).length + prior.length + value + 3) + (n + 2) by omega,
      Function.iterate_add_apply]
    rw [List.append_assoc,
      skipCycleTrace index source destination his hid hsd base prior.length n]
    exact ih none

/-- Successful array access, with explicit selected value and preserved framing. -/
theorem lookupTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp selected).1
  have hlength : (values.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hsource : encodeWords (values.take i) ++
      (encodeWord value ++ (encodeWords (values.drop (i + 1)) ++ suffix)) =
      encodeWords values ++ suffix := by
    rw [MachineLookupSpec.encoded_selected_split values i value selected]
    simp only [List.append_assoc]
  have htime : MachineLookupSpec.steps values i =
      (encodeWords (values.take i)).length + i + value + 3 := by
    rw [MachineLookupSpec.steps_eq_scannedBits_of_some values i value selected,
      MachineLookupSpec.scannedBits_of_some values i value selected]
    omega
  have h := successPrefixTrace index source destination his hid hsd base (values.take i)
    value indexSuffix (encodeWords (values.drop (i + 1)) ++ suffix) output ambient register
  rw [hlength, hsource] at h
  simpa only [htime] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

/-- Tape roles: original table, unary query, scan work, output, copy scratch. -/
def initialTapes (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord index ++ indexSuffix) workSuffix output

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat)
    (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord 0 ++ indexSuffix)
    (encodeWords (values.drop (index + 1)) ++ workSuffix) (encodeWord value ++ output)

theorem lookupFramedHaltTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (MachineLookup.program index source destination)))^[
      MachineLookupSpec.steps values i + 1]
      (some ⟨some MachineLookup.Label.guard, (ambient,register),
        MachineLookup.tapes index source destination base (encodeWord i ++ indexSuffix)
          (encodeWords values ++ suffix) output⟩) =
      some ⟨none, (ambient,none), MachineLookup.tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  rw [Function.iterate_succ_apply',
    MachineLookup.lookupTrace_some index source destination his hid hsd
      base values i value selected indexSuffix suffix output ambient register]
  simp only [advance_some, TM2.step, MachineLookup.program, TM2.stepAux]

/-- Code-level interfaces specify the actual two copy loops and six lookup
instructions in the caller's program. No execution premise is supplied. -/
theorem preservingLookupTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1]
      (some ⟨some firstLabel, (ambient,register),
        initialTapes tape base i indexSuffix workSuffix output⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  let start := initialTapes tape base i indexSuffix workSuffix output
  have htable : start (tape 0) = encodeWords values := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 0 3 (by decide))] using tableWord
  have hs : start (tape 4) = [] := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 4 1 (by decide)) (hd 4 2 (by decide)) (hd 4 3 (by decide))] using scratchEmpty
  have hwork : start (tape 2) = workSuffix := by
    simp only [start, initialTapes, MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide))]
  have hcopy := MachineCopy.copyTrace (tape 0) (tape 2) (tape 4)
    (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
    firstLabel secondLabel (some (lookupLabels .guard)) program atFirst atSecond start hs ambient register
  rw [htable, hwork] at hcopy
  simp only [start, initialTapes, MachineLookup.update_source _ _ _ (hd 2 3 (by decide))] at hcopy
  have hlookup := MachineSubroutine.trace lookupLabels exit
    (MachineLookup.program (tape 1) (tape 2) (tape 3)) program atLookup
    (MachineLookupSpec.steps values i + 1) _ _
    (lookupFramedHaltTrace_some (tape 1) (tape 2) (tape 3)
      (hd 1 2 (by decide)) (hd 1 3 (by decide)) (hd 2 3 (by decide))
      base values i value selected indexSuffix workSuffix output ambient none)
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hlookup
  rw [show 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 =
      (MachineLookupSpec.steps values i + 1) + 2 * ((encodeWords values).length + 1) by omega,
    Function.iterate_add_apply]
  change (advance (TM2.step program))^[MachineLookupSpec.steps values i + 1]
    ((advance (TM2.step program))^[2 * ((encodeWords values).length + 1)]
      (some ⟨some firstLabel, (ambient,register),
        MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
          (encodeWord i ++ indexSuffix) workSuffix output⟩)) = _
  rw [hcopy]
  exact hlookup

theorem preservingLookup_steps_le (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) :
    2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 ≤
      5 * (encodeWords values).length + 3 := by
  have ht := MachineLookupSpec.steps_le_input_encoding_size values i
  have hi := MachineLookupSpec.index_length_le values i value selected
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def instruction (source : K) (tape : Fin 5 → K) (coefficient offset : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed (tape 1) offset (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source (tape 4) (tape 1)
      coefficient (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt (tape 4) source id false
      (labels .restore) (some (labels .copyFirst))
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false
      (labels .copySecond) (some (labels (.lookup .guard)))
  | .lookup l => MachineSubroutine.statement (fun q => labels (.lookup q)) exit
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

def steps (values : List Nat) (a coefficient offset : Nat) : Nat :=
  (2 * (a + 1) + 1) +
    (2 * ((encodeWords values).length + 1) +
      MachineLookupSpec.steps values (coefficient * a + offset) + 1)

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) : K → List Bool :=
  MachinePreservingLookup.finalTapes tape base values index value
    (base (tape 1)) (base (tape 2)) (base (tape 3))

theorem initialTapes_eq_update (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (i : Nat) :
    MachinePreservingLookup.initialTapes tape base i
      (base (tape 1)) (base (tape 2)) (base (tape 3)) =
      Function.update base (tape 1) (encodeWord i ++ base (tape 1)) := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  funext k
  by_cases h₁ : k = tape 1
  · subst k
    simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
      hd 1 2 (by decide), hd 1 3 (by decide)]
  · by_cases h₂ : k = tape 2
    · subst k
      simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁,
        hd 2 3 (by decide)]
    · by_cases h₃ : k = tape 3
      · subst k
        simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁]
      · simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁, h₂, h₃]

/-- An exact trace for the actual composite instructions. `atLabels` specifies
the caller's finite program; there is no execution or runtime premise. -/
theorem affineLookupTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (coefficient offset : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape coefficient offset labels exit l)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values) (scratchEmpty : base (tape 4) = [])
    (a : Nat) (suffix : List Bool) (sourceWord : base source = encodeWord a ++ suffix)
    (value : Nat) (selected : values[coefficient * a + offset]? = some value)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values a coefficient offset]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values (coefficient * a + offset) value⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have haffine := MachineUnaryAffineAt.seededAffineTrace source (tape 4) (tape 1)
    (outside 4) (outside 1) (hd 4 1 (by decide)) coefficient offset
    (labels .seed) (labels .scan) (labels .restore) (some (labels .copyFirst))
    program (atLabels .seed) (atLabels .scan) (atLabels .restore)
    base a suffix sourceWord scratchEmpty ambient register
  have hlookup := MachinePreservingLookup.preservingLookupTrace tape distinct
    (labels .copyFirst) (labels .copySecond) (fun q => labels (.lookup q)) exit
    program (atLabels .copyFirst) (atLabels .copySecond) (fun q => atLabels (.lookup q))
    base values tableWord scratchEmpty (coefficient * a + offset) value selected
    (base (tape 1)) (base (tape 2)) (base (tape 3)) ambient none
  rw [initialTapes_eq_update tape distinct] at hlookup
  rw [steps, Nat.add_comm, Function.iterate_add_apply, haffine]
  exact hlookup

theorem steps_le (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value) :
    steps values a coefficient offset ≤ 2 * a + 5 * (encodeWords values).length + 6 := by
  have h := MachinePreservingLookup.preservingLookup_steps_le values
    (coefficient * a + offset) value selected
  unfold steps
  omega

theorem finalTapes_other (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) (k : K)
    (h₁ : k ≠ tape 1) (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) :
    finalTapes tape base values index value k = base k :=
  MachineLookup.tapes_other _ _ _ _ h₁ h₂ h₃ _ _ _ _

theorem finalTapes_output (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) :
    finalTapes tape base values index value (tape 3) = encodeWord value ++ base (tape 3) :=
  MachineLookup.tapes_destination _ _ _ _ _ _ _

end UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

/-!
A fixed-width gather from an input-resident table. Every coordinate index lives
on a unary tape. The coefficient and coordinate-dependent offsets alone live
in finite control. Actual preserving affine lookup instructions read each
requested field, and the proof below composes their traces. This is the gather
phase of product-row construction, before the fixed-width Horner phase.
-/

namespace UniqueGamesTheorem.Explicit.MachineProductGather

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def instruction : (width : Nat) → (Tape width → K) → Nat → (Fin width → Nat) →
    (Label width → Λ) → Option Λ → Label width →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | 0, placement, _, _, _, exit, _ =>
    .load (fun state => (state.1, none))
      (UniqueGamesTheorem.Reduction.MachineTransfer.exitAt (placement (.inl 0)) exit)
  | width + 1, placement, coefficient, offsets, labels, exit, label =>
    match label with
    | .inl inner => MachineAffineLookup.instruction (placement (.inr (.inl 0)))
        (placement ∘ lookupRole width) coefficient (offsets 0)
        (fun l => labels (.inl l)) (some (labels (.inr (entry width)))) inner
    | .inr inner => instruction width (placement ∘ shift width) coefficient
        (fun i => offsets i.succ) (fun l => labels (.inr l)) exit inner

def steps (values : List Nat) (coefficient : Nat) :
    (width : Nat) → (Fin width → Nat) → (Fin width → Nat) → Nat
  | 0, _, _ => 1
  | width + 1, indices, offsets =>
    MachineAffineLookup.steps values (indices 0) coefficient (offsets 0) +
      steps values coefficient width (fun i => indices i.succ) (fun i => offsets i.succ)

def finalTapes (values : List Nat) (coefficient : Nat) :
    (width : Nat) → (Tape width → K) → (Fin width → Nat) →
      (Fin width → Nat) → (Fin width → Nat) → (K → List Bool) → K → List Bool
  | 0, _, _, _, _, base => base
  | width + 1, placement, indices, offsets, fields, base =>
    finalTapes values coefficient width (placement ∘ shift width)
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
        (coefficient * indices 0 + offsets 0) (fields 0))

theorem finalTapes_other (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (indices offsets fields : Fin width → Nat)
    (base : K → List Bool) (k : K)
    (query : k ≠ placement (.inl 1)) (scan : k ≠ placement (.inl 2))
    (outputs : ∀ i, k ≠ placement (.inr (.inr i))) :
    finalTapes values coefficient width placement indices offsets fields base k = base k := by
  induction width generalizing base with
  | zero => rfl
  | succ width ih =>
    rw [finalTapes]
    rw [ih (placement ∘ shift width) (fun i => indices i.succ)
      (fun i => offsets i.succ) (fun i => fields i.succ) _ query scan
      (fun i => outputs i.succ)]
    exact MachineAffineLookup.finalTapes_other _ _ _ _ _ k query scan (outputs 0)

theorem gatherTrace (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction width placement coefficient offsets labels exit l)
    (base : K → List Bool) (suffixes : Fin width → List Bool)
    (tableWord : base (placement (.inl 0)) = encodeWords values)
    (scratchEmpty : base (placement (.inl 3)) = [])
    (sourceWords : ∀ i, base (placement (.inr (.inl i))) = encodeWord (indices i) ++ suffixes i)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values coefficient width indices offsets]
      (some ⟨some (labels (entry width)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        finalTapes values coefficient width placement indices offsets fields base⟩ := by
  induction width generalizing base register with
  | zero =>
    change some (TM2.stepAux (program (labels ())) _ _) = _
    erw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, finalTapes,
      UniqueGamesTheorem.Reduction.MachineTransfer.exitAt]
  | succ width ih =>
    have hd (a b : Tape (width + 1)) (hne : a ≠ b) : placement a ≠ placement b :=
      fun h => hne (distinct h)
    have outside : ∀ i : Fin 5,
        placement (.inr (.inl 0)) ≠ (placement ∘ lookupRole width) i := by
      intro i
      apply hd
      fin_cases i <;> simp [lookupRole]
    have first := MachineAffineLookup.affineLookupTrace (placement (.inr (.inl 0)))
      (placement ∘ lookupRole width) (distinct.comp (lookupRole_injective width)) outside
      coefficient (offsets 0) (fun l => labels (.inl l))
      (some (labels (.inr (entry width)))) program (fun l => atLabels (.inl l))
      base values tableWord scratchEmpty (indices 0) (suffixes 0) (sourceWords 0)
      (fields 0) (selected 0) ambient register
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    have frame (k : Tape (width + 1)) (h1 : k ≠ .inl 1) (h2 : k ≠ .inl 2)
        (h3 : k ≠ .inr (.inr 0)) : mid (placement k) = base (placement k) :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ (hd _ _ h1) (hd _ _ h2) (hd _ _ h3)
    have middleTable : mid (placement (.inl 0)) = encodeWords values := by
      rw [frame (.inl 0) (by simp) (by simp) (by simp)]
      exact tableWord
    have middleScratch : mid (placement (.inl 3)) = [] := by
      rw [frame (.inl 3) (by simp) (by simp) (by simp)]
      exact scratchEmpty
    have middleSources (i : Fin width) : mid (placement (.inr (.inl i.succ))) =
        encodeWord (indices i.succ) ++ suffixes i.succ := by
      rw [frame (.inr (.inl i.succ)) (by simp) (by simp) (by simp)]
      exact sourceWords i.succ
    have rest := ih (placement ∘ shift width) (distinct.comp (shift_injective width))
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (fun i => selected i.succ) (fun l => labels (.inr l))
      (fun l => atLabels (.inr l)) mid (fun i => suffixes i.succ)
      middleTable middleScratch middleSources none
    simp only [entry]
    rw [steps, Nat.add_comm, Function.iterate_add_apply, first]
    exact rest

/-- Every output is the physically gathered unary field, with its old suffix
preserved. This identifies the operands consumed by the Horner phase. -/
theorem finalTapes_field (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (i : Fin width) :
    finalTapes values coefficient width placement indices offsets fields base
      (placement (.inr (.inr i))) =
      encodeWord (fields i) ++ base (placement (.inr (.inr i))) := by
  induction width generalizing base with
  | zero => exact Fin.elim0 i
  | succ width ih =>
    have hd (a b : Tape (width + 1)) (hne : a ≠ b) : placement a ≠ placement b :=
      fun h => hne (distinct h)
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    refine Fin.cases ?_ (fun j => ?_) i
    · change finalTapes values coefficient width (placement ∘ shift width)
        (fun j => indices j.succ) (fun j => offsets j.succ) (fun j => fields j.succ)
        mid (placement (.inr (.inr 0))) = _
      rw [finalTapes_other values coefficient width _ _ _ _ mid _
        (hd _ _ (by simp [shift])) (hd _ _ (by simp [shift]))
        (fun j => hd _ _ (by simp [shift, Fin.ext_iff]))]
      exact MachineAffineLookup.finalTapes_output _ _ _ _ _
    · change finalTapes values coefficient width (placement ∘ shift width)
        (fun j => indices j.succ) (fun j => offsets j.succ) (fun j => fields j.succ)
        mid ((placement ∘ shift width) (.inr (.inr j))) = _
      rw [ih (placement ∘ shift width) (distinct.comp (shift_injective width))
        (fun j => indices j.succ) (fun j => offsets j.succ) (fun j => fields j.succ) mid j]
      congr 1
      exact MachineAffineLookup.finalTapes_other (placement ∘ lookupRole width) base values
        (coefficient * indices 0 + offsets 0) (fields 0)
        (placement (.inr (.inr j.succ)))
        (hd _ _ (by simp [lookupRole])) (hd _ _ (by simp [lookupRole]))
        (hd _ _ (by simp [lookupRole, Fin.ext_iff]))

/-- For fixed width, gather time is linear in the encoded table size plus
coordinate magnitudes. Query and scan debris is never rescanned. -/
theorem steps_le (values : List Nat) (coefficient width magnitude : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (bounded : ∀ i, indices i ≤ magnitude) :
    steps values coefficient width indices offsets ≤
      width * (2 * magnitude + 5 * (encodeWords values).length + 6) + 1 := by
  induction width with
  | zero => simp [steps]
  | succ width ih =>
    have first := MachineAffineLookup.steps_le values (indices 0) coefficient (offsets 0)
      (fields 0) (selected 0)
    have rest := ih (fun i => indices i.succ) (fun i => offsets i.succ)
      (fun i => fields i.succ) (fun i => selected i.succ) (fun i => bounded i.succ)
    have hb := bounded 0
    rw [steps, Nat.add_mul, Nat.one_mul]
    omega

end UniqueGamesTheorem.Explicit.MachineProductGather

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductGatherBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual work stacks left by the preserving gather. These
bounds justify clearing the query/scan remnants after each product field;
they are consequences of the exact tape formulas, not runtime assumptions. -/

namespace UniqueGamesTheorem.Explicit.MachineProductGather

open UniqueGamesTheorem.Foundations.Complexity

variable {K : Type} [DecidableEq K]

theorem affine_final_length (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (values : List Nat) (index value : Nat) (selected : values[index]? = some value)
    (base : K → List Bool) (k : K) :
    (MachineAffineLookup.finalTapes tape base values index value k).length ≤
      (base k).length + (encodeWords values).length + 1 := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  have hov := MachineLookupSpec.output_length_le values index value selected
  have hdrop : (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
    have split : encodeWords (values.take (index + 1)) ++
        encodeWords (values.drop (index + 1)) = encodeWords values := by
      rw [← encodeWords_append, List.take_append_drop]
    have h := congrArg List.length split
    simp only [List.length_append] at h
    omega
  by_cases h1 : k = tape 1
  · subst k
    simp only [MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes_index _ _ _ (hd 1 2 (by decide)) (hd 1 3 (by decide)),
      List.length_append, encodeWord_length]
    omega
  · by_cases h2 : k = tape 2
    · subst k
      simp only [MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
        MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide)), List.length_append]
      omega
    · by_cases h3 : k = tape 3
      · subst k
        rw [MachineAffineLookup.finalTapes_output, List.length_append]
        omega
      · rw [MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h1 h2 h3]
        omega

/-- One field query adds at most one table's worth of bits to any tape.
A width-fold gather therefore has a uniform linear-in-width space bound. -/
theorem finalTapes_length (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (k : K) :
    (finalTapes values coefficient width placement indices offsets fields base k).length ≤
      (base k).length + width * ((encodeWords values).length + 1) := by
  induction width generalizing base with
  | zero => simp [finalTapes]
  | succ width ih =>
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    have first := affine_final_length (placement ∘ lookupRole width)
      (distinct.comp (lookupRole_injective width)) values
      (coefficient * indices 0 + offsets 0) (fields 0) (selected 0) base k
    have rest := ih (placement ∘ shift width) (distinct.comp (shift_injective width))
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (fun i => selected i.succ) mid
    change (finalTapes values coefficient width (placement ∘ shift width)
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ) mid k).length ≤ _
    rw [Nat.add_mul, Nat.one_mul]
    dsimp only [mid] at rest
    dsimp only [mid]
    omega

end UniqueGamesTheorem.Explicit.MachineProductGather

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUnaryAddAt
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

def finish (destination : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun state => (state.1, none)) (exitAt destination exit)

/-- A fixed finite statement; arithmetic is performed by the physical unary tapes. -/
def loop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.branch (fun state => state.2.isSome)
        (.push source (fun _ => false) (finish destination exit))
        (finish destination exit)))

/-- A caller's tape frame with the two unary prefixes and their unread suffixes. -/
def unaryTapes (source destination : K) (base : K → List Bool) (a b : Nat)
    (sourceSuffix destinationSuffix : List Bool) : K → List Bool :=
  tapesAt source destination base (encodeWord a ++ sourceSuffix)
    (encodeWord b ++ destinationSuffix)

@[simp] theorem unaryTapes_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix source =
      encodeWord a ++ sourceSuffix := by
  simp [unaryTapes, distinct]

@[simp] theorem unaryTapes_destination (source destination : K)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix destination =
      encodeWord b ++ destinationSuffix := by
  simp [unaryTapes]

theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  funext k
  by_cases hd : k = destination
  · subst k
    simp [tapesAt]
  · simp [tapesAt, hd]

theorem stepAux_true (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool)
    (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (tapesAt source destination base (true :: input) output) =
      ⟨some loopLabel, (ambient, some true),
        tapesAt source destination base input (true :: output)⟩ := by
  simp [loop, TM2.stepAux, distinct, update_source, update_destination]

/-- The zero branch restores the delimiter, clears the register, and exits. -/
theorem stepAux_false (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool)
    (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (tapesAt source destination base (false :: input) output) =
      ⟨exit, (ambient, none), tapesAt source destination base (false :: input) output⟩ := by
  cases exit <;> simp [loop, finish, exitAt, TM2.stepAux, distinct, update_source]

theorem stepAux_succ (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool) (a b : Nat)
    (sourceSuffix destinationSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix) =
      ⟨some loopLabel, (ambient, some true),
        unaryTapes source destination base a (b + 1) sourceSuffix destinationSuffix⟩ := by
  simpa only [unaryTapes, encodeWord, List.replicate_succ, List.cons_append] using
    stepAux_true source destination distinct loopLabel exit base
      (encodeWord a ++ sourceSuffix) (encodeWord b ++ destinationSuffix) ambient register

theorem stepAux_zero (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool) (b : Nat)
    (sourceSuffix destinationSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (unaryTapes source destination base 0 b sourceSuffix destinationSuffix) =
      ⟨exit, (ambient, none),
        unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ := by
  simpa only [unaryTapes, encodeWord, List.replicate_zero, List.nil_append,
    List.singleton_append] using
    stepAux_false source destination distinct loopLabel exit base sourceSuffix
      (encodeWord b ++ destinationSuffix) ambient register

theorem step_succ (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register),
      unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix⟩ =
      some ⟨some loopLabel, (ambient, some true),
        unaryTapes source destination base a (b + 1) sourceSuffix destinationSuffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix)) = _
  rw [atLoop, stepAux_succ source destination distinct]

theorem step_zero (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register),
      unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (unaryTapes source destination base 0 b sourceSuffix destinationSuffix)) = _
  rw [atLoop, stepAux_zero source destination distinct]

/-- Exactly `a` positive-bit transitions followed by the delimiter transition. -/
theorem addTrace (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[a + 1]
      (some ⟨some loopLabel, (ambient, register),
        unaryTapes source destination base a b sourceSuffix destinationSuffix⟩) =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩ := by
  induction a generalizing b register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      step_zero source destination distinct loopLabel exit program atLoop
        base b sourceSuffix destinationSuffix ambient register
  | succ a ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[a + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix⟩) = _
    rw [step_succ source destination distinct loopLabel exit program atLoop]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (b + 1) (some true)

/-- The same actual execution from a caller's supplied tape configuration. -/
theorem addFromTapes (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[a + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩ := by
  have hbase : unaryTapes source destination base a b sourceSuffix destinationSuffix =
      base := by
    simp only [unaryTapes, ← sourceInput, ← destinationInput, tapesAt_self]
  have h := addTrace source destination distinct loopLabel exit program atLoop
    base a b sourceSuffix destinationSuffix ambient register
  rw [hbase] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineTransducerCopy
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTransducerCopy

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ Q : Type} [DecidableEq K]

def emitter (destination : K) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (scanLabel : Λ) (control : Q) (symbol : Bool) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .load (fun state => ((state.1.1, transition control symbol), state.2))
    (pushWord destination (emit control symbol) (.goto fun _ => scanLabel))

abbrev tapes (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input scratchWord outputWord

theorem update_source (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      source replacement = tapes source scratch destination base replacement scratchWord outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, sourceScratch, sourceDestination]
  · by_cases ht : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceScratch, scratchDestination]
    · by_cases hd : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceDestination]
      · simp [tapes, MachineCopy.forkTapes, hs, ht, hd]

theorem update_scratch (source scratch destination : K)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      scratch replacement = tapes source scratch destination base input replacement outputWord := by
  funext k
  by_cases ht : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, scratchDestination]
  · by_cases hd : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm scratchDestination]
    · simp [tapes, MachineCopy.forkTapes, ht, hd]

theorem update_output (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      destination replacement = tapes source scratch destination base input scratchWord replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem scanStep_empty (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base [] scratchWord outputWord⟩ =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] scratchWord outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base [] scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source]

theorem scanStep_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩ =
      some ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord) outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base (symbol :: input) scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source, update_scratch]

theorem emitterStep (source scratch destination : K)
    (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (symbol : Bool) :
    TM2.step program ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
      tapes source scratch destination base input scratchWord outputWord⟩ =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input scratchWord
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change some (TM2.stepAux (program (emitterLabel control symbol)) ((ambient, control), some symbol)
    (tapes source scratch destination base input scratchWord outputWord)) = _
  rw [atEmitter]
  simp only [emitter, TM2.stepAux]
  rw [stepAux_pushWord]
  simp only [TM2.stepAux, MachineCopy.forkTapes_right]
  rw [update_output]

theorem twoSteps_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩) =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord)
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change (TM2.step program ⟨some scanLabel, ((ambient, control), register),
    tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩).bind
      (TM2.step program) = _
  rw [scanStep_cons source scratch destination sourceScratch sourceDestination scratchDestination
    initial scanLabel restoreLabel emitterLabel program atScan base symbol input scratchWord
    outputWord ambient control register]
  exact emitterStep source scratch destination transition emit scanLabel emitterLabel program
    atEmitter base input (symbol :: scratchWord) outputWord ambient control symbol

theorem scanTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * input.length + 1]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base input scratchWord outputWord⟩) =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] (input.reverse ++ scratchWord)
          ((Reduction.MachineTransducer.output transition emit control input).reverse ++ outputWord)⟩ := by
  induction input generalizing control scratchWord outputWord register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, Reduction.MachineTransducer.output, List.reverse_nil,
      List.nil_append] using
      scanStep_empty source scratch destination sourceScratch sourceDestination scratchDestination
        initial scanLabel restoreLabel emitterLabel program atScan base scratchWord outputWord
        ambient control register
  | cons symbol input ih =>
    rw [List.length_cons, show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega,
      Function.iterate_add_apply]
    rw [twoSteps_cons source scratch destination sourceScratch sourceDestination scratchDestination
      initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
      symbol input scratchWord outputWord ambient control register, ih]
    simp only [Reduction.MachineTransducer.output, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.singleton_append]

theorem restoreTapes (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (outputWord : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base [] (base source).reverse outputWord)
      [] (base source) = Function.update base destination outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [Reduction.MachineTransfer.tapesAt, sourceDestination]
  · by_cases ht : k = scratch
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch, scratchDestination, scratchEmpty]
    · by_cases hd : k = destination
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes,
          Ne.symm sourceDestination, Ne.symm scratchDestination]
      · simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes, hs, ht, hd]

theorem transduceCopyTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (atRestore : program restoreLabel =
      Reduction.MachineTransfer.loopAt scratch source id false restoreLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * (base source).length + 2]
      (some ⟨some scanLabel, ((ambient, control), register), base⟩) =
      some ⟨exit, ((ambient, initial), none),
        Function.update base destination
          ((Reduction.MachineTransducer.output transition emit control (base source)).reverse ++
            base destination)⟩ := by
  have scan := scanTrace source scratch destination sourceScratch sourceDestination scratchDestination
    initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
    (base source) (base scratch) (base destination) ambient control register
  have tapesSelf : tapes source scratch destination base (base source) (base scratch)
      (base destination) = base := MachineCopy.forkTapes_self source scratch destination base
  rw [tapesSelf] at scan
  simp only [scratchEmpty, List.append_nil] at scan
  let outputWord :=
    (Reduction.MachineTransducer.output transition emit control (base source)).reverse ++ base destination
  let scanned := tapes source scratch destination base [] (base source).reverse outputWord
  have restore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm sourceScratch)
    id false restoreLabel exit program atRestore scanned (ambient, initial) none
  change (MachineComposition.advance (TM2.step program))^[(scanned scratch).length + 1]
    (some ⟨some restoreLabel, ((ambient, initial), none), scanned⟩) = _ at restore
  have scratchWord : scanned scratch = (base source).reverse := by
    simp [scanned, scratchDestination]
  have sourceWord : scanned source = [] := by
    simp [scanned, sourceScratch, sourceDestination]
  rw [scratchWord, sourceWord] at restore
  simp only [List.map_id, List.reverse_reverse, List.append_nil, List.length_reverse] at restore
  rw [restoreTapes source scratch destination sourceScratch sourceDestination scratchDestination
    base scratchEmpty outputWord] at restore
  rw [show 3 * (base source).length + 2 =
    ((base source).length + 1) + (2 * (base source).length + 1) by omega,
    Function.iterate_add_apply, scan]
  exact restore

end UniqueGamesTheorem.Foundations.Complexity.MachineTransducerCopy

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineUnaryMultiply
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An actual five-stack unary multiplication subroutine. Both isolated input
fields are preserved. The product field prefixes the previous output stack;
the counter and scratch return empty and all other stacks are framed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type}

variable [DecidableEq K]

/-- Slots 0 and 1 contain the operands, 2 the output, 3 the counter, and
4 the reusable empty scratch. The code is independent of operand values. -/
def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .copyDrain => Reduction.MachineTransfer.loopAt (slots 1) (slots 4) id false
      (labels .copyDrain) (some (labels .copyFork))
  | .copyFork => MachineCopy.forkLoop (slots 4) (slots 1) (slots 3) false
      (labels .copyFork) (some (labels .seed))
  | .seed => .push (slots 2) (fun _ => false) (.goto fun _ => labels .guard)
  | .guard => MachineUnaryCounter.guard (slots 3) (labels .scan) (labels .finish)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore)
  | .emitFalse => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () false
  | .emitTrue => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () true
  | .restore => Reduction.MachineTransfer.loopAt (slots 4) (slots 0) id false
      (labels .restore) (some (labels .guard))
  | .finish => .pop (slots 3) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 2) exit)

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (product : ℕ) : K → List Bool :=
  Function.update base (slots 2) (encodeWord product ++ base (slots 2))

@[simp] theorem resultTapes_output (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ) :
    resultTapes slots base p (slots 2) = encodeWord p ++ base (slots 2) := by
  simp [resultTapes]

theorem output_encodeWord (a : ℕ) :
    Reduction.MachineTransducer.output transition payload () (encodeWord a) =
      List.replicate a true := by
  induction a with
  | zero => simp [encodeWord, Reduction.MachineTransducer.output, payload]
  | succ a ih =>
    simpa only [encodeWord, List.replicate_succ, List.cons_append,
      Reduction.MachineTransducer.output, payload, Bool.cond_true, transition,
      ite_true, if_true, List.singleton_append, List.nil_append] using congrArg (List.cons true) ih

theorem prepend_payload (a p : ℕ) (suffix : List Bool) :
    List.replicate a true ++ (encodeWord p ++ suffix) = encodeWord (a + p) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

/-- The accumulator is indexed by the remaining number of outer iterations. -/
def loopBase (slots : Fin 5 ↪ K) (base : K → List Bool) (a b r : ℕ) : K → List Bool :=
  resultTapes slots base (a * (b - r))

theorem bodyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b r : ℕ) (hr : r < b)
    (operand : base (slots 0) = encodeWord a) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[bodySteps a]
      (some (MachineCountedLoop.bodyConfiguration (slots 3) (labels .scan) []
        (fun _ => (ambient, ())) (loopBase slots base a b) r)) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) r) := by
  have h04 : slots 0 ≠ slots 4 := slots.injective.ne (by decide)
  have h02 : slots 0 ≠ slots 2 := slots.injective.ne (by decide)
  have h42 : slots 4 ≠ slots 2 := slots.injective.ne (by decide)
  have h03 : slots 0 ≠ slots 3 := slots.injective.ne (by decide)
  have h43 : slots 4 ≠ slots 3 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let start := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b (r + 1)) r []
  have hstartA : start (slots 0) = encodeWord a := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h03, h02, operand]
  have hstartScratch : start (slots 4) = [] := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h43, h42, scratchEmpty]
  have hscan : p (labels .scan) = MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore) := atLabels .scan
  have hemit : ∀ control bit, p (emitterLabel labels control bit) =
      MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) control bit := by
    intro control bit
    cases control
    cases bit <;> exact atLabels _
  have hrestore : p (labels .restore) = Reduction.MachineTransfer.loopAt (slots 4) (slots 0)
      id false (labels .restore) (some (labels .guard)) := atLabels .restore
  have hcopy := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 4) (slots 2)
    h04 h02 h42 () transition payload (labels .scan) (labels .restore) (emitterLabel labels)
    (some (labels .guard)) p hscan hemit hrestore start hstartScratch ambient () none
  rw [hstartA, output_encodeWord, List.reverse_replicate] at hcopy
  have hcount : a + a * (b - (r + 1)) = a * (b - r) := by
    have hr' : b - r = b - (r + 1) + 1 := by omega
    rw [hr']
    ring
  have hfinish : Function.update start (slots 2)
      (List.replicate a true ++ start (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b r) r [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp only [Function.update_self]
      simp only [start, MachineUnaryCounter.counterTapes_other (slots 3) (slots 2) h23,
        loopBase, resultTapes_output]
      rw [prepend_payload, hcount]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [start, MachineUnaryCounter.counterTapes, hk2]
      · simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  rw [hfinish] at hcopy
  simpa only [bodySteps, encodeWord, List.length_append, List.length_replicate,
    List.length_singleton, MachineCountedLoop.bodyConfiguration,
    MachineCountedLoop.guardConfiguration] using hcopy

/-- Exact execution in any ambient program containing the nine declared
statements. The body traces are derived from the actual copy transducer. -/
theorem multiplyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps a b]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
  have h13 : slots 1 ≠ slots 3 := slots.injective.ne (by decide)
  have h14 : slots 1 ≠ slots 4 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let copied := Function.update base (slots 3) (encodeWord b)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (b + 2)]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .seed), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 1) (slots 3) (slots 4) h13 h14 h34 false
      (labels .copyDrain) (labels .copyFork) (some (labels .seed)) p
      (atLabels .copyDrain) (atLabels .copyFork) base scratchEmpty (ambient, ()) register
    simpa only [copied, operandB, counterEmpty, List.append_nil, encodeWord, List.length_append,
      List.length_replicate, List.length_singleton, Nat.add_assoc, Nat.reduceAdd] using h
  have hseedTapes : Function.update copied (slots 2) (false :: copied (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b b) b [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h23, encodeWord]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [copied, MachineUnaryCounter.counterTapes, hk2]
      · simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), none), copied⟩) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) b) := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), none) copied) = _
    rw [atLabels .seed]
    change some (⟨some (labels .guard), ((ambient, ()), none),
      Function.update copied (slots 2) (false :: copied (slots 2))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
    rw [hseedTapes]
    rfl
  have hloop := MachineCountedLoop.loopTrace (slots 3) (labels .guard) (labels .scan)
    (labels .finish) p (atLabels .guard) [] (fun _ => (ambient, ())) (fun _ => none)
    (loopBase slots base a b) (fun _ => bodySteps a) b
    (fun r hr => bodyTrace slots labels exit p atLabels base a b r hr operandA scratchEmpty ambient)
  let finalCounter := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b 0) 0 []
  have hfinishTapes : Function.update finalCounter (slots 3) ((finalCounter (slots 3)).tail) =
      resultTapes slots base (a * b) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp [finalCounter, MachineUnaryCounter.counterTapes, encodeWord, resultTapes,
        Ne.symm h23, counterEmpty]
    · simp [finalCounter, MachineUnaryCounter.counterTapes, loopBase, hk3]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some (MachineCountedLoop.exitConfiguration (slots 3) (labels .finish) []
        (fun _ => (ambient, ())) (loopBase slots base a b))) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) finalCounter) = _
    rw [atLabels .finish]
    cases exit <;>
      simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using
        congrArg (fun tapes => some (⟨_, ((ambient, ()), none), tapes⟩ :
          TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
  rw [show steps a b = 1 + (MachineCountedLoop.totalSteps (fun _ => bodySteps a) b +
      (1 + 2 * (b + 2))) by rw [totalSteps_eq]; unfold steps bodySteps; ring]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    hcopy, hseed, hloop]
  exact hfinish

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryMultiply

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRadixStepLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
One actual Horner step on unary field stacks. Multiplication and addition are
executions of the same finite program. All three operands are preserved; only
the output stack receives a new field and both work stacks return empty.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRadixStep

open Turing

variable {K Λ σ : Type}

variable [DecidableEq K]

def statement (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .multiply label => MachineUnaryMultiply.statement (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) label
  | .digitDrain => Reduction.MachineTransfer.loopAt (slots 2) (slots 5) id false
      (labels .digitDrain) (some (labels .digitFork))
  | .digitFork => MachineCopy.forkLoop (slots 5) (slots 2) (slots 4) false
      (labels .digitFork) (some (labels .add))
  | .add => MachineUnaryAddAt.loop (slots 4) (slots 3) (labels .add) (some (labels .finish))
  | .finish => .pop (slots 4) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 3) exit)

def resultTapes (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) : K → List Bool :=
  Function.update base (slots 3) (encodeWord value ++ base (slots 3))

@[simp] theorem resultTapes_output (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) :
    resultTapes slots base value (slots 3) = encodeWord value ++ base (slots 3) := by
  simp [resultTapes]

/-- A concrete Horner execution. Caller hypotheses identify the finite code,
not an assumed execution or arithmetic oracle. -/
theorem radixStepTrace (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix acc digit]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  have h24 : slots 2 ≠ slots 4 := slots.injective.ne (by decide)
  have h25 : slots 2 ≠ slots 5 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h53 : slots 5 ≠ slots 3 := slots.injective.ne (by decide)
  have h45 : slots 4 ≠ slots 5 := slots.injective.ne (by decide)
  let multiplied := resultTapes slots base (radix * acc)
  have hmul : (MachineComposition.advance (TM2.step p))^[MachineUnaryMultiply.steps radix acc]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩ := by
    have h := MachineUnaryMultiply.multiplyTrace (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) p
      (fun l => atLabels (.multiply l)) base radix acc operandRadix operandAcc
      counterEmpty scratchEmpty ambient register
    simpa only [MachineUnaryMultiply.resultTapes, multiplySlots_two, multiplied, resultTapes] using h
  have hmulDigit : multiplied (slots 2) = encodeWord digit := by
    simp [multiplied, resultTapes, h23, operandDigit]
  have hmulCounter : multiplied (slots 4) = [] := by
    simp [multiplied, resultTapes, Ne.symm h34, counterEmpty]
  have hmulScratch : multiplied (slots 5) = [] := by
    simp [multiplied, resultTapes, h53, scratchEmpty]
  let copied := Function.update multiplied (slots 4) (encodeWord digit)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (digit + 2)]
      (some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩) =
      some ⟨some (labels .add), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 2) (slots 4) (slots 5) h24 h25 h45 false
      (labels .digitDrain) (labels .digitFork) (some (labels .add)) p
      (atLabels .digitDrain) (atLabels .digitFork) multiplied hmulScratch (ambient, ()) none
    simpa only [copied, hmulDigit, hmulCounter, List.append_nil, encodeWord,
      List.length_append, List.length_replicate, List.length_singleton,
      Nat.add_assoc, Nat.reduceAdd] using h
  have hcopiedCounter : copied (slots 4) = encodeWord digit ++ [] := by simp [copied]
  have hcopiedOutput : copied (slots 3) = encodeWord (radix * acc) ++ base (slots 3) := by
    simp [copied, multiplied, resultTapes, h34]
  let added := MachineUnaryAddAt.unaryTapes (slots 4) (slots 3) copied
    0 (digit + radix * acc) [] (base (slots 3))
  have hadd : (MachineComposition.advance (TM2.step p))^[digit + 1]
      (some ⟨some (labels .add), ((ambient, ()), none), copied⟩) =
      some ⟨some (labels .finish), ((ambient, ()), none), added⟩ :=
    MachineUnaryAddAt.addFromTapes (slots 4) (slots 3) (Ne.symm h34)
      (labels .add) (some (labels .finish)) p (atLabels .add) copied digit (radix * acc)
      [] (base (slots 3)) hcopiedCounter hcopiedOutput (ambient, ()) none
  have hfinishTapes : Function.update added (slots 4) ((added (slots 4)).tail) =
      resultTapes slots base (radix * acc + digit) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp only [Function.update_of_ne h34, added, MachineUnaryAddAt.unaryTapes_destination,
        resultTapes_output]
      rw [Nat.add_comm digit (radix * acc)]
    · by_cases hk4 : k = slots 4
      · subst k
        simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          resultTapes, encodeWord, Ne.symm h34, counterEmpty]
      · simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          copied, multiplied, resultTapes, hk3, hk4]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .finish), ((ambient, ()), none), added⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) added) = _
    rw [atLabels .finish]
    have hcfg := congrArg (fun tapes => some (⟨exit, ((ambient, ()), none), tapes⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
    cases exit <;> simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using hcfg
  rw [show steps radix acc digit =
      1 + ((digit + 1) + (2 * (digit + 2) + MachineUnaryMultiply.steps radix acc)) by
        unfold steps MachineUnaryMultiply.steps; ring]
  rw [Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ (digit + 1),
    Function.iterate_add_apply _ (2 * (digit + 2)), hmul, hcopy, hadd]
  exact hfinish

end UniqueGamesTheorem.Foundations.Complexity.MachineRadixStep

/-!
Fixed-width Horner traversal by actual radix steps. Two accumulators alternate:
a radix step writes into the empty alternate, then the previous accumulator is
consumed. The base, digit fields, and arbitrary external tapes are preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

/-- Consume an isolated unary field, including its delimiter. -/
def drainLoop (tape : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .pop tape (fun state bit => (state.1, bit))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt tape exit)))

variable [DecidableEq K]

def statement (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => .push (slots (.inl 1)) (fun _ => false)
      (.load (fun state => (state.1, none)) (.goto fun _ => labels (entryLabel width 0)))
  | .radix i inner => MachineRadixStep.statement (radixSlots slots i)
      (fun l => labels (.radix i l)) (some (labels (.clear i))) inner
  | .clear i => drainLoop (slots (.inl (accumulator (parity i.val))))
      (labels (.clear i)) (some (labels (entryLabel width (i.val + 1))))
  | .finishDrain => Reduction.MachineTransfer.loopAt
      (slots (.inl (accumulator (parity width)))) (slots (.inl 5)) id false
      (labels .finishDrain) (some (labels .finishRestore))
  | .finishRestore => Reduction.MachineTransfer.loopAt (slots (.inl 5)) (slots (.inl 3)) id false
      (labels .finishRestore) exit

def stageTapes (slots : Layout width ↪ K) (base : K → List Bool) (n acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl (accumulator (parity n)))) (encodeWord acc)

def resultTapes (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl 3)) (encodeWord acc ++ base (slots (.inl 3)))

theorem drainTrace (tape : K) (loopLabel : Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLoop : p loopLabel = drainLoop tape loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[n + 1]
      (some ⟨some loopLabel, ((ambient, ()), register),
        Function.update base tape (encodeWord n ++ suffix)⟩) =
      some ⟨exit, ((ambient, ()), none), Function.update base tape suffix⟩ := by
  induction n generalizing register with
  | zero =>
    change some (TM2.stepAux (p loopLabel) _ _) = _
    rw [atLoop]
    cases exit <;> simp [drainLoop, TM2.stepAux, encodeWord, Reduction.MachineTransfer.exitAt]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step p))^[n + 1]
      (some (TM2.stepAux (p loopLabel) _ _)) = _
    rw [atLoop]
    simp only [drainLoop, TM2.stepAux, Function.update_self, encodeWord,
      List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
      Option.getD_some, Function.update_idem]
    exact ih (some true)

/-- One genuine radix execution followed by a unary drain of its old input
accumulator. The new accumulator is left in the alternate physical tape. -/
theorem digitTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : Nat) (i : Fin width)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigit : base (slots (.inr i)) = encodeWord digit)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[stepCost radix acc digit]
      (some ⟨some (labels (.radix i (.multiply .copyDrain))), ((ambient, ()), register),
        stageTapes slots base i.val acc⟩) =
      some ⟨some (labels (entryLabel width (i.val + 1))), ((ambient, ()), none),
        stageTapes slots base (i.val + 1) (radix * acc + digit)⟩ := by
  let rs := radixSlots slots i
  let before := stageTapes slots base i.val acc
  let after := MachineRadixStep.resultTapes rs before (radix * acc + digit)
  have h01 : rs 0 ≠ rs 1 := rs.injective.ne (by decide)
  have h21 : rs 2 ≠ rs 1 := rs.injective.ne (by decide)
  have h31 : rs 3 ≠ rs 1 := rs.injective.ne (by decide)
  have h41 : rs 4 ≠ rs 1 := rs.injective.ne (by decide)
  have h51 : rs 5 ≠ rs 1 := rs.injective.ne (by decide)
  have hb : before (rs 0) = encodeWord radix := by
    change Function.update base (rs 1) (encodeWord acc) (rs 0) = _
    rw [Function.update_of_ne h01]
    exact operandRadix
  have ha : before (rs 1) = encodeWord acc := by
    exact Function.update_self _ _ _
  have hd : before (rs 2) = encodeWord digit := by
    change Function.update base (rs 1) (encodeWord acc) (rs 2) = _
    rw [Function.update_of_ne h21]
    exact operandDigit
  have hc : before (rs 4) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 4) = _
    rw [Function.update_of_ne h41]
    exact clean.counter
  have hs : before (rs 5) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 5) = _
    rw [Function.update_of_ne h51]
    exact clean.scratch
  have hout : before (rs 3) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 3) = _
    rw [Function.update_of_ne h31]
    exact clean.acc _
  have hradix := MachineRadixStep.radixStepTrace rs (fun l => labels (.radix i l))
    (some (labels (.clear i))) p (fun l => atLabels (.radix i l)) before radix acc digit
    hb ha hd hc hs ambient register
  have hold : after (rs 1) = encodeWord acc := by
    change Function.update before (rs 3) _ (rs 1) = _
    rw [Function.update_of_ne (Ne.symm h31), ha]
  have hstart : Function.update after (rs 1) (encodeWord acc ++ []) = after := by
    rw [List.append_nil, ← hold, Function.update_eq_self]
  have hfinish : Function.update after (rs 1) [] =
      stageTapes slots base (i.val + 1) (radix * acc + digit) := by
    have hempty : base (rs 1) = [] := clean.acc _
    change Function.update (Function.update (Function.update base (rs 1) (encodeWord acc))
      (rs 3) (encodeWord (radix * acc + digit) ++ before (rs 3))) (rs 1) [] =
      Function.update base (rs 3) (encodeWord (radix * acc + digit))
    rw [hout, List.append_nil]
    funext k
    by_cases h1 : k = rs 1
    · subst k; simp [Ne.symm h31, hempty]
    · by_cases h3 : k = rs 3
      · subst k; simp [h31]
      · simp [h1, h3]
  have hdrain := drainTrace (rs 1) (labels (.clear i))
    (some (labels (entryLabel width (i.val + 1)))) p (atLabels (.clear i))
    after acc [] ambient none
  rw [hstart, hfinish] at hdrain
  rw [show stepCost radix acc digit = (acc + 1) + MachineRadixStep.steps radix acc digit by
    unfold stepCost; omega, Function.iterate_add_apply, hradix]
  exact hdrain

/-- Prefix induction follows the fixed finite sequence of digit labels. -/
theorem prefixTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (n : Nat) (hn : n ≤ width) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps radix digits n]
      (some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩) =
      some ⟨some (labels (entryLabel width n)), ((ambient, ()), none),
        stageTapes slots base n (value radix digits n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < width := by omega
    let i : Fin width := ⟨n, hlt⟩
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    have h := digitTrace slots labels exit p atLabels base radix (value radix digits n)
      (digits n) i operandRadix (operandDigits i) clean ambient none
    simpa only [entryLabel, dite_eq_left hlt, i, value] using h

/-- Move the final accumulator to the external output, restoring its order and
emptying accumulator/scratch. The old destination is retained as a suffix. -/
theorem finishTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (acc : Nat) (clean : Clean slots base) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[2 * acc + 4]
      (some ⟨some (labels .finishDrain), ((ambient, ()), none), stageTapes slots base width acc⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ := by
  let src := slots (.inl (accumulator (parity width)))
  let scratch := slots (.inl 5)
  let dst := slots (.inl 3)
  have hsrcScratch : src ≠ scratch := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hsrcDst : src ≠ dst := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hscratchDst : scratch ≠ dst := slots.injective.ne (by simp)
  have hsrc : base src = [] := clean.acc _
  have hs : base scratch = [] := clean.scratch
  let before := stageTapes slots base width acc
  let middle := Function.update base scratch (encodeWord acc).reverse
  have hinput : before src = encodeWord acc := Function.update_self _ _ _
  have hscratch : before scratch = [] := by
    change Function.update base src (encodeWord acc) scratch = []
    rw [Function.update_of_ne (Ne.symm hsrcScratch), hs]
  have hfirstTapes : Reduction.MachineTransfer.tapesAt src scratch before []
      ((before src).reverse.map id ++ before scratch) = middle := by
    rw [hinput, hscratch, List.append_nil, List.map_id]
    funext k
    by_cases h1 : k = src
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, middle, hsrcScratch, hsrc]
    · by_cases h2 : k = scratch
      · subst k; simp [Reduction.MachineTransfer.tapesAt, middle]
      · simp [Reduction.MachineTransfer.tapesAt, middle, before, stageTapes, h1, h2, src]
  have first := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) src scratch hsrcScratch id false
    (labels .finishDrain) (some (labels .finishRestore)) p (atLabels .finishDrain)
    before (ambient, ()) none
  rw [hfirstTapes] at first
  have hlength : (before src).length + 1 = acc + 2 := by
    simp [hinput, encodeWord, Nat.add_assoc]
  rw [hlength] at first
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishDrain), ((ambient, ()), none), before⟩) =
      some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩ at first
  have hmSource : middle scratch = (encodeWord acc).reverse := Function.update_self _ _ _
  have hmOutput : middle dst = base dst := by
    exact Function.update_of_ne (Ne.symm hscratchDst) _ _
  have hsecondTapes : Reduction.MachineTransfer.tapesAt scratch dst middle []
      ((middle scratch).reverse.map id ++ middle dst) = resultTapes slots base acc := by
    rw [hmSource, hmOutput, List.reverse_reverse, List.map_id]
    funext k
    by_cases h1 : k = dst
    · subst k; simp [Reduction.MachineTransfer.tapesAt, resultTapes, dst]
    · by_cases h2 : k = scratch
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, hscratchDst, hs, scratch, dst]
      · simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, h1, h2, dst]
  have second := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) scratch dst hscratchDst id false
    (labels .finishRestore) exit p (atLabels .finishRestore) middle (ambient, ()) none
  rw [hsecondTapes] at second
  have hmLength : (middle scratch).length + 1 = acc + 2 := by
    simp [hmSource, encodeWord, Nat.add_assoc]
  rw [hmLength] at second
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ at second
  rw [show 2 * acc + 4 = (acc + 2) + (acc + 2) by omega,
    Function.iterate_add_apply, first]
  exact second

/-- Complete actual Horner execution on preserved digit/base fields. Initial
work tapes are empty; only the destination changes at the optional continuation. -/
theorem hornerTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix digits width]
      (some ⟨some (labels .start), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩ := by
  have start : TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩ =
      some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩ := by
    change some (TM2.stepAux (p (labels .start)) _ _) = _
    rw [atLabels .start]
    simp only [statement, TM2.stepAux, clean.accA, stageTapes, parity, accumulator,
      Bool.false_eq_true, ↓reduceIte, encodeWord, List.replicate_zero, List.nil_append]
  have prefixRun := prefixTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient width (Nat.le_refl _)
  have final := finishTrace slots labels exit p atLabels base (value radix digits width) clean ambient
  have hend : entryLabel width width = .finishDrain := by simp [entryLabel]
  rw [hend] at prefixRun
  rw [show steps radix digits width =
    ((2 * value radix digits width + 4) + prefixSteps radix digits width) + 1 by
      unfold steps; omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[
    (2 * value radix digits width + 4) + prefixSteps radix digits width]
      (TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩) = _
  rw [start, Function.iterate_add_apply, prefixRun]
  exact final

open scoped BigOperators

@[simp] theorem resultTapes_output (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) :
    resultTapes slots base acc (slots (.inl 3)) = encodeWord acc ++ base (slots (.inl 3)) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat)
    (k : K) (hk : k ≠ slots (.inl 3)) : resultTapes slots base acc k = base k := by
  simp [resultTapes, hk]

end UniqueGamesTheorem.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductFieldLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

namespace UniqueGamesTheorem.Explicit.MachineProductField

section

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

def hornerRole : MachineHorner.Layout width → Layout width
  | .inl 0 => .inr 0
  | .inl 1 => .inr 1
  | .inl 2 => .inr 2
  | .inl 3 => .inr 5
  | .inl 4 => .inr 3
  | .inl 5 => .inr 4
  | .inr i => .inl (.inr (.inr i.rev))

theorem hornerRole_injective : Function.Injective (hornerRole (width := width)) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [hornerRole]
    | inr b => fin_cases a <;> simp [hornerRole] at h
  | inr a =>
    cases b with
    | inl b => fin_cases b <;> simp [hornerRole] at h
    | inr b => simpa [hornerRole] using h

def hornerSlots (slots : Layout width ↪ K) : MachineHorner.Layout width ↪ K :=
  Function.Embedding.trans ⟨hornerRole, hornerRole_injective⟩ slots

def instruction (slots : Layout width ↪ K) (coefficient : Nat) (offsets : Fin width → Nat)
    (labels : Label slots → Λ) (exit : Option Λ) :
    Label slots → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl l => MachineProductGather.instruction width (gatherSlots slots) coefficient offsets
      (fun x => labels (.inl x)) (some (labels (.inr (.inl .start)))) l
  | .inr (.inl l) => MachineHorner.statement (hornerSlots slots)
      (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ()))))) l
  | .inr (.inr (.inl _)) => loopAt (slots (.inr 5)) (slots (.inr 6)) id false
      (labels (.inr (.inr (.inl ()))))
      (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
  | .inr (.inr (.inr l)) => MachineDrainMany.instruction (clearTapes slots)
      (fun x => labels (.inr (.inr (.inr x)))) exit l

def gathered (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) : K → List Bool :=
  MachineProductGather.finalTapes values coefficient width (gatherSlots slots)
    indices offsets fields base

def evaluated (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  MachineHorner.resultTapes (hornerSlots slots)
    (gathered slots values coefficient indices offsets fields base) value

def emitted (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  tapesAt (slots (.inr 5)) (slots (.inr 6))
    (evaluated slots values coefficient indices offsets fields base value) []
    ((encodeWord value).reverse ++ base (slots (.inr 6)))

def finalTapes (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  MachineDrainMany.finalTapes (clearTapes slots)
    (emitted slots values coefficient indices offsets fields base value)

def steps (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (radix : Nat) (digits : Nat → Nat) : Nat :=
  MachineProductGather.steps values coefficient width indices offsets +
    MachineHorner.steps radix digits width + (MachineHorner.value radix digits width + 2) +
    MachineDrainMany.steps (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base
        (MachineHorner.value radix digits width))

theorem gathered_extra (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (i : Fin 7) :
    gathered slots values coefficient indices offsets fields base (slots (.inr i)) =
      base (slots (.inr i)) := by
  apply MachineProductGather.finalTapes_other
  · apply slots.injective.ne; simp
  · apply slots.injective.ne; simp
  · intro j; apply slots.injective.ne; simp

/-- Actual execution of the complete gather/Horner/emit/cleanup phase. The
field equality connects only mathematical tape contents; all transition work
is proved from the concrete instructions. -/
theorem fieldTrace (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (labels : Label slots → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots coefficient offsets labels exit l)
    (base : K → List Bool) (suffixes : Fin width → List Bool) (ready : Ready slots base)
    (tableWord : base (slots (.inl (.inl 0))) = encodeWords values)
    (sourceWords : ∀ i, base (slots (.inl (.inr (.inl i)))) =
      encodeWord (indices i) ++ suffixes i)
    (radix : Nat) (digits : Nat → Nat)
    (radixWord : base (slots (.inr 0)) = encodeWord radix)
    (digitWords : ∀ i : Fin width, digits i.val = fields i.rev)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps slots values coefficient indices offsets fields base radix digits]
      (some ⟨some (labels (entry slots)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), finalTapes slots values coefficient indices offsets fields
        base (MachineHorner.value radix digits width)⟩ := by
  let middle := gathered slots values coefficient indices offsets fields base
  have gather := MachineProductGather.gatherTrace values coefficient width (gatherSlots slots)
    (gatherSlots slots).injective indices offsets fields selected (fun x => labels (.inl x))
    (some (labels (.inr (.inl .start)))) program (fun x => atLabels (.inl x))
    base suffixes tableWord ready.gatherScratch sourceWords (ambient, ()) register
  have preserved (i : Fin 7) : middle (slots (.inr i)) = base (slots (.inr i)) :=
    gathered_extra slots values coefficient indices offsets fields base i
  have middleRadix : middle (hornerSlots slots (.inl 0)) = encodeWord radix := by
    rw [show hornerSlots slots (.inl 0) = slots (.inr 0) from rfl, preserved]
    exact radixWord
  have middleDigits (i : Fin width) :
      middle (hornerSlots slots (.inr i)) = encodeWord (digits i.val) := by
    rw [show hornerSlots slots (.inr i) =
      gatherSlots slots (.inr (.inr i.rev)) from rfl]
    dsimp only [middle, gathered]
    rw [MachineProductGather.finalTapes_field values coefficient width (gatherSlots slots)
      (gatherSlots slots).injective indices offsets fields base i.rev]
    rw [show base (gatherSlots slots (.inr (.inr i.rev))) = [] from ready.fields i.rev,
      List.append_nil, digitWords i]
  have clean : MachineHorner.Clean (hornerSlots slots) middle := by
    constructor
    · change middle (slots (.inr 1)) = []; rw [preserved]; exact ready.accA
    · change middle (slots (.inr 2)) = []; rw [preserved]; exact ready.accB
    · change middle (slots (.inr 3)) = []; rw [preserved]; exact ready.counter
    · change middle (slots (.inr 4)) = []; rw [preserved]; exact ready.hornerScratch
  have horner := MachineHorner.hornerTrace (hornerSlots slots)
    (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ())))))
    program (fun x => atLabels (.inr (.inl x))) middle radix digits middleRadix
    middleDigits clean ambient none
  let value := MachineHorner.value radix digits width
  let after := evaluated slots values coefficient indices offsets fields base value
  have outputWord : after (slots (.inr 5)) = encodeWord value := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value
      (hornerSlots slots (.inl 3)) = _
    rw [MachineHorner.resultTapes_output]
    rw [show hornerSlots slots (.inl 3) = slots (.inr 5) from rfl,
      preserved, ready.output, List.append_nil]
  have accWord : after (slots (.inr 6)) = base (slots (.inr 6)) := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value (slots (.inr 6)) = _
    rw [MachineHorner.resultTapes_other _ _ _ _ (slots.injective.ne (by simp [hornerRole])), preserved]
  have emit := transferAt_fromTapes (Γ := fun _ : K => Bool)
    (slots (.inr 5)) (slots (.inr 6)) (slots.injective.ne (by simp)) id false
    (labels (.inr (.inr (.inl ()))))
    (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
    program (atLabels (.inr (.inr (.inl ())))) after (ambient, ()) none
  rw [outputWord, accWord, List.map_id] at emit
  simp only [encodeWord_length] at emit
  have drain := MachineDrainMany.trace (clearTapes slots)
    (fun x => labels (.inr (.inr (.inr x)))) exit program
    (fun x => atLabels (.inr (.inr (.inr x))))
    (emitted slots values coefficient indices offsets fields base value) (ambient, ()) none
  rw [MachineDrainMany.finalRegister_none] at drain
  have emit' : (advance (TM2.step program))^[value + 2]
      (some ⟨some (labels (.inr (.inr (.inl ())))), ((ambient, ()), none), after⟩) =
      some ⟨MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit,
        ((ambient, ()), none), emitted slots values coefficient indices offsets fields base value⟩ := emit
  have compose {a b : Nat} {x y z : Option (TM2.Cfg (fun _ : K => Bool) Λ (MachineHorner.State σ))}
      (first : (advance (TM2.step program))^[a] x = y)
      (second : (advance (TM2.step program))^[b] y = z) :
      (advance (TM2.step program))^[a + b] x = z := by
    rw [Nat.add_comm, Function.iterate_add_apply, first, second]
  have gh := compose gather horner
  have ghe := compose gh emit'
  have whole := compose ghe drain
  simpa only [steps, value, entry, finalTapes] using whole

end

/-! The product-field machine restores every work tape and appends precisely
one field to the reversed output. This boundary is strong enough to compose
all fields and every odometer visit without retaining an unbounded history. -/

open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K : Type} [DecidableEq K] {width : Nat}

theorem gathered_frame (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (k : K) (outside : k ∉ clearTapes slots) :
    gathered slots values coefficient indices offsets fields base k = base k := by
  rw [mem_clearTapes] at outside
  apply MachineProductGather.finalTapes_other
  · exact fun h => outside (Or.inl h)
  · exact fun h => outside (Or.inr (Or.inl h))
  · intro i h; exact outside (Or.inr (Or.inr ⟨i, h⟩))

/-- The complete row-field phase changes just the output accumulator. -/
theorem finalTapes_eq (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (ready : Ready slots base) (value : Nat) :
    finalTapes slots values coefficient indices offsets fields base value =
      Function.update base (slots (.inr 6))
        ((encodeWord value).reverse ++ base (slots (.inr 6))) := by
  funext k
  rw [finalTapes, MachineDrainMany.finalTapes_apply]
  by_cases member : k ∈ clearTapes slots
  · have notOutput : k ≠ slots (.inr 6) := by
      intro h; subst k; exact extra_not_mem_clearTapes slots 6 member
    simp [member, Function.update_of_ne notOutput, ready.empty_clearTapes slots base k member]
  · rw [ite_eq_right member]
    by_cases output : k = slots (.inr 6)
    · subst k
      simp [emitted, tapesAt]
    · by_cases field : k = slots (.inr 5)
      · subst k
        simp [emitted, tapesAt, output, ready.output]
      · have frame := gathered_frame slots values coefficient indices offsets fields base k member
        simp only [emitted, tapesAt, Function.update_of_ne output, Function.update_of_ne field,
          evaluated, MachineHorner.resultTapes]
        change Function.update (gathered slots values coefficient indices offsets fields base)
          (slots (.inr 5)) _ k = base k
        rw [Function.update_of_ne field, frame]

/-- Cleanup only touches gather work; it never scans the global accumulator. -/
theorem emitted_clear_length (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : Ready slots base) (value : Nat)
    (k : K) (member : k ∈ clearTapes slots) :
    (emitted slots values coefficient indices offsets fields base value k).length ≤
      width * ((encodeWords values).length + 1) := by
  have notExtra (i : Fin 7) : k ≠ slots (.inr i) := by
    intro h; subst k; exact extra_not_mem_clearTapes slots i member
  have h := MachineProductGather.finalTapes_length values coefficient width (gatherSlots slots)
    (gatherSlots slots).injective indices offsets fields selected base k
  rw [ready.empty_clearTapes slots base k member, List.length_nil, Nat.zero_add] at h
  simpa only [emitted, tapesAt, Function.update_of_ne (notExtra 6),
    Function.update_of_ne (notExtra 5), evaluated, MachineHorner.resultTapes,
    show hornerSlots slots (.inl 3) = slots (.inr 5) from rfl,
    Function.update_of_ne (notExtra 5), gathered] using h

theorem cleanup_steps_le (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : Ready slots base) (value : Nat) :
    MachineDrainMany.steps (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base value) ≤
      (width + 2) * (width * ((encodeWords values).length + 1) + 1) := by
  have sumBound : MachineDrainMany.lengthSum (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base value) ≤
      (clearTapes slots).length * (width * ((encodeWords values).length + 1)) := by
    have hs := List.sum_le_card_nsmul
      ((clearTapes slots).map (fun k => (emitted slots values coefficient indices offsets fields base value k).length))
      (width * ((encodeWords values).length + 1)) (by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
        exact emitted_clear_length slots values coefficient indices offsets fields selected base ready value k hk)
    simpa [MachineDrainMany.lengthSum, nsmul_eq_mul] using hs
  have h := MachineDrainMany.steps_le (clearTapes slots)
    (emitted slots values coefficient indices offsets fields base value)
  rw [clearTapes_length] at sumBound h
  rw [Nat.mul_add, Nat.mul_one]
  omega

end UniqueGamesTheorem.Explicit.MachineProductField

/-! Actual power-header emission by fixed-width Horner evaluation of
`[1,0,...,0]`, followed by physical transfer to the reverse accumulator. -/

namespace UniqueGamesTheorem.Explicit.MachineProductPower

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {exponent : Nat}

def instruction (slots : MachineHorner.Layout (exponent + 1) ↪ K) (output : K)
    (labels : Label exponent → Λ) (exit : Option Λ) :
    Label exponent → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl l => MachineHorner.statement slots (fun x => labels (.inl x))
      (some (labels (.inr ()))) l
  | .inr _ => loopAt (slots (.inl 3)) output id false (labels (.inr ())) exit

end UniqueGamesTheorem.Explicit.MachineProductPower

/-! A finite row-field schedule. Endpoint fields use the input vertex radix;
permutation fields use the fixed alphabet radix. The complete list of columns
is in finite control, while all row indices, table entries and radix magnitudes
remain data on tapes. -/

namespace UniqueGamesTheorem.Explicit.MachineProductRow

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

def localInstruction (slots : Layout width ↪ K) (coefficient : Nat) (command : Command width)
    (labels : LocalLabel slots command → Λ) (exit : Option Λ) :
    LocalLabel slots command → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineProductField.instruction (fieldSlots slots command.1) coefficient command.2 labels exit

def instruction (slots : Layout width ↪ K) (coefficient : Nat) (commands : List (Command width))
    (labels : Label slots commands → Λ) (exit : Option Λ) :
    Label slots commands → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction slots coefficient) commands labels exit

def appendField (slots : Layout width ↪ K) (value : Nat) (base : K → List Bool) : K → List Bool :=
  Function.update base (outputTape slots) ((encodeWord value).reverse ++ base (outputTape slots))

/-- Exact literal output of the command list in field order. -/
def rowBits (values : Command width → Nat) (commands : List (Command width)) : List Bool :=
  commands.flatMap (fun command => encodeWord (values command))

def result (slots : Layout width ↪ K) (values : Command width → Nat)
    (command : Command width) (base : K → List Bool) : K → List Bool :=
  appendField slots (values command) base

/-- The input-dependent data needed for one whole row, held invariant by
all physical field executions. -/
structure Ready (slots : Layout width ↪ K) (table : List Nat) (indices : Fin width → Nat)
    (radices : Bool → Nat) (base : K → List Bool) : Prop where
  work : ∀ useAlphabet, MachineProductField.Ready (fieldSlots slots useAlphabet) base
  tableWord : base (slots (.inl (.inl (.inl 0)))) = encodeWords table
  sourceWords : ∀ i, base (slots (.inl (.inl (.inr (.inl i))))) = encodeWord (indices i)
  radixWords : ∀ b, base (fieldSlots slots b (.inr 0)) = encodeWord (radices b)

theorem Ready.appendField (slots : Layout width ↪ K) (table : List Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat) (base : K → List Bool)
    (ready : Ready slots table indices radices base) (value : Nat) :
    Ready slots table indices radices (appendField slots value base) := by
  constructor
  · intro b
    have h := MachineProductField.Ready.output_update (fieldSlots slots b) base (ready.work b)
      ((encodeWord value).reverse ++ base (outputTape slots))
    exact h
  · rw [MachineProductRow.appendField, outputTape, Function.update_of_ne (slots.injective.ne (by simp))]
    exact ready.tableWord
  · intro i
    rw [MachineProductRow.appendField, outputTape, Function.update_of_ne (slots.injective.ne (by simp))]
    exact ready.sourceWords i
  · intro b
    rw [MachineProductRow.appendField, Function.update_of_ne]
    · exact ready.radixWords b
    · apply slots.injective.ne
      cases b <;> simp [fieldRole]

end UniqueGamesTheorem.Explicit.MachineProductRow

/-! Polynomial bounds for actual field and row traces. The output accumulator
is excluded from local cleanup and is never rescanned by row emission. -/

namespace UniqueGamesTheorem.Explicit.MachineProductBounds

open UniqueGamesTheorem.Foundations.Complexity

variable {K : Type} [DecidableEq K] {width : Nat}

theorem field_steps_le (slots : MachineProductField.Layout width ↪ K) (table : List Nat)
    (coefficient : Nat) (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, table[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : MachineProductField.Ready slots base)
    (radix : Nat) (digits : Nat → Nat) (magnitude : Nat)
    (tableBound : (encodeWords table).length ≤ magnitude)
    (indexBound : ∀ i, indices i ≤ magnitude) (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    MachineProductField.steps slots table coefficient indices offsets fields base radix digits ≤
      (fieldPolynomial width).eval magnitude := by
  have gather := MachineProductGather.steps_le table coefficient width magnitude indices offsets fields selected indexBound
  have horner := MachineHorner.steps_le_timePolynomial radix digits width magnitude radixBound digitBound
  have value := MachineHorner.value_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  have cleanup := MachineProductField.cleanup_steps_le slots table coefficient indices offsets fields selected
    base ready (MachineHorner.value radix digits width)
  have gatherBound : width * (2 * magnitude + 5 * (encodeWords table).length + 6) + 1 ≤
      width * (7 * magnitude + 6) + 1 := by gcongr; omega
  have cleanupBound : (width + 2) * (width * ((encodeWords table).length + 1) + 1) ≤
      (width + 2) * (width * (magnitude + 1) + 1) := by gcongr
  rw [fieldPolynomial_eval]
  unfold MachineProductField.steps
  omega

def rowCost (slots : MachineProductRow.Layout width ↪ K) (table : List Nat) (coefficient : Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat)
    (fields : MachineProductRow.Command width → Fin width → Nat)
    (digits : MachineProductRow.Command width → Nat → Nat)
    (c : MachineProductRow.Command width) (base : K → List Bool) : Nat :=
  MachineProductField.steps (MachineProductRow.fieldSlots slots c.1) table coefficient indices c.2
    (fields c) base (radices c.1) (digits c)

theorem row_steps_le (slots : MachineProductRow.Layout width ↪ K) (table : List Nat)
    (coefficient : Nat) (indices : Fin width → Nat) (radices : Bool → Nat)
    (commands : List (MachineProductRow.Command width))
    (fields : MachineProductRow.Command width → Fin width → Nat)
    (digits : MachineProductRow.Command width → Nat → Nat)
    (selected : ∀ c ∈ commands, ∀ i, table[coefficient * indices i + c.2 i]? = some (fields c i))
    (base : K → List Bool) (ready : MachineProductRow.Ready slots table indices radices base)
    (magnitude : Nat) (tableBound : (encodeWords table).length ≤ magnitude)
    (indexBound : ∀ i, indices i ≤ magnitude) (radixBound : ∀ b, radices b ≤ magnitude)
    (digitBound : ∀ c ∈ commands, ∀ i, i < width → digits c i ≤ magnitude) :
    MachineFiniteSequence.steps
      (MachineProductRow.result slots (fun c => MachineHorner.value (radices c.1) (digits c) width))
      (rowCost slots table coefficient indices radices fields digits) commands base ≤
      commands.length * (fieldPolynomial width).eval magnitude := by
  induction commands generalizing base with
  | nil => simp [MachineFiniteSequence.steps]
  | cons command commands ih =>
    have first := field_steps_le (MachineProductRow.fieldSlots slots command.1) table coefficient
      indices command.2 (fields command) (selected command (by simp)) base (ready.work command.1)
      (radices command.1) (digits command) magnitude tableBound indexBound (radixBound command.1)
      (digitBound command (by simp))
    have nextReady := MachineProductRow.Ready.appendField slots table indices radices base ready
      (MachineHorner.value (radices command.1) (digits command) width)
    have rest := ih (fun c hc => selected c (by simp [hc]))
      (MachineProductRow.result slots (fun c => MachineHorner.value (radices c.1) (digits c) width)
        command base) nextReady (fun c hc => digitBound c (by simp [hc]))
    rw [MachineFiniteSequence.steps, List.length_cons, Nat.add_mul, Nat.one_mul]
    simpa only [Nat.add_comm, rowCost] using Nat.add_le_add first rest

end UniqueGamesTheorem.Explicit.MachineProductBounds

/-! Fixed natural polynomials are represented by literal Horner coefficients.
The coefficient representation is independent of the machine input. The actual
machine wrapper is built from the shared physical unary Horner subroutine. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductMachineSemantics
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The exact table lookups and field schedule consumed by the product machine.
The table contains rows only: the three input header words have already been
consumed, so each affine lookup has coefficient `q+2` and no header offset.
-/

namespace UniqueGamesTheorem.Explicit.ProductMachineSemantics

open UniqueGamesTheorem.Foundations
open Target
open Complexity
open MachineOutputContract

variable {n q t : ℕ}

/-- Indexing a flattened constant-width row list preserves the literal field
position, not merely the multiset of row contents. -/
theorem row_table_lookup (constraints : List (Constraint n q))
    (e : Fin constraints.length) (field : Fin (q + 2)) :
    (constraints.flatMap constraintWords)[(q + 2) * e.val + field.val]? =
      (constraintWords constraints[e])[field.val]? := by
  induction constraints with
  | nil => exact Fin.elim0 e
  | cons c constraints ih =>
    refine Fin.cases ?_ (fun i => ?_) e
    · simp [List.flatMap_cons, List.getElem?_append, constraintWords_length, field.isLt]
    · rw [List.flatMap_cons, List.getElem?_append]
      have hlarge : ¬ (q + 2) * i.succ.val + field.val < (constraintWords c).length := by
        simp only [Fin.val_succ, constraintWords_length, Nat.mul_succ]
        omega
      rw [ite_eq_right hlarge]
      have hindex : (q + 2) * i.succ.val + field.val - (constraintWords c).length =
          (q + 2) * i.val + field.val := by
        simp only [Fin.val_succ, constraintWords_length, Nat.mul_succ]
        omega
      rw [hindex]
      exact ih i

def inputTable (H : Instance q) : List ℕ := H.constraints.flatMap constraintWords

def fields (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (command : MachineProductRow.Command t) : Fin t → ℕ := fun j =>
  ((inputTable H)[(q + 2) * (edges j).val + command.2 j]?).getD 0

def fieldValue (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (command : MachineProductRow.Command t) : ℕ :=
  MachineHorner.value (if command.1 then q else H.vertices)
    (reverseDigits (fields H edges command)) t

/-- Product rows are emitted in ascending radix address, exactly the literal
order of the output constraint list. -/
def allRowsBits (H : Instance q) (t : ℕ) : List Bool :=
  (List.finRange (H.constraints.length ^ t)).flatMap (fun i =>
    MachineProductRow.rowBits (fieldValue H (finFunctionFinEquiv.symm i)) (commands q t))

end UniqueGamesTheorem.Explicit.ProductMachineSemantics

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineTupleOdometer
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev digitTapes (current remaining : K) (base : K → List Bool) (d r : ℕ)
    (currentSuffix remainingSuffix : List Bool) : K → List Bool :=
  MachineUnaryAddAt.unaryTapes current remaining base d r currentSuffix remainingSuffix

/-- Reset conserves the digit's unary budget, then enters the next coordinate. -/
def reset (current remaining : K) (resetLabel carryLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineUnaryAddAt.loop current remaining resetLabel (some carryLabel)

end UniqueGamesTheorem.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_CanonicalBodyTemplateLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Lower a complete canonical-body template to the actual field-template
machine. There are four saved fields per query position, numbered by
`field + 4 * position`. The template constants depend only on finite coefficient
and RHS data; names and occurrence identifiers remain saved tape contents. -/

namespace UniqueGamesTheorem.Reduction.CanonicalBodyMachine

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding

variable {k : Nat}

def savedFields (fields : Fin k → Fin 4 → Nat) (index : Fin (4*k)) : List Bool :=
  encodeWord (fields ((fieldEquiv k).symm index).1 ((fieldEquiv k).symm index).2)

@[simp] theorem savedFields_fieldIndex (fields : Fin k → Fin 4 → Nat)
    (position : Fin k) (field : Fin 4) :
    savedFields fields (fieldIndex position field) = encodeWord (fields position field) := by
  simp [savedFields, fieldIndex]

end UniqueGamesTheorem.Reduction.CanonicalBodyMachine

end

section

/-! An occurrence-preserving E3LIN table codec. The word stream contains its
declared variable count and equation count, followed by four words per equation.
Parsing checks all three indices, the Boolean right-hand side, the exact count,
absence of trailing words, and nonemptiness. Length theorems below concern the
actual serialized output; they make no running-time claim. -/

namespace UniqueGamesTheorem.Reduction.SourceEncoding

open UniqueGamesTheorem.Foundations.Complexity

structure Input where
  «variables» : Nat
  equations : List (CloneGap.Equation (Fin «variables»))
  nonempty : equations ≠ []

def equationWords {n : Nat} (e : CloneGap.Equation (Fin n)) : List Nat :=
  [e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0]

def inputWords (input : Input) : List Nat :=
  [input.variables, input.equations.length] ++ input.equations.flatMap equationWords

def inputBits (input : Input) : List Bool := encodeWords (inputWords input)

@[simp] theorem equationWords_length {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (equationWords e).length = 4 := by simp [equationWords]

theorem equationsWords_length {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (equations.flatMap equationWords).length = 4 * equations.length := by
  induction equations with
  | nil => rfl
  | cons e equations ih =>
      simp only [List.flatMap_cons, List.length_append, equationWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem inputWords_length (input : Input) :
    (inputWords input).length = 2 + 4 * input.equations.length := by
  simp only [inputWords, List.length_append, List.length_cons, List.length_nil,
    equationsWords_length]

theorem equationBits_length_le {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (encodeWords (equationWords e)).length ≤ 3 * n + 2 := by
  have hfirst := e.first.isLt
  have hsecond := e.second.isLt
  have hthird := e.third.isLt
  cases hrhs : e.rhs <;> simp [equationWords, hrhs] <;> omega

theorem equationsBits_length_le {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (encodeWords (equations.flatMap equationWords)).length ≤
      equations.length * (3 * n + 2) := by
  induction equations with
  | nil => simp [encodeWords]
  | cons e equations ih =>
      have he := equationBits_length_le e
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem inputBits_length (input : Input) :
    (inputBits input).length = input.variables + input.equations.length + 2 +
      (encodeWords (input.equations.flatMap equationWords)).length := by
  simp only [inputBits, inputWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem inputBits_length_le (input : Input) :
    (inputBits input).length ≤ input.variables + input.equations.length + 2 +
      input.equations.length * (3 * input.variables + 2) := by
  rw [inputBits_length]
  exact Nat.add_le_add_left (equationsBits_length_le input.equations) _

theorem inputBits_length_ge_variables (input : Input) :
    input.variables ≤ (inputBits input).length := by rw [inputBits_length]; omega

theorem inputBits_length_ge_equations (input : Input) :
    input.equations.length ≤ (inputBits input).length := by rw [inputBits_length]; omega

end UniqueGamesTheorem.Reduction.SourceEncoding

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100TableLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The literal four-word row used by the hundred-clone finite machine. The
natural-number triple is a fixed program parameter; its bounds and distinctness
are needed only when identifying the output with the typed parity instance.
-/

namespace UniqueGamesTheorem.Explicit.MachineClone100Table

open UniqueGamesTheorem.Reduction

def cloneEquationWords {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * e.first.val, t.2.1 + 100 * e.second.val,
    t.2.2 + 100 * e.third.val, if e.rhs then 1 else 0]

end UniqueGamesTheorem.Explicit.MachineClone100Table

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Model

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

def emission (triples : List (Nat × Nat × Nat)) (c : Context triples.length) :
    Bool → List Bool := affineEmit (contextScale c) (contextOffset triples c)

def program (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) :
    Label triples.length → TM2.Stmt Alphabet (Label triples.length) (State triples.length)
  | .headerStart j => SourceMachine.fieldStart (headerTape j) (.headerLoop j)
  | .headerLoop j => SourceMachine.fieldLoop .input (headerTape j) (.headerLoop j)
      (if j.val = 0 then some (.headerStart 1) else some (.setup (.inl 0)))
  | .setup c => .load (fun _ => (((), c), none)) (.goto fun _ => .scan c)
  | .scan c => MachineTransducerCopy.scanLoop (contextSource c) .scratch
      (defaultControl _) (fun q b => .emit c q b) (.restore c)
  | .emit c q b => MachineTransducerCopy.emitter .reversed (fun q _ => q)
      (emission triples) (.scan c) q b
  | .restore c => MachineTransfer.loopAt .scratch (contextSource c) id false
      (.restore c) (contextNext c)
  | .clearHeader => drain .header .clearHeader .guard
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) .finalCounter
  | .fieldStart j => SourceMachine.fieldStart (.field j) (.fieldLoop j)
  | .fieldLoop j => SourceMachine.fieldLoop .input (.field j) (.fieldLoop j)
      (SourceMachine.fieldNext Label.fieldStart
        (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0)))) j)
  | .cleanup j => drain (.field j) (.cleanup j) (cleanupNext j)
  | .finalCounter => .pop .counter (fun state _ => (state.1, none))
      (.goto fun _ => .finalReverse)
  | .finalReverse => MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label triples.length
  main := .headerStart 0
  σ := State triples.length
  initialState := initialState _
  m := program triples nonempty

end UniqueGamesTheorem.Explicit.MachineClone100Model

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Affine

open UniqueGamesTheorem.Reduction

open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

theorem affineEmit_replicate_true (scale offset v : Nat) :
    (List.replicate v true).flatMap (affineEmit scale offset) =
      List.replicate (scale * v) true := by
  rw [List.flatMap_replicate]
  change (List.replicate v (List.replicate scale true)).flatten = _
  rw [List.flatten_replicate_replicate, Nat.mul_comm v scale]

/-- This includes zero scale and zero offset, with no positivity assumptions. -/
theorem affineEmit_word (scale offset v : Nat) :
    (encodeWord v).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) := by
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, affineEmit_replicate_true, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * v) offset]

/-- Exact symbolic context transform used by the shared clone-table machine. -/
theorem output_word (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWord v) =
      encodeWord (contextOffset triples c + contextScale c * v) := by
  rw [output_eq_flatMap]
  exact affineEmit_word (contextScale c) (contextOffset triples c) v

end UniqueGamesTheorem.Explicit.MachineClone100Affine

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Cleanup

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

variable {D : Nat}

/-- Direct list induction gives exactly one transition per symbol plus the
empty-tape exit; no whole execution trace is assumed. -/
theorem drainTrace (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (input : List Bool)
    (control : Unit × Context D) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, (control, register), Function.update base tape input⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  induction input generalizing register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some] using
      drainStep_nil tape again next program atAgain base control register
  | cons bit input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (TM2.step program ⟨some again, (control, register),
        Function.update base tape (bit :: input)⟩) = _
    rw [drainStep_cons tape again next program atAgain, ih]

/-- Caller form: the selected tape's initial contents are read from the frame. -/
theorem drainTrace_base (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(base tape).length + 1]
      (some ⟨some again, (control, register), base⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self] using
    drainTrace tape again next program atAgain base (base tape) control register

theorem clearHeaderTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[(base .header).length + 1]
      (some ⟨some .clearHeader, (control, register), base⟩) =
      some ⟨some .guard, (control, none), Function.update base .header []⟩ :=
  drainTrace_base .header .clearHeader .guard (program triples nonempty) rfl base control register

theorem cleanupTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (slot : Fin 4) (base : Tape → List Bool)
    (control : Unit × Context triples.length) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
      (base (.field slot)).length + 1]
      (some ⟨some (.cleanup slot), (control, register), base⟩) =
      some ⟨some (cleanupNext slot), (control, none), Function.update base (.field slot) []⟩ :=
  drainTrace_base (.field slot) (.cleanup slot) (cleanupNext slot)
    (program triples nonempty) rfl base control register

/-- All four field stacks are consumed by the actual cleanup program. -/
theorem cleanupFourTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[cleanupSteps base]
      (some ⟨some (.cleanup 0), (control, register), base⟩) =
      some ⟨some .guard, (control, none), clearFields base⟩ := by
  let t₀ := Function.update base (.field 0) []
  let t₁ := Function.update t₀ (.field 1) []
  let t₂ := Function.update t₁ (.field 2) []
  have h₀ := cleanupTrace triples nonempty 0 base control register
  have h₁ := cleanupTrace triples nonempty 1 t₀ control none
  have h₂ := cleanupTrace triples nonempty 2 t₁ control none
  have h₃ := cleanupTrace triples nonempty 3 t₂ control none
  have hn₀ : cleanupNext (D := triples.length) 0 = .cleanup 1 := by simp [cleanupNext]
  have hn₁ : cleanupNext (D := triples.length) 1 = .cleanup 2 := by simp [cleanupNext]
  have hn₂ : cleanupNext (D := triples.length) 2 = .cleanup 3 := by simp [cleanupNext]
  have hn₃ : cleanupNext (D := triples.length) 3 = .guard := by simp [cleanupNext]
  rw [hn₀] at h₀
  rw [hn₁] at h₁
  rw [hn₂] at h₂
  rw [hn₃] at h₃
  have ht₁ : t₀ (.field 1) = base (.field 1) := by simp [t₀]
  have ht₂ : t₁ (.field 2) = base (.field 2) := by simp [t₁, t₀]
  have ht₃ : t₂ (.field 3) = base (.field 3) := by simp [t₂, t₁, t₀]
  rw [ht₁] at h₁
  rw [ht₂] at h₂
  rw [ht₃] at h₃
  have time : cleanupSteps base =
      ((base (.field 3)).length + 1) +
      (((base (.field 2)).length + 1) +
      (((base (.field 1)).length + 1) + ((base (.field 0)).length + 1))) := by
    unfold cleanupSteps
    omega
  rw [time, Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (base (.field 2)).length + 1)]
  rw [Function.iterate_add_apply (m := (base (.field 1)).length + 1)]
  rw [h₀, h₁, h₂, h₃]
  rfl

def cleanupFourInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.cleanup 0), (control, register), base⟩
      (some ⟨some .guard, (control, none), clearFields base⟩)
      (cleanupSteps base) where
  steps := cleanupSteps base
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step (program triples nonempty)))^[_] _ = _
    exact cleanupFourTrace triples nonempty base control register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Explicit.MachineClone100Cleanup

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Context

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

def contextTapes (triples : List (Nat × Nat × Nat)) (context : Context triples.length)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .reversed
    ((MachineTransducer.output (fun control _ => control) (emission triples)
      context (base (contextSource context))).reverse ++ base .reversed)

@[simp] theorem contextTapes_reversed (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base .reversed =
      (MachineTransducer.output (fun control _ => control) (emission triples)
        context (base (contextSource context))).reverse ++ base .reversed := by
  simp [contextTapes]

theorem contextTapes_other (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) (tape : Tape)
    (different : tape ≠ .reversed) :
    contextTapes triples context base tape = base tape := by
  simp [contextTapes, different]

@[simp] theorem contextTapes_source (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base (contextSource context) = base (contextSource context) :=
  contextTapes_other triples context base _ (contextSource_ne_reversed context)

@[simp] theorem contextTapes_scratch (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base .scratch = base .scratch :=
  contextTapes_other triples context base _ (by decide)

/-- Setup discards arbitrary old control and register values before scanning. -/
theorem setupStep (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (state : State triples.length) :
    TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩ =
      some ⟨some (.scan context), (((), context), none), base⟩ := rfl

theorem contextTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
        3 * (base (contextSource context)).length + 3]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState _, contextTapes triples context base⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (contextSource context) Tape.scratch Tape.reversed
    (contextSource_ne_scratch context) (contextSource_ne_reversed context) (by decide)
    (defaultControl triples.length) (fun control _ => control) (emission triples)
    (.scan context) (.restore context) (fun control symbol => .emit context control symbol)
    (contextNext context) (program triples nonempty)
    rfl (by intros; rfl) rfl base scratchEmpty () context none
  rw [show 3 * (base (contextSource context)).length + 3 =
      (3 * (base (contextSource context)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program triples nonempty)))^[
    3 * (base (contextSource context)).length + 2]
    (TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩) = _
  rw [setupStep]
  exact copied

/-- The exact trace packaged for composition with neighboring cloning stages. -/
def contextInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.setup context), state, base⟩
      (some ⟨contextNext context, initialState _, contextTapes triples context base⟩)
      (3 * (base (contextSource context)).length + 3) where
  steps := 3 * (base (contextSource context)).length + 3
  evals_in_steps := contextTrace triples nonempty context base scratchEmpty state
  steps_le_m := Nat.le_refl _

@[simp] theorem contextInTime_steps (triples : List (Nat × Nat × Nat))
    (nonempty : triples ≠ []) (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (contextInTime triples nonempty context base scratchEmpty state).steps =
      3 * (base (contextSource context)).length + 3 := rfl

end UniqueGamesTheorem.Explicit.MachineClone100Context

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Finish

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

def finishTapes (base : Tape → List Bool) : Tape → List Bool :=
  MachineTransfer.tapesAt .reversed .output (Function.update base .counter []) []
    ((base .reversed).reverse ++ base .output)

@[simp] theorem finishTapes_counter (base : Tape → List Bool) :
    finishTapes base .counter = [] := by simp [finishTapes, MachineTransfer.tapesAt]

@[simp] theorem finishTapes_reversed (base : Tape → List Bool) :
    finishTapes base .reversed = [] := by simp [finishTapes, MachineTransfer.tapesAt]

@[simp] theorem finishTapes_output (base : Tape → List Bool) :
    finishTapes base .output = (base .reversed).reverse ++ base .output := by
  simp [finishTapes, MachineTransfer.tapesAt]

theorem counterStep (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    TM2.step (program triples hne)
      ⟨some .finalCounter, initialState _, base⟩ =
        some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩ := by
  simp [TM2.step, TM2.stepAux, program, initialState, hcounter]

theorem finishTrace (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 2]
      (some ⟨some .finalCounter, initialState _, base⟩) =
        some ⟨none, initialState _, finishTapes base⟩ := by
  have first := counterStep triples hne base hcounter
  have rest := MachineTransfer.transferAt_fromTapes Tape.reversed Tape.output
    (by decide) id false (Label.finalReverse : Label triples.length) none
    (program triples hne) rfl (Function.update base Tape.counter [])
    ((), defaultControl triples.length) none
  change (MachineComposition.advance (TM2.step (program triples hne)))^[
      ((Function.update base Tape.counter []) Tape.reversed).length + 1]
    (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) = _ at rest
  have rest' :
      (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 1]
        (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) =
          some ⟨none, initialState _, finishTapes base⟩ := by
    simpa only [finishTapes, initialState,
      Function.update_of_ne (by decide : Tape.reversed ≠ Tape.counter),
      Function.update_of_ne (by decide : Tape.output ≠ Tape.counter), List.map_id] using rest
  rw [show (base .reversed).length + 2 = ((base .reversed).length + 1) + 1 by omega,
    Function.iterate_succ_apply, MachineComposition.advance_some, first]
  exact rest'

def finishInTime (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    StateTransition.EvalsToInTime (TM2.step (program triples hne))
      ⟨some .finalCounter, initialState _, base⟩
      (some ⟨none, initialState _, finishTapes base⟩) ((base .reversed).length + 2) where
  steps := (base .reversed).length + 2
  evals_in_steps := finishTrace triples hne base hcounter
  steps_le_m := Nat.le_refl _

theorem finish_eq_haltList (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool)
    (emptyOther : ∀ tape, tape ≠ .counter → tape ≠ .reversed → base tape = []) :
    (⟨none, initialState _, finishTapes base⟩ : (machine triples hne).Cfg) =
      haltList (machine triples hne) ((base .reversed).reverse) := by
  have hout := emptyOther .output (by decide) (by decide)
  have ht : finishTapes base =
      (haltList (machine triples hne) ((base .reversed).reverse)).stk := by
    funext tape
    cases tape <;> simp [finishTapes, MachineTransfer.tapesAt, haltList, machine, hout,
      emptyOther]
    rfl
  exact congrArg
    (fun tapes => (⟨none, initialState triples.length, tapes⟩ : (machine triples hne).Cfg)) ht

end UniqueGamesTheorem.Explicit.MachineClone100Finish

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100Headers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Headers

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineClone100Model

def parsedTapes (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    Tape → List Bool
  | .input => suffix
  | .header => encodeWord n
  | .counter => encodeWord m
  | tape => base tape

/-- Exact header-stage endpoint. The occurrence counter is retained for the
body loop; generated output is accumulated in reverse. -/
def resultTapes (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (n m : Nat) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .header => []
  | .counter => encodeWord m
  | .reversed => (encodeWords [100 * n, triples.length * m]).reverse
  | tape => base tape

@[simp] theorem resultTapes_input (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .input = suffix := rfl
@[simp] theorem resultTapes_header (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .header = [] := rfl
@[simp] theorem resultTapes_counter (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .counter = encodeWord m := rfl
@[simp] theorem resultTapes_reversed (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .reversed =
      (encodeWords [100 * n, triples.length * m]).reverse := rfl
@[simp] theorem resultTapes_scratch (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .scratch = base .scratch := rfl
@[simp] theorem resultTapes_field (triples) (base) (n m) (suffix) (j : Fin 4) :
    resultTapes triples base n m suffix (.field j) = base (.field j) := rfl
@[simp] theorem resultTapes_output (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .output = base .output := rfl

theorem twoFieldsTapes (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hheader : base .header = []) (hcounter : base .counter = []) :
    SourceMachine.afterField .input .counter
      (SourceMachine.afterField .input .header base n (encodeWord m ++ suffix)) m suffix =
      parsedTapes base n m suffix := by
  funext tape
  cases tape <;>
    simp [SourceMachine.afterField, SourceMachine.fieldTapes, parsedTapes, hheader, hcounter]

theorem firstContextTapes (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hreversed : base .reversed = []) :
    MachineClone100Context.contextTapes triples (.inl 0) (parsedTapes base n m suffix) =
      Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale, hreversed]

theorem secondContextTapes (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    MachineClone100Context.contextTapes triples (.inl 1)
      (Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse) =
      Function.update (parsedTapes base n m suffix) .reversed
        (encodeWords [100 * n, triples.length * m]).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale,
    encodeWords, List.reverse_append]

theorem clearHeaderTapes (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (parsedTapes base n m suffix) .reversed
        (encodeWords [100 * n, triples.length * m]).reverse) .header [] =
      resultTapes triples base n m suffix := by
  funext tape
  cases tape <;> simp [parsedTapes, resultTapes]

theorem headersTrace (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m] ++ suffix)
    (hheader : base .header = []) (hcounter : base .counter = [])
    (hscratch : base .scratch = []) (hreversed : base .reversed = []) :
    (MachineComposition.advance (TM2.step (program triples hne)))^[5 * n + 4 * m + 18]
      (some ⟨some (.headerStart 0), initialState triples.length, base⟩) =
      some ⟨some .guard, initialState triples.length,
        resultTapes triples base n m suffix⟩ := by
  let t₀ := SourceMachine.afterField .input .header base n (encodeWord m ++ suffix)
  let t₁ := parsedTapes base n m suffix
  let t₂ := Function.update t₁ .reversed (encodeWord (100 * n)).reverse
  let t₃ := Function.update t₁ .reversed (encodeWords [100 * n, triples.length * m]).reverse
  have h₀ : base .input = encodeWord n ++ (encodeWord m ++ suffix) := by
    simpa only [encodeWords, List.append_nil, List.append_assoc] using hinput
  have p₀ := (SourceMachine.fieldInTime .input .header (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1))
    (program triples hne) rfl rfl base n (encodeWord m ++ suffix) h₀
    ((), defaultControl triples.length) none).evals_in_steps
  change (MachineComposition.advance (TM2.step (program triples hne)))^[n + 2]
    (some ⟨some (.headerStart 0), initialState triples.length, base⟩) =
    some ⟨some (.headerStart 1), initialState triples.length, t₀⟩ at p₀
  have h₁ : t₀ .input = encodeWord m ++ suffix := by
    simp [t₀, SourceMachine.afterField]
  have p₁ := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some (.setup (.inl 0)))
    (program triples hne) rfl rfl t₀ m suffix h₁
    ((), defaultControl triples.length) none).evals_in_steps
  change (MachineComposition.advance (TM2.step (program triples hne)))^[m + 2]
    (some ⟨some (.headerStart 1), initialState triples.length, t₀⟩) =
    some ⟨some (.setup (.inl 0)), initialState triples.length,
      SourceMachine.afterField .input .counter t₀ m suffix⟩ at p₁
  have ht₁ : SourceMachine.afterField .input .counter t₀ m suffix = t₁ :=
    twoFieldsTapes base n m suffix hheader hcounter
  rw [ht₁] at p₁
  have hs₁ : t₁ .scratch = [] := by simpa [t₁, parsedTapes] using hscratch
  have p₂ := MachineClone100Context.contextTrace triples hne (.inl 0) t₁ hs₁
    (initialState triples.length)
  have ht₂ : MachineClone100Context.contextTapes triples (.inl 0) t₁ = t₂ :=
    firstContextTapes triples base n m suffix hreversed
  rw [ht₂] at p₂
  have hlen₂ : (t₁ (contextSource (.inl 0 : Context triples.length))).length = n + 1 := by
    simp [contextSource, headerTape, t₁, parsedTapes]
  rw [hlen₂] at p₂
  change (MachineComposition.advance (TM2.step (program triples hne)))^[3 * (n + 1) + 3]
    (some ⟨some (.setup (.inl 0)), initialState triples.length, t₁⟩) =
    some ⟨some (.setup (.inl 1)), initialState triples.length, t₂⟩ at p₂
  have hs₂ : t₂ .scratch = [] := by simp [t₂, t₁, parsedTapes, hscratch]
  have p₃ := MachineClone100Context.contextTrace triples hne (.inl 1) t₂ hs₂
    (initialState triples.length)
  have ht₃ : MachineClone100Context.contextTapes triples (.inl 1) t₂ = t₃ :=
    secondContextTapes triples base n m suffix
  rw [ht₃] at p₃
  have hlen₃ : (t₂ (contextSource (.inl 1 : Context triples.length))).length = m + 1 := by
    simp [contextSource, headerTape, t₂, t₁, parsedTapes]
  rw [hlen₃] at p₃
  change (MachineComposition.advance (TM2.step (program triples hne)))^[3 * (m + 1) + 3]
    (some ⟨some (.setup (.inl 1)), initialState triples.length, t₂⟩) =
    some ⟨some .clearHeader, initialState triples.length, t₃⟩ at p₃
  have p₄ := MachineClone100Cleanup.clearHeaderTrace triples hne t₃
    ((), defaultControl triples.length) none
  have ht₄ : Function.update t₃ .header [] = resultTapes triples base n m suffix :=
    clearHeaderTapes triples base n m suffix
  rw [ht₄] at p₄
  have hh₃ : t₃ .header = encodeWord n := by simp [t₃, t₁, parsedTapes]
  rw [hh₃, encodeWord_length] at p₄
  change (MachineComposition.advance (TM2.step (program triples hne)))^[(n + 1) + 1]
    (some ⟨some .clearHeader, initialState triples.length, t₃⟩) =
    some ⟨some .guard, initialState triples.length, resultTapes triples base n m suffix⟩ at p₄
  rw [show 5 * n + 4 * m + 18 =
      (n + 2) + (3 * (m + 1) + 3) + (3 * (n + 1) + 3) + (m + 2) + (n + 2) by omega,
    Function.iterate_add_apply, p₀, Function.iterate_add_apply, p₁,
    Function.iterate_add_apply, p₂, Function.iterate_add_apply, p₃]
  exact p₄

/-- The exact header trace packaged in the machine execution-time interface. -/
def headersInTime (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m] ++ suffix)
    (hheader : base .header = []) (hcounter : base .counter = [])
    (hscratch : base .scratch = []) (hreversed : base .reversed = []) :
    StateTransition.EvalsToInTime (TM2.step (program triples hne))
      ⟨some (.headerStart 0), initialState triples.length, base⟩
      (some ⟨some .guard, initialState triples.length,
        resultTapes triples base n m suffix⟩) (5 * n + 4 * m + 18) where
  steps := 5 * n + 4 * m + 18
  evals_in_steps := headersTrace triples hne base n m suffix hinput hheader hcounter hscratch hreversed
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Explicit.MachineClone100Headers

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100Triples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Triples

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model MachineClone100Context MachineClone100Affine

def rowOutput (t : Nat × Nat × Nat) (base : Tape → List Bool) : List Bool :=
  (base (.field 0)).flatMap (affineEmit 100 t.1) ++
    (base (.field 1)).flatMap (affineEmit 100 t.2.1) ++
    (base (.field 2)).flatMap (affineEmit 100 t.2.2) ++
    (base (.field 3)).flatMap (affineEmit 1 0)

def rowSteps (base : Tape → List Bool) : Nat :=
  3 * ((base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length) + 12

def startAt (D i : Nat) : Option (Label D) :=
  if h : i < D then some (.setup (.inr (⟨i, h⟩, 0))) else some (.cleanup 0)

@[simp] theorem contextTapes_field (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (base : Tape → List Bool) (j : Fin 4) :
    contextTapes triples c base (.field j) = base (.field j) :=
  contextTapes_other triples c base _ (by intro h; cases h)

@[simp] theorem rowOutput_update (t : Nat × Nat × Nat) (base : Tape → List Bool)
    (out : List Bool) :
    rowOutput t (Function.update base .reversed out) = rowOutput t base := by
  simp [rowOutput]

@[simp] theorem rowSteps_update (base : Tape → List Bool) (out : List Bool) :
    rowSteps (Function.update base .reversed out) = rowSteps base := by
  simp [rowSteps]

theorem fourContexts_tapes (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (base : Tape → List Bool) :
    contextTapes triples (.inr (i, 3))
      (contextTapes triples (.inr (i, 2))
        (contextTapes triples (.inr (i, 1))
          (contextTapes triples (.inr (i, 0)) base))) =
      Function.update base .reversed ((rowOutput (triples.get i) base).reverse ++
        base .reversed) := by
  simp [contextTapes, output_eq_flatMap, emission, contextSource, contextScale,
    contextOffset, tripleField, rowOutput, List.reverse_append, List.append_assoc]

/-- Execute each of the four actual contexts in slot order. -/
theorem rowTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (i : Fin triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[rowSteps base]
      (some ⟨some (.setup (.inr (i, 0))), state, base⟩) =
      some ⟨startAt triples.length (i.val + 1), initialState _,
        Function.update base .reversed ((rowOutput (triples.get i) base).reverse ++
          base .reversed)⟩ := by
  let b1 := contextTapes triples (.inr (i, 0)) base
  let b2 := contextTapes triples (.inr (i, 1)) b1
  let b3 := contextTapes triples (.inr (i, 2)) b2
  have h0 := contextTrace triples nonempty (.inr (i, 0)) base scratchEmpty state
  have h1 := contextTrace triples nonempty (.inr (i, 1)) b1
    (by simpa [b1] using scratchEmpty) (initialState _)
  have h2 := contextTrace triples nonempty (.inr (i, 2)) b2
    (by simpa [b2, b1] using scratchEmpty) (initialState _)
  have h3 := contextTrace triples nonempty (.inr (i, 3)) b3
    (by simpa [b3, b2, b1] using scratchEmpty) (initialState _)
  have next0 : contextNext (.inr (i, (0 : Fin 4))) = some (.setup (.inr (i, 1))) := rfl
  have next1 : contextNext (.inr (i, (1 : Fin 4))) = some (.setup (.inr (i, 2))) := rfl
  have next2 : contextNext (.inr (i, (2 : Fin 4))) = some (.setup (.inr (i, 3))) := rfl
  have next3 : contextNext (.inr (i, (3 : Fin 4))) =
      startAt triples.length (i.val + 1) := by simp [contextNext, startAt]
  rw [next0] at h0
  rw [next1] at h1
  rw [next2] at h2
  rw [next3] at h3
  have combined := chain (chain (chain h0 h1) h2) h3
  simp only [contextSource, b3, b2, b1, contextTapes_field] at combined
  rw [fourContexts_tapes] at combined
  convert combined using 1
  all_goals try with_reducible_and_instances rfl
  unfold rowSteps
  congr 1
  omega

theorem tailTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (remaining : Nat) :
    ∀ (i : Nat), i + remaining = triples.length →
      ∀ (base : Tape → List Bool) (_scratchEmpty : base .scratch = [])
        (state : State triples.length),
        (remaining = 0 → state = initialState _) →
        (MachineComposition.advance (TM2.step (program triples nonempty)))^[remaining * rowSteps base]
          (some ⟨startAt triples.length i, state, base⟩) =
          some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
            (((triples.drop i).flatMap (fun t => rowOutput t base)).reverse ++ base .reversed)⟩ := by
  induction remaining with
  | zero =>
      intro i hi base scratchEmpty state finalState
      have heq : i = triples.length := by omega
      subst i
      rw [finalState rfl]
      simp [startAt]
  | succ remaining ih =>
      intro i hi base scratchEmpty state finalState
      have hiLt : i < triples.length := by omega
      let index : Fin triples.length := ⟨i, hiLt⟩
      let after := Function.update base .reversed
        ((rowOutput (triples.get index) base).reverse ++ base .reversed)
      have row := rowTrace triples nonempty index base scratchEmpty state
      have rest := ih (i + 1) (by omega) after
        (by simpa [after] using scratchEmpty) (initialState _) (by intro _; rfl)
      have combined := chain row rest
      have dropHead : triples.drop i = triples.get index :: triples.drop (i + 1) :=
        List.drop_eq_getElem_cons hiLt
      have hstart : startAt triples.length i = some (.setup (.inr (index, 0))) := by
        simp [startAt, hiLt, index]
      rw [hstart]
      simp only [after, rowSteps_update, rowOutput_update] at combined
      simp only [Function.update_self, Function.update_idem] at combined
      rw [dropHead]
      simp only [List.flatMap_cons, List.reverse_append, List.append_assoc]
      convert combined using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      simp [Nat.add_mul]

theorem tableTrace_raw (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (scratchEmpty : base .scratch = [])
    (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[triples.length * rowSteps base]
      (some ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), state, base⟩) =
      some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
        ((triples.flatMap (fun t => rowOutput t base)).reverse ++ base .reversed)⟩ := by
  have h := tailTrace triples nonempty triples.length 0 (by omega) base scratchEmpty state
    (by intro hz; exact False.elim (by have := List.length_pos_iff.mpr nonempty; omega))
  simpa [startAt, List.length_pos_iff.mpr nonempty] using h

theorem rowOutput_words (t : Nat × Nat × Nat) (base : Tape → List Bool)
    (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    rowOutput t base = encodeWords (affineRecord a b c rhs t) := by
  simp [rowOutput, h0, h1, h2, h3, affineEmit_word, affineRecord, encodeWords,
    List.append_assoc]

theorem tableOutput_words (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    triples.flatMap (fun t => rowOutput t base) =
      encodeWords (triples.flatMap (affineRecord a b c rhs)) := by
  induction triples with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.flatMap_cons, encodeWords_append, ih,
        rowOutput_words t base a b c rhs h0 h1 h2 h3]

/-- The actual inner loop outputs the concrete cloned equation words. -/
theorem tableTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (scratchEmpty : base .scratch = [])
    (state : State triples.length) (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
      triples.length * (3 * ((a + 1) + (b + 1) + (c + 1) + (rhs + 1)) + 12)]
      (some ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), state, base⟩) =
      some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
        ((encodeWords (triples.flatMap (affineRecord a b c rhs))).reverse ++ base .reversed)⟩ := by
  have h := tableTrace_raw triples nonempty base scratchEmpty state
  rw [tableOutput_words triples base a b c rhs h0 h1 h2 h3] at h
  simpa only [rowSteps, h0, h1, h2, h3, encodeWord_length] using h

end UniqueGamesTheorem.Explicit.MachineClone100Triples

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100Loop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Loop

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineClone100Model

def recordBits (r : Record) : List Bool := encodeWords (recordWords r)
def recordsBits (rs : List Record) : List Bool := rs.flatMap recordBits

def clonedRecordBits (triples : List (Nat × Nat × Nat)) (r : Record) : List Bool :=
  encodeWords (triples.flatMap (MachineClone100Triples.affineRecord r.a r.b r.c r.rhs))

def clonedRecordsBits (triples : List (Nat × Nat × Nat)) (rs : List Record) : List Bool :=
  rs.flatMap (clonedRecordBits triples)

def recordFields (r : Record) (j : Fin 4) : List Bool :=
  encodeWord (match j.val with | 0 => r.a | 1 => r.b | 2 => r.c | _ => r.rhs)

/-- The frame records all tapes, including untouched header and output tapes.
At every loop guard the four fields are empty and scratch is empty. -/
def tapes (base : Tape → List Bool) (input counter accumulator : List Bool)
    (fields : Fin 4 → List Bool) : Tape → List Bool
  | .input => input
  | .header => base .header
  | .counter => counter
  | .field j => fields j
  | .scratch => []
  | .reversed => accumulator
  | .output => base .output

theorem update_reversed (base : Tape → List Bool) (input counter acc out : List Bool)
    (fields : Fin 4 → List Bool) :
    Function.update (tapes base input counter acc fields) .reversed out =
      tapes base input counter out fields := by
  funext tape
  cases tape <;> simp [tapes]

theorem counterTapes_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes .counter
      (tapes base input counter acc fields) n [] =
      tapes base input (encodeWord n) acc fields := by
  funext tape
  cases tape <;> simp [MachineUnaryCounter.counterTapes, tapes]

theorem fourTapes_eq (base : Tape → List Bool) (input counter acc suffix : List Bool)
    (r : Record) :
    SourceMachine.fourTapes .input Tape.field
      (tapes base input counter acc (fun _ => [])) r.a r.b r.c r.rhs suffix =
      tapes base suffix counter acc (recordFields r) := by
  funext tape
  cases tape with
  | field j =>
    fin_cases j <;>
      simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
        tapes, recordFields]
  | _ =>
    simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
      tapes]

theorem clearFields_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) :
    MachineClone100Cleanup.clearFields (tapes base input counter acc fields) =
      tapes base input counter acc (fun _ => []) := by
  funext tape
  cases tape <;> simp [tapes]

theorem cleanupSteps_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (r : Record) :
    MachineClone100Cleanup.cleanupSteps (tapes base input counter acc (recordFields r)) =
      r.a + r.b + r.c + r.rhs + 8 := by
  simp [MachineClone100Cleanup.cleanupSteps, tapes, recordFields]
  omega

theorem recordBits_length (r : Record) :
    (recordBits r).length = r.a + r.b + r.c + r.rhs + 4 := by
  simp [recordBits, recordWords, encodeWords]
  omega

def bodyCost (D : Nat) (r : Record) : Nat :=
  (2 + 3 * D) * (recordBits r).length + (8 + 12 * D)

theorem bodyCost_eq (D : Nat) (r : Record) :
    ((r.a + r.b + r.c + r.rhs + 8) +
      D * (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)) +
      (r.a + r.b + r.c + r.rhs + 8) = bodyCost D r := by
  rw [bodyCost, recordBits_length]
  ring

def bodyInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (r : Record) (suffix counter acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.fieldStart 0), initialState _,
        tapes base (recordBits r ++ suffix) counter acc (fun _ => [])⟩
      (some ⟨some .guard, initialState _,
        tapes base suffix counter ((clonedRecordBits triples r).reverse ++ acc)
          (fun _ => [])⟩)
      (bodyCost triples.length r) := by
  let before := tapes base (recordBits r ++ suffix) counter acc (fun _ => [])
  let parsed := tapes base suffix counter acc (recordFields r)
  let out := (clonedRecordBits triples r).reverse ++ acc
  let emitted := tapes base suffix counter out (recordFields r)
  let parse := SourceMachine.fourFieldsInTime .input Tape.field
    (by intro j h; cases h) Label.fieldStart Label.fieldLoop
    (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))))
    (program triples nonempty) (by intro j; rfl) (by intro j; rfl)
    before r.a r.b r.c r.rhs suffix rfl ((), defaultControl _) none
  have parsed_eq : SourceMachine.fourTapes .input Tape.field before
      r.a r.b r.c r.rhs suffix = parsed := fourTapes_eq _ _ _ _ _ _
  rw [parsed_eq] at parse
  let table : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), initialState _, parsed⟩
      (some ⟨some (.cleanup 0), initialState _, emitted⟩)
      (triples.length * (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)) := {
    steps := triples.length *
      (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)
    evals_in_steps := by
      change (MachineComposition.advance (TM2.step (program triples nonempty)))^[_] _ = _
      have h := MachineClone100Triples.tableTrace triples nonempty parsed rfl
        (initialState _) r.a r.b r.c r.rhs rfl rfl rfl rfl
      simpa only [parsed, tapes, update_reversed, clonedRecordBits, emitted, out] using h
    steps_le_m := Nat.le_refl _ }
  let cleanup := MachineClone100Cleanup.cleanupFourInTime triples nonempty emitted
    ((), defaultControl _) none
  have cleared : MachineClone100Cleanup.clearFields emitted =
      tapes base suffix counter out (fun _ => []) := clearFields_eq _ _ _ _ _
  rw [cleared] at cleanup
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parse table
  let combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first cleanup
  exact {
    toEvalsTo := combined.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans combined.steps_le_m
      have hc : MachineClone100Cleanup.cleanupSteps emitted =
          r.a + r.b + r.c + r.rhs + 8 := cleanupSteps_eq _ _ _ _ _
      have hb := bodyCost_eq triples.length r
      omega }

def loopCost (D : Nat) : List Record → Nat
  | [] => 1
  | r :: rs => (1 + bodyCost D r) + loopCost D rs

theorem loopCost_eq (D : Nat) (rs : List Record) :
    loopCost D rs = (2 + 3 * D) * (recordsBits rs).length +
      (9 + 12 * D) * rs.length + 1 := by
  induction rs with
  | nil => simp [loopCost, recordsBits]
  | cons r rs ih =>
    simp only [loopCost, ih, recordsBits, List.flatMap_cons, List.length_append,
      List.length_cons, bodyCost]
    ring

/-- The complete record loop consumes exactly the specified occurrence list.
The final zero guard retains the counter delimiter for the final cleanup stage.
Arbitrary suffixes and already emitted prefixes are preserved explicitly. -/
def loopInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (suffix : List Bool) (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _,
        tapes base (recordsBits rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _,
        tapes base suffix (encodeWord 0) ((clonedRecordsBits triples rs).reverse ++ acc)
          (fun _ => [])⟩)
      (loopCost triples.length rs) := by
  induction rs generalizing acc with
  | nil =>
    let guard := MachineUnaryCounter.guardInTime_zero .counter Label.guard
      (.fieldStart 0) .finalCounter (program triples nonempty) rfl
      (tapes base suffix (encodeWord 0) acc (fun _ => [])) []
      ((), defaultControl _) none
    simpa only [counterTapes_eq, loopCost, recordsBits, clonedRecordsBits,
      List.flatMap_nil, List.reverse_nil, List.nil_append, List.length_nil,
      initialState] using guard
  | cons r rs ih =>
    let before := tapes base (recordBits r ++ (recordsBits rs ++ suffix))
      (encodeWord (rs.length + 1)) acc (fun _ => [])
    let guard := MachineUnaryCounter.guardInTime_succ .counter Label.guard
      (.fieldStart 0) .finalCounter (program triples nonempty) rfl before rs.length []
      ((), defaultControl _) none
    simp only [before, counterTapes_eq] at guard
    let body := bodyInTime triples nonempty base r (recordsBits rs ++ suffix)
      (encodeWord rs.length) acc
    let rest := ih ((clonedRecordBits triples r).reverse ++ acc)
    let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    let combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [loopCost, recordsBits, clonedRecordsBits, List.flatMap_cons,
      List.length_cons, List.reverse_append, List.append_assoc, initialState,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

/-- A linear bound derived from the actual composed execution. -/
def loopInTime_linear (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (suffix : List Bool) (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _,
        tapes base (recordsBits rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _,
        tapes base suffix (encodeWord 0) ((clonedRecordsBits triples rs).reverse ++ acc)
          (fun _ => [])⟩)
      ((2 + 3 * triples.length) * (recordsBits rs).length +
        (9 + 12 * triples.length) * rs.length + 1) := by
  simpa only [loopCost_eq] using loopInTime triples nonempty base suffix rs acc

def recordOfEquation {n : Nat} (e : CloneGap.Equation (Fin n)) : Record :=
  ⟨e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0⟩

theorem recordsBits_equations {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    recordsBits (es.map recordOfEquation) =
      encodeWords (es.flatMap SourceEncoding.equationWords) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, recordsBits, List.flatMap_cons, encodeWords_append] at *
    rw [ih]
    rfl

theorem clonedRecordsBits_equations_table (triples : List (Nat × Nat × Nat))
    {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    clonedRecordsBits triples (es.map recordOfEquation) =
      encodeWords (es.flatMap fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, clonedRecordsBits, List.flatMap_cons, encodeWords_append] at *
    rw [ih]
    rfl

def sourceLoopInTime_table (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (base : Tape → List Bool) (suffix acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _, tapes base
        (encodeWords (es.flatMap SourceEncoding.equationWords) ++ suffix)
        (encodeWord es.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _, tapes base suffix (encodeWord 0)
        ((encodeWords (es.flatMap fun e => triples.flatMap
          (MachineClone100Table.cloneEquationWords e))).reverse ++ acc) (fun _ => [])⟩)
      ((2 + 3 * triples.length) *
        (encodeWords (es.flatMap SourceEncoding.equationWords)).length +
        (9 + 12 * triples.length) * es.length + 1) := by
  simpa only [recordsBits_equations, clonedRecordsBits_equations_table, List.length_map] using
    loopInTime_linear triples nonempty base suffix (es.map recordOfEquation) acc

end UniqueGamesTheorem.Explicit.MachineClone100Loop

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100Run
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Run

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

def tm (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 :=
  machine triples nonempty

def emptyTapes : Tape → List Bool := fun _ => []

def sourceBody (input : SourceEncoding.Input) : List Bool :=
  encodeWords (input.equations.flatMap SourceEncoding.equationWords)

def outputHeaders (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  encodeWords [100 * input.variables, triples.length * input.equations.length]

def outputBody (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  encodeWords (input.equations.flatMap fun equation =>
    triples.flatMap (MachineClone100Table.cloneEquationWords equation))

def outputBits (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  outputHeaders triples input ++ outputBody triples input

def inputTapes (input : SourceEncoding.Input) : Tape → List Bool :=
  fun tape => if tape = .input then SourceEncoding.inputBits input else []

def guardTapes (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    Tape → List Bool :=
  MachineClone100Loop.tapes emptyTapes (sourceBody input) (encodeWord input.equations.length)
    (outputHeaders triples input).reverse (fun _ => [])

def afterLoopTapes (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    Tape → List Bool :=
  MachineClone100Loop.tapes emptyTapes [] (encodeWord 0)
    ((outputBody triples input).reverse ++ (outputHeaders triples input).reverse) (fun _ => [])

theorem inputBits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.variables, input.equations.length] ++ sourceBody input := by
  simp only [SourceEncoding.inputBits, SourceEncoding.inputWords, encodeWords_append, sourceBody]

theorem initList_eq (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    initList (tm triples nonempty) (SourceEncoding.inputBits input) =
      ⟨some (.headerStart 0), initialState triples.length, inputTapes input⟩ := by
  change (⟨some (.headerStart 0), initialState triples.length,
    (initList (tm triples nonempty) (SourceEncoding.inputBits input)).stk⟩ :
    (tm triples nonempty).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨some (.headerStart 0), initialState triples.length, tapes⟩ : (tm triples nonempty).Cfg))
  funext tape
  cases tape <;> simp [initList, tm, machine, inputTapes]
  rfl

theorem headers_result_eq (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    MachineClone100Headers.resultTapes triples (inputTapes input)
      input.variables input.equations.length (sourceBody input) = guardTapes triples input := by
  funext tape
  cases tape <;> simp [MachineClone100Headers.resultTapes, inputTapes, guardTapes,
    MachineClone100Loop.tapes, emptyTapes, outputHeaders]

theorem afterLoop_reversed (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    (afterLoopTapes triples input .reversed).reverse = outputBits triples input := by
  simp only [afterLoopTapes, MachineClone100Loop.tapes, List.reverse_append,
    List.reverse_reverse, outputBits]

theorem afterLoop_length (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    (afterLoopTapes triples input .reversed).length = (outputBits triples input).length := by
  calc
    _ = ((afterLoopTapes triples input .reversed).reverse).length := List.length_reverse.symm
    _ = _ := congrArg List.length (afterLoop_reversed triples input)

theorem finish_eq (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    (⟨none, initialState triples.length,
      MachineClone100Finish.finishTapes (afterLoopTapes triples input)⟩ :
      (tm triples nonempty).Cfg) =
        haltList (tm triples nonempty) (outputBits triples input) := by
  have finished := MachineClone100Finish.finish_eq_haltList triples nonempty
    (afterLoopTapes triples input) (by
      intro tape counter reversed
      cases tape <;> simp_all [afterLoopTapes, MachineClone100Loop.tapes, emptyTapes])
  simpa only [afterLoop_reversed, tm] using finished

/-- Actual execution from the existing input codec to the complete literal
halt configuration, with the sum of the three proved phase budgets. -/
def runInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    TM2OutputsInTime (tm triples nonempty) (SourceEncoding.inputBits input)
      (some (outputBits triples input))
      (((outputBits triples input).length + 2) +
        (((2 + 3 * triples.length) * (sourceBody input).length +
            (9 + 12 * triples.length) * input.equations.length + 1) +
          (5 * input.variables + 4 * input.equations.length + 18))) := by
  let first := MachineClone100Headers.headersInTime triples nonempty
    (inputTapes input) input.variables input.equations.length (sourceBody input)
    (by simpa only [inputTapes, ite_true, if_true] using inputBits_eq input) rfl rfl rfl rfl
  have first' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      (initList (tm triples nonempty) (SourceEncoding.inputBits input))
      (some ⟨some .guard, initialState _, guardTapes triples input⟩)
      (5 * input.variables + 4 * input.equations.length + 18) := by
    rw [initList_eq, ← headers_result_eq]
    exact first
  let middle := MachineClone100Loop.sourceLoopInTime_table triples nonempty
    (n := input.variables) input.equations emptyTapes [] (outputHeaders triples input).reverse
  have middle' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _, guardTapes triples input⟩
      (some ⟨some .finalCounter, initialState _, afterLoopTapes triples input⟩)
      ((2 + 3 * triples.length) * (sourceBody input).length +
        (9 + 12 * triples.length) * input.equations.length + 1) := by
    simpa only [List.append_nil, guardTapes, afterLoopTapes, sourceBody, outputBody] using middle
  let last := MachineClone100Finish.finishInTime triples nonempty (afterLoopTapes triples input) rfl
  have last' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .finalCounter, initialState _, afterLoopTapes triples input⟩
      (some (haltList (tm triples nonempty) (outputBits triples input)))
      ((outputBits triples input).length + 2) := by
    rw [← afterLoop_length, ← finish_eq]
    exact last
  let firstTwo := StateTransition.EvalsToInTime.trans
    (TM2.step (program triples nonempty)) _ _ _ _ _ first' middle'
  let allThree := StateTransition.EvalsToInTime.trans
    (TM2.step (program triples nonempty)) _ _ _ _ _ firstTwo last'
  exact { toEvalsTo := allThree.toEvalsTo, steps_le_m := allThree.steps_le_m }

end UniqueGamesTheorem.Explicit.MachineClone100Run

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100Certified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Certified

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity

noncomputable def certifiedFunction (triples : List (CloneGap.Index × CloneGap.Index × CloneGap.Index))
    (nonempty : triples ≠ []) (f : SourceEncoding.Input → SourceEncoding.Input)
    (output_eq : ∀ input, SourceEncoding.inputBits (f input) =
      MachineClone100Run.outputBits triples input)
    (size_bound : ∀ input,
      (SourceEncoding.inputBits (f input)).length ≤
        (300 * triples.length) * (SourceEncoding.inputBits input).length *
            (SourceEncoding.inputBits input).length +
          (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2) :
    TM2ComputableInPolyTime SourceEncoding.inputBits SourceEncoding.inputBits f where
  tm := MachineClone100Run.tm triples nonempty
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial triples.length
  outputsFun input := by
    change TM2OutputsInTime (MachineClone100Run.tm triples nonempty)
      ((SourceEncoding.inputBits input).map id)
      (some ((SourceEncoding.inputBits (f input)).map id))
      ((timePolynomial triples.length).eval (SourceEncoding.inputBits input).length)
    rw [@List.map_id ((MachineClone100Run.tm triples nonempty).Γ
      (MachineClone100Run.tm triples nonempty).k₀) (SourceEncoding.inputBits input),
      @List.map_id ((MachineClone100Run.tm triples nonempty).Γ
        (MachineClone100Run.tm triples nonempty).k₁) (SourceEncoding.inputBits (f input)),
      output_eq input, timePolynomial_eval]
    let actual := MachineClone100Run.runInTime triples nonempty input
    refine { toEvalsTo := actual.toEvalsTo, steps_le_m := actual.steps_le_m.trans ?_ }
    apply numericalBudget
    · exact SourceEncoding.inputBits_length_ge_variables input
    · exact SourceEncoding.inputBits_length_ge_equations input
    · have h := SourceEncoding.inputBits_length input
      change (SourceEncoding.inputBits input).length =
        input.variables + input.equations.length + 2 +
          (MachineClone100Run.sourceBody input).length at h
      omega
    · rw [← output_eq input]
      exact size_bound input

end UniqueGamesTheorem.Explicit.MachineClone100Certified

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FoldedEquationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type}

/-- One sampled test becomes exactly one three-occurrence equation. -/
def equation (π : J → I) (i₀ : I) (j₀ : J)
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr (canonicalInput j₀ g)
  third := .inr (canonicalInput j₀ (thirdQuery π f g μ))
  rhs := rhsCorrection π i₀ j₀ f μ

/-- Conditioned storage uses only satisfying-assignment coordinates, so identical
restricted canonical inputs are the same variable, even for distinct raw queries. -/
def conditionedEquation (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (f : Cube I) (g μ : Cube J) : Equation (Address i₀ j₀) :=
  equation (fun j => π j.val) i₀ j₀ f (restrictQuery valid g) (restrictQuery valid μ)

end UniqueGamesTheorem.Foundations.Hastad.FoldedEquation

end

section

/-!
Actual equations for clause contexts having no valid local assignment. The
right answer is the constant false bit, represented by two occurrences of one
dummy variable. Those occurrences cancel for every assignment. The remaining
left answer is folded, so its uniform bias is exactly zero.
-/

namespace UniqueGamesTheorem.Foundations.Hastad

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

/-- Rename the three occurrences without merging or dropping any occurrence. -/
def mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) : Equation Name' where
  first := rename e.first
  second := rename e.second
  third := rename e.third
  rhs := e.rhs

namespace EmptyContext

variable {I : Type}

/-- The dummy appears twice. Its assigned bit cancels in the equation. -/
def equation (i₀ : I) (f : Cube I) : Equation (Address i₀) where
  first := .inl (canonicalInput i₀ f)
  second := .inr ()
  third := .inr ()
  rhs := f i₀

@[simp] theorem equation_second_eq_third (i₀ : I) (f : Cube I) :
    (equation i₀ f).second = (equation i₀ f).third := rfl

/-- The two opposite queries give an explicit balanced list of equations. -/
def pairedEquations (i₀ : I) (f : Cube I) : List (Equation (Address i₀)) :=
  [equation i₀ f, equation i₀ (cubeFlip f)]

@[simp] theorem pairedEquations_length (i₀ : I) (f : Cube I) :
    (pairedEquations i₀ f).length = 2 := rfl

end EmptyContext
end UniqueGamesTheorem.Foundations.Hastad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Clone100
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

def equation {n : Nat} (e : Equation (Fin n)) (t : GoodTriple) :
    Equation (Fin (n * 100)) :=
  ⟨nameEquiv n (e.first, t.val.1), nameEquiv n (e.second, t.val.2.1),
    nameEquiv n (e.third, t.val.2.2), e.rhs⟩

def equations {n : Nat} (es : List (Equation (Fin n))) :
    List (Equation (Fin (n * 100))) :=
  es.flatMap (fun e => triples.map (equation e))

theorem equations_length {n : Nat} (es : List (Equation (Fin n))) :
    (equations es).length = es.length * 970200 := by
  induction es with
  | nil => simp [equations]
  | cons e es ih =>
    simp only [equations, List.flatMap_cons, List.length_append, List.length_map,
      triples_length, List.length_cons] at *
    omega

theorem equations_nonempty {n : Nat} (es : List (Equation (Fin n))) (hne : es ≠ []) :
    equations es ≠ [] := by
  apply List.length_pos_iff.mp
  rw [equations_length]
  exact Nat.mul_pos (List.length_pos_iff.mpr hne) (by decide)

def clonedInput (input : SourceEncoding.Input) : SourceEncoding.Input where
  «variables» := input.variables * 100
  equations := equations input.equations
  nonempty := equations_nonempty input.equations input.nonempty

theorem clonedInput_bits_length_le (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (clonedInput input)).length ≤
      input.variables * 100 + input.equations.length * 970200 + 2 +
        input.equations.length * 970200 * (300 * input.variables + 2) := by
  have h := SourceEncoding.inputBits_length_le (clonedInput input)
  simpa [clonedInput, equations_length, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

end
end UniqueGamesTheorem.Outer.Clone100

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineClone100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100

open Turing UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Foundations.Complexity

noncomputable section

theorem equation_words {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Outer.Clone100Triples.GoodTriple) :
    SourceEncoding.equationWords (Outer.Clone100.equation e t) =
      MachineClone100Table.cloneEquationWords e (indices t) := by
  simp [SourceEncoding.equationWords, Outer.Clone100.equation,
    Outer.Clone100.nameEquiv, finProdFinEquiv,
    MachineClone100Table.cloneEquationWords, indices, Nat.mul_comm]

theorem body_words {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    (Outer.Clone100.equations es).flatMap SourceEncoding.equationWords =
      es.flatMap (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [Outer.Clone100.equations, List.flatMap_assoc, List.flatMap_map,
    equation_words, triples]

theorem input_words_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputWords (Outer.Clone100.clonedInput input) =
      [100 * input.variables, triples.length * input.equations.length] ++
        input.equations.flatMap
          (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [SourceEncoding.inputWords, Outer.Clone100.clonedInput,
    Outer.Clone100.equations_length, body_words, triples_length]
  simp [Nat.mul_comm]

theorem input_bits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits (Outer.Clone100.clonedInput input) =
      MachineClone100Run.outputBits triples input := by
  rw [SourceEncoding.inputBits, input_words_eq, encodeWords_append]
  rfl

theorem size_bound (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (Outer.Clone100.clonedInput input)).length ≤
      (300 * triples.length) * (SourceEncoding.inputBits input).length *
        (SourceEncoding.inputBits input).length +
      (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2 := by
  rw [triples_length]
  exact (Outer.Clone100.clonedInput_bits_length_le input).trans
    (serialized_polynomial 970200 (SourceEncoding.inputBits input).length
      input.variables input.equations.length
      (SourceEncoding.inputBits_length_ge_variables input)
      (SourceEncoding.inputBits_length_ge_equations input))

def computation : TM2ComputableInPolyTime SourceEncoding.inputBits
    SourceEncoding.inputBits Outer.Clone100.clonedInput :=
  MachineClone100Certified.certifiedFunction triples triples_nonempty
    Outer.Clone100.clonedInput input_bits_eq size_bound

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

end

end UniqueGamesTheorem.Explicit.MachineClone100

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductSeed
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

namespace UniqueGamesTheorem.Explicit.MachineProductSeed

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open UniqueGamesTheorem.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def localInstruction (command : Command K) (_ : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  pushWord command.1 command.2.reverse (exitAt command.1 exit)

def instruction (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ) :
    Label commands → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction LocalLabel (fun _ => ()) localInstruction commands labels exit

end UniqueGamesTheorem.Explicit.MachineProductSeed

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceFieldArrayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition SourceMachine

/-- Normal form for the changing counter and consumed work-copy prefix. -/
def scanTapes (base : Tape → List Bool) (index : Nat)
    (indexSuffix input : List Bool) : Tape → List Bool :=
  MachineUnaryCounter.counterTapes .index (Function.update base .work input) index indexSuffix

@[simp] theorem scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) : scanTapes base i indexSuffix input .work = input := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

@[simp] theorem scanTapes_index (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) :
    scanTapes base i indexSuffix input .index = encodeWord i ++ indexSuffix := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

end UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextLoad
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A shared-arena context loader. Its finite program copies each selected
clause index, executes the checked lookup, and clears consumed scratch tapes.
Tuple digits and arbitrary extra tapes are protected throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {u : Nat} {Extra : Type}

def place (j : Fin u) : SourceClauseLookup.Tape → Tape u Extra
  | .formula => .formula | .index => .index | .work => .work | .scratch => .scratch
  | .field s => .field j s

def fill (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) : Tape u Extra → List Bool
  | .formula => localTapes .formula | .index => localTapes .index
  | .work => localTapes .work | .scratch => localTapes .scratch
  | .field i s => if i = j then localTapes (.field s) else base (.field i s)
  | p => base p

@[simp] theorem fill_place (j : Fin u) (base : Tape u Extra → List Bool)
    (localTapes : SourceClauseLookup.Tape → List Bool) (p : SourceClauseLookup.Tape) :
    fill j base localTapes (place j p) = localTapes p := by
  cases p <;> simp [fill, place]

@[simp] theorem fill_self (j : Fin u) (base : Tape u Extra → List Bool) :
    fill j base (base ∘ place j) = base := by
  funext p
  cases p <;> simp [fill, place]
  intro h
  subst h
  rfl

variable [DecidableEq Extra]

def coordinateOutput {n : Nat} (j : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .index | .work => []
  | .field k s => if k = j then
      encodeWord ((clauseWords clause)[s.val]'(by simp)) ++ base (.field k s)
    else base (.field k s)
  | p => base p

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_current {n : Nat} (j k : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.current k) = base (.current k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_remaining {n : Nat} (j k : Fin u) (clause : Target.Clause n)
    (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.remaining k) = base (.remaining k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_field {n : Nat} (j : Fin u) (s : Fin 6)
    (clause : Target.Clause n) (base : Tape u Extra → List Bool) :
    coordinateOutput j clause base (.field j s) =
      encodeWord ((clauseWords clause)[s.val]'(by simp)) ++ base (.field j s) := by
  simp [coordinateOutput]

def variableField (j : Fin u) (s : Fin 3) : Tape u Extra := .field j (variableSlot s)

end UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceLoopInitLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition SourceMachine

abbrev Tape (u : Nat) (Extra : Type) := SourceContextLoad.Tape u (HeaderTape ⊕ Extra)

variable {u : Nat} {Extra : Type}

def variableHeader : Tape u Extra := .extra (.inl .variableCount)
def clauseHeader : Tape u Extra := .extra (.inl .clauseCount)

variable [DecidableEq Extra]

def headerOutput (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update (Function.update (Function.update base .work []) variableHeader
    (encodeWord F.variables ++ base variableHeader)) clauseHeader
    (encodeWord F.clauses.length ++ base clauseHeader)

theorem headerOutput_frame (F : Target.Formula) (base : Tape u Extra → List Bool)
    (p : Tape u Extra) (hw : p ≠ .work) (hn : p ≠ variableHeader) (hm : p ≠ clauseHeader) :
    headerOutput F base p = base p := by simp [headerOutput, hw, hn, hm]

def digitOutput (j : Fin u) (m : Nat) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update (Function.update base (.current j) (encodeWord 0)) (.remaining j) (encodeWord (m - 1))

theorem digitOutput_frame (j : Fin u) (m : Nat) (base : Tape u Extra → List Bool)
    (p : Tape u Extra) (hc : p ≠ .current j) (hr : p ≠ .remaining j) :
    digitOutput j m base p = base p := by simp [digitOutput, hc, hr]

def stageTapes (m : Nat) (base : Tape u Extra → List Bool) : Nat → Tape u Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < u then digitOutput ⟨r, h⟩ m (stageTapes m base r)
    else stageTapes m base r

theorem stageTapes_frame (m : Nat) (base : Tape u Extra → List Bool) (r : Nat)
    (p : Tape u Extra) (hc : ∀ j, p ≠ .current j) (hr : ∀ j, p ≠ .remaining j) :
    stageTapes m base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · rw [digitOutput_frame _ _ _ _ (hc _) (hr _), ih]
    · exact ih

theorem stageTapes_current (m : Nat) (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) :
    stageTapes m base r (.current j) = if j.val < r then encodeWord 0 else base (.current j) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j; simp [digitOutput]
      · rw [digitOutput_frame _ _ _ _ (by simpa using hj) (by simp), ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true, if_true]

theorem stageTapes_remaining (m : Nat) (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) :
    stageTapes m base r (.remaining j) =
      if j.val < r then encodeWord (m - 1) else base (.remaining j) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j; simp [digitOutput]
      · rw [digitOutput_frame _ _ _ _ (by simp) (by simpa using hj), ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true, if_true]

def outputTapes (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  stageTapes F.clauses.length (headerOutput F base) u

@[simp] theorem output_current (F : Target.Formula) (base : Tape u Extra → List Bool) (j : Fin u) :
    outputTapes F base (.current j) = encodeWord 0 := by
  simp only [outputTapes, stageTapes_current, j.isLt, ite_true, if_true]

@[simp] theorem output_remaining (F : Target.Formula) (base : Tape u Extra → List Bool) (j : Fin u) :
    outputTapes F base (.remaining j) = encodeWord (F.clauses.length - 1) := by
  simp only [outputTapes, stageTapes_remaining, j.isLt, ite_true, if_true]

theorem output_frame (F : Target.Formula) (base : Tape u Extra → List Bool) (p : Tape u Extra)
    (hw : p ≠ .work) (hn : p ≠ variableHeader) (hm : p ≠ clauseHeader)
    (hc : ∀ j, p ≠ .current j) (hr : ∀ j, p ≠ .remaining j) :
    outputTapes F base p = base p := by
  rw [outputTapes, stageTapes_frame _ _ _ _ hc hr, headerOutput_frame _ _ _ hw hn hm]

@[simp] theorem output_work (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base .work = [] := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp) (by simp)]
  simp [headerOutput, variableHeader, clauseHeader]

@[simp] theorem output_variableHeader (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base variableHeader = encodeWord F.variables ++ base variableHeader := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp [variableHeader]) (by simp [variableHeader])]
  simp [headerOutput, variableHeader, clauseHeader]

@[simp] theorem output_clauseHeader (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base clauseHeader = encodeWord F.clauses.length ++ base clauseHeader := by
  rw [outputTapes, stageTapes_frame _ _ _ _ (by simp [clauseHeader]) (by simp [clauseHeader])]
  simp [headerOutput]

@[simp] theorem output_formula (F : Target.Formula) (base : Tape u Extra → List Bool) :
    outputTapes F base .formula = base .formula :=
  output_frame F base .formula (by simp) (by simp [variableHeader])
    (by simp [clauseHeader]) (by simp) (by simp)

end UniqueGamesTheorem.Foundations.Hastad.SourceLoopInit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

/-- All instructions act on physical stacks. The final load only resets the
finite internal register; no input-dependent integer is stored in it. -/
def statement (clearKeys : List K) (accumulator output : K) (canonical : σ)
    (labels : Label clearKeys → Λ) (exit : Option Λ) :
    Label clearKeys → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl label => MachineDrainMany.instruction clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) label
  | .inr false => Reduction.MachineTransfer.loopAt accumulator output id false
      (labels (.inr false)) (some (labels (.inr true)))
  | .inr true => .load (fun _ => (canonical, none)) (Reduction.MachineTransfer.exitAt output exit)

open scoped BigOperators

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeFinish

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_HonestTestLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem event_nonempty (F : Formula) (hne : F.clauses ≠ []) :
    Nonempty (RandomEvent F) :=
  ⟨(⟨0, List.length_pos_iff.mpr hne⟩, .first)⟩

def eventLaw (F : Formula) (hne : F.clauses ≠ []) :
    FiniteDistribution (RandomEvent F) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  exact FiniteDistribution.uniform _

def visibleQuestion (F : Formula) (e : RandomEvent F) :
    Fin F.variables × Fin F.clauses.length :=
  (nameAt (clauseAt F e.1) e.2, e.1)

def baseGame (F : Formula) (hne : F.clauses ≠ []) :
    Game (Fin F.variables) (Fin F.clauses.length) Bool ClauseAnswer where
  questions := (eventLaw F hne).pushforward (visibleQuestion F)
  accepts := baseAccepts F

@[simp] theorem baseGame_accepts (F : Formula) (hne : F.clauses ≠ [])
    (v : Fin F.variables) (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    (baseGame F hne).accepts v c i j = baseAccepts F v c i j := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceGame

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceOccurrences
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Executable radix numbering of padded global long-code tables and an ordered
equation occurrence list. The code enumerates random tapes, not distinct
equations: coinciding equations and repeated variable occurrences are retained.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

/-- Distinct table vertices and the three side tags never share storage.
Unused ambient query positions are harmless explicit padding. -/
abbrev GlobalKey (V C I J : Type) := (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit)

def globalEncoding {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    Encoding (GlobalKey V C I J) :=
  (v.prod (i.function Encoding.bool)).sum
    ((c.prod (j.function Encoding.bool)).sum Encoding.unit)

@[simp] theorem globalEncoding_size {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J) :
    (globalEncoding v c i j).size =
      v.size * 2 ^ i.size + (c.size * 2 ^ j.size + 1) := rfl

/-- Extending by false gives a unique padded address to a restricted query. -/
def extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) : Cube J :=
  fun j => if h : valid j = true then f ⟨j, h⟩ else false

@[simp] theorem extendRestricted_valid {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) (j : {j : J // valid j = true}) :
    extendRestricted valid f j.val = f j := by simp [extendRestricted, j.property]

@[simp] theorem restrictQuery_extendRestricted {J : Type} (valid : J → Bool)
    (f : Cube {j : J // valid j = true}) :
    restrictQuery valid (extendRestricted valid f) = f := by
  funext j
  exact extendRestricted_valid valid f j

@[simp] theorem canonicalInput_half {I : Type} [Fintype I] [DecidableEq I]
    (i₀ : I) (f : HalfCube i₀) :
    canonicalInput i₀ f.val = f := by
  apply Subtype.ext
  simp [canonicalInput, representative, f.property]

/-- The global index map is an explicit equivalence, including all padding. -/
def assignmentOfKey {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) : Fin (globalEncoding v c i j).size → Bool :=
  fun q => bits ((globalEncoding v c i j).code.symm q)

@[simp] theorem assignmentOfKey_code {V C I J : Type}
    (v : Encoding V) (c : Encoding C) (i : Encoding I) (j : Encoding J)
    (bits : GlobalKey V C I J → Bool) (key : GlobalKey V C I J) :
    assignmentOfKey v c i j bits ((globalEncoding v c i j).code key) = bits key := by
  exact congrArg bits ((globalEncoding v c i j).code.symm_apply_apply key)

section LocalEquations

variable {V C I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def localAddress (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (i₀ : I) (j₀ : {j : J // valid j = true}) :
    FoldedEquation.Address i₀ j₀ → Fin (globalEncoding vE cE iE jE).size
  | .inl f => (globalEncoding vE cE iE jE).code (.inl (v, f.val))
  | .inr g => (globalEncoding vE cE iE jE).code (.inr (.inl (c, extendRestricted valid g.val)))

def conditionedOccurrence
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true}) (f : Cube I) (g μ : Cube J) :
    Equation (Fin (globalEncoding vE cE iE jE).size) :=
  mapEquation (localAddress vE cE iE jE v c valid i₀ j₀)
    (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)

end LocalEquations

def firstValid {J : Type} (e : Encoding J) (valid : J → Bool) :
    Option {j : J // valid j = true} := findValid valid e.enumerate

/-- Mapping the ordered enumeration preserves all sampled occurrences. -/
def occurrenceList {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : List (Equation Name) := tape.enumerate.map emit

@[simp] theorem occurrenceList_length {Tape Name : Type} (tape : Encoding Tape)
    (emit : Tape → Equation Name) : (occurrenceList tape emit).length = tape.size := by
  simp [occurrenceList]

section ConcreteSource

open SourceContexts
open UniqueGamesTheorem.Reduction.FiniteNoise

def clauseAnswerEncoding : Encoding PCP.ClauseAnswer := ⟨8, clauseAnswerFinEquiv⟩

def slotEncoding : Encoding PCP.Slot where
  size := 3
  code :=
    { toFun := fun s => match s with | .first => 0 | .second => 1 | .third => 2
      invFun := fun i => if i.val = 0 then .first else if i.val = 1 then .second else .third
      left_inv := by intro s; cases s <;> rfl
      right_inv := by decide }

def iEncoding (u : ℕ) : Encoding (I u) := (Encoding.fin u).function Encoding.bool
def jEncoding (u : ℕ) : Encoding (J u) := (Encoding.fin u).function clauseAnswerEncoding
def variableEncoding (F : Target.Formula) (u : ℕ) : Encoding (VariableContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.variables)
def clauseEncoding (F : Target.Formula) (u : ℕ) : Encoding (ClauseContext F u) :=
  (Encoding.fin u).function (Encoding.fin F.clauses.length)
def slotContextEncoding (u : ℕ) : Encoding (SlotContext u) :=
  (Encoding.fin u).function slotEncoding

def proofEncoding (F : Target.Formula) (u : ℕ) :
    Encoding (GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :=
  globalEncoding (variableEncoding F u) (clauseEncoding F u) (iEncoding u) (jEncoding u)

def nBits (F : Target.Formula) (u : ℕ) : ℕ := (proofEncoding F u).size

@[simp] theorem nBits_eq (F : Target.Formula) (u : ℕ) :
    nBits F u = F.variables ^ u * 2 ^ (2 ^ u) +
      (F.clauses.length ^ u * 2 ^ (8 ^ u) + 1) := rfl

def dummyIndex (F : Target.Formula) (u : ℕ) : Fin (nBits F u) :=
  (proofEncoding F u).code (.inr (.inr ()))

def rightAnchor (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) :
    Option {j : J u // validJ F c j = true} := firstValid (jEncoding u) (validJ F c)

/-- Independent actual half-tables extend to the explicit padded key space.
Only the canonically selected right anchor is read at each clause context. -/
def halfTableKeyAssignment (F : Target.Formula) (u : ℕ)
    (a : VariableContext F u → HalfCube (leftAnchor u) → Bool)
    (b : ∀ c : ClauseContext F u, ∀ j₀ : {j : J u // validJ F c j = true},
      HalfCube j₀ → Bool) :
    GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u) → Bool
  | .inl (v, f) => a v (canonicalInput (leftAnchor u) f)
  | .inr (.inl (c, g)) =>
    match rightAnchor F c with
    | none => false
    | some j₀ => b c j₀ (canonicalInput j₀ (restrictQuery (validJ F c) g))
  | .inr (.inr _) => false

def emptyAddress (F : Target.Formula) (u : ℕ) (v : VariableContext F u) :
    EmptyContext.Address (leftAnchor u) → Fin (nBits F u)
  | .inl h => (proofEncoding F u).code (.inl (v, h.val))
  | .inr _ => dummyIndex F u

/-- The private query law depends only on the two visible contexts.
In particular, the hidden sampled slots are not inputs to `pi`. -/
def contextEquation (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) : Equation (Fin (nBits F u)) :=
  match rightAnchor F c with
  | none => mapEquation (emptyAddress F u v) (EmptyContext.equation (leftAnchor u) t.1)
  | some j₀ => conditionedOccurrence (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      t.1 t.2.2 (realizedNoise t.2.1)

def testTapeEncoding (u D : ℕ) : Encoding (SourceTape.TestTape (I u) (J u) D) :=
  ((iEncoding u).function Encoding.bool).prod
    (((jEncoding u).function (Encoding.fin D)).prod ((jEncoding u).function Encoding.bool))

abbrev SourceIndex (F : Target.Formula) (u D : ℕ) :=
  (ClauseContext F u × SlotContext u) × SourceTape.TestTape (I u) (J u) D

def sourceIndexEncoding (F : Target.Formula) (u D : ℕ) : Encoding (SourceIndex F u D) :=
  ((clauseEncoding F u).prod (slotContextEncoding u)).prod (testTapeEncoding u D)

def sourceEquation (F : Target.Formula) (u D : ℕ) (p : SourceIndex F u D) :
    Equation (Fin (nBits F u)) :=
  contextEquation F u D p.1.1 (sampledVariables F p.1.1 p.1.2) p.2

/-- The entire finite random-tape population, including repeated visible
contexts and all equation multiplicities, in a fixed explicit order. -/
def rawSourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  occurrenceList (sourceIndexEncoding F u D) (sourceEquation F u D)

@[simp] theorem rawSourceList_length (F : Target.Formula) (u D : ℕ) :
    (rawSourceList F u D).length =
      (F.clauses.length ^ u * 3 ^ u) *
        (2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u))) := by
  rw [rawSourceList, occurrenceList_length]
  rfl

end ConcreteSource

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHonestLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHonest

open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.FiniteNoise
open scoped BigOperators

/-- Padded query tables are evaluated at one coordinate per context. Left and
right tables have disjoint tags, and the unused dummy bit is fixed to false. -/
def taggedAssignment {V C I J : Type} (left : V → I) (right : C → J) :
    (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit) → Bool
  | .inl (v, f) => f (left v)
  | .inr (.inl (c, g)) => g (right c)
  | .inr (.inr _) => false

@[simp] theorem taggedAssignment_left {V C I J : Type}
    (left : V → I) (right : C → J) (v : V) (f : Cube I) :
    taggedAssignment left right (.inl (v, f)) = f (left v) := rfl

@[simp] theorem taggedAssignment_right {V C I J : Type}
    (left : V → I) (right : C → J) (c : C) (g : Cube J) :
    taggedAssignment left right (.inr (.inl (c, g))) = g (right c) := rfl

open SourceContexts
open SourceOccurrences

/-- A single assignment to the globally tagged padded tables. It is defined
from the input assignment alone, before any incidence or test is sampled. -/
def honestGlobal (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) :
    (VariableContext F u × Cube (I u)) ⊕
      ((ClauseContext F u × Cube (J u)) ⊕ Unit) → Bool :=
  taggedAssignment (fun v => honestI F v assignment) (fun c => honestJ F c assignment)

/-- The same global proof in the construction's explicit radix numbering. -/
def honestBits (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool) : Fin (nBits F u) → Bool :=
  assignmentOfKey (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
    (jEncoding u) (honestGlobal F u assignment)

@[simp] theorem honestBits_code (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.variables → Bool)
    (key : GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :
    honestBits F u assignment ((proofEncoding F u).code key) =
      honestGlobal F u assignment key :=
  assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u)
    (iEncoding u) (jEncoding u) (honestGlobal F u assignment) key

end UniqueGamesTheorem.Foundations.Hastad.SourceHonest

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceDescriptorEmissionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Emit one fixed descriptor equation from three preserved unary base registers.
The output order is first address, second address, third address, RHS. The actual
stack program emits those fields in reverse order. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

open Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences

variable {K Λ σ : Type} {width : Nat}

/-- Reverse only digit positions. All six fixed work/control roles stay put. -/
def reverseSlots (slots : MachineHorner.Layout width ↪ K) : MachineHorner.Layout width ↪ K :=
  (Equiv.sumCongr (Equiv.refl (Fin 6)) (Fin.revPerm (n := width))).toEmbedding.trans slots

@[simp] theorem reverseSlots_control (slots : MachineHorner.Layout width ↪ K) (i : Fin 6) :
    reverseSlots slots (.inl i) = slots (.inl i) := rfl

@[simp] theorem reverseSlots_digit (slots : MachineHorner.Layout width ↪ K) (i : Fin width) :
    reverseSlots slots (.inr i) = slots (.inr i.rev) := rfl

variable [DecidableEq K]

variable {u : Nat} {Extra : Type}

/-- Control roles may include preserved headers and dedicated protected extras. -/
def clauseSlots (controls : Fin 6 ↪ Extra) :
    MachineHorner.Layout u ↪ SourceContextLoad.Tape u Extra where
  toFun
    | .inl i => .extra (controls i)
    | .inr i => .current i
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (controls.injective (SourceContextLoad.Tape.extra.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (SourceContextLoad.Tape.current.inj h)

/-- Each coordinate selects its own loaded variable field, even if names repeat. -/
def variableSlots (controls : Fin 6 ↪ Extra) (selected : SlotContext u) :
    MachineHorner.Layout u ↪ SourceContextLoad.Tape u Extra where
  toFun
    | .inl i => .extra (controls i)
    | .inr i => SourceContextLoad.variableField i (slotEncoding.code (selected i))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (controls.injective (SourceContextLoad.Tape.extra.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (SourceContextLoad.Tape.field.inj h).1

@[simp] theorem clauseSlots_control (controls : Fin 6 ↪ Extra) (i : Fin 6) :
    clauseSlots (u := u) controls (.inl i) = .extra (controls i) := rfl

@[simp] theorem clauseSlots_digit (controls : Fin 6 ↪ Extra) (i : Fin u) :
    clauseSlots controls (.inr i) = .current i := rfl

@[simp] theorem variableSlots_control (controls : Fin 6 ↪ Extra) (selected : SlotContext u) (i : Fin 6) :
    variableSlots controls selected (.inl i) = .extra (controls i) := rfl

@[simp] theorem variableSlots_digit (controls : Fin 6 ↪ Extra) (selected : SlotContext u) (i : Fin u) :
    variableSlots controls selected (.inr i) =
      SourceContextLoad.variableField i (slotEncoding.code (selected i)) := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryLoopLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual fixed finite traversal of all query/noise tapes. The finite
control contains one branch for each prescribed tape. The input-dependent
signature and the three address bases remain in registers throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOdometerSchedule

open Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

abbrev Tape := SourceContextLoad.Tape

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

/-- Set the active low coordinates; higher digits and every other tape retain
their original contents. Unary digit stacks have no unread suffix. -/
def setDigits (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .current i => if h : i.val < q then encodeWord (digits ⟨i.val, h⟩)
      else base (.current i)
  | .remaining i => if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (.remaining i)
  | k => base k

def setAcc (accumulator : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    Tape u Extra → List Bool := Function.update base (.extra accumulator) bits

def putDigit (i : Fin u) (base : Tape u Extra → List Bool) (d r : ℕ) :
    Tape u Extra → List Bool := digitTapes (.current i) (.remaining i) base d r [] []

omit [DecidableEq Extra] in
@[simp] theorem setDigits_zero (m : ℕ) (digits : Fin 0 → ℕ)
    (base : Tape u Extra → List Bool) : setDigits m digits base = base := by
  funext k
  cases k <;> simp [setDigits]

omit [DecidableEq Extra] in
@[simp] theorem setDigits_extra (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (a : Extra) :
    setDigits m digits base (.extra a) = base (.extra a) := rfl

@[simp] theorem setAcc_self (a : Extra) (base : Tape u Extra → List Bool) :
    setAcc a base (base (.extra a)) = base := by
  simp [setAcc]

@[simp] theorem setAcc_setAcc (a : Extra) (base : Tape u Extra → List Bool)
    (first second : List Bool) : setAcc a (setAcc a base first) second = setAcc a base second := by
  simp [setAcc]

@[simp] theorem setAcc_apply (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setAcc a base bits (.extra a) = bits := by simp [setAcc]

@[simp] theorem putDigit_extra (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) : putDigit i base d r (.extra a) = base (.extra a) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

def configuration (label : Λ) (canonical : σ) (tapes : Tape u Extra → List Bool) :
    Configuration (Tape u Extra) Λ σ := ⟨some label, (canonical, none), tapes⟩

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape u Extra → List Bool) : Configuration (Tape u Extra) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape u Extra) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc accumulator base ((allBits bits).reverse ++ base (.extra accumulator))))

omit [DecidableEq Extra] in
@[simp] theorem initial_current (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.current i) =
      encodeWord 0 := by simp [initialConfiguration, configuration, setDigits]

omit [DecidableEq Extra] in
@[simp] theorem initial_remaining (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.remaining i) =
      encodeWord (m - 1) := by simp [initialConfiguration, configuration, setDigits]

@[simp] theorem final_current (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.current i) =
      encodeWord 0 := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_remaining (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.remaining i) =
      encodeWord (m - 1) := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_accumulator (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.extra accumulator) =
      ((tupleOrder m u).flatMap bits).reverse ++ base (.extra accumulator) := by
  simp [finalConfiguration, configuration, allBits]

end UniqueGamesTheorem.Foundations.Hastad.SourceOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductProgram
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Explicit.MachineProductProgram

open Turing
open UniqueGamesTheorem.Foundations
open Complexity Hastad
open UniqueGamesTheorem.Reduction.MachineTransfer


abbrev Tape (t : Nat) := SourceContextLoad.Tape t (Extra t)

def auxiliary (t : Nat) (i : Fin 10) : Tape t := .extra (.inl i)
def constantDigit (t : Nat) (i : Fin (t + 1)) : Tape t := .extra (.inr i)
def accumulator (t : Nat) : Tape t := auxiliary t 6
def output (t : Nat) : Tape t := auxiliary t 9

def rowRole (t : Nat) : MachineProductRow.Layout t → Tape t
  | .inl (.inl (.inl 0)) => .formula
  | .inl (.inl (.inl 1)) => .index
  | .inl (.inl (.inl 2)) => .work
  | .inl (.inl (.inl 3)) => .scratch
  | .inl (.inl (.inr (.inl i))) => .current i
  | .inl (.inl (.inr (.inr i))) => .field i 0
  | .inl (.inr i) => auxiliary t (Fin.castLE (by omega) i)
  | .inr _ => auxiliary t 7

def decodeRow (t : Nat) : Tape t → Option (MachineProductRow.Layout t)
  | .formula => some (.inl (.inl (.inl 0)))
  | .index => some (.inl (.inl (.inl 1)))
  | .work => some (.inl (.inl (.inl 2)))
  | .scratch => some (.inl (.inl (.inl 3)))
  | .current i => some (.inl (.inl (.inr (.inl i))))
  | .field i s => if s = 0 then some (.inl (.inl (.inr (.inr i)))) else none
  | .extra (.inl i) => if h : i.val < 7 then some (.inl (.inr ⟨i.val, h⟩))
      else if i = 7 then some (.inr ()) else none
  | _ => none

theorem decodeRow_role (t : Nat) (i : MachineProductRow.Layout t) :
    decodeRow t (rowRole t i) = some i := by
  rcases i with (((i | (i | i)) | i) | i)
  · fin_cases i <;> rfl
  · rfl
  · simp [decodeRow, rowRole]
  · simp [rowRole, auxiliary, decodeRow, i.isLt]
  · cases i; rfl

def rowSlots (t : Nat) : MachineProductRow.Layout t ↪ Tape t where
  toFun := rowRole t
  inj' := by
    intro a b h
    have d := congrArg (decodeRow t) h
    exact Option.some.inj (by simpa only [decodeRow_role] using d)

def powerRole (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) → Tape t
  | .inl 0 => auxiliary t (if edgeCount then 8 else 0)
  | .inl 1 => auxiliary t 1
  | .inl 2 => auxiliary t 2
  | .inl 3 => auxiliary t 5
  | .inl 4 => auxiliary t 3
  | .inl 5 => auxiliary t 4
  | .inr i => constantDigit t i

theorem powerRole_injective (t : Nat) (edgeCount : Bool) : Function.Injective (powerRole t edgeCount) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;> cases edgeCount <;> simp_all [powerRole, auxiliary]
    | inr b => fin_cases a <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
  | inr a =>
    cases b with
    | inl b => fin_cases b <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
    | inr b => simpa [powerRole, constantDigit] using h

def powerSlots (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) ↪ Tape t :=
  ⟨powerRole t edgeCount, powerRole_injective t edgeCount⟩

def initRole (t : Nat) : MachineOdometerInit.Tape t → Tape t
  | .radix => auxiliary t 8
  | .scratch => .copyScratch
  | .current i => .current i
  | .remaining i => .remaining i

def seedCommands (t : Nat) : List (MachineProductSeed.Command (Tape t)) :=
  List.ofFn (fun i : Fin (t + 1) => (constantDigit t i, encodeWord (MachineProductPower.digits i.val)))

noncomputable def clearKeys (t : Nat) : List (Tape t) :=
  Finset.univ.toList.filter (fun k => decide (k ≠ accumulator t ∧ k ≠ output t))

@[simp] theorem mem_clearKeys (t : Nat) (k : Tape t) :
    k ∈ clearKeys t ↔ k ≠ accumulator t ∧ k ≠ output t := by
  simp [clearKeys]

noncomputable section

inductive Label (q t : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | seedStart
  | seed (inner : MachineProductSeed.Label (seedCommands t))
  | power (edgeCount : Bool) (inner : MachineProductPower.Label t)
  | alphabetHeader
  | initialize_ (inner : MachineOdometerInit.Label t)
  | row (inner : MachineProductRow.Label (rowSlots t) (ProductMachineSemantics.commands q t))
  | check (i : Fin t)
  | reset (i : Fin t)
  | finishStart
  | finish (inner : SourceRuntimeFinish.Label (clearKeys t))
  deriving DecidableEq, Fintype

def headerDestination (t : Nat) : Fin 3 → Tape t
  | 0 => auxiliary t 0
  | 1 => auxiliary t 7
  | 2 => auxiliary t 8

def rowMain (q t : Nat) : Label q t :=
  .row (.inl (MachineProductRow.localMain (rowSlots t) (ProductMachineSemantics.sourceCommand t)))

def nextCheck (q t i : Nat) : Label q t := if h : i < t then .check ⟨i, h⟩ else .finishStart

def headerNext (q t : Nat) (i : Fin 3) : Label q t :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .seedStart

def program (q t : Nat) : Label q t → TM2.Stmt (fun _ : Tape t => Bool) (Label q t) State
  | .headerStart i => SourceMachine.fieldStart (headerDestination t i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .formula (headerDestination t i)
      (.headerRead i) (some (headerNext q t i))
  | .seedStart => exitAt .formula (MachineProductSeed.entry (seedCommands t) Label.seed
      (some (.power false (.inl .start))))
  | .seed inner => MachineProductSeed.instruction (seedCommands t) Label.seed
      (some (.power false (.inl .start))) inner
  | .power false inner => MachineProductPower.instruction (powerSlots t false) (accumulator t)
      (Label.power false) (some .alphabetHeader) inner
  | .power true inner => MachineProductPower.instruction (powerSlots t true) (accumulator t)
      (Label.power true) (some (MachineOdometerInit.labelAt Label.initialize_ 0)) inner
  | .alphabetHeader => UniqueGamesTheorem.Reduction.MachineSubstitution.pushWord (accumulator t)
      (encodeWord (q ^ t)) (.goto fun _ => .power true (.inl .start))
  | .initialize_ inner => MachineOdometerInit.statement (initRole t) Label.initialize_
      (some (rowMain q t)) inner
  | .row inner => MachineProductRow.instruction (rowSlots t) (q + 2)
      (ProductMachineSemantics.commands q t) Label.row (some (nextCheck q t 0)) inner
  | .check i => MachineTupleOdometer.increment (.current i) (.remaining i)
      (rowMain q t) (.reset i)
  | .reset i => MachineTupleOdometer.reset (.current i) (.remaining i)
      (.reset i) (nextCheck q t (i.val + 1))
  | .finishStart => exitAt .formula (SourceRuntimeFinish.entry (clearKeys t) Label.finish)
  | .finish inner => SourceRuntimeFinish.statement (clearKeys t) (accumulator t) (output t)
      ((), ()) Label.finish none inner

def machine (q t : Nat) : FinTM2 where
  K := Tape t
  k₀ := .formula
  k₁ := output t
  Γ _ := Bool
  Λ := Label q t
  main := .headerStart 0
  σ := State
  initialState := (((), ()), none)
  m := program q t

end

end UniqueGamesTheorem.Explicit.MachineProductProgram

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductHeadersFrameLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Concrete header and initialized work-tape frames for the product machine. -/

namespace UniqueGamesTheorem.Explicit.MachineProductHeaders

open Turing
open UniqueGamesTheorem.Foundations Target Complexity Hastad
open MachineProductProgram


/-- All permanent input fields and fixed Horner digits are explicit tape words.
The argument is the forward-order emitted already emitted. -/
def frame {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) : Tape t → List Bool
  | .formula => encodeWords (ProductMachineSemantics.inputTable H)
  | .extra (.inl i) =>
      if i = 0 then encodeWord H.vertices
      else if i = 7 then encodeWord q
      else if i = 8 then encodeWord H.constraints.length
      else if i = 6 then emitted.reverse else []
  | .extra (.inr i) => encodeWord (MachineProductPower.digits i.val)
  | _ => []

def headerBits {q : Nat} (H : Instance q) (t : Nat) : List Bool :=
  encodeWords [H.vertices ^ t, q ^ t, H.constraints.length ^ t]

/-- Canonical frame before the odometer digits are filled. -/
def baseTapes {q : Nat} (H : Instance q) (t : Nat) : Tape t → List Bool :=
  frame H t (headerBits H t)

@[simp] theorem frame_accumulator {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    frame H t emitted (accumulator t) = emitted.reverse := by simp [frame, accumulator, auxiliary]

@[simp] theorem frame_output {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    frame H t emitted (output t) = [] := by simp [frame, output, auxiliary]

@[simp] theorem frame_radix {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) :
    frame H t emitted (powerSlots t edgeCount (.inl 0)) =
      encodeWord (if edgeCount then H.constraints.length else H.vertices) := by
  cases edgeCount <;> simp [frame, powerSlots, powerRole, auxiliary]

@[simp] theorem frame_digit {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) (i : Fin (t + 1)) :
    frame H t emitted (powerSlots t edgeCount (.inr i)) =
      encodeWord (MachineProductPower.digits i.val) := rfl

@[simp] theorem frame_power_output {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) : frame H t emitted (powerSlots t edgeCount (.inl 3)) = [] := by
  simp [frame, powerSlots, powerRole, auxiliary]




/-! The three actual output-header emissions of the product controller. -/




end UniqueGamesTheorem.Explicit.MachineProductHeaders



/-! Three actual header reads for the fixed-alphabet, fixed-power product
machine. The constraint table stays in its original order on the formula tape. -/



/-! Actual literal initialization of the finitely many product power digits. -/



/-! Whole tuple traversal of the concrete product program. The odometer theorem
is instantiated by the proved actual row trace, not by an assumed row machine. -/

namespace UniqueGamesTheorem.Explicit.MachineProductLoop

open Turing
open UniqueGamesTheorem.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram


variable {q t : Nat}

noncomputable section

def tupleTapes (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) : Tape t → List Bool :=
  SourceOdometerSchedule.setDigits H.constraints.length (fun i => (edges i).val)
    (SourceOdometerSchedule.setAcc (Sum.inl (6 : Fin 10)) base out)

@[simp] theorem tupleTapes_current (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) (i : Fin t) :
    tupleTapes H base edges out (.current i) = encodeWord (edges i).val := by
  simp [tupleTapes, SourceOdometerSchedule.setDigits, i.isLt]

@[simp] theorem tupleTapes_accumulator (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) :
    tupleTapes H base edges out (accumulator t) = out := by
  simp [tupleTapes, accumulator, auxiliary, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]

def rowBits (H : Target.Instance q) (edges : Fin t → Fin H.constraints.length) : List Bool :=
  MachineProductRow.rowBits (ProductMachineSemantics.fieldValue H edges)
    (ProductMachineSemantics.commands q t)

end

end UniqueGamesTheorem.Explicit.MachineProductLoop



/-! Exact final cleanup and binary-output identification for the product
controller. The final runtime bound is derived from actual stack lengths. -/

namespace UniqueGamesTheorem.Explicit.MachineProductFinish

open Turing
open UniqueGamesTheorem.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram


variable {q t : Nat}

noncomputable section

def afterRows (H : Target.Instance q) (t : Nat) : (machine q t).Cfg :=
  SourceOdometerSchedule.finalConfiguration (nextCheck q t t) ((), ())
    (Sum.inl (6 : Fin 10)) (MachineProductHeaders.baseTapes H t) (MachineProductLoop.rowBits (t := t) H)

theorem allRows_eq (H : Target.Instance q) (t : Nat) :
    (MachineTupleOdometer.tupleOrder H.constraints.length t).flatMap (MachineProductLoop.rowBits (t := t) H) =
      ProductMachineSemantics.allRowsBits H t := by
  simp only [MachineTupleOdometer.tupleOrder, ProductMachineSemantics.allRowsBits,
    List.ofFn_eq_map, List.flatMap_map, MachineProductLoop.rowBits]

end

end UniqueGamesTheorem.Explicit.MachineProductFinish

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

namespace Header

abbrev Tape := MachineCloudPrefix.Tape ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool

end Header

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end


