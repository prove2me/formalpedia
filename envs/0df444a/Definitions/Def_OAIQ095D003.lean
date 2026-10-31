-- Prove2me | Definitions.Def_OAIQ095D003
-- name    : OAIQ095D003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:01:13.501266+00:00
-- url     : https://prove2.me/theorems/91bd3829-31f7-4f9b-b063-096dabe7d7be
-- title:
--   Definitions bundle OAIQ095D003 of the split of OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 210 declarations of OpenAI's Lean: 38 definitions, 4 inductive types or structures and 168 theorems. The definitions and types are `OAI.Ostmann.ActualProgressionTheta`, `OAI.Ostmann.ActualRealLowHeightRegion`, `OAI.Ostmann.BulkIntegrand.headSlice`, `OAI.Ostmann.BulkIntegrand.pullBulk`, `OAI.Ostmann.BulkIntegrand.withLogCutoffs`, `OAI.Ostmann.DensityZeroBin`, `OAI.Ostmann.DensityZeroIndex`, `OAI.Ostmann.PrimitiveComplexCharacter.atModulus`, `OAI.Ostmann.PublishedComplexZeroDensity`, `OAI.Ostmann.PublishedComplexZeroRegion`, `OAI.Ostmann.PublishedProgressionInput`, `OAI.Ostmann.PublishedProgressionInput.mertensConstant`, `OAI.Ostmann.PublishedProgressionInput.restrictKappa`, `OAI.Ostmann.PublishedRealZeroInput`, `OAI.Ostmann.PublishedSiegelBound`, `OAI.Ostmann.PublishedSmoothExplicitFormula`, `OAI.Ostmann.SmoothExplicitFormulaCore`, `OAI.Ostmann.SmoothExplicitFormulaCore.toPublished`, `OAI.Ostmann.actualLocalZero`, `OAI.Ostmann.actualPageConstant`, `OAI.Ostmann.canonicalCharacterRieszTerm`, `OAI.Ostmann.characterRieszMean`, `OAI.Ostmann.characterRieszVerticalTerm`, `OAI.Ostmann.characterRieszZeroTerm`, `OAI.Ostmann.characterZeroCopySelfReflection`, `OAI.Ostmann.characterZeroIndexSelfReflection`, `OAI.Ostmann.imprimitiveEulerProduct`, `OAI.Ostmann.indexedRealZero`, `OAI.Ostmann.liftPrimitiveCharacter`, `OAI.Ostmann.pageBeta`, `OAI.Ostmann.pageRieszKernelNorm`, `OAI.Ostmann.primitiveCharacterReduction`, `OAI.Ostmann.primitiveOfNonprincipal`, `OAI.Ostmann.reducedRieszMain`, `OAI.Ostmann.reducedRieszMean`, `OAI.Ostmann.rightRieszIntegrand`, `OAI.Ostmann.scheduledNodeLevel`, `OAI.Ostmann.smoothTrivialZeroTerm`, `OAI.Ostmann.smoothZeroTerm`, `OAI.Ostmann.zetaAtHeight` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Mathlib_Analysis_SpecialFunctions_ImproperIntegrals`, `Mathlib_NumberTheory_AbelSummation`, `Mathlib_NumberTheory_LSeries_RiemannZetaAbelContinuation`, `Mathlib_NumberTheory_LSeries_RiemannZetaAbelKernel`, `Mathlib_NumberTheory_LSeries_RiemannZetaPartialSum`, `Ostmann_Arithmetic_BulkCoordinateInsertion`, `Ostmann_Arithmetic_BulkLeafPolynomials`, `Ostmann_Arithmetic_BulkLogContinuity`, `Ostmann_Arithmetic_BulkLogWeightedIntegrand`, `Ostmann_Arithmetic_BulkNodePolynomials`, `Ostmann_Arithmetic_BulkPiIntegral`, `Ostmann_Arithmetic_BulkSlotPolynomials`, `Ostmann_Characters_CharacterAbsoluteRightBound`, `Ostmann_Characters_CharacterCompletedLogDerivative`, `Ostmann_Characters_CharacterLogDerivativePole`, `Ostmann_Characters_CharacterLogarithmicSeparation`, `Ostmann_Characters_CharacterPageComparison`, `Ostmann_Characters_CharacterSelfReflection`, `Ostmann_Characters_LogCutoffPolynomial`, `Ostmann_Characters_PrimitiveCharacterReduction`, `Ostmann_Characters_PrimitiveLiftReduction`, `Ostmann_Construction_ScheduledNodeSources`, `Ostmann_Preliminaries_DivisorPowerBound`, `Ostmann_ZeroDensity_ActualLocalZeros`, `Ostmann_ZeroDensity_ActualPageUniqueness`, `Ostmann_ZeroDensity_ActualProgressionInput`, `Ostmann_ZeroDensity_ActualRealZeroExpansion`, `Ostmann_ZeroDensity_ActualRealZeroIndices`, `Ostmann_ZeroDensity_ActualThetaEstimate`, `Ostmann_ZeroDensity_CanonicalRieszKernelBound`, `Ostmann_ZeroDensity_CanonicalThetaSize`, `Ostmann_ZeroDensity_CharacterContourDiskZeros`, `Ostmann_ZeroDensity_CharacterContourZeros`, `Ostmann_ZeroDensity_CharacterGammaContour`, `Ostmann_ZeroDensity_CharacterGammaGrowth`, `Ostmann_ZeroDensity_CharacterHadamardBounds`, `Ostmann_ZeroDensity_CharacterIndexedRealZero`, `Ostmann_ZeroDensity_CharacterNearZeroSimple`, `Ostmann_ZeroDensity_CharacterNearZeroUnique`, `Ostmann_ZeroDensity_CharacterRieszBoundary`, `Ostmann_ZeroDensity_CharacterRieszResidueBound`, `Ostmann_ZeroDensity_CharacterRieszZeroSelection`, `Ostmann_ZeroDensity_CharacterTrivialZero`, `Ostmann_ZeroDensity_CharacterZeroPartialSums`, `Ostmann_ZeroDensity_CompletedLogDerivativeSeparated`, `Ostmann_ZeroDensity_ComplexCharacterConjugation`, `Ostmann_ZeroDensity_ComplexCharacterHadamard`, `Ostmann_ZeroDensity_DensityZeroBins`, `Ostmann_ZeroDensity_FullHeightRealExclusion`, `Ostmann_ZeroDensity_FullHeightRealRegion`, `Ostmann_ZeroDensity_FullHeightRealShiftedBound`, `Ostmann_ZeroDensity_GammaHalfStripBound`, `Ostmann_ZeroDensity_ImprimitiveEulerBound`, `Ostmann_ZeroDensity_InducedCharacterRieszDecay`, `Ostmann_ZeroDensity_LowHeightZeroBounds`, `Ostmann_ZeroDensity_LowHeightZeroExclusion`, `Ostmann_ZeroDensity_MertensFromProgression`, `Ostmann_ZeroDensity_NonprincipalLogDerivative`, `Ostmann_ZeroDensity_NonquadraticZeroBound`, `Ostmann_ZeroDensity_NonquadraticZeroRegion`, `Ostmann_ZeroDensity_OrdinaryPrimeIntervals`, `Ostmann_ZeroDensity_PrimitiveCharacterCard`, `Ostmann_ZeroDensity_PrimitiveRieszComparison`, `Ostmann_ZeroDensity_ProgressionConstantRestriction`, `Ostmann_ZeroDensity_PublishedComplexZeroDensity`, `Ostmann_ZeroDensity_PublishedProgressionInputs`, `Ostmann_ZeroDensity_PublishedRealZeros`, `Ostmann_ZeroDensity_PublishedSmoothExplicitFormula`, `Ostmann_ZeroDensity_RealCharacterConjugateZeros`, `Ostmann_ZeroDensity_RealCharacterPairZeroBound`, `Ostmann_ZeroDensity_RealCharacterTrigonometric`, `Ostmann_ZeroDensity_RealZeroPairExclusion`, `Ostmann_ZeroDensity_RegularizedZeta`, `Ostmann_ZeroDensity_ResiduePrimePowerRemoval`, `Ostmann_ZeroDensity_ResiduePsiLargeModulus`, `Ostmann_ZeroDensity_RieszCanonicalResidueMain`, `Ostmann_ZeroDensity_RieszCharacterMainSum`, `Ostmann_ZeroDensity_RieszContourRectangle`, `Ostmann_ZeroDensity_RieszDirichletIntegral`, `Ostmann_ZeroDensity_RieszSingleZeroRectangle`, `Ostmann_ZeroDensity_RieszTailEstimate`, `Ostmann_ZeroDensity_RieszVerticalWeight`, `Ostmann_ZeroDensity_SmallDiskLogDerivative`, `Ostmann_ZeroDensity_SmoothExplicitFormulaCore`, `Ostmann_ZeroDensity_TotientSqrtBound`, `Ostmann_ZeroDensity_VonMangoldtLogarithmicBound`, `Ostmann_ZeroDensity_ZeroFreeNumerics`, `Ostmann_ZeroDensity_ZetaDiskBounds`, `Ostmann_ZeroDensity_ZetaDiskQuotient`, `Ostmann_ZeroDensity_ZetaDiskZeros`, `Ostmann_ZeroDensity_ZetaLocalLogDerivative`.
--
--   **Imports.** It imports the bundles `OAIQ095D000` and `OAIQ095D001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ095D006` and `OAIQ095D007`; the statements `OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction`, `OAI.Ostmann.common_center_biased_populations_impossible`, `OAI.Ostmann.inverseGoldbach_of_published`, `OAI.Ostmann.inverseGoldbach_without_summand_size`, `OAI.Ostmann.publishedComplexZeroDensity`, `OAI.Ostmann.quadraticBandMass_isLittleO`, `OAI.Ostmann.twoInfiniteSummandsImpossible_of_published` and `OAI.Ostmann.twoInfiniteSummandsImpossible_without_summand_size`; the proofs of `OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction`, `OAI.Ostmann.inverseGoldbach`, `OAI.Ostmann.inverseGoldbach_of_published`, `OAI.Ostmann.quadraticBandMass_isLittleO`, `OAI.Ostmann.quadratic_first_total_growth`, `OAI.Ostmann.quadratic_gcd_corrections_power_bound`, `OAI.Ostmann.quadratic_gcd_main_growth`, `OAI.Ostmann.quadratic_rough_power_growth` and `OAI.Ostmann.twoInfiniteSummandsImpossible`.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ095D000
import Definitions.Def_OAIQ095D001

section
-- module Solutions.OAIQ095_OS.Mathlib_Analysis_SpecialFunctions_ImproperIntegrals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Improper-integral estimates

Elementary power-integral evaluations and convergence criteria for interval integrals on
half-lines.
-/

section

open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology

theorem intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (g : ℝ → ℝ) (c : ℝ)
    (hfm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ioi c)))
    (hbound : ∀ᵐ u ∂MeasureTheory.volume.restrict (Ioi c), ‖f u‖ ≤ g u)
    (hg : MeasureTheory.IntegrableOn g (Ioi c) MeasureTheory.volume) :
    Tendsto (fun N : ℕ => ∫ u in c..N, f u) atTop (𝓝 (∫ u in Ioi c, f u)) :=
  intervalIntegral_tendsto_integral_Ioi c (MeasureTheory.IntegrableOn.mono' hg hfm hbound)
    tendsto_natCast_atTop_atTop
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_NumberTheory_AbelSummation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite-sum reindexing for Abel summation

Elementary reindexing lemmas for sums over initial intervals, used when passing between
floor sums and range sums.
-/

section

open Finset
open scoped BigOperators

variable {𝕜 : Type*} [AddCommGroup 𝕜]

/-- Floor-summation reindexing for sequences with `c 0 = 0`. -/
theorem _root_.sum_Icc_zero_floor_eq_sum_range {c : ℕ → 𝕜} (hc0 : c 0 = 0) (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, c k = ∑ n ∈ range ⌊t⌋₊, c (n + 1) :=
  Finset.sum_Icc_zero_eq_sum_range_succ (m := ⌊t⌋₊) (f := c) hc0
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_NumberTheory_LSeries_RiemannZetaAbelKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fractional-part kernel for the Abel zeta formula

`K_s(u) = {u} · u^{-s-1}` and its integrability / domination lemmas, used in
`RiemannZetaPartialSum` and `RiemannZetaAbelContinuation`.

## Main results

* `zetaAbelFractKernel`, `norm_zetaAbelFractKernel_le`
* `ZetaAbelFractKernel.intervalIntegrable`, `integrableOn_Ioi`, `tendsto_integral_Ioi`
* `ZetaAbelFractKernel.hasDerivAt_in_param`, `kernel_deriv_norm_bound_on_ball`
* `ZetaAbelFractKernel.integral_analytic`
-/

section

open scoped Topology
open Real Set Filter Topology MeasureTheory Complex

/-- `{u} · u^{-s-1}` is dominated by `u^{- re s - 1}` for `u ≥ 1`. -/
theorem norm_zetaAbelFractKernel_le (u : ℝ) (hu : 1 ≤ u) (s : ℂ) :
    ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) := by
  have hu0 : 0 < u := one_pos.trans_le hu
  have hfract_le1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by simpa using Int.fract_abs_le_one u
  have hle : ‖zetaAbelFractKernel s u‖ ≤ ‖(u : ℂ) ^ (-s - 1)‖ := by
    calc
      _ = ‖((Int.fract u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by rw [zetaAbelFractKernel, norm_mul]
      _ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ := by
        exact mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
      _ = ‖(u : ℂ) ^ (-s - 1)‖ := one_mul _
  have hb : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    have hre : (-s - 1).re = -s.re - 1 := by
      simp [sub_eq_add_neg]
    simpa [hre] using Complex.norm_cpow_eq_rpow_re_of_pos hu0 (-s - 1)
  exact hle.trans_eq hb

namespace ZetaAbelFractKernel

lemma ae_bound_Ioi (s : ℂ) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) :=
  ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
    norm_zetaAbelFractKernel_le u (le_of_lt hu) s

lemma intervalIntegrable (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => zetaAbelFractKernel s u) volume a b := by
  let μ := volume.restrict (Icc a b)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
  have hmeas := aestronglyMeasurable s (Icc a b) measurableSet_Icc
  have hbound_ae : ∀ᵐ u ∂μ, ‖zetaAbelFractKernel s u‖ ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ ?_)
    intro u huIcc
    have hu0 : 0 < u := lt_of_lt_of_le one_pos (ha.trans huIcc.1)
    have hg_eq : g u = u ^ (-s.re - 1) := by
      simp [g, Complex.norm_cpow_eq_rpow_re_of_pos hu0, sub_eq_add_neg]
    exact (norm_zetaAbelFractKernel_le u (ha.trans huIcc.1) s).trans (le_of_eq hg_eq.symm)
  have hg : Integrable g μ := by
    simpa [μ, g] using!
      (Complex.continuousOn_ofReal_cpow (ha := one_pos.trans_le ha)).norm.integrableOn_compact
        isCompact_Icc
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
    integrable_of_norm_sub_le hmeas hf0 hg
      (hbound_ae.mono fun u hu => by simpa [sub_eq_add_neg, μ, g] using hu)

theorem tendsto_integral_Ioi (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) :=
  intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le (f := fun u => zetaAbelFractKernel s u)
    (g := fun u => u ^ (-s.re - 1)) 1
    (aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi) (ae_bound_Ioi s)
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)

theorem integrableOn_Ioi (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun u => zetaAbelFractKernel s u) (volume.restrict (Ioi (1 : ℝ))) := by
  set ε : ℝ := s.re / 2
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
  have hfm := aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi
  have hε : 0 < ε := half_pos hs
  have hεle : ε ≤ s.re := half_le_self (le_of_lt hs)
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖zetaAbelFractKernel s u‖ ≤ g u :=
    ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
      (norm_zetaAbelFractKernel_le u (le_of_lt hu) s).trans
        (Real.rpow_le_rpow_of_exponent_le (le_of_lt hu) (by linarith [hεle]))
  simpa [IntegrableOn] using
    IntegrableOn.mono' (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) hfm hbound

theorem hasDerivAt_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
    HasDerivAt (fun w => zetaAbelFractKernel w u)
      (-((Real.log u) : ℂ) * zetaAbelFractKernel z u) z := by
  have h := HasDerivAt.const_mul_ofReal_cpow_neg_sub_one ((Int.fract u : ℝ) : ℂ)
    (lt_trans zero_lt_one hu) z
  have hfun : (fun w => zetaAbelFractKernel w u) = fun w => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1) := by
    ext w; simp [zetaAbelFractKernel]
  exact (h.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by
    simp [zetaAbelFractKernel, Complex.ofReal_log (x := u) (hx := le_of_lt (lt_trans zero_lt_one hu)),
      mul_comm, mul_assoc, mul_left_comm])

theorem kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖ ≤ Real.log u * u ^ (-1 - ε) := by
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
  have hinner : ‖zetaAbelFractKernel x u‖ ≤ u ^ (-1 - ε) :=
    (norm_zetaAbelFractKernel_le u hu1 x).trans (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith))
  have hlognorm : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
  calc
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖
        = Real.log u * ‖zetaAbelFractKernel x u‖ := by rw [norm_mul, hlognorm]
    _ ≤ Real.log u * u ^ (-1 - ε) := mul_le_mul_of_nonneg_left hinner (le_of_lt (Real.log_pos hu))

/-- `∫_{(1,∞)} K_z` is analytic in `z` for `re z > 0`. -/
theorem integral_analytic (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u) s := by
  set ε : ℝ := s.re / 2
  have hεpos : 0 < ε := half_pos hs
  obtain ⟨δ, hδpos, hδprop⟩ :=
    Complex.exists_pos_radius_forall_mem_ball_re_ge (z₀ := s) (a := ε) (half_lt_self hs)
  set F : ℂ → ℝ → ℂ := zetaAbelFractKernel
  set F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
  set bound : ℝ → ℝ := fun u => (2 / ε) * u ^ (-1 - ε / 2)
  have hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [bound, IntegrableOn] using
      (integrableOn_Ioi_rpow_of_lt (by linarith [half_pos hεpos]) one_pos).const_mul (2 / ε)
  have hDiff : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds s (half_pos hδpos)) ?_
    intro z hz
    set δ' : ℝ := δ / 2
    have hz_lt : dist z s < δ := dist_lt_of_mem_ball_half hz hδpos
    have hRe : ∀ y ∈ Metric.ball z δ', ε ≤ y.re := fun y hy =>
      hδprop z y hz_lt (dist_lt_of_mem_ball_half hy hδpos)
    have hzRe : ε ≤ z.re := hδprop s z (by simpa [dist_self] using hδpos) hz_lt
    exact (hasDerivAt_integral_param_dominated_Ioi F F' z δ' (half_pos hδpos)
      (eventually_aestronglyMeasurable_param z)
      (by simpa using integrableOn_Ioi z (lt_of_lt_of_le hεpos hzRe))
      (by simpa [F, F'] using aestronglyMeasurable_param_deriv z)
      bound hbound_int
      (ae_on_Ioi_of_all fun u hu w hw =>
        (kernel_deriv_norm_bound_on_ball ε u hu w (hRe w hw)).trans
          (by simpa [bound] using Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg hεpos hu))
      (ae_on_Ioi_of_all fun u hu w hw => by simpa [F, F'] using hasDerivAt_in_param u hu w)).differentiableAt
  exact (Complex.analyticAt_iff_eventually_differentiableAt
    (f := fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u)).2 hDiff

end ZetaAbelFractKernel
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_NumberTheory_LSeries_RiemannZetaPartialSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Abel-summation partial sums for the Riemann zeta function

For `re s > 1`, the partial Dirichlet sum `∑_{n<N} (n+1)^{-s}` satisfies the classical
Abel tail identity in `ZetaPartialSum.abel_formula`, and converges to `riemannZeta s`.

Used in `RiemannZetaAbelContinuation` to match the Abel integral formula for `re s > 1`.
-/

section

open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex Nat ZetaAbelFractKernel

namespace ZetaPartialSum

lemma intervalIntegrable_mul_cpow_id (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Icc a b) :=
    Complex.continuous_ofReal.continuousOn.mul
      (Complex.continuousOn_ofReal_cpow (r := -s - 1) (ha := one_pos.trans_le ha))
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
    (f := fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) hab).2
    (hcont.integrableOn_compact isCompact_Icc)

lemma abel_summation (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) * (N : ℂ) ^ (-s)
        - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else (1 : ℂ)
  have hle : (1 : ℝ) ≤ N := mod_cast hN
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t := fun t ht => by
    by_cases hs : s = 0; · simp [f, hs]
    simpa [f] using (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le zero_lt_one ht.1).ne'
      (neg_ne_zero.mpr hs)).differentiableAt
  have hint : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) (N : ℝ)) :=
    (Complex.continuousOn_deriv_ofReal_cpow_neg (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) zero_lt_one).integrableOn_compact
      isCompact_Icc
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (f := f) (m := N)
      (hc := by simp [c]) (hf_diff := hdiff) (hf_int := hint)
  have hLHS : (∑ k ∈ Finset.Icc 0 N, f k * c k) = zetaPartialSum s N := by
    rw [Finset.sum_Icc_zero_eq_sum_range_succ (by simp [c])]
    simp [zetaPartialSum, f, c]
  have hInt_congr :
      (∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    apply intervalIntegral.integral_congr_Ioc_of_le hle
    intro u hu
    rw [sum_Icc_zero_floor_eq_sum_range (hc0 := by simp [c]) u, Complex.deriv_ofReal_cpow_neg s (lt_trans zero_lt_one hu.1)]
    simp [c, Finset.sum_const, Finset.card_range, mul_comm, mul_left_comm]
  calc
    zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
          simpa [hLHS] using habel.trans (by rw [← intervalIntegral.integral_of_le hle])
    _ = f N * (∑ k ∈ Finset.Icc 0 N, c k)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt_congr]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
            - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          have hMain : f N * (∑ k ∈ Finset.Icc 0 N, c k) = (N : ℂ) * f N := by
            rw [Finset.sum_Icc_zero_eq_sum_range_succ (by simp [c])]
            simp [c, f, Finset.sum_const, Finset.card_range, mul_comm]
          rw [hMain]; simp [f]

lemma abel_split (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N = (N : ℂ) ^ (1 - s) + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  rw [abel_summation s N hN]
  have hInt :
      ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
        = (-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr_Ioc_of_le (mod_cast hN)]
    intro u _; simp [neg_mul, mul_left_comm]
  rw [hInt, sub_eq_add_neg, neg_mul, neg_neg]
  simp [Complex.natCast_mul_cpow_neg_eq_cpow_one_sub N s (Nat.ne_of_gt (Nat.succ_le_iff.mp hN))]

lemma integral_split_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hab : (1 : ℝ) ≤ N := mod_cast hN
  have hI1 := intervalIntegrable_mul_cpow_id s le_rfl hab
  have hI2 := ZetaAbelFractKernel.intervalIntegrable s le_rfl hab
  calc
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
        = ∫ u in (1 : ℝ)..N, ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u hu
          simp [natCast_floor_eq_sub_fract u (le_trans zero_le_one (le_of_lt hu.1)), sub_eq_add_neg]
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
          rw [← intervalIntegral.integral_sub hI1 hI2]
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u _; simp [sub_mul, zetaAbelFractKernel]
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
          - ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
          congr 1
          apply intervalIntegral.integral_congr_Ioc_of_le hab
          intro u hu
          exact Complex.ofReal_cpow_mul_cpow_neg_sub_one (s := s) (hu := lt_trans zero_lt_one hu.1)

lemma abel_sub_fract (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s)
        + (s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - (s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) := by
  rw [abel_split s N hN, integral_split_fract s N hN, mul_sub, add_sub_assoc]

/-- Abel tail formula for `re s > 1`. -/
theorem abel_formula (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u := by
  have hstep := abel_sub_fract s N hN
  rw [cpow_integral s hs N hN] at hstep
  let A := (N : ℂ) ^ (1 - s)
  have halg : A + s / (1 - s) * (A - 1) = A / (1 - s) + 1 + 1 / (s - 1) := by
    field_simp [sub_ne_zero.mpr hs, sub_ne_zero.mpr hs.symm]; ring
  rwa [halg] at hstep

end ZetaPartialSum
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_NumberTheory_LSeries_RiemannZetaAbelContinuation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Abel-summation continuation of the Riemann zeta function

For `s ≠ 1` in the half-plane `{re s > σ₀}` with `σ₀ = 1/10`, the Riemann zeta function equals the
Abel-summation tail formula from [`Mathlib.NumberTheory.AbelSummation`]: writing `{u}` for the
fractional part of `u > 0` and `K_s(u) = {u} · u^{-s-1}`, one has

`ζ(s) = 1 + (s - 1)⁻¹ - s ∫_{(1,∞)} K_s(u) du`.

The threshold `σ₀`, the domain, the kernel, and the renormalized integral are bundled in
`zetaAbelContinuationReLower`, `zetaAbelContinuationDomain`, `zetaAbelFractKernel`, and
`zetaAbelContinuationFormula`. The equality with `riemannZeta` on that domain is proved by analytic
continuation from `re s > 1`, where the formula is the classical Abel partial-sum limit.

Kernel and partial-sum input live in `RiemannZetaAbelKernel` and `RiemannZetaPartialSum`.

## Main results

* `zetaAbelContinuationDomain`, `zetaAbelContinuationFormula`
* `riemannZeta_eq_zetaAbelContinuationFormula`
* `norm_zetaAbelContinuationFormula_le`, `analyticOn_zetaAbelContinuationFormula`
-/

section

open scoped Topology
open Real Set Filter Topology MeasureTheory Complex ZetaPartialSum ZetaAbelFractKernel

theorem isPreconnected_zetaAbelContinuationDomain : IsPreconnected zetaAbelContinuationDomain := by
  convert (Complex.isPathConnected_halfSpace_re_gt_diff_singleton
      (a := zetaAbelContinuationReLower) (p := (1 : ℂ)) one_lt_zetaAbelContinuationReLower).isConnected.isPreconnected using 1
  all_goals try with_reducible_and_instances rfl
  ext z; simp [zetaAbelContinuationDomain, and_comm]

theorem riemannZeta_abel_integral (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hsne : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by simp [h]
    linarith
  set G : ℕ → ℂ := fun N =>
    (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
      - s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hEv : ∀ᶠ N in atTop, zetaPartialSum s N = G N :=
    (eventually_ge_atTop 1).mono fun N hN => (abel_formula s hsne N hN).trans rfl
  have hG_to_zeta := (tendsto_congr' hEv).mp (tendsto_riemannZeta s hs)
  have hA : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Tendsto.const_mul (1 / (1 - s))
        (tendsto_natCast_cpow_zero_of_neg_re (1 - s)
          (by rw [Complex.sub_re, Complex.one_re]; linarith)))
  have hK : Tendsto (fun _ : ℕ => (1 + 1 / (s - 1) : ℂ)) atTop
      (𝓝 (1 + 1 / (s - 1))) := tendsto_const_nhds
  have hIntMul := (tendsto_integral_Ioi s hs).const_mul s
  set Aseq : ℕ → ℂ := fun N => (N : ℂ) ^ (1 - s) / (1 - s)
  set Kseq : ℕ → ℂ := fun _ => (1 + 1 / (s - 1) : ℂ)
  set Iseq : ℕ → ℂ := fun N => s * ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u
  have hSum : Tendsto (fun N => Aseq N + Kseq N) atTop (𝓝 (1 + 1 / (s - 1))) := by
    simpa using! ((continuous_fst.add continuous_snd).tendsto _).comp (hA.prodMk_nhds hK)
  have hG_limit : Tendsto G atTop
      (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
    have hSub : Tendsto (fun N => Aseq N + Kseq N - Iseq N) atTop
        (𝓝 ((1 + 1 / (s - 1)) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) := by
      simpa [Function.comp_apply, Function.comp_def, sub_eq_add_neg] using
        ((continuous_fst.add continuous_snd).tendsto _).comp (hSum.prodMk_nhds hIntMul.neg)
    have hGdef : (fun N => Aseq N + Kseq N - Iseq N) = G := by
      funext N
      simp [Aseq, Kseq, Iseq, G, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [hGdef] using hSub
  have huniq := tendsto_nhds_unique hG_to_zeta hG_limit
  simpa [zetaAbelContinuationFormula, sub_eq_add_neg] using huniq

/-- On `zetaAbelContinuationDomain`, the Abel formula satisfies the standard strip bound. -/
theorem norm_zetaAbelContinuationFormula_le (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    ‖zetaAbelContinuationFormula s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
  set g : ℝ → ℝ := fun u => u ^ (-s.re - 1)
  let μ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ))
  have hs_re := zetaAbelContinuationDomain_re_pos hs
  have hint :
      ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ ≤ ‖s‖ / s.re :=
    mul_le_mul_of_nonneg_left
      ((MeasureTheory.norm_integral_le_of_norm_le (μ := μ)
        (f := fun u => zetaAbelFractKernel s u) (g := g)
        (by
          simpa [μ, g, IntegrableOn] using
            (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos))
        (by
          refine (ae_restrict_iff' measurableSet_Ioi).2 (MeasureTheory.ae_of_all _ ?_)
          intro u hu
          simpa [g] using norm_zetaAbelFractKernel_le u (le_of_lt hu) s)).trans
        (by simpa [μ, g, one_div] using
          (le_of_eq (by simp [integral_Ioi_rpow_neg_re_sub_one (s := s) hs_re]))))
      (norm_nonneg s)
  have hsplit :
      ‖zetaAbelContinuationFormula s‖ ≤
        1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
    simp only [zetaAbelContinuationFormula, one_div]
    calc
      ‖1 + (s - 1)⁻¹ - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖
          ≤ ‖1 + (s - 1)⁻¹‖ + ‖-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le (1 + (s - 1)⁻¹) (-s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)
      _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := by
        gcongr
        · simpa [norm_one] using norm_add_le (1 : ℂ) ((s - 1)⁻¹)
        · exact (norm_mul_le (-s) (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)).trans_eq
            (by rw [norm_neg])
  calc
    ‖zetaAbelContinuationFormula s‖
        ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u‖ := hsplit
    _ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / s.re := add_le_add_right hint _
    _ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by simp [one_div]

/-- The Abel continuation formula is analytic on `zetaAbelContinuationDomain`. -/
theorem analyticOn_zetaAbelContinuationFormula :
    AnalyticOn ℂ zetaAbelContinuationFormula zetaAbelContinuationDomain := by
  simp only [AnalyticOn, zetaAbelContinuationDomain, Set.mem_ofPred_eq]
  intro s ⟨hs_ne, hs_re⟩
  apply AnalyticAt.analyticWithinAt
  refine analyticAt_const.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_) |>.sub
    (analyticAt_id.mul (integral_analytic s (lt_trans zetaAbelContinuationReLower_pos hs_re)))
  exact sub_ne_zero.mpr hs_ne

/-- The Abel integral formula agrees with `ζ` on `zetaAbelContinuationDomain`. -/
theorem riemannZeta_eq_zetaAbelContinuationFormula (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hUo := isOpen_zetaAbelContinuationDomain
  have hζ : AnalyticOnNhd ℂ riemannZeta zetaAbelContinuationDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    have h : AnalyticOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
      isOpen_compl_singleton.analyticOn_iff_analyticOnNhd.mpr analyticOn_riemannZeta
    exact AnalyticOn.mono h fun _ hz => hz.1
  have hF : AnalyticOnNhd ℂ zetaAbelContinuationFormula zetaAbelContinuationDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    exact analyticOn_zetaAbelContinuationFormula
  have hEq : riemannZeta =ᶠ[𝓝 (2 : ℂ)] zetaAbelContinuationFormula := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
      using riemannZeta_abel_integral w hw
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hζ hF isPreconnected_zetaAbelContinuationDomain two_mem_zetaAbelContinuationDomain hEq) hs
end
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkPiIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The joint bulk integral in ordinary finite product coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def BulkIntegrand.headSlice {n : ℕ}
    (f : BulkIntegrand (Fin (n + 1))) (a : ℝ) : BulkIntegrand (Fin n) where
  toFun x := f (Fin.cons a x)
  measurable := f.measurable.comp (Measurable.of_eval (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_const
    · exact measurable_pi_apply j))
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    exact ⟨C, hC, fun x => hf _⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkCoordinateInsertion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freeze the nonbulk coordinates and integrate the selected bulk slots -/

namespace Ostmann
open MeasureTheory
open scoped Classical

noncomputable def BulkIntegrand.pullBulk {σ J : Type*} [Fintype σ] [Fintype J]
    (f : BulkIntegrand σ) (base : σ → ℝ) (e : J ↪ σ) : BulkIntegrand J where
  toFun y := f (bulkCoordinateInsert base e y)
  measurable := f.measurable.comp (Measurable.of_eval fun i => by
    by_cases h : ∃ j, e j = i
    · simpa only [bulkCoordinateInsert, dite_eq_left h] using (measurable_pi_apply h.choose :
        Measurable (fun y : J → ℝ => y h.choose))
    · simpa only [bulkCoordinateInsert, dite_eq_right h] using (measurable_const :
        Measurable (fun _ : J → ℝ => base i)))
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    exact ⟨C, hC, fun y => hf _⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedProgressionInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Precisely stated published inputs for primes in progressions

Reference: H. L. Montgomery and R. C. Vaughan, *Multiplicative Number
Theory I: Classical Theory*, Cambridge Studies in Advanced Mathematics 97,
Chapter 11, DOI 10.1017/CBO9780511618314.013.

`PublishedProgressionInput.theta` is Corollary 11.20, equations (11.32) and
(11.34), p. 381. `complete` specifies the exceptional zero in Theorem 11.3,
p. 360. `unique` is the real-zero specialization of Corollary 11.10 (Page),
p. 369. The positive zero-free constant can be decreased so these use one
constant and the harmless denominator `log (4*q)` throughout.

These are explicit conditional inputs. In particular, no logarithmic
interval estimate or arithmetic comparison is assumed here.
-/

namespace Ostmann

noncomputable def pageBeta (z : Option PrimitiveRealZero) : ℝ :=
  match z with
  | none => 1
  | some e => e.beta

theorem pageCoefficient_abs_le_one (z : Option PrimitiveRealZero) (a : ℕ) :
    |pageCoefficient z a| ≤ 1 := by
  cases z with
  | none => simp [pageCoefficient]
  | some e => exact (Real.norm_eq_abs _).symm ▸ e.character.norm_le_one _

theorem pageBeta_pos (z : Option PrimitiveRealZero) : 0 < pageBeta z := by
  cases z with
  | none => norm_num [pageBeta]
  | some e => exact e.beta_pos

theorem pageBeta_le_one (z : Option PrimitiveRealZero) : pageBeta z ≤ 1 := by
  cases z with
  | none => exact le_rfl
  | some e => exact e.beta_lt_one.le

/-- The restricted classical analytic input. The family chooses the local
exceptional primitive character, if one exists, for each modulus. -/
structure PublishedProgressionInput where
  kappa : ℝ
  decay : ℝ
  errorConstant : ℝ
  kappa_pos : 0 < kappa
  decay_pos : 0 < decay
  errorConstant_nonneg : 0 ≤ errorConstant
  localZero : ℕ → Option PrimitiveRealZero
  divides : ∀ q e, localZero q = some e → e.modulus ∣ q
  /-- Theorem 11.3: any zero in the stated exceptional region is retained. -/
  complete : ∀ q, 1 ≤ q → ∀ e : PrimitiveRealZero, e.modulus ∣ q →
    1 - kappa / Real.log (4 * (q : ℝ)) ≤ e.beta → localZero q = some e
  /-- Corollary 11.10, restricted to positive real zeros. -/
  unique : ∀ Q, 2 ≤ Q → ∀ e f : PrimitiveRealZero,
    e.modulus ≤ Q → f.modulus ≤ Q →
    1 - kappa / Real.log (4 * (Q : ℝ)) ≤ e.beta →
    1 - kappa / Real.log (4 * (Q : ℝ)) ≤ f.beta → e = f
  /-- Corollary 11.20, with absolute constants uniform in the modulus. -/
  theta : ∀ q, 1 ≤ q → ∀ a, a.Coprime q → ∀ x : ℝ, 2 ≤ x →
    |primeProgressionTheta q a x -
      thetaMainTerm (Nat.totient q) (pageCoefficient (localZero q) a)
        (pageBeta (localZero q)) x| ≤
      errorConstant * x * Real.exp (-decay * Real.sqrt (Real.log x))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedRealZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published inputs for the real-character zero argument

The Hadamard input is the real-axis specialization of H. A. Helfgott,
*The ternary Goldbach problem*, Part I, 15 December 2019, section 3.7.4,
equations (3.97)--(3.102), printed pp. 86--87:
https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf .
The bounded gamma term on 1 < s <= 2 is included in the absolute constant.

The low-height region and single simple exception are H. L. Montgomery and
R. C. Vaughan, *Multiplicative Number Theory I*, Theorem 11.3 and Corollary
11.10, pp. 360 and 369, using the same decreased constant as
`PublishedProgressionInput`. The separate Siegel specialization is Corollary
11.15 of that book. All these are explicit conditional parameters.
-/

namespace Ostmann

open scoped BigOperators

/-- Hadamard factorization and the full low-height zero-free region. Page
uniqueness for the resulting actual real zeros is already in P. -/
structure PublishedRealZeroInput (P : PublishedProgressionInput) where
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  expansion : ∀ χ : PrimitiveRealCharacter, RealCharacterZeroExpansion χ errorConstant
  region : ∀ (χ : PrimitiveRealCharacter) (Q : ℕ), 2 ≤ Q → χ.modulus ≤ Q →
    ∃ E : Finset ℕ, E.card ≤ 1 ∧
      (∀ i ∈ E, ((expansion χ).zeros i).im = 0 ∧
        1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ ((expansion χ).zeros i).re) ∧
      (∀ i ∉ E, ((expansion χ).zeros i).im ^ 2 < 1 →
        ((expansion χ).zeros i).re ≤ 1 - P.kappa / Real.log (4 * (Q : ℝ)))

/-- The one-sided real-zero consequence of Siegel's theorem, for every fixed
positive exponent. Its constant is allowed to be ineffective. -/
def PublishedSiegelBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ e : PrimitiveRealZero,
    (1 - e.beta)⁻¹ ≤ C * (e.modulus : ℝ) ^ ε

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_OrdinaryPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordinary prime interval and its normalization

The conductor-one character is trivial, so the ordinary prime prior has
no Page correction. Its logarithmic interval mass and inverse bound are
derived from the same published theta input.
-/

namespace Ostmann

open Filter MeasureTheory

theorem PrimitiveRealZero.modulus_ne_one (e : PrimitiveRealZero) : e.modulus ≠ 1 := by
  let : NeZero e.modulus := ⟨Nat.ne_of_gt e.positive⟩
  intro h
  apply e.nontrivial
  exact (DirichletCharacter.eq_one_iff_conductor_eq_one (χ := e.character)).mpr (e.primitive.trans h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_LogCutoffPolynomial
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial factors for the actual logarithmic node cutoff -/

namespace Ostmann

/-- Clipping changes no node factor, including nonpositive inserted values
and both boundary points of the compact logarithmic cutoff. -/
theorem logCutoffPolynomialFactor_value (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    (logCutoffPolynomialFactor P φ G B D hB hD hφ hlip).value z =
      (positiveLogCutoff φ G (P.eval z) : ℂ) := by
  let x := P.eval z
  have hlow : φ (Real.log (Real.exp (G - 1)) - G) = 0 := by
    rw [Real.log_exp]
    apply hout
    norm_num
  have hhigh : φ (Real.log (Real.exp (G + 1)) - G) = 0 := by
    rw [Real.log_exp]
    apply hout
    norm_num
  by_cases hxlo : x < Real.exp (G - 1)
  · have he : clipRealInterval (Real.exp (G - 1)) (Real.exp (G + 1)) x = Real.exp (G - 1) := by
      simp only [clipRealInterval, max_eq_left (le_trans (min_le_right _ _) hxlo.le)]
    change (φ (Real.log (clipRealInterval (Real.exp (G - 1)) (Real.exp (G + 1)) x) - G) : ℂ) = (positiveLogCutoff φ G x : ℂ)
    rw [he, hlow]
    by_cases hx0 : 0 < x
    · have hlog : Real.log x < G - 1 := (Real.log_lt_iff_lt_exp hx0).mpr hxlo
      have hz : φ (Real.log x - G) = 0 := hout _ (by rw [abs_of_neg (by linarith)]; linarith)
      simp only [positiveLogCutoff, ite_eq_left hx0, hz, Complex.ofReal_zero]
    · simp only [positiveLogCutoff, ite_eq_right hx0, Complex.ofReal_zero]
  · have hxlo' : Real.exp (G - 1) ≤ x := le_of_not_gt hxlo
    have hx0 : 0 < x := (Real.exp_pos _).trans_le hxlo'
    by_cases hxhi : Real.exp (G + 1) < x
    · have he : clipRealInterval (Real.exp (G - 1)) (Real.exp (G + 1)) x = Real.exp (G + 1) := by
        simp only [clipRealInterval, min_eq_left hxhi.le,
          max_eq_right (Real.exp_le_exp.mpr (by linarith : G - 1 ≤ G + 1))]
      change (φ (Real.log (clipRealInterval (Real.exp (G - 1)) (Real.exp (G + 1)) x) - G) : ℂ) = (positiveLogCutoff φ G x : ℂ)
      rw [he, hhigh]
      have hlog : G + 1 < Real.log x := (Real.lt_log_iff_exp_lt hx0).mpr hxhi
      have hz : φ (Real.log x - G) = 0 := hout _ (by rw [abs_of_pos (by linarith)]; linarith)
      simp only [positiveLogCutoff, ite_eq_left hx0, hz, Complex.ofReal_zero]
    · rw [ClippedPolynomialFactor.value_of_mem _ z ⟨hxlo', le_of_not_gt hxhi⟩]
      simp only [logCutoffPolynomialFactor, positiveLogCutoff, x, ite_eq_left hx0]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial dependence on one original bulk-prime slot -/

namespace Ostmann
open scoped Classical

theorem bulkSlotProduct_eval {σ : Type*} (value : σ → ℝ)
    (i : σ) (slots : List σ) (p : ℝ) :
    (bulkSlotProduct value i slots).eval p =
      realSlotProduct (Function.update value i p) slots := by
  induction slots with
  | nil => simp [bulkSlotProduct, realSlotProduct]
  | cons j slots ih =>
    by_cases hji : j = i
    · subst j
      simp only [bulkSlotProduct, List.map_cons, List.prod_cons, Polynomial.eval_mul,
        ite_true, if_true, Polynomial.eval_X, realSlotProduct,
        Function.update_self] at *
      exact congrArg (p * ·) ih
    · simp only [bulkSlotProduct, List.map_cons, List.prod_cons, Polynomial.eval_mul,
        ite_eq_right hji, Polynomial.eval_C, realSlotProduct,
        Function.update_of_ne hji] at *
      exact congrArg (value j * ·) ih

theorem MovingSlotReversal.bulkPivotPolynomial_eval {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ)
    (hi : i ∉ s.compensationSlots) (L R : Polynomial ℝ) (p : ℝ) :
    (s.bulkPivotPolynomial value i L R).eval p =
      s.realValuePivot (Function.update value i p) (L.eval p) (R.eval p) := by
  simp only [bulkPivotPolynomial, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    bulkSlotProduct_eval, realValuePivot, realSlotProduct_update_of_absent value i _ hi, div_eq_mul_inv]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLeafPolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal moduli as polynomials in a bulk-prime coordinate -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.bulkLeafPolynomials_eval {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (L R : Polynomial ℝ) (p : ℝ) (j : TreeLeafIndex n) :
    (T.bulkLeafPolynomials value i L R j).eval (p : ℝ) =
      T.realValueLeafModuli (Function.update value i p) (L.eval (p : ℝ)) (R.eval (p : ℝ)) j := by
  induction T generalizing L R with
  | leaf => simp only [bulkLeafPolynomials, Polynomial.eval_mul, bulkSlotProduct_eval,
      realValueLeafModuli]
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_eval
      value i hT.1 L R p
    cases j with
    | inl j => simp only [bulkLeafPolynomials, realValueLeafModuli, ihL hT.2.1, hp]
    | inr j => simp only [bulkLeafPolynomials, realValueLeafModuli, ihR hT.2.2, hp]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkNodePolynomials
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every node cutoff in the same bulk-prime polynomial coordinate -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotData.bulkNodePolynomials_value {σ : Type*} (value : σ → ℝ) (i : σ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : T.CompensationAbsent i) (L R : Polynomial ℝ) (p : ℝ) :
    ((T.bulkNodePolynomials value i L R).map
      (fun f => (positiveLogCutoff φ (G f.1) (f.2.eval (p : ℝ)) : ℂ))).prod =
      realValueNodeCutoff (Function.update value i p) φ G T
        (L.eval (p : ℝ)) (R.eval (p : ℝ)) := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial_eval
      value i hT.1 L R p
    simp only [bulkNodePolynomials, List.map_cons, List.map_append, List.prod_cons,
      List.prod_append, ihL hT.2.1, ihR hT.2.2, hp, realValueNodeCutoff]
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLogContinuity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth tree as a continuous function of the bulk logarithms -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate BoundedContinuousFunction

theorem realSlotProduct_bulkLogValues {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (l : List σ) (hl : ∀ i ∈ l, i ∉ S) (x : σ → ℝ) :
    realSlotProduct (bulkLogValues base S x) l = realSlotProduct base l := by
  unfold realSlotProduct
  congr 1
  apply List.map_congr_left
  intro i hi
  exact ite_eq_right (hl i hi)

theorem MovingSlotReversal.continuous_bulkLogPivot {σ : Type*}
    (base : σ → ℝ) (S : Finset σ) (s : MovingSlotReversal σ)
    (hs : ∀ i ∈ S, i ∉ s.compensationSlots)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => s.realValuePivot (bulkLogValues base S x) (L x) (R x)) := by
  have hc (x : σ → ℝ) : realSlotProduct (bulkLogValues base S x) s.compensationSlots =
      realSlotProduct base s.compensationSlots :=
    realSlotProduct_bulkLogValues base S _ (fun i hi hS => hs i hS hi) x
  simp_rw [realValuePivot, hc]
  exact (((continuous_const.mul
    (continuous_realSlotProduct _ (continuous_bulkLogValues base S) s.rightSlots)).mul hR).sub
    ((continuous_const.mul
    (continuous_realSlotProduct _ (continuous_bulkLogValues base S) s.leftSlots)).mul hL)).div_const _

theorem MovingSlotData.continuous_bulkLogLeafModuli {σ : Type*}
    (base : σ → ℝ) (S : Finset σ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) (j : TreeLeafIndex n) :
    Continuous (fun x => T.realValueLeafModuli (bulkLogValues base S x) (L x) (R x) j) := by
  induction T generalizing L R with
  | leaf s regular =>
    exact (hL.mul hR).mul (continuous_realSlotProduct _ (continuous_bulkLogValues base S) regular)
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).continuous_bulkLogPivot
      base S (fun i hi => (hT i hi).1) L R hL hR
    cases j with
    | inl j => exact ihL (fun i hi => (hT i hi).2.1) _ L hp hL j
    | inr j => exact ihR (fun i hi => (hT i hi).2.2) _ R hp hR j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLogWeightedIntegrand
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded measurable bulk integrands retaining the initial cutoffs -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem continuous_bulkLogCutoffWeight {σ A : Type*} [TopologicalSpace A]
    (value : A → σ → ℝ) (hvalue : ∀ i, Continuous (fun x => value x i))
    (cb : ℝ) (slots : List σ) :
    Continuous (fun x => (bulkLogCutoffWeight (value x) cb slots : ℂ)) := by
  obtain ⟨D, hD, hlip⟩ := logCellProfile_lipschitz
  let f := logCutoffPolynomialFactor Polynomial.X logCellProfile cb 1 D zero_le_one hD
    (fun x => by rw [abs_of_nonneg (logCellProfile_nonneg x)]; exact logCellProfile_le_one x) hlip
  have hf : Continuous (fun z => (positiveLogCutoff logCellProfile cb z : ℂ)) := by
    apply f.continuous_value.congr
    intro z
    simpa only [f, Polynomial.eval_X] using
      logCutoffPolynomialFactor_value Polynomial.X logCellProfile cb 1 D zero_le_one hD
        (fun x => by rw [abs_of_nonneg (logCellProfile_nonneg x)]; exact logCellProfile_le_one x)
        hlip logCellProfile_zero_outside z
  exact hf.comp (continuous_realSlotProduct value hvalue slots)

noncomputable def BulkIntegrand.withLogCutoffs {σ : Type*} [Fintype σ] {t : ℕ}
    (f : BulkIntegrand σ) (base : σ → ℝ) (S : Finset σ) (cb : ℝ)
    (slots : Fin t → List σ) : BulkIntegrand σ where
  toFun x := ((∏ j, bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j) : ℝ) : ℂ) * f x
  measurable := by
    have hcont : Continuous (fun x =>
        ∏ j, (bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j) : ℂ)) :=
      continuous_finsetProd _ (fun j _ => continuous_bulkLogCutoffWeight
        (bulkLogValues base S) (continuous_bulkLogValues base S) cb (slots j))
    convert hcont.measurable.mul f.measurable using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact congrArg (fun z : ℂ => z * f x) (Complex.ofReal_prod _ _)
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    refine ⟨C, hC, fun x => ?_⟩
    have hnonneg : 0 ≤ ∏ j, bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j) :=
      Finset.prod_nonneg (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
    have hle : (∏ j, bulkLogCutoffWeight (bulkLogValues base S x) cb (slots j)) ≤ 1 :=
      Finset.prod_le_one (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).1)
        (fun j _ => (bulkLogCutoffWeight_bounds _ _ _).2)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) hle).trans (hf x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedComplexZeroDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published zero-density and zero-free inputs for the smooth prime mean

H. L. Montgomery, *Zeros of L-functions*, Invent. Math. 8 (1969), 346–354,
Theorem 1, in the explicit form of S. Inoue, *Some explicit formulas for
partial sums of Möbius functions*, JTNB 33 (2021), 273–315, Lemma 1, p. 282:
https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1162.pdf .

The region below is the bounded-height consequence of K. Ford, B. Green,
S. Konyagin, J. Maynard and T. Tao, *Long gaps between primes*, JAMS 31
(2018), 65–105, Lemma 7.1. Deleting the whole exceptional primitive character
and replacing `Q*(1+|t|)` by `2*Q*T` only weakens that statement.
https://doi.org/10.1090/jams/876 .

These are explicit conditional parameters. The zero enumeration is shared
with the explicit-formula input; no smooth-prime-mean estimate is assumed.
-/

namespace Ostmann
open scoped Classical BigOperators

/-- The exact Montgomery–Inoue estimate, restricted to an arbitrary finite
subfamily of the primitive nonprincipal characters of conductor at most Q. -/
def PublishedComplexZeroDensity (Z : ∀ χ, ComplexZeroEnumeration χ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ), 1 ≤ Q → ∀ (T σ : ℝ), 2 ≤ T →
    1 / 2 ≤ σ → σ ≤ 1 → ∀ F : Finset PrimitiveComplexCharacter,
    (∀ χ ∈ F, χ.modulus ≤ Q) →
    (∑ χ ∈ F, ((Z χ).count σ T : ℝ)) ≤
      C * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) *
        (Real.log ((Q : ℝ) * T)) ^ 13

/-- Bounded-height Landau–Page, with the entire possible exceptional
character removed. The exception can be avoided by one prime deletion. -/
def PublishedComplexZeroRegion (Z : ∀ χ, ComplexZeroEnumeration χ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (Q : ℕ), 101 ≤ Q → ∀ T : ℝ, 2 ≤ T →
    ∃ exception : Option PrimitiveComplexCharacter,
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ≤ Q → some χ ≠ exception →
      ∀ i : ℕ, |((Z χ).zeros i).im| ≤ T →
        c / Real.log (2 * (Q : ℝ) * T) ≤ 1 - ((Z χ).zeros i).re

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterAbsoluteRightBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute Euler-series control on every right-hand vertical line -/

namespace Ostmann

open Complex LSeries
open scoped ComplexOrder

 theorem character_logDeriv_right_pole_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      ‖logDeriv χ.L s‖ ≤ 1 / (s.re - 1) + C := by
  obtain ⟨C, hC, hb⟩ := exists_vonMangoldt_series_bound
  refine ⟨C, hC, ?_⟩
  intro χ s hs hs2
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have ha : LSeriesSummable a (s.re : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have ht : LSeriesSummable (characterMangoldtCoefficient χ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character hs
  have hsame (n : ℕ) : ‖LSeries.term a s n‖ = ‖LSeries.term a (s.re : ℂ) n‖ := by
    simp only [LSeries.norm_term_eq, Complex.ofReal_re]
  have hn (n : ℕ) : ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ ≤
      ‖LSeries.term a (s.re : ℂ) n‖ := by
    rw [← hsame n]
    apply LSeries.norm_term_le
    change ‖χ.character (n : ZMod χ.modulus) * a n‖ ≤ ‖a n‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.character.norm_le_one _)
  have hr (n : ℕ) : ‖LSeries.term a (s.re : ℂ) n‖ =
      (LSeries.term a (s.re : ℂ) n).re := by
    have hp : (0 : ℂ) ≤ a n := by
      change (0 : ℂ) ≤ (ArithmeticFunction.vonMangoldt n : ℂ)
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hh := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg hp s.re))
    simpa only [Complex.ofReal_re] using hh.symm
  calc
    _ = ‖LSeries (characterMangoldtCoefficient χ) s‖ := by
      rw [χ.mangoldt_LSeries_eq s hs, logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ := norm_tsum_le_tsum_norm ht.norm
    _ ≤ ∑' n, ‖LSeries.term a (s.re : ℂ) n‖ := ht.norm.tsum_le_tsum hn ha.norm
    _ = (LSeries a (s.re : ℂ)).re := by simp_rw [hr]; exact (Complex.re_tsum ha).symm
    _ ≤ ‖LSeries a (s.re : ℂ)‖ := Complex.re_le_norm _
    _ ≤ _ := hb s.re hs hs2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterTrivialZero
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The residue at the origin in the primitive explicit formula -/

namespace Ostmann

open Filter
open scoped Topology Classical

theorem PrimitiveComplexCharacter.completed_order_zero (χ : PrimitiveComplexCharacter) :
    analyticOrderAt χ.completed 0 = 0 := by
  rw [show (0 : ℂ) = 1 - 1 by ring, χ.completed_order_reflection]
  rw [← χ.inverse.L_order_eq_completed 1 (by norm_num)]
  apply (χ.inverse.L_analytic 1).analyticOrderAt_eq_zero.mpr
  let : NeZero χ.inverse.modulus := ⟨χ.inverse.positive.ne'⟩
  exact DirichletCharacter.LFunction_apply_one_ne_zero χ.inverse.nontrivial

theorem PrimitiveComplexCharacter.L_order_at_zero (χ : PrimitiveComplexCharacter) :
    analyticOrderAt χ.L 0 = if χ.character.Even then 1 else 0 := by
  classical
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : χ.modulus ≠ 1 := fun h => χ.nontrivial (DirichletCharacter.level_one' χ.character h)
  have he : χ.L = χ.completed * χ.gammaInverse := by
    funext s
    exact (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.character s (.inr hq)).trans
      (div_eq_mul_inv _ _)
  rw [he, analyticOrderAt_mul (χ.completed_analytic 0) (χ.gammaInverse_analytic 0),
    χ.completed_order_zero, zero_add]
  by_cases hχ : χ.character.Even
  · simp only [hχ, ↓reduceIte]
    change analyticOrderAt (fun s => (DirichletCharacter.gammaFactor χ.character s)⁻¹) 0 = 1
    simp_rw [hχ.gammaFactor_def]
    exact gammaReal_inverse_order_zero
  · simp only [hχ, ↓reduceIte]
    apply (χ.gammaInverse_analytic 0).analyticOrderAt_eq_zero.mpr
    simp [PrimitiveComplexCharacter.gammaInverse, DirichletCharacter.gammaFactor, hχ,
      Complex.Gammaℝ_one]

theorem PrimitiveComplexCharacter.L_multiplicity_at_zero (χ : PrimitiveComplexCharacter) :
    analyticOrderNatAt χ.L 0 = if χ.character (-1) = 1 then 1 else 0 := by
  classical
  unfold analyticOrderNatAt
  rw [χ.L_order_at_zero]
  split_ifs <;> simp_all [DirichletCharacter.Even]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterContourZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The only zeros crossed by the fixed smooth contour

Between Re(s)=-1/2 and Re(s)=2 the poles of the logarithmic derivative are
precisely the critical-strip zeros, together with the possible zero at zero.
-/

namespace Ostmann

open Complex

theorem PrimitiveComplexCharacter.L_ne_zero_left_ne_origin (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : -(1 / 2 : ℝ) ≤ z.re) (hz' : z.re ≤ 0) (hne : z ≠ 0) : χ.L z ≠ 0 := by
  rw [χ.L_eq_completed_mul z hne]
  apply mul_ne_zero (χ.completed_ne_zero_left z hz')
  classical
  unfold PrimitiveComplexCharacter.gammaInverse DirichletCharacter.gammaFactor
  split_ifs
  · rw [gammaReal_inverse_factor]
    apply mul_ne_zero hne
    apply mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
    apply inv_ne_zero
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re]
    norm_num
    linarith
  · apply inv_ne_zero
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith

theorem PrimitiveComplexCharacter.contour_zero_location (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : -(1 / 2 : ℝ) ≤ z.re) (hzero : χ.L z = 0) :
    z = 0 ∨ z ∈ complexCharacterZeros χ := by
  by_cases hne : z = 0
  · exact .inl hne
  right
  have hpos : 0 < z.re := by
    by_contra hh
    exact χ.L_ne_zero_left_ne_origin z hz (not_lt.mp hh) hne hzero
  have hlt : z.re < 1 := by
    by_contra hh
    exact χ.L_ne_zero_one_le_re z (not_lt.mp hh) hzero
  exact ⟨hpos, hlt, hzero⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual character Gamma factors on both vertical contour lines -/

namespace Ostmann

open Complex
open scoped Classical

theorem PrimitiveComplexCharacter.gammaFactor_differentiableAt
    (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ.character) s := by
  by_cases hc : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact gammaReal_differentiableAt s (gammaReal_contour_regular s (contourLine_expanded s hs))
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact (gammaReal_differentiableAt (s + 1) (gammaReal_contour_regular _ (contourLine_shift s hs))).comp s
      (differentiableAt_id.add_const (1 : ℂ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCompletedLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The functional equation at the level of logarithmic derivatives -/

namespace Ostmann

open Complex
open scoped Classical

theorem PrimitiveComplexCharacter.logDeriv_L_eq_completed_add
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : χ.L s ≠ 0) :
    logDeriv χ.L s = logDeriv χ.completed s + logDeriv χ.gammaInverse s := by
  have he := congrFun χ.L_eq_completed_mul_all s
  change χ.L s = χ.completed s * χ.gammaInverse s at he
  have hne : χ.completed s ≠ 0 ∧ χ.gammaInverse s ≠ 0 :=
    mul_ne_zero_iff.mp (he ▸ hs)
  rw [χ.L_eq_completed_mul_all]
  exact
    logDeriv_mul s hne.1 hne.2 (χ.completed_analytic s).differentiableAt
      (χ.gammaInverse_analytic s).differentiableAt

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLogDerivativePole
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact local poles of a character logarithmic derivative -/

namespace Ostmann

open Filter
open scoped Topology

/-- Removing the actual analytic zero order leaves a nonvanishing analytic factor. -/
theorem PrimitiveComplexCharacter.logDeriv_local_split (χ : PrimitiveComplexCharacter)
    (z : ℂ) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
      logDeriv χ.L =ᶠ[𝓝[≠] z] fun w =>
        (analyticOrderNatAt χ.L z : ℂ) / (w - z) + logDeriv g w := by
  obtain ⟨g, hg, hgne, he⟩ := (χ.L_analytic z).analyticOrderAt_ne_top.mp (χ.L_order_ne_top z)
  have he' : χ.L =ᶠ[𝓝 z] fun w => (w - z) ^ analyticOrderNatAt χ.L z * g w := by
    simpa only [smul_eq_mul] using he
  have hlog := logDeriv_congr_nhds he'
  refine ⟨g, hg, hgne, ?_⟩
  filter_upwards [hlog.filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hgne).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw hgw hgnw hwz
  have hnz : w - z ≠ 0 := sub_ne_zero.mpr hwz
  rw [hw, logDeriv_mul (f := fun u : ℂ => (u - z) ^ analyticOrderNatAt χ.L z)
    (g := g) w (pow_ne_zero _ hnz) hgnw
    ((differentiableAt_id.sub_const z).pow _) hgw.differentiableAt]
  have hp : logDeriv (fun u : ℂ => (u - z) ^ analyticOrderNatAt χ.L z) w =
      (analyticOrderNatAt χ.L z : ℂ) * logDeriv (fun u : ℂ => u - z) w := by
    simpa only [id_eq] using logDeriv_fun_pow
      (f := fun u : ℂ => u - z) (x := w) (differentiableAt_id.sub_const z)
      (analyticOrderNatAt χ.L z)
  rw [hp]
  simp [logDeriv_apply, div_eq_mul_inv]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimitiveCharacterCard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary conductor-family cardinality bound -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def PrimitiveComplexCharacter.atModulus (χ : PrimitiveComplexCharacter)
    (q : ℕ) (h : χ.modulus = q) : DirichletCharacter ℂ q := h ▸ χ.character

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedSmoothExplicitFormula
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published smooth explicit formula, for one fixed test function

H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2007),
Chapter 10: the functional equation, ordinary zero count and explicit formula.
See also H. A. Helfgott, *The ternary Goldbach problem*, Part I (15 December
2019), §§3.7.1 and 3.7.3. We use only the fixed `primeMeanTest`, supported
in [5/8,7/8]. Its Mellin transform has eighth-order decay in the fixed strip.

The formula shifts to Re(s)=-1/2, retaining the even-character residue at
zero. Its error has no dependence on an exceptional zero's distance from 1.
The count is the ordinary individual zero count summed over a finite
primitive family; there are at most Q² Dirichlet characters of conductor ≤Q.
This input contains no prime-average or favorable-prime conclusion.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothZeroTerm (Z : ∀ χ, ComplexZeroEnumeration χ)
    (χ : PrimitiveComplexCharacter) (X : ℝ) (i : ℕ) : ℂ :=
  Complex.exp (((Z χ).zeros i) * (Real.log X : ℂ)) * primeMeanMellin ((Z χ).zeros i)

noncomputable def smoothTrivialZeroTerm (χ : PrimitiveComplexCharacter) : ℂ :=
  if χ.character (-1) = 1 then primeMeanMellin 0 else 0

structure PublishedSmoothExplicitFormula (Z : ∀ χ, ComplexZeroEnumeration χ) where
  errorConstant : ℝ
  errorConstant_pos : 0 < errorConstant
  mellinConstant : ℝ
  mellinConstant_pos : 0 < mellinConstant
  zeroCountConstant : ℝ
  zeroCountConstant_pos : 0 < zeroCountConstant
  mellin_decay : ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
    ‖primeMeanMellin s‖ ≤ mellinConstant * Real.exp (-8 * Real.log (1 + |s.im|))
  zero_count : ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 0 ≤ T →
    ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((Z χ).count 0 T : ℝ)) ≤
        zeroCountConstant * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2))
  absolute_summability : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
    Summable (fun i => ‖smoothZeroTerm Z χ X i‖)
  explicit_formula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
    ‖smoothMangoldtMean χ.modulus χ.character X +
      (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ ≤
        errorConstant / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothExplicitFormulaCore
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the elementary fields of the smooth explicit-formula input

The analytic input is only the zero count and fixed-test explicit formula.
The Mellin decay and absolute summability are derived for the actual test.
-/

namespace Ostmann

open Finset
open scoped Classical BigOperators

/-- The fixed-test explicit formula. -/
structure SmoothExplicitFormulaCore (Z : ∀ χ, ComplexZeroEnumeration χ) where
  errorConstant : ℝ
  errorConstant_pos : 0 < errorConstant
  zeroCountConstant : ℝ
  zeroCountConstant_pos : 0 < zeroCountConstant
  zero_count : ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 0 ≤ T →
    ∀ F : Finset PrimitiveComplexCharacter, (∀ χ ∈ F, χ.modulus ≤ Q) →
      (∑ χ ∈ F, ((Z χ).count 0 T : ℝ)) ≤
        zeroCountConstant * (Q : ℝ) ^ 2 * (T + 1) * Real.log ((Q : ℝ) * (T + 2))
  explicit_formula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
    ‖smoothMangoldtMean χ.modulus χ.character X +
      (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ ≤
        errorConstant / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))

theorem SmoothExplicitFormulaCore.finite_height_count {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : SmoothExplicitFormulaCore Z) (χ : PrimitiveComplexCharacter) (S : Finset ℕ)
    (T : ℝ) (hT : 0 ≤ T) :
    (((S.filter fun i => |((Z χ).zeros i).im| ≤ T).card : ℝ)) ≤
      (P.zeroCountConstant * (χ.modulus : ℝ) ^ 2) * (T + 1) *
        Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  have hsub : (S.filter fun i => |((Z χ).zeros i).im| ≤ T) ⊆ (Z χ).heightIndices T := by
    intro i hi
    exact ((Z χ).mem_heightIndices T i).mpr (mem_filter.mp hi).2
  have hcard : ((Z χ).heightIndices T).card = (Z χ).count 0 T := by
    unfold ComplexZeroEnumeration.count
    rw [filter_eq_self.mpr (fun i _ => ((Z χ).in_strip i).1.le)]
  have h := P.zero_count χ.modulus (Nat.succ_le_iff.mpr χ.positive) T hT {χ} (by simp)
  simp only [sum_singleton] at h
  calc
    _ ≤ (((Z χ).heightIndices T).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = ((Z χ).count 0 T : ℝ) := by rw [hcard]
    _ ≤ _ := h

theorem smoothZeroTerm_bound_of_mellin {Z : ∀ χ, ComplexZeroEnumeration χ}
    (C : ℝ)
    (hM : ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖primeMeanMellin s‖ ≤ C * Real.exp (-8 * Real.log (1 + |s.im|)))
    (χ : PrimitiveComplexCharacter) (X : ℝ) (hX : 1 ≤ X) (i : ℕ) :
    ‖smoothZeroTerm Z χ X i‖ ≤
      (X * C) * Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) := by
  have hs := (Z χ).in_strip i
  have hm := hM ((Z χ).zeros i) (by linarith) (by linarith)
  have hX0 : 0 < X := by linarith
  have he : Real.exp (((Z χ).zeros i).re * Real.log X) ≤ X := by
    calc
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2.le (Real.log_nonneg hX))
      _ = X := Real.exp_log hX0
  rw [smoothZeroTerm, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ ≤ X * (C * Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|))) :=
      mul_le_mul he hm (norm_nonneg _) hX0.le
    _ = _ := by ring

theorem SmoothExplicitFormulaCore.absolute_summability {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : SmoothExplicitFormulaCore Z) (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 2 ≤ X) : Summable (fun i => ‖smoothZeroTerm Z χ X i‖) := by
  obtain ⟨C, hC, hM⟩ := primeMeanMellin_decay
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  apply summable_of_sum_le (fun i => norm_nonneg _)
    (c := (X * C) * (2 * (2 * (P.zeroCountConstant * (χ.modulus : ℝ) ^ 2) *
      (Real.log χ.modulus + 3)) ^ 2))
  intro S
  have hh := finite_high_zero_tail_bound S (fun i => |((Z χ).zeros i).im|)
    (χ.modulus : ℝ) (P.zeroCountConstant * (χ.modulus : ℝ) ^ 2) 0 hq
    (mul_nonneg P.zeroCountConstant_pos.le (sq_nonneg _)) le_rfl
    (fun _ _ => abs_nonneg _) (P.finite_height_count χ S)
  simp only [add_zero, Real.log_one, mul_zero, Real.exp_zero, mul_one] at hh
  calc
    _ ≤ ∑ i ∈ S, (X * C) * Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) :=
      sum_le_sum (fun i _ => smoothZeroTerm_bound_of_mellin C hM χ X (by linarith) i)
    _ = (X * C) * ∑ i ∈ S, Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) :=
      (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

noncomputable def SmoothExplicitFormulaCore.toPublished {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : SmoothExplicitFormulaCore Z) : PublishedSmoothExplicitFormula Z where
  errorConstant := P.errorConstant
  errorConstant_pos := P.errorConstant_pos
  mellinConstant := Classical.choose primeMeanMellin_decay
  mellinConstant_pos := (Classical.choose_spec primeMeanMellin_decay).1
  mellin_decay := (Classical.choose_spec primeMeanMellin_decay).2
  zeroCountConstant := P.zeroCountConstant
  zeroCountConstant_pos := P.zeroCountConstant_pos
  zero_count := P.zero_count
  absolute_summability := P.absolute_summability
  explicit_formula := P.explicit_formula

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Gamma factors for the horizontal-contour growth estimate -/

namespace Ostmann

open Complex
open scoped Classical

theorem PrimitiveComplexCharacter.L_reflection_product (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : s.re < 1) :
    χ.L s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
      @DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character *
      χ.inverse.L (1 - s) * DirichletCharacter.gammaFactor χ.inverse.character (1 - s) *
      χ.gammaInverse s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hpos : 0 < (1 - s).re := by simp; linarith
  have hgne : DirichletCharacter.gammaFactor χ.inverse.character (1 - s) ≠ 0 := by
    intro hz
    have hh := χ.inverse.gammaInverse_ne_zero _ hpos
    apply hh
    change (DirichletCharacter.gammaFactor χ.inverse.character (1 - s))⁻¹ = 0
    rw [hz, inv_zero]
  have hLi := congrFun χ.inverse.L_eq_completed_mul_all (1 - s)
  change χ.inverse.L (1 - s) = χ.inverse.completed (1 - s) /
    DirichletCharacter.gammaFactor χ.inverse.character (1 - s) at hLi
  have hCi := (eq_div_iff hgne).mp hLi
  have hfun := χ.primitive.completedLFunction_one_sub (1 - s)
  have harg : 1 - (1 - s) = s := by ring
  have hexp : (1 - s) - 1 / 2 = 1 / 2 - s := by ring
  rw [harg, hexp] at hfun
  have hL := congrFun χ.L_eq_completed_mul_all s
  change χ.L s = χ.completed s * χ.gammaInverse s at hL
  rw [hL]
  change χ.completed s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
    DirichletCharacter.rootNumber χ.character * χ.inverse.completed (1 - s) at hfun
  rw [hfun, ← hCi]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroPartialSums
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the finite contour zero sum with the true zero enumeration -/

namespace Ostmann

open Filter
open scoped Topology BigOperators Classical

theorem ComplexZeroEnumeration.tendsto_heightIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) : Tendsto Z.heightIndices atTop atTop := by
  apply tendsto_atTop.2
  intro S
  have hh : ∀ᶠ T : ℝ in atTop, ∀ i ∈ S, |(Z.zeros i).im| ≤ T :=
    (Filter.eventually_all_finset S).mpr (fun i _ => eventually_ge_atTop _)
  filter_upwards [hh] with T hT
  intro i hi
  exact (Z.mem_heightIndices T i).mpr (hT i hi)

theorem ComplexZeroEnumeration.tendsto_height_sum {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (f : ℕ → ℂ) (hf : Summable f) :
    Tendsto (fun T : ℝ => ∑ i ∈ Z.heightIndices T, f i) atTop (𝓝 (∑' i, f i)) :=
  hf.hasSum.comp Z.tendsto_heightIndices

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualRealZeroExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual real-character Hadamard expansion -/

namespace Ostmann

open Complex

theorem actualRealZeroErrorConstant_pos : 0 < actualRealZeroErrorConstant :=
  (Classical.choose_spec characterGamma_real_logDeriv_bound).1

/-- The low-height clause of Montgomery--Vaughan 11.3/11.10,
stated for the analytic multiplicity enumeration. -/
def ActualRealLowHeightRegion (P : PublishedProgressionInput) : Prop :=
  ∀ (χ : PrimitiveRealCharacter) (Q : ℕ), 2 ≤ Q → χ.modulus ≤ Q →
    ∃ E : Finset ℕ, E.card ≤ 1 ∧
      (∀ i ∈ E, ((realCharacterActualZeros χ).zeros i).im = 0 ∧
        1 - P.kappa / Real.log (4 * (Q : ℝ)) ≤ ((realCharacterActualZeros χ).zeros i).re) ∧
      (∀ i ∉ E, ((realCharacterActualZeros χ).zeros i).im ^ 2 < 1 →
        ((realCharacterActualZeros χ).zeros i).re ≤ 1 - P.kappa / Real.log (4 * (Q : ℝ)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LowHeightZeroBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual zero sums and bounded low-height errors -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem shifted_real_zero_term_le (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) (i : ℕ) :
    ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re ≤ shiftedRealCharacterZeroSum χ s := by
  exact (shifted_real_zero_summable χ s hs hs2).le_tsum i (fun j _ => by
    rw [realZeroKernel_complex_sub]
    exact realZeroKernel_nonneg (by linarith [((realCharacterActualZeros χ).in_strip j).2]))

theorem shifted_real_zero_pair_le (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) (i j : ℕ) (hij : i ≠ j) :
    ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re +
      ((s - (realCharacterActualZeros χ).zeros j)⁻¹).re ≤ shiftedRealCharacterZeroSum χ s := by
  have hh := (shifted_real_zero_summable χ s hs hs2).sum_le_tsum {i,j} (fun k _ => by
    rw [realZeroKernel_complex_sub]
    exact realZeroKernel_nonneg (by linarith [((realCharacterActualZeros χ).in_strip k).2]))
  simpa only [Finset.sum_pair hij, shiftedRealCharacterZeroSum] using hh

/-- On the real axis the elementary Euler bound gives a single pole, uniformly
in the primitive real character. -/
theorem exists_real_zero_sum_upper : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveRealCharacter) (s : ℝ), 1 < s → s ≤ 2 →
      shiftedRealCharacterZeroSum χ (s : ℂ) ≤ 1 / (s - 1) +
        (1 / 2) * Real.log χ.modulus + C := by
  obtain ⟨C, hC, hb⟩ := exists_low_height_zero_sum_error
  obtain ⟨D, hD, hd⟩ := exists_dirichlet_logDerivative_bound
  refine ⟨C + D, by positivity, ?_⟩
  intro χ s hs hs2
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hh := hb χ (s : ℂ) hs hs2 (by simp)
  have hnorm := hd χ.modulus χ.complexCharacter s hs hs2
  change ‖logDeriv χ.L (s : ℂ)‖ ≤ _ at hnorm
  have hre := (Complex.re_le_norm _).trans hnorm
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealCharacterTrigonometric
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive trigonometric polynomial for real characters -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem real_character_trigonometric_term_nonneg (χ : PrimitiveRealCharacter) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      4 * (LSeries.term (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I) n).re +
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by
  by_cases hn : n = 0
  · subst n; simp
  let u : ℂ := (n : ℂ) ^ (-(t : ℂ) * I)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have ha : |χ.character n| ≤ 1 := by simpa [Real.norm_eq_abs] using χ.character.norm_le_one n
  have hp := real_character_unit_polynomial (χ.character n) ha u hu
  have hb : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hphase : (n : ℂ) ^ (-((2 * t : ℝ) : ℂ) * I) = u * u := by
    rw [show -((2 * t : ℝ) : ℂ) * I = -(t : ℂ) * I + -(t : ℂ) * I by push_cast; ring]
    exact Complex.cpow_add _ _ (by exact_mod_cast hn)
  have hzero := LSeries_term_vertical (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) n hn σ 0
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one, add_zero] at hzero
  rw [hzero, LSeries_term_vertical _ n hn, LSeries_term_vertical _ n hn, hphase]
  simp only [PrimitiveRealCharacter.complexCharacter, MulChar.ringHomComp_apply,
    Complex.ofRealHom_eq_coe, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_zero, sub_zero, add_zero]
  change 0 ≤ 3 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) +
    4 * (χ.character n * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * u.re) +
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * (u * u).re
  convert mul_nonneg hb hp using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- The Euler series inherits positivity term by term; no prime distribution
input or zero-free assumption is used. -/
theorem real_character_trigonometric_sum_nonneg (χ : PrimitiveRealCharacter)
    (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I)).re +
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
  have h0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ
  have h1 := χ.complexCharacter.LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
  change LSeriesSummable (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ))
    ((σ : ℂ) + (t : ℂ) * I) at h1
  have h2 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) (by simpa using hσ)
  have hh := tsum_nonneg (L := SummationFilter.unconditional ℕ)
    (real_character_trigonometric_term_nonneg χ σ t)
  have h0r := (Complex.hasSum_re h0.hasSum).summable
  have h1r := (Complex.hasSum_re h1.hasSum).summable
  have h2r := (Complex.hasSum_re h2.hasSum).summable
  rw [Summable.tsum_add ((h0r.mul_left 3).add (h1r.mul_left 4)) h2r,
    Summable.tsum_add (h0r.mul_left 3) (h1r.mul_left 4), tsum_mul_left, tsum_mul_left,
    ← Complex.re_tsum h0, ← Complex.re_tsum h1, ← Complex.re_tsum h2] at hh
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealCharacterConjugateZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugate partners in the actual real-character zero family -/

namespace Ostmann

open Complex Filter Set
open scoped Topology ComplexConjugate

theorem PrimitiveRealCharacter.L_conj_right (χ : PrimitiveRealCharacter)
    (s : ℂ) (hs : 1 < s.re) : χ.L (conj s) = conj (χ.L s) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  change DirichletCharacter.LFunction χ.complexCharacter (conj s) =
    conj (DirichletCharacter.LFunction χ.complexCharacter s)
  rw [χ.complexCharacter.LFunction_eq_LSeries (by simpa using hs),
    χ.complexCharacter.LFunction_eq_LSeries hs]
  change (∑' n, LSeries.term _ (conj s) n) = conj (∑' n, LSeries.term _ s n)
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have ha : (n : ℂ).arg ≠ Real.pi := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) from rfl,
        Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_pos.ne
    rw [Complex.cpow_conj _ _ ha]
    simp [PrimitiveRealCharacter.complexCharacter]

theorem PrimitiveRealCharacter.L_conj (χ : PrimitiveRealCharacter) (s : ℂ) :
    χ.L (conj s) = conj (χ.L s) := by
  let g : ℂ → ℂ := conj ∘ χ.L ∘ conj
  have hd : Differentiable ℂ g := by
    intro z
    have hh := (χ.asComplex.L_analytic (conj z)).differentiableAt
    rw [PrimitiveRealCharacter.asComplex_L] at hh
    simpa only [g, Complex.conj_conj] using hh.conj_conj
  have hg : AnalyticOnNhd ℂ g univ := hd.differentiableOn.analyticOnNhd isOpen_univ
  have hf : AnalyticOnNhd ℂ χ.L univ := fun z _ => χ.asComplex.L_analytic z
  have he : g =ᶠ[𝓝 (2 : ℂ)] χ.L := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    simp only [g, Function.comp_apply, χ.L_conj_right z hz, Complex.conj_conj]
  have heq : g = χ.L := hg.eq_of_eventuallyEq hf he
  have hh := congrFun heq s
  change conj (χ.L (conj s)) = χ.L s at hh
  simpa using congrArg conj hh

theorem actualCharacterZeros_complete (χ : PrimitiveComplexCharacter) (z : ℂ)
    (hz : z ∈ complexCharacterZeros χ) : ∃ i, (actualCharacterZeros χ).zeros i = z := by
  have hp : 0 < analyticOrderNatAt χ.L z := by
    have h := (characterZeroOrder_pos_iff χ z).mpr hz.2.2
    rwa [characterZeroOrder_eq_nat, Int.natCast_pos] at h
  let c : CharacterZeroCopy χ := ⟨(z, 0), hz, hp⟩
  refine ⟨(faithfulCharacterZeroEquiv χ).symm c, ?_⟩
  change ((faithfulCharacterZeroEquiv χ) ((faithfulCharacterZeroEquiv χ).symm c)).val.1 = z
  simp [c]

theorem realCharacterActualZeros_conjugate (χ : PrimitiveRealCharacter) (i : ℕ) :
    ∃ j, (realCharacterActualZeros χ).zeros j = conj ((realCharacterActualZeros χ).zeros i) := by
  apply actualCharacterZeros_complete χ.asComplex
  have hi := (realCharacterActualZeros χ).in_strip i
  refine ⟨by simpa using hi.1, by simpa using hi.2, ?_⟩
  change χ.L (conj ((realCharacterActualZeros χ).zeros i)) = 0
  have hz := (realCharacterActualZeros χ).actual_zero i
  change χ.L _ = 0 at hz
  rw [χ.L_conj, hz, map_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexCharacterConjugation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation and multiplicity for general primitive character zeros -/

namespace Ostmann

open Complex Filter Set
open scoped ComplexConjugate Topology

theorem PrimitiveComplexCharacter.L_order_conjugate (χ : PrimitiveComplexCharacter) (z : ℂ) :
    analyticOrderAt χ.inverse.L (conj z) = analyticOrderAt χ.L z := by
  rw [χ.inverse_L_eq_conjugate, analyticOrderAt_conjugation χ.L χ.L_analytic]
  · simp
  · simpa using χ.L_order_ne_top z

theorem PrimitiveComplexCharacter.L_order_self_reflection (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1) :
    analyticOrderAt χ.L (1 - conj z) = analyticOrderAt χ.L z := by
  rw [χ.L_order_reflection (conj z) (by simpa using hz) (by simpa using hz1), χ.L_order_conjugate]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelfReflection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The zero-copy permutation across the critical line -/

namespace Ostmann

open Complex
open scoped ComplexConjugate Classical

theorem PrimitiveComplexCharacter.zero_self_reflection (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : z ∈ complexCharacterZeros χ) : 1 - conj z ∈ complexCharacterZeros χ := by
  refine ⟨by simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith [hz.2.1],
    by simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith [hz.1], ?_⟩
  have hn := (χ.L_analytic z).analyticOrderAt_ne_zero.mpr hz.2.2
  rw [← χ.L_order_self_reflection z hz.1 hz.2.1] at hn
  exact (χ.L_analytic (1 - conj z)).analyticOrderAt_ne_zero.mp hn

noncomputable def characterZeroCopySelfReflection (χ : PrimitiveComplexCharacter) :
    CharacterZeroCopy χ ≃ CharacterZeroCopy χ := by
  let f : CharacterZeroCopy χ → CharacterZeroCopy χ := fun c =>
    ⟨(1 - conj c.val.1, c.val.2), χ.zero_self_reflection c.val.1 c.property.1, by
      unfold analyticOrderNatAt
      rw [χ.L_order_self_reflection _ c.property.1.1 c.property.1.2.1]
      exact c.property.2⟩
  apply Function.Involutive.toPerm (f := f)
  intro c
  apply Subtype.ext
  apply Prod.ext
  · change 1 - conj (1 - conj c.val.1) = c.val.1
    simp
  · rfl

noncomputable def characterZeroIndexSelfReflection (χ : PrimitiveComplexCharacter) : ℕ ≃ ℕ :=
  (faithfulCharacterZeroEquiv χ).trans
    ((characterZeroCopySelfReflection χ).trans (faithfulCharacterZeroEquiv χ).symm)

theorem characterZeroIndexSelfReflection_zeros (χ : PrimitiveComplexCharacter) (i : ℕ) :
    (actualCharacterZeros χ).zeros (characterZeroIndexSelfReflection χ i) =
      1 - conj ((actualCharacterZeros χ).zeros i) := by
  simp [actualCharacterZeros, characterZeroEnumeration,
    characterZeroIndexSelfReflection, characterZeroCopySelfReflection, Function.Involutive.toPerm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexCharacterHadamard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual real-part Hadamard identity for complex characters -/

namespace Ostmann

open Complex Filter
open scoped Topology BigOperators ComplexConjugate

theorem character_real_zero_summable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    Summable (fun i => ((s - (actualCharacterZeros χ).zeros i)⁻¹).re) := by
  let Z := actualCharacterZeros χ
  have hh := character_zero_inverse_square_summable χ
  let C := 8 + 4 * (s.re - 1)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply Summable.of_nonneg_of_le
    (fun i => by rw [realZeroKernel_complex_sub]; exact realZeroKernel_nonneg (by linarith [(Z.in_strip i).2]))
    (fun i => ?_) (hh.mul_left (C * (1 + |s.im|) ^ 2))
  rw [realZeroKernel_complex_sub]
  calc
    _ ≤ C * ((1 + |s.im - (Z.zeros i).im|) ^ 2)⁻¹ :=
      real_zero_kernel_square_bound _ _ (s.re - 1) (by linarith)
        (by linarith [(Z.in_strip i).2]) (by linarith [(Z.in_strip i).1])
    _ ≤ C * ((1 + |s.im|) ^ 2 * ((1 + |(Z.zeros i).im|) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left (inverse_square_shift_bound _ _) hC
    _ = _ := by dsimp [Z]; ring

theorem character_real_zero_self_reflection (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    Summable (fun i => ((1 - conj s - (actualCharacterZeros χ).zeros i)⁻¹).re) ∧
      characterRealZeroSum χ (1 - conj s) = -characterRealZeroSum χ s := by
  have he (i : ℕ) : ((1 - conj s - (actualCharacterZeros χ).zeros i)⁻¹).re =
      -((s - (actualCharacterZeros χ).zeros (characterZeroIndexSelfReflection χ i))⁻¹).re := by
    rw [characterZeroIndexSelfReflection_zeros]
    have ha : s - (1 - conj ((actualCharacterZeros χ).zeros i)) =
        -conj (1 - conj s - (actualCharacterZeros χ).zeros i) := by simp; ring
    rw [ha, inv_neg, Complex.neg_re, neg_neg, ← map_inv₀, Complex.conj_re]
  have hsum := character_real_zero_summable χ s hs hs2
  constructor
  · simpa only [he, Function.comp_def] using
      (hsum.comp_injective (characterZeroIndexSelfReflection χ).injective).neg
  · unfold characterRealZeroSum
    simp_rw [he]
    rw [tsum_neg]
    congr 1
    exact (characterZeroIndexSelfReflection χ).tsum_eq
      (fun i => ((s - (actualCharacterZeros χ).zeros i)⁻¹).re)

/-- The conjugate functional equation cancels the constant term, yielding the
actual zero sum used in the full-height zero-free argument. -/
theorem complex_character_hadamard_identity (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    characterRealZeroSum χ s = (logDeriv χ.completed s).re +
      (1 / 2) * Real.log χ.modulus := by
  have hp := character_completed_partial_real_limit χ s (character_real_zero_summable χ s hs hs2)
  obtain ⟨hn, heq⟩ := character_real_zero_self_reflection χ s hs hs2
  have hm := character_completed_partial_real_limit χ (1 - conj s) hn
  have hc := completed_partial_fraction_difference_tendsto χ (1 - conj s) s
    (χ.completed_ne_zero_left _ (by simp; linarith)) (χ.completed_ne_zero_right _ hs.le)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  have hlim : characterRealZeroSum χ s - characterRealZeroSum χ (1 - conj s) =
      (logDeriv χ.completed s - logDeriv χ.completed (1 - conj s)).re := by
    apply tendsto_nhds_unique (hp.sub hm)
    simpa only [Function.comp_def, Complex.sub_re] using hr
  rw [heq, χ.completed_logDeriv_self_reflection s hs.le] at hlim
  simp only [Complex.sub_re, Complex.neg_re, Complex.conj_re, Complex.log_re, Complex.norm_natCast] at hlim
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterHadamardBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic bounds from the actual character zero sum -/

namespace Ostmann

open Complex

theorem character_real_zero_term_le (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) (i : ℕ) :
    ((s - (actualCharacterZeros χ).zeros i)⁻¹).re ≤ characterRealZeroSum χ s := by
  exact (character_real_zero_summable χ s hs hs2).le_tsum i (fun j _ => by
    rw [realZeroKernel_complex_sub]
    exact realZeroKernel_nonneg (by linarith [((actualCharacterZeros χ).in_strip j).2]))

theorem exists_character_zero_sum_log_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      characterRealZeroSum χ s ≤ (logDeriv χ.L s).re +
        (1 / 2) * Real.log χ.modulus + B * Real.log (|s.im| + 2) := by
  obtain ⟨B, hB, hb⟩ := characterGamma_logarithmic_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs hs2
  rw [complex_character_hadamard_identity χ s hs hs2,
    χ.completed_logDeriv_eq_add s hs.le, Complex.add_re]
  have hh := (Complex.re_le_norm _).trans (hb χ s hs hs2)
  linarith

/-- Positivity of every actual zero contribution gives the uniform lower bound
for the ordinary logarithmic derivative used in the zero-free argument. -/
theorem exists_character_logDeriv_real_lower : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      -(1 / 2) * Real.log χ.modulus - B * Real.log (|s.im| + 2) ≤
        (logDeriv χ.L s).re := by
  obtain ⟨B, hB, hb⟩ := exists_character_zero_sum_log_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs hs2
  have hh := hb χ s hs hs2
  have hn := character_real_zero_sum_nonneg χ s hs
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ImprimitiveEulerBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Euler-factor cost of changing a character's level -/

namespace Ostmann

open Complex Filter
open scoped BigOperators Topology

noncomputable def imprimitiveEulerProduct {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (s : ℂ) : ℂ := ∏ p ∈ N.primeFactors, imprimitiveEulerFactor χ p s

theorem imprimitiveEulerFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) : imprimitiveEulerFactor χ p s ≠ 0 := by
  intro h
  have hh := euler_tail_norm_le_half χ hp s hs
  have he : χ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hh
  norm_num at hh

theorem imprimitiveEulerFactor_hasDeriv {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (imprimitiveEulerFactor χ p)
      ((χ p * (p : ℂ) ^ (-s)) * Complex.log (p : ℂ)) s := by
  have hn : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hh := (((hasDerivAt_id s).neg).const_cpow (.inl hn)).const_mul (χ p) |>.const_sub 1
  change HasDerivAt (fun x : ℂ => 1 - χ p * (p : ℂ) ^ (-x)) _ s
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp)
  ring

theorem imprimitiveEulerFactor_logDeriv_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (imprimitiveEulerFactor χ p) s‖ ≤ Real.log p := by
  let u := χ p * (p : ℂ) ^ (-s)
  have hu : ‖u‖ ≤ 1 / 2 := euler_tail_norm_le_half χ hp s hs
  have hden : 0 < ‖1 - u‖ := norm_pos_iff.mpr (imprimitiveEulerFactor_ne_zero χ hp s hs)
  have hcomp : ‖u‖ ≤ ‖1 - u‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) u
    rw [norm_one] at hh
    linarith
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
  rw [logDeriv_apply, (imprimitiveEulerFactor_hasDeriv χ hp s).deriv, norm_div, norm_mul, hlog]
  apply (div_le_iff₀ hden).mpr
  change ‖u‖ * Real.log p ≤ Real.log p * ‖1 - u‖
  have hplog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le)
  nlinarith [mul_le_mul_of_nonneg_right hcomp hplog]

theorem imprimitiveEulerProduct_logDeriv_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 0 < N) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (imprimitiveEulerProduct χ N) s‖ ≤ Real.log N := by
  have he : logDeriv (imprimitiveEulerProduct χ N) s =
      ∑ p ∈ N.primeFactors, logDeriv (imprimitiveEulerFactor χ p) s := by
    unfold imprimitiveEulerProduct
    rw [logDeriv_prod]
    · intro p hp
      exact imprimitiveEulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp) s hs
    · intro p hp
      exact (imprimitiveEulerFactor_hasDeriv χ (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  rw [he]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun p hp =>
    imprimitiveEulerFactor_logDeriv_bound χ (Nat.prime_of_mem_primeFactors hp) s hs)).trans
  exact sum_log_prime_divisors_le _ hN (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun _ hp => Nat.dvd_of_mem_primeFactors hp)

/-- Passing from a primitive character to any multiple level costs at most
`log N` in its logarithmic derivative, uniformly throughout Re(s)>1. -/
theorem logDeriv_changeLevel_bound {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (hN : q ∣ N) (s : ℂ) (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction (DirichletCharacter.changeLevel hN χ)) s -
      logDeriv (DirichletCharacter.LFunction χ) s‖ ≤ Real.log N := by
  have he : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hN χ) =ᶠ[𝓝 s]
      (DirichletCharacter.LFunction χ) * imprimitiveEulerProduct χ N := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_changeLevel hN χ (.inr (by intro h; simp [h] at hz))
  have hprod : imprimitiveEulerProduct χ N s ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p hp => imprimitiveEulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp) s hs.le)
  have hprodD : DifferentiableAt ℂ (imprimitiveEulerProduct χ N) s :=
    DifferentiableAt.fun_finsetProd (fun p hp =>
      (imprimitiveEulerFactor_hasDeriv χ (Nat.prime_of_mem_primeFactors hp) s).differentiableAt)
  have hl := (logDeriv_congr_nhds he).self_of_nhds
  rw [show (DirichletCharacter.LFunction χ * imprimitiveEulerProduct χ N) =
    fun z => DirichletCharacter.LFunction χ z * imprimitiveEulerProduct χ N z from rfl] at hl
  rw [logDeriv_mul s (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (.inr (by intro h; simp [h] at hs)) hs.le) hprod
    (DirichletCharacter.differentiableAt_LFunction χ s (.inl (by intro h; simp [h] at hs))) hprodD] at hl
  rw [hl, add_sub_cancel_left]
  exact imprimitiveEulerProduct_logDeriv_bound χ N (NeZero.pos N) s hs.le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_NonprincipalLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic-derivative lower bound at an arbitrary character level -/

namespace Ostmann

open Complex

noncomputable def primitiveOfNonprincipal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : PrimitiveComplexCharacter where
  modulus := χ.conductor
  positive := Nat.pos_of_ne_zero χ.conductor_ne_zero
  character := χ.primitiveCharacter
  primitive := χ.primitiveCharacter_isPrimitive
  nontrivial := by
    intro he
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, he, DirichletCharacter.changeLevel_one]

theorem primitiveOfNonprincipal_logDeriv_difference {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s -
      logDeriv (primitiveOfNonprincipal χ hχ).L s‖ ≤ Real.log q := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hh := logDeriv_changeLevel_bound χ.primitiveCharacter χ.conductor_dvd_level s hs
  rw [χ.changeLevel_primitiveCharacter] at hh
  exact hh

/-- Only a logarithmic modulus loss is incurred by imprimitive characters. -/
theorem exists_nonprincipal_logDeriv_real_lower : ∃ B : ℝ, 0 < B ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
        -(3 / 2) * Real.log q - B * Real.log (|s.im| + 2) ≤
          (logDeriv (DirichletCharacter.LFunction χ) s).re := by
  obtain ⟨B, hB, hb⟩ := exists_character_logDeriv_real_lower
  refine ⟨B, hB, ?_⟩
  intro q _ χ hχ s hs hs2
  have hprimitive := hb (primitiveOfNonprincipal χ hχ) s hs hs2
  have herr := primitiveOfNonprincipal_logDeriv_difference χ hχ s hs
  have hre := Complex.re_le_norm (-(logDeriv (DirichletCharacter.LFunction χ) s -
    logDeriv (primitiveOfNonprincipal χ hχ).L s))
  rw [Complex.neg_re, Complex.sub_re, norm_neg] at hre
  have hlog : Real.log χ.conductor ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
  change -(1 / 2) * Real.log χ.conductor - B * Real.log (|s.im| + 2) ≤ _ at hprimitive
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_NonquadraticZeroBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full-height zero-sum bound when the squared character is nonprincipal -/

namespace Ostmann

open Complex

theorem exists_nonquadratic_zero_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter), χ.character ^ 2 ≠ 1 →
      ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
        4 * characterRealZeroSum χ ((σ : ℂ) + (t : ℂ) * I) ≤
          3 / (σ - 1) + C * (Real.log χ.modulus + Real.log (|t| + 2) + 1) := by
  obtain ⟨B, hB, hb⟩ := exists_nonprincipal_logDeriv_real_lower
  obtain ⟨G, hG, hg⟩ := exists_character_zero_sum_log_bound
  obtain ⟨V, hV, hv⟩ := exists_vonMangoldt_series_bound
  refine ⟨4 * G + 2 * B + 4 * V + 4, by positivity, ?_⟩
  intro χ hχ σ t hσ hσ2
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hp := complex_character_trigonometric_sum_nonneg χ.character σ t hσ
  rw [dirichlet_mangoldt_LSeries_eq _ _ (by simpa using hσ),
    dirichlet_mangoldt_LSeries_eq _ _ (by simpa using hσ), Complex.neg_re, Complex.neg_re] at hp
  have hh := hg χ ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ) (by simpa using hσ2)
  have hd := hb χ.modulus (χ.character ^ 2) hχ
    ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) (by simpa using hσ) (by simpa using hσ2)
  have hvr := (Complex.re_le_norm _).trans (hv σ hσ hσ2)
  have hlog := log_double_abs_height_le t
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
    Complex.ofReal_re, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hh hd
  change 4 * characterRealZeroSum χ _ ≤ _
  change characterRealZeroSum χ _ ≤
    (logDeriv (DirichletCharacter.LFunction χ.character) _).re +
      (1 / 2) * Real.log χ.modulus + G * Real.log (|t| + 2) at hh
  have hBlog := mul_le_mul_of_nonneg_left hlog hB.le
  have hGq := mul_nonneg hG.le hq
  have hBq := mul_nonneg hB.le hq
  have hVq := mul_nonneg hV.le hq
  have hVt := mul_nonneg hV.le ht
  simp only [div_eq_mul_inv] at hvr ⊢
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmallDiskLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed small-disk logarithmic-derivative estimate -/

namespace Ostmann

open Complex Metric Set

theorem logDeriv_norm_le_small_disk (g : ℂ → ℂ) (A : ℝ) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 (3 / 2)))
    (hne : ∀ z ∈ ball 0 (3 / 2), g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 (3 / 2), Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (w : ℂ) (hw : ‖w‖ ≤ 1) : ‖logDeriv g w‖ ≤ 48 * A := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g (3 / 2)
    (by norm_num) hg hne
  have hd : DifferentiableOn ℂ F (ball 0 (3 / 2)) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 (3 / 2)) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self (by norm_num))) (heF z hz)]
    exact hlog z hz
  have hv (v : ℂ) (hv : v ∈ closedBall w (1 / 8)) : ‖v‖ ≤ 9 / 8 := by
    have hh := norm_le_norm_sub_add v w
    have hdist : ‖v - w‖ ≤ 1 / 8 := by simpa only [mem_closedBall, dist_eq_norm] using hv
    linarith
  have hvball (v : ℂ) (h : v ∈ closedBall w (1 / 8)) : v ∈ ball 0 (3 / 2) := by
    rw [mem_ball, dist_zero_right]
    linarith [hv v h]
  have hdc : DiffContOnCl ℂ F (ball w (1 / 8)) := by
    apply DiffContOnCl.mk_ball
    · intro v hv'
      exact (hF v (hvball v (ball_subset_closedBall hv'))).differentiableAt.differentiableWithinAt
    · exact fun v hv' => (hF v (hvball v hv')).continuousAt.continuousWithinAt
  have hbound : ∀ v ∈ sphere w (1 / 8), ‖F v‖ ≤ 6 * A := by
    intro v hv'
    have hvC := sphere_subset_closedBall hv'
    have hnv := hv v hvC
    have hden : 0 < 3 / 2 - ‖v‖ := by linarith
    have hh := Complex.borelCaratheodory_zero hA hd hreal (by norm_num)
      (hvball v hvC) hF0
    apply hh.trans
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 8) hdc hbound
  have hwball : w ∈ ball 0 (3 / 2) := by rw [mem_ball, dist_zero_right]; linarith
  rw [(hF w hwball).deriv] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RegularizedZeta
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the zeta pole and bounding the resulting entire function -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem regularizedZeta_norm_bound (s : ℂ) (hs : 1 / 4 ≤ s.re) :
    ‖regularizedZeta s‖ ≤ ‖s - 1‖ + 1 + 4 * ‖s - 1‖ * ‖s‖ := by
  by_cases he : s = 1
  · simp [he]
  · have hdomain : s ∈ zetaAbelContinuationDomain := ⟨he, by
      change (1 / 10 : ℝ) < s.re
      linarith⟩
    have hb := norm_zetaAbelContinuationFormula_le s hdomain
    rw [← riemannZeta_eq_zetaAbelContinuationFormula s hdomain] at hb
    rw [regularizedZeta_eq s he, norm_mul]
    have hn : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
    have hsr : 0 < s.re := by linarith
    have hc : ‖s‖ / s.re ≤ 4 * ‖s‖ := by
      apply (div_le_iff₀ hsr).mpr
      nlinarith [norm_nonneg s]
    have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (s - 1))
    rw [one_div, norm_inv, mul_add, mul_add, mul_one, mul_inv_cancel₀ hn.ne'] at hm
    nlinarith [mul_le_mul_of_nonneg_left hc (norm_nonneg (s - 1))]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaDiskBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the pole-removed zeta function on right-half-plane disks -/

namespace Ostmann

open Complex Metric Set

theorem riemannZeta_lower_re_two (s : ℂ) (hs : s.re = 2) :
    1 / 3 ≤ ‖riemannZeta s‖ := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)
  have hf (n : ℕ) (_hn : n ≠ 0) : ‖f n‖ ≤ 1 := by
    dsimp [f]
    norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  have hb := lSeries_norm_bound_re_two f hf s hs
  have he : riemannZeta s * LSeries f s = 1 := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by rw [hs]; norm_num)]
    exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (by rw [hs]; norm_num)
  have hn := congrArg norm he
  rw [norm_mul, norm_one] at hn
  have hpi : Real.pi ^ 2 / 6 ≤ 3 := by
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hm := mul_le_mul_of_nonneg_left (hb.trans hpi) (norm_nonneg (riemannZeta s))
  rw [hn] at hm
  linarith

theorem regularizedZeta_lower_center (t : ℝ) :
    1 / 3 ≤ ‖regularizedZeta (characterZeroCenter t)‖ := by
  have hne : characterZeroCenter t ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
  have hlo := riemannZeta_lower_re_two (characterZeroCenter t) (characterZeroCenter_re t)
  have hnorm : 1 ≤ ‖characterZeroCenter t - 1‖ := by
    have hh := Complex.re_le_norm (characterZeroCenter t - 1)
    norm_num only [Complex.sub_re, characterZeroCenter_re, Complex.one_re, Nat.reduceSub,
      show (2 : ℝ) - 1 = 1 by norm_num] at hh
    exact hh
  rw [regularizedZeta_eq _ hne, norm_mul]
  nlinarith [norm_nonneg (riemannZeta (characterZeroCenter t))]

theorem regularizedZeta_disk_bound (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (7 / 4 : ℝ)) :
    ‖regularizedZeta z‖ ≤ 32 * (|t| + 2) ^ 2 := by
  have hbound := regularizedZeta_norm_bound z (character_disk_re t z hz)
  have hn := character_disk_norm t z hz
  have hsub : ‖z - 1‖ ≤ |t| + 5 := by
    have hh := norm_sub_le z 1
    rw [norm_one] at hh
    linarith
  have hprod : ‖z - 1‖ * ‖z‖ ≤ (|t| + 5) * (|t| + 4) :=
    mul_le_mul hsub hn (norm_nonneg _) (by positivity)
  nlinarith [abs_nonneg t, sq_nonneg t]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaDiskZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite zeta zero factors in a small right-half-plane disk -/

namespace Ostmann

open Complex Filter Metric Set MeromorphicOn
open scoped Classical BigOperators

noncomputable def zetaAtHeight (t : ℝ) (w : ℂ) : ℂ :=
  regularizedZeta (w + characterZeroCenter t)

theorem zetaAtHeight_analytic (t : ℝ) (w : ℂ) : AnalyticAt ℂ (zetaAtHeight t) w :=
  (regularizedZeta_analytic _).comp (analyticAt_id.add analyticAt_const)

theorem zetaAtHeight_lower_zero (t : ℝ) : 1 / 3 ≤ ‖zetaAtHeight t 0‖ := by
  simpa [zetaAtHeight] using regularizedZeta_lower_center t

theorem zetaAtHeight_order_ne_top (t : ℝ) (w : ℂ) :
    analyticOrderAt (zetaAtHeight t) w ≠ ⊤ := by
  intro he
  have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero w (zetaAtHeight_analytic t)).mp he
  have hl := zetaAtHeight_lower_zero t
  rw [hz] at hl
  norm_num at hl

noncomputable def zetaDiskDivisor (t : ℝ) :=
  divisor (zetaAtHeight t) (closedBall 0 (3 / 2 : ℝ))

noncomputable def zetaDiskZeros (t : ℝ) : Finset ℂ :=
  ((zetaDiskDivisor t).finiteSupport (isCompact_closedBall 0 (3 / 2 : ℝ))).toFinset

theorem zetaDiskDivisor_eq (t : ℝ) (w : ℂ) (hw : ‖w‖ ≤ 3 / 2) :
    zetaDiskDivisor t w = (analyticOrderNatAt (zetaAtHeight t) w : ℤ) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (zetaAtHeight_order_ne_top t w)
  rw [zetaDiskDivisor, AnalyticOnNhd.divisor_apply
    (fun z _ => zetaAtHeight_analytic t z) (by simpa using hw)]
  simp [analyticOrderNatAt, ← hn]

theorem mem_zetaDiskZeros (t : ℝ) (w : ℂ) :
    w ∈ zetaDiskZeros t ↔ ‖w‖ ≤ 3 / 2 ∧ zetaAtHeight t w = 0 := by
  change w ∈ ((zetaDiskDivisor t).finiteSupport (isCompact_closedBall _ _)).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  change zetaDiskDivisor t w ≠ 0 ↔ _
  have hord : analyticOrderNatAt (zetaAtHeight t) w ≠ 0 ↔ zetaAtHeight t w = 0 := by
    have hh := (zetaAtHeight_analytic t w).analyticOrderAt_ne_zero
    rw [← Nat.cast_analyticOrderNatAt (zetaAtHeight_order_ne_top t w)] at hh
    simpa only [Nat.cast_ne_zero] using hh
  constructor
  · intro hn
    have hw : ‖w‖ ≤ 3 / 2 := by
      simpa using (zetaDiskDivisor t).supportWithinDomain hn
    exact ⟨hw, hord.mp (by simpa only [zetaDiskDivisor_eq t w hw, Int.natCast_ne_zero] using hn)⟩
  · rintro ⟨hw, hz⟩
    rw [zetaDiskDivisor_eq t w hw, Int.natCast_ne_zero]
    exact hord.mpr hz

theorem zetaAtHeight_disk_bound (t : ℝ) (w : ℂ) (hw : ‖w‖ ≤ 7 / 4) :
    ‖zetaAtHeight t w‖ ≤ 32 * (|t| + 2) ^ 2 := by
  apply regularizedZeta_disk_bound
  simpa [dist_eq_norm] using hw

theorem zetaDiskZeros_mass_bound (t : ℝ) :
    (∑ w ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) w : ℝ)) ≤
      Real.log (96 * (|t| + 2) ^ 2) / Real.log (7 / 6) := by
  let M := 32 * (|t| + 2) ^ 2
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t, sq_nonneg (|t| + 2)]
  have hlo := zetaAtHeight_lower_zero t
  have hne : zetaAtHeight t 0 ≠ 0 := by intro he; rw [he, norm_zero] at hlo; linarith
  have ha : AnalyticOnNhd ℂ (zetaAtHeight t) (closedBall 0 |(7 / 4 : ℝ)|) :=
    fun z _ => zetaAtHeight_analytic t z
  have hj := ha.sum_divisor_le (r := (3 / 2 : ℝ)) (R := (7 / 4 : ℝ))
    (by norm_num) (by norm_num) hM hne (fun z hz =>
      zetaAtHeight_disk_bound t z (by
        simpa only [mem_closedBall, dist_zero_right, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)]
          using sphere_subset_closedBall hz))
  have hratio : M / ‖zetaAtHeight t 0‖ ≤ 3 * M := by
    apply (div_le_iff₀ (by linarith : 0 < ‖zetaAtHeight t 0‖)).mpr
    nlinarith
  have hlog := Real.log_le_log (div_pos (by linarith : 0 < M) (norm_pos_iff.mpr hne)) hratio
  have hlogp : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
  have hmass : (∑ w ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) w : ℝ)) =
      ((∑ᶠ w, zetaDiskDivisor t w : ℤ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset (s := zetaDiskZeros t) _ (by
      intro w hw
      exact ((zetaDiskDivisor t).finiteSupport (isCompact_closedBall _ _)).mem_toFinset.mpr hw),
      Int.cast_sum]
    apply Finset.sum_congr rfl
    intro w hw
    rw [zetaDiskDivisor_eq t w ((mem_zetaDiskZeros t w).mp hw).1]
    simp
  rw [hmass]
  change ((∑ᶠ w, divisor (zetaAtHeight t) (closedBall 0 (3 / 2 : ℝ)) w : ℤ) : ℝ) ≤ _
  rw [show |(3 / 2 : ℝ)| = 3 / 2 by norm_num,
    show (7 / 4 : ℝ) / (3 / 2) = 7 / 6 by norm_num] at hj
  apply hj.trans
  convert div_le_div_of_nonneg_right hlog hlogp.le using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [M]
  congr 2
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaDiskQuotient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the actual local zeta zeros, with a logarithmic error -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem zeta_disk_quotient_exists (t : ℝ) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      (∀ z, zetaAtHeight t z = finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) z * g z) ∧
      (∀ z ∈ closedBall 0 (3 / 2 : ℝ), g z ≠ 0) := by
  obtain ⟨g, hg, he, hne⟩ := remove_finite_analytic_zeros (zetaAtHeight t)
    (zetaAtHeight_analytic t) (zetaAtHeight_order_ne_top t) (zetaDiskZeros t)
  refine ⟨g, hg, he, ?_⟩
  intro z hz
  by_cases hS : z ∈ zetaDiskZeros t
  · exact hne z hS
  · intro hzero
    apply hS
    apply (mem_zetaDiskZeros t z).mpr
    exact ⟨by simpa using hz, by rw [he, hzero, mul_zero]⟩

theorem zeta_disk_quotient_bound (t M : ℝ) (hM : 32 * (|t| + 2) ^ 2 ≤ M)
    (g : ℂ → ℂ) (hg : ∀ z, AnalyticAt ℂ g z)
    (he : ∀ z, zetaAtHeight t z = finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) z * g z)
    (z : ℂ) (hz : ‖z‖ ≤ 7 / 4) :
    ‖g z‖ ≤ M * 4 ^ (∑ w ∈ zetaDiskZeros t, analyticOrderNatAt (zetaAtHeight t) w) := by
  let N := ∑ w ∈ zetaDiskZeros t, analyticOrderNatAt (zetaAtHeight t) w
  have hb : ∀ u ∈ sphere (0 : ℂ) (7 / 4), ‖g u‖ ≤ M * 4 ^ N := by
    intro u hu
    have hnu : ‖u‖ = 7 / 4 := by simpa using hu
    have hp : (1 / 4 : ℝ) ^ N ≤ ‖finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) u‖ := by
      apply finiteZeroPolynomial_norm_ge _ _ _ _ (by norm_num)
      intro w hw
      have hnw := ((mem_zetaDiskZeros t w).mp hw).1
      have htri := norm_le_norm_sub_add u w
      linarith
    have hm := (zetaAtHeight_disk_bound t u hnu.le).trans hM
    rw [he, norm_mul] at hm
    have hprod := (mul_le_mul_of_nonneg_right hp (norm_nonneg (g u))).trans hm
    have hh := (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 1 / 4) N)).mpr
      (by simpa only [mul_comm] using hprod)
    simpa only [one_div, inv_pow, div_inv_eq_mul] using hh
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) (7 / 4)) isBounded_ball
  · exact DiffContOnCl.mk_ball (fun u _ => (hg u).differentiableAt.differentiableWithinAt)
      (fun u _ => (hg u).continuousAt.continuousWithinAt)
  · rw [frontier_ball (0 : ℂ) (by norm_num : (7 / 4 : ℝ) ≠ 0)]
    exact hb
  · simpa [closure_ball (0 : ℂ) (by norm_num : (7 / 4 : ℝ) ≠ 0)] using hz

theorem zeta_disk_quotient_log_bound (t M : ℝ) (hM : 32 * (|t| + 2) ^ 2 ≤ M)
    (g : ℂ → ℂ) (hg : ∀ z, AnalyticAt ℂ g z)
    (he : ∀ z, zetaAtHeight t z = finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) z * g z)
    (hne : ∀ z ∈ closedBall 0 (3 / 2 : ℝ), g z ≠ 0)
    (z : ℂ) (hz : ‖z‖ ≤ 3 / 2) :
    Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ Real.log (3 * M) +
      (∑ w ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) w : ℝ)) * Real.log 6 := by
  let N := ∑ w ∈ zetaDiskZeros t, analyticOrderNatAt (zetaAtHeight t) w
  have hMp : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hgc : 0 < ‖g 0‖ := norm_pos_iff.mpr (hne 0 (mem_closedBall_self (by norm_num)))
  have hp : ‖finiteZeroPolynomial (zetaAtHeight t) (zetaDiskZeros t) 0‖ ≤ (3 / 2 : ℝ) ^ N := by
    apply finiteZeroPolynomial_norm_le _ _ _ _ (by norm_num)
    intro w hw
    simpa only [zero_sub, norm_neg] using ((mem_zetaDiskZeros t w).mp hw).1
  have hlo : (1 / 3 : ℝ) ≤ (3 / 2 : ℝ) ^ N * ‖g 0‖ := by
    have hh := zetaAtHeight_lower_zero t
    rw [he, norm_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  have hpow : (4 : ℝ) ^ N * (3 / 2 : ℝ) ^ N = 6 ^ N := by rw [← mul_pow]; norm_num
  have hm : M * 4 ^ N ≤ 3 * M * 6 ^ N * ‖g 0‖ := by
    calc
      _ = (3 * M * 4 ^ N) * (1 / 3) := by ring
      _ ≤ (3 * M * 4 ^ N) * ((3 / 2) ^ N * ‖g 0‖) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = 3 * M * (4 ^ N * (3 / 2) ^ N) * ‖g 0‖ := by ring
      _ = _ := by rw [hpow]
  have hu := zeta_disk_quotient_bound t M hM g hg he z (by linarith)
  have hratio : ‖g z‖ / ‖g 0‖ ≤ 3 * M * 6 ^ N := (div_le_iff₀ hgc).mpr (hu.trans hm)
  have hgz : 0 < ‖g z‖ := norm_pos_iff.mpr (hne z (by simpa using hz))
  rw [← Real.log_div hgz.ne' hgc.ne']
  apply (Real.log_le_log (div_pos hgz hgc) hratio).trans_eq
  rw [Real.log_mul (by positivity : 3 * M ≠ 0) (by positivity : (6 : ℝ) ^ N ≠ 0), Real.log_pow]
  simp only [N, Nat.cast_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZetaLocalLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A logarithmic error for the zeta pole throughout the right-hand strip -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem zetaAtHeight_zero_left (t : ℝ) (z : ℂ) (hz : zetaAtHeight t z = 0) : z.re < -1 := by
  have hn : ¬ 1 ≤ (z + characterZeroCenter t).re := by
    intro h
    exact regularizedZeta_ne_zero_right _ h hz
  simp only [Complex.add_re, characterZeroCenter_re] at hn
  linarith

theorem zetaAtHeight_logDeriv_lower (t σ : ℝ) (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    -(logDeriv (zetaAtHeight t) ((σ - 2 : ℝ) : ℂ)).re ≤
      48 * (Real.log (96 * (|t| + 2) ^ 2) +
        (Real.log (96 * (|t| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 + 1) := by
  obtain ⟨g, hg, he, hne⟩ := zeta_disk_quotient_exists t
  let M := 32 * (|t| + 2) ^ 2
  let N := ∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℝ)
  let A := Real.log (3 * M) + N * Real.log 6 + 1
  let w : ℂ := ((σ - 2 : ℝ) : ℂ)
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [abs_nonneg t, sq_nonneg (|t| + 2)]
  have hA : 0 < A := by
    have hl : 0 ≤ Real.log (3 * M) := Real.log_nonneg (by linarith)
    have hl6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
    have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    dsimp [A]
    positivity
  have hw : ‖w‖ ≤ 1 := by
    change ‖((σ - 2 : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hgb := logDeriv_norm_le_small_disk g A hA (fun z _ => hg z)
    (fun z hz => hne z (ball_subset_closedBall hz)) (fun z hz => ?_) w hw
  · have hwball : w ∈ closedBall 0 (3 / 2 : ℝ) := by
      simpa using hw.trans (by norm_num : (1 : ℝ) ≤ 3 / 2)
    have hfne : zetaAtHeight t w ≠ 0 := by
      apply regularizedZeta_ne_zero_right
      simp only [w, Complex.add_re, Complex.ofReal_re, characterZeroCenter_re]
      linarith
    have hwS : w ∉ zetaDiskZeros t := fun hh => hfne ((mem_zetaDiskZeros t w).mp hh).2
    have hsplit : logDeriv (zetaAtHeight t) w =
        (∑ z ∈ zetaDiskZeros t, (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)) +
          logDeriv g w := by
      have hfun := funext he
      conv_lhs => rw [hfun]
      rw [logDeriv_mul w (finiteZeroPolynomial_ne_zero _ _ w hwS) (hne w hwball)
        (finiteZeroPolynomial_analytic _ _ w).differentiableAt (hg w).differentiableAt,
        finiteZeroPolynomial_logDeriv _ _ w hwS]
    have hsum : 0 ≤ (∑ z ∈ zetaDiskZeros t,
        (analyticOrderNatAt (zetaAtHeight t) z : ℂ) / (w - z)).re := by
      rw [Complex.re_sum]
      apply Finset.sum_nonneg
      intro z hz
      have hzleft := zetaAtHeight_zero_left t z ((mem_zetaDiskZeros t z).mp hz).2
      have hd : 0 ≤ (w - z).re := by
        simp only [Complex.sub_re, w, Complex.ofReal_re]
        linarith
      rw [div_eq_mul_inv, Complex.mul_re]
      simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (by
        rw [Complex.inv_re]
        exact div_nonneg hd (Complex.normSq_nonneg _))
    have hre := Complex.re_le_norm (-logDeriv g w)
    rw [Complex.neg_re, norm_neg] at hre
    have hmass := zetaDiskZeros_mass_bound t
    have hprod := mul_le_mul_of_nonneg_right hmass (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6))
    have hlog : Real.log (3 * M) = Real.log (96 * (|t| + 2) ^ 2) := by
      congr 1
      dsimp [M]
      ring
    rw [hsplit, Complex.add_re]
    dsimp only [A, N] at hgb
    rw [hlog] at hgb
    linarith
  · exact (zeta_disk_quotient_log_bound t M le_rfl g hg he hne z
      (by simpa using (mem_ball_iff_norm.mp hz).le)).trans (by dsimp [A, N]; linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_VonMangoldtLogarithmicBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The zeta-pole upper bound with logarithmic dependence on height -/

namespace Ostmann

open Complex

theorem regularizedZeta_logDeriv_lower (s : ℂ) (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    -(logDeriv regularizedZeta s).re ≤
      48 * (Real.log (96 * (|s.im| + 2) ^ 2) +
        (Real.log (96 * (|s.im| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 + 1) := by
  have hh := zetaAtHeight_logDeriv_lower s.im s.re hs hs2
  have hcomp : logDeriv (zetaAtHeight s.im) ((s.re - 2 : ℝ) : ℂ) =
      logDeriv regularizedZeta s := by
    change logDeriv (regularizedZeta ∘ (fun z : ℂ => z + characterZeroCenter s.im)) _ = _
    rw [logDeriv_comp (g := fun z : ℂ => z + characterZeroCenter s.im)
      (regularizedZeta_analytic _).differentiableAt
      (differentiableAt_id.add_const _)]
    have he : ((s.re - 2 : ℝ) : ℂ) + characterZeroCenter s.im = s := by
      apply Complex.ext <;> simp [characterZeroCenter]
    convert congrArg (logDeriv regularizedZeta) he using 1
    all_goals try with_reducible_and_instances rfl
    simp
  rwa [hcomp] at hh

theorem exists_regularizedZeta_log_bound : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      -(logDeriv regularizedZeta s).re ≤ C * Real.log (|s.im| + 2) := by
  let D := 1 + Real.log 6 / Real.log (7 / 6 : ℝ)
  let E := Real.log 96 / Real.log 2 + 2
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
  have h76 : 0 < Real.log (7 / 6 : ℝ) := Real.log_pos (by norm_num)
  have h96 : 0 < Real.log (96 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨48 * (D * E + 1 / Real.log 2), by positivity, ?_⟩
  intro s hs hs2
  let L := Real.log (|s.im| + 2)
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num)
    (show (2 : ℝ) ≤ |s.im| + 2 by linarith [abs_nonneg s.im])
  have hone : 1 ≤ (1 / Real.log 2) * L := by
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ h2).mpr (by simpa using hL)
  have hconst : Real.log 96 ≤ (Real.log 96 / Real.log 2) * L := by
    have hh := mul_le_mul_of_nonneg_left hone h96.le
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hlog : Real.log (96 * (|s.im| + 2) ^ 2) = Real.log 96 + 2 * L := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rfl
  have he : Real.log (96 * (|s.im| + 2) ^ 2) ≤ E * L := by
    rw [hlog]
    dsimp [E]
    nlinarith
  have hh := regularizedZeta_logDeriv_lower s hs hs2
  have hm := mul_le_mul_of_nonneg_left he hD.le
  have hform : Real.log (96 * (|s.im| + 2) ^ 2) +
      (Real.log (96 * (|s.im| + 2) ^ 2) / Real.log (7 / 6)) * Real.log 6 =
        D * Real.log (96 * (|s.im| + 2) ^ 2) := by dsimp [D]; ring
  rw [hform] at hh
  change _ ≤ 48 * (D * E + 1 / Real.log 2) * L
  nlinarith

/-- Uniform zeta-pole estimate, without any zero-free-region assumption. -/
theorem exists_vonMangoldt_logarithmic_upper : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤
        realZeroKernel (s.re - 1) s.im + C * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedZeta_log_bound
  refine ⟨C, hC, ?_⟩
  intro s hs hs2
  have hh := hb s hs hs2
  rw [regularizedZeta_logDeriv s hs, Complex.add_re] at hh
  have he := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s = _ at he
  rw [he, neg_div, Complex.neg_re]
  have hk : ((s - 1)⁻¹).re = realZeroKernel (s.re - 1) s.im := by
    simpa using realZeroKernel_complex_sub s 1
  rw [hk] at hh
  simp only [logDeriv_apply] at hh
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FullHeightRealShiftedBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real-character shifted zero sum at every height -/

namespace Ostmann

open Complex

theorem exists_full_height_real_shifted_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveRealCharacter) (σ t : ℝ), 1 < σ → σ ≤ 2 →
      4 * shiftedRealCharacterZeroSum χ ((σ : ℂ) + (t : ℂ) * I) ≤
        3 / (σ - 1) + realZeroKernel (σ - 1) (2 * t) +
          C * (Real.log χ.modulus + Real.log (|t| + 2) + 1) := by
  obtain ⟨G, hG, hg⟩ := exists_character_zero_sum_log_bound
  obtain ⟨V, hV, hv⟩ := exists_vonMangoldt_logarithmic_upper
  obtain ⟨R, hR, hr⟩ := exists_vonMangoldt_series_bound
  refine ⟨4 * G + 2 * V + 3 * R + 4, by positivity, ?_⟩
  intro χ σ t hσ hσ2
  have hzero := hg χ.asComplex ((σ : ℂ) + (t : ℂ) * I)
    (by simpa using hσ) (by simpa using hσ2)
  have hreal := (Complex.re_le_norm _).trans (hr σ hσ hσ2)
  have hdouble := hv ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)
    (by simpa using hσ) (by simpa using hσ2)
  have hp := real_character_trigonometric_sum_nonneg χ σ t hσ
  have he := χ.asComplex.mangoldt_LSeries_eq ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
  change LSeries (fun n => χ.complexCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ)) _ = _ at he
  rw [PrimitiveRealCharacter.asComplex_L] at he
  rw [he, neg_div, Complex.neg_re] at hp
  change shiftedRealCharacterZeroSum χ _ ≤ (logDeriv χ.L _).re +
    (1 / 2) * Real.log χ.modulus + G * Real.log (|((σ : ℂ) + (t : ℂ) * I).im| + 2) at hzero
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, add_zero, sub_zero] at hdouble hzero
  have hlog := mul_le_mul_of_nonneg_left (log_double_abs_height_le t) hV.le
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hGq := mul_nonneg hG.le hq
  have hVq := mul_nonneg hV.le hq
  have hRq := mul_nonneg hR.le hq
  have hRt := mul_nonneg hR.le ht
  simp only [logDeriv_apply] at hzero
  simp only [div_eq_mul_inv] at hreal ⊢
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZeroFreeNumerics
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete kernel comparisons for the low-height zero-free region -/

namespace Ostmann

theorem real_zero_near_mass (δ a y : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (ha' : a ≤ (21 / 20) * δ) (hy : |y| ≤ δ / 2) :
    7 / 10 ≤ δ * realZeroKernel a y := by
  have ha0 : 0 < a := hδ.trans_le ha
  have hden : 0 < a ^ 2 + y ^ 2 := by positivity
  have hasq : a ^ 2 ≤ ((21 / 20) * δ) ^ 2 := by nlinarith
  have hysq : y ^ 2 ≤ (δ / 2) ^ 2 := by
    nlinarith [sq_abs y, abs_nonneg y]
  have had : δ ^ 2 ≤ δ * a := by nlinarith
  unfold realZeroKernel
  rw [← mul_div_assoc, le_div_iff₀ hden]
  nlinarith [sq_pos_of_pos hδ]

theorem real_zero_double_height_mass (δ t : ℝ) (hδ : 0 < δ) (ht : δ / 2 ≤ |t|) :
    δ * realZeroKernel δ (2 * t) ≤ 1 / 2 := by
  have hden : 0 < δ ^ 2 + (2 * t) ^ 2 := by positivity
  have htsq : δ ^ 2 / 4 ≤ t ^ 2 := by nlinarith [sq_abs t]
  unfold realZeroKernel
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LowHeightZeroExclusion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local exceptional-zero argument with explicit margins -/

namespace Ostmann

open Complex
open scoped ComplexConjugate

theorem near_axis_zero_indices_unique (χ : PrimitiveRealCharacter) (δ R : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : δ * R ≤ 1 / 10)
    (hupper : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + R)
    (i j : ℕ)
    (hi : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re)
    (hj : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros j).re)
    (hiy : |((realCharacterActualZeros χ).zeros i).im| ≤ δ / 2)
    (hjy : |((realCharacterActualZeros χ).zeros j).im| ≤ δ / 2) : i = j := by
  by_contra hij
  have hpair := (shifted_real_zero_pair_le χ ((1 + δ : ℝ) : ℂ)
    (by simp; linarith) (by simp; linarith) i j hij).trans hupper
  rw [realZeroKernel_complex, realZeroKernel_complex] at hpair
  have hmi := real_zero_near_mass δ (1 + δ - ((realCharacterActualZeros χ).zeros i).re)
    _ hδ (by linarith [((realCharacterActualZeros χ).in_strip i).2]) (by linarith) hiy
  have hmj := real_zero_near_mass δ (1 + δ - ((realCharacterActualZeros χ).zeros j).re)
    _ hδ (by linarith [((realCharacterActualZeros χ).in_strip j).2]) (by linarith) hjy
  have hp := mul_le_mul_of_nonneg_left hpair hδ.le
  have he : δ * (1 / δ + R) = 1 + δ * R := by field_simp
  rw [he, mul_add] at hp
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FullHeightRealExclusion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exceptional real-zero argument in a bounded ordinate range -/

namespace Ostmann

open Complex
open scoped ComplexConjugate

theorem near_real_zero_small_ordinate (χ : PrimitiveRealCharacter) (δ S T : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : δ * S ≤ 1 / 10)
    (hupper : ∀ t : ℝ, |t| ≤ T →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + S)
    (i : ℕ) (hi : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re)
    (hiy : |((realCharacterActualZeros χ).zeros i).im| ≤ T) :
    |((realCharacterActualZeros χ).zeros i).im| < δ / 2 := by
  by_contra hy
  let ρ := (realCharacterActualZeros χ).zeros i
  let a : ℝ := 1 + δ - ρ.re
  let s : ℂ := ((1 + δ : ℝ) : ℂ) + (ρ.im : ℂ) * I
  have ha : δ ≤ a := by dsimp [a, ρ]; linarith [((realCharacterActualZeros χ).in_strip i).2]
  have ha' : a ≤ (21 / 20) * δ := by dsimp [a, ρ]; linarith
  have hterm := shifted_real_zero_term_le χ s (by dsimp [s]; simp; linarith)
    (by dsimp [s]; simp; linarith) i
  have hdiff : s - (realCharacterActualZeros χ).zeros i = (a : ℂ) := by
    apply Complex.ext <;> simp [s, a, ρ]
  rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re] at hterm
  have hb := (mul_le_mul_of_nonneg_left hterm (by norm_num : (0 : ℝ) ≤ 4)).trans (hupper ρ.im hiy)
  have hp := mul_le_mul_of_nonneg_left hb hδ.le
  have he : δ * (3 / δ + realZeroKernel δ (2 * ρ.im) + S) =
      3 + δ * realZeroKernel δ (2 * ρ.im) + δ * S := by field_simp
  rw [he] at hp
  have hm := real_zero_shifted_mass δ a hδ ha ha'
  have hk := real_zero_double_height_mass δ ρ.im hδ (le_of_not_gt hy)
  simp only [div_eq_mul_inv] at hm
  linarith

theorem near_real_zeros_real_unique_height (χ : PrimitiveRealCharacter) (δ R S T : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : δ * R ≤ 1 / 10) (hS : δ * S ≤ 1 / 10)
    (hreal : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + R)
    (hshift : ∀ t : ℝ, |t| ≤ T →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + S) :
    (∀ i, 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re →
      |((realCharacterActualZeros χ).zeros i).im| ≤ T →
      ((realCharacterActualZeros χ).zeros i).im = 0) ∧
    (∀ i j, 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re →
      1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros j).re →
      |((realCharacterActualZeros χ).zeros i).im| ≤ T →
      |((realCharacterActualZeros χ).zeros j).im| ≤ T → i = j) := by
  have hsmall := near_real_zero_small_ordinate χ δ S T hδ hδ1 hS hshift
  have huniq := near_axis_zero_indices_unique χ δ R hδ hδ1 hR hreal
  constructor
  · intro i hi hiy
    obtain ⟨j, hj⟩ := realCharacterActualZeros_conjugate χ i
    have hjre : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros j).re := by simpa [hj] using hi
    have hjim : |((realCharacterActualZeros χ).zeros j).im| ≤ δ / 2 := by
      simpa [hj] using (hsmall i hi hiy).le
    have hij := huniq i j hi hjre (hsmall i hi hiy).le hjim
    rw [← hij] at hj
    have hh := congrArg Complex.im hj
    simp only [Complex.conj_im] at hh
    linarith
  · intro i j hi hj hiy hjy
    exact huniq i j hi hj (hsmall i hi hiy).le (hsmall j hj hjy).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FullHeightRealRegion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform full-height real-character zero-free region with one simple exception -/

namespace Ostmann

open Complex

theorem exists_full_height_real_region : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : PrimitiveRealCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 2) + 1
      (∀ i, |((realCharacterActualZeros χ).zeros i).im| ≤ T →
        1 - c / H ≤ ((realCharacterActualZeros χ).zeros i).re →
        ((realCharacterActualZeros χ).zeros i).im = 0) ∧
      (∀ i j, |((realCharacterActualZeros χ).zeros i).im| ≤ T →
        |((realCharacterActualZeros χ).zeros j).im| ≤ T →
        1 - c / H ≤ ((realCharacterActualZeros χ).zeros i).re →
        1 - c / H ≤ ((realCharacterActualZeros χ).zeros j).re → i = j) := by
  obtain ⟨C, hC, hshift⟩ := exists_full_height_real_shifted_bound
  obtain ⟨R, hR, hreal⟩ := exists_real_zero_sum_upper
  let D := R + C + 4
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1 / (2000 * D), by positivity, ?_⟩
  intro χ T hT
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 2) + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := by linarith
  have hqH : Real.log χ.modulus ≤ H := by dsimp [H]; linarith
  let δ := 1 / (100 * D * H)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hDH : 1 ≤ D * H := by
    have hmul := mul_le_mul_of_nonneg_left hH hD.le
    dsimp [D] at *
    linarith
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hmass : δ * (D * H) = 1 / 100 := by dsimp [δ]; field_simp
  have hRE : (1 / 2) * Real.log χ.modulus + R ≤ D * H := by
    have hrh := mul_le_mul_of_nonneg_left hH hR.le
    have hch := mul_nonneg hC.le hHp.le
    dsimp [D]
    nlinarith
  have hCE : C * H ≤ D * H := by dsimp [D]; nlinarith [mul_nonneg hR.le hHp.le]
  have hRb : δ * ((1 / 2) * Real.log χ.modulus + R) ≤ 1 / 10 := by
    have hh := mul_le_mul_of_nonneg_left hRE hδ.le
    rw [hmass] at hh
    linarith
  have hCb : δ * (C * H) ≤ 1 / 10 := by
    have hh := mul_le_mul_of_nonneg_left hCE hδ.le
    rw [hmass] at hh
    linarith
  have hr : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤
      1 / δ + ((1 / 2) * Real.log χ.modulus + R) := by
    simpa only [add_sub_cancel_left, add_assoc] using
      hreal χ (1 + δ) (by linarith) (by linarith)
  have hs : ∀ t : ℝ, |t| ≤ T →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + C * H := by
    intro t htT
    have hh := hshift χ (1 + δ) t (by linarith) (by linarith)
    simp only [add_sub_cancel_left] at hh
    have hlog : Real.log (|t| + 2) ≤ Real.log (T + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hm := mul_le_mul_of_nonneg_left hlog hC.le
    dsimp [H]
    linarith
  obtain ⟨ha, hu⟩ := near_real_zeros_real_unique_height χ δ
    ((1 / 2) * Real.log χ.modulus + R) (C * H) T hδ hδ1 hRb hCb hr hs
  have hcut : (1 / (2000 * D)) / H = δ / 20 := by
    dsimp [δ]
    field_simp
    ring
  constructor
  · intro i hi hnear
    apply ha i _ hi
    change 1 - (1 / (2000 * D)) / H ≤ _ at hnear
    rwa [hcut] at hnear
  · intro i j hi hj hnear hnear'
    apply hu i j _ _ hi hj
    · change 1 - (1 / (2000 * D)) / H ≤ _ at hnear
      rwa [hcut] at hnear
    · change 1 - (1 / (2000 * D)) / H ≤ _ at hnear'
      rwa [hcut] at hnear'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_NonquadraticZeroRegion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional logarithmic zero-free region for nonquadratic characters -/

namespace Ostmann

open Complex

theorem exists_nonquadratic_zero_free_region : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : PrimitiveComplexCharacter), χ.character ^ 2 ≠ 1 → ∀ i : ℕ,
      c / (Real.log χ.modulus + Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) + 1) ≤
        1 - ((actualCharacterZeros χ).zeros i).re := by
  obtain ⟨C, hC, hb⟩ := exists_nonquadratic_zero_sum_bound
  refine ⟨1 / (2000 * (C + 1)), by positivity, ?_⟩
  intro χ hχ i
  let ρ := (actualCharacterZeros χ).zeros i
  let H := Real.log χ.modulus + Real.log (|ρ.im| + 2) + 1
  let δ := 1 / (100 * (C + 1) * H)
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have ht : 0 ≤ Real.log (|ρ.im| + 2) := Real.log_nonneg (by linarith [abs_nonneg ρ.im])
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hbudget : δ * (C * H) ≤ 1 / 100 := by
    dsimp [δ]
    have he : (1 / (100 * (C + 1) * H)) * (C * H) = C / (100 * (C + 1)) := by
      field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hcut : (1 / (2000 * (C + 1))) / H = δ / 20 := by
    dsimp [δ]
    field_simp
    ring
  rw [hcut]
  by_contra hnot
  have hnear : 1 - δ / 20 ≤ ρ.re := by dsimp [ρ]; linarith [lt_of_not_ge hnot]
  let a := 1 + δ - ρ.re
  let s : ℂ := ((1 + δ : ℝ) : ℂ) + (ρ.im : ℂ) * I
  have ha : δ ≤ a := by dsimp [a]; linarith [((actualCharacterZeros χ).in_strip i).2]
  have ha' : a ≤ (21 / 20) * δ := by dsimp [a]; linarith
  have hterm := character_real_zero_term_le χ s (by dsimp [s]; simp; linarith)
    (by dsimp [s]; simp; linarith) i
  have hdiff : s - (actualCharacterZeros χ).zeros i = (a : ℂ) := by
    apply Complex.ext <;> simp [s, a, ρ]
  rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re] at hterm
  have hupper := hb χ hχ (1 + δ) ρ.im (by linarith) (by linarith)
  have hup : 4 * characterRealZeroSum χ s ≤ 3 / δ + C * H := by
    simpa only [add_sub_cancel_left] using hupper
  have hp := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left hterm (by norm_num : (0 : ℝ) ≤ 4)).trans hup) hδ.le
  have he : δ * (3 / δ + C * H) = 3 + δ * (C * H) := by field_simp
  rw [he] at hp
  have hm := real_zero_shifted_mass δ a hδ ha ha'
  simp only [div_eq_mul_inv] at hm
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualRealZeroIndices
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Locating every actual real zero in the faithful multiplicity enumeration -/

namespace Ostmann

open Complex

theorem PrimitiveRealZero.has_actual_index (e : PrimitiveRealZero) :
    ∃ i, (realCharacterActualZeros e.asRealCharacter).zeros i = (e.beta : ℂ) := by
  apply actualCharacterZeros_complete e.asRealCharacter.asComplex
  exact ⟨e.beta_pos, e.beta_lt_one, e.zero⟩

theorem PrimitiveRealZero.kernel_le_zero_sum (e : PrimitiveRealZero) (σ : ℝ)
    (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    1 / (σ - e.beta) ≤ shiftedRealCharacterZeroSum e.asRealCharacter (σ : ℂ) := by
  obtain ⟨i, hi⟩ := e.has_actual_index
  have hh := shifted_real_zero_term_le e.asRealCharacter (σ : ℂ) hσ hσ2 i
  rw [hi, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re] at hh
  simpa only [one_div] using hh

theorem PrimitiveRealZero.eq_of_character_beta {e f : PrimitiveRealZero}
    (hχ : e.asRealCharacter = f.asRealCharacter) (hβ : e.beta = f.beta) : e = f := by
  cases e
  cases f
  cases hχ
  cases hβ
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedLogDerivativeSeparated
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The completed logarithmic derivative away from the actual zeros -/

namespace Ostmann

open Complex Filter
open scoped BigOperators Topology

theorem completed_logDeriv_difference_bound (χ : PrimitiveComplexCharacter)
    (s w : ℂ) (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hw : w.re = 2) (hshift : ‖w - s‖ ≤ A)
    (hsep : ∀ i : ℕ, δ ≤ ‖s - (actualCharacterZeros χ).zeros i‖) :
    ‖logDeriv χ.completed s - logDeriv χ.completed w‖ ≤
      A * (1 + A / δ) * characterRealZeroSum χ w := by
  have hsne : χ.completed s ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := actualCharacterZeros_complete χ s ((χ.completed_zero_iff s).mp hz)
    have hh := hsep i
    rw [hi, sub_self, norm_zero] at hh
    linarith
  have hwne : χ.completed w ≠ 0 := χ.completed_ne_zero_right w (by linarith)
  have hsum := character_real_zero_summable χ w (by linarith) (by linarith)
  have hbound (n : ℕ) :
      ‖completedZeroPartialFraction χ ((n : ℝ) + 1) s -
        completedZeroPartialFraction χ ((n : ℝ) + 1) w‖ ≤
          A * (1 + A / δ) * characterRealZeroSum χ w := by
    rw [completedZeroPartialFraction_index_sum χ (faithfulCharacterZeroEquiv χ),
      completedZeroPartialFraction_index_sum χ (faithfulCharacterZeroEquiv χ),
      ← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i ∈ (actualCharacterZeros χ).diskIndices ((n : ℝ) + 1),
          (A * (1 + A / δ)) * ((w - (actualCharacterZeros χ).zeros i)⁻¹).re := by
        apply Finset.sum_le_sum
        intro i _
        exact zero_resolvent_difference_bound s w _ A δ hA hδ (hsep i) hshift (by
          change 1 ≤ w.re - ((actualCharacterZeros χ).zeros i).re
          rw [hw]
          linarith [((actualCharacterZeros χ).in_strip i).2])
      _ ≤ A * (1 + A / δ) * characterRealZeroSum χ w := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsum.sum_le_tsum _ (fun i _ => by
          rw [realZeroKernel_complex_sub]
          exact realZeroKernel_nonneg (by linarith [((actualCharacterZeros χ).in_strip i).2]))
  have hlim := (completed_partial_fraction_difference_tendsto χ w s hwne hsne).norm
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaHalfStripBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Gamma bound on the positive strip used for contour displacement -/

namespace Ostmann

open Complex

theorem gammaReal_logarithmic_half_strip : ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ,
    1 / 2 ≤ s.re → s.re ≤ 3 →
      ‖logDeriv Complex.Gammaℝ s‖ ≤ B * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC, hb⟩ := Complex.exists_norm_digamma_div_two_le_log
    (a := 1 / 2) (b := 3) (by norm_num)
  let D := |Real.log Real.pi| / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C + D + 1, by positivity, ?_⟩
  intro s hs hs'
  have hregular : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hh := congrArg Complex.re hn
    simp only [div_ofNat_re, neg_re, natCast_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hlog : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlogpos : 0 < Real.log (|s.im| + 2) := hlog2.trans_le hlog
  have hDlog : |Real.log Real.pi| ≤ D * Real.log (|s.im| + 2) := by
    have hm := mul_le_mul_of_nonneg_left hlog hD
    dsimp [D] at hm
    rwa [div_mul_cancel₀ _ hlog2.ne'] at hm
  have hpi : ‖Complex.log (Real.pi : ℂ)‖ = |Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
  rw [gammaReal_logDeriv s hregular, norm_div, norm_ofNat]
  have hh := (norm_sub_le (Complex.digamma (s / 2)) (Complex.log (Real.pi : ℂ))).trans
    (add_le_add (hb s hs hs') (le_refl _))
  rw [hpi] at hh
  change ‖Complex.digamma (s / 2) - Complex.log (Real.pi : ℂ)‖ / 2 ≤ _
  nlinarith

theorem characterGamma_logarithmic_half_strip : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) s‖ ≤
        B * Real.log (|s.im| + 2) := by
  obtain ⟨B, hB, hb⟩ := gammaReal_logarithmic_half_strip
  refine ⟨B, hB, ?_⟩
  intro χ s hs hs'
  by_cases he : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    exact hb s hs (by linarith)
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := s)
      (gammaReal_analyticAt_pos (s + 1) (by simp; linarith)).differentiableAt
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hb (s + 1) (by simp; linarith) (by simp; linarith)

theorem characterGammaInverse_logarithmic_half_strip : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖logDeriv χ.gammaInverse s‖ ≤ B * Real.log (|s.im| + 2) := by
  obtain ⟨B, hB, hb⟩ := characterGamma_logarithmic_half_strip
  refine ⟨B, hB, ?_⟩
  intro χ s hs hs2
  have he := logDeriv_fun_zpow (χ.gammaFactor_differentiableAt_pos s (by linarith)) (-1 : ℤ)
  have hi : logDeriv χ.gammaInverse s = -logDeriv (DirichletCharacter.gammaFactor χ.character) s := by
    rw [show χ.gammaInverse = (fun x => (DirichletCharacter.gammaFactor χ.character x)⁻¹) from rfl]
    simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one, neg_one_mul] using he
  rw [hi, norm_neg]
  exact hb χ s hs hs2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLogarithmicSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A conductor-uniform logarithmic derivative estimate

The actual Hadamard difference and the positive reference zero sum control
L'/L throughout the positive half-strip, with the explicit cost of the
separation from all actual zeros.
-/

namespace Ostmann

open Complex

theorem character_logDeriv_logarithmic_separation : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ) (δ : ℝ),
      1 / 2 ≤ s.re → s.re ≤ 2 → 0 < δ →
      (∀ i : ℕ, δ ≤ ‖s - (actualCharacterZeros χ).zeros i‖) →
      ‖logDeriv χ.L s‖ ≤
        C * (Real.log χ.modulus + Real.log (|s.im| + 2) + 1) * (1 + δ⁻¹) := by
  obtain ⟨C0, hC0, hright⟩ := character_logDeriv_right_uniform_bound
  obtain ⟨B0, hB0, hzeros⟩ := exists_character_zero_sum_log_bound
  obtain ⟨B1, hB1, hgamma⟩ := characterGamma_logarithmic_half_strip
  obtain ⟨B2, hB2, hinv⟩ := characterGammaInverse_logarithmic_half_strip
  let D := C0 + B0 + B1 + B2 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨5 * D, by positivity, ?_⟩
  intro χ s δ hs hs2 hδ hsep
  let w : ℂ := 2 + (s.im : ℂ) * I
  have hw : w.re = 2 := by simp [w]
  have hwi : w.im = s.im := by simp [w]
  have hshift : ‖w - s‖ ≤ 2 := by
    have he : w - s = ((2 - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [w]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hdiff := completed_logDeriv_difference_bound χ s w 2 δ
    (by norm_num) hδ hw hshift hsep
  have hcne : χ.completed s ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := actualCharacterZeros_complete χ s ((χ.completed_zero_iff s).mp hz)
    have hh := hsep i
    rw [hi, sub_self, norm_zero] at hh
    linarith
  have hL : χ.L s ≠ 0 := by
    rw [χ.L_eq_completed_mul_all]
    exact mul_ne_zero hcne (χ.gammaInverse_ne_zero s (by linarith))
  have hcw := χ.completed_logDeriv_eq_add w (by linarith)
  have hls := χ.logDeriv_L_eq_completed_add s hL
  have hzsum := hzeros χ w (by linarith) (by linarith)
  have hr := hright χ w hw.ge
  have hgw := hgamma χ w (by linarith) (by linarith)
  have hgs := hinv χ s hs hs2
  rw [hwi] at hzsum hgw
  have hz : characterRealZeroSum χ w ≤
      C0 + (1 / 2) * Real.log χ.modulus + B0 * Real.log (|s.im| + 2) := by
    have hh := (Complex.re_le_norm (logDeriv χ.L w)).trans hr
    linarith
  have hbound : ‖logDeriv χ.L s‖ ≤
      (2 * (1 + 2 / δ)) *
        (C0 + (1 / 2) * Real.log χ.modulus + B0 * Real.log (|s.im| + 2)) +
          C0 + (B1 + B2) * Real.log (|s.im| + 2) := by
    have hc := norm_le_norm_sub_add (logDeriv χ.completed s) (logDeriv χ.completed w)
    have hwbound : ‖logDeriv χ.completed w‖ ≤ C0 + B1 * Real.log (|s.im| + 2) := by
      rw [hcw]
      exact (norm_add_le _ _).trans (add_le_add hr hgw)
    have hsbound : ‖logDeriv χ.L s‖ ≤ ‖logDeriv χ.completed s‖ +
        ‖logDeriv χ.gammaInverse s‖ := by rw [hls]; exact norm_add_le _ _
    have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left hz (by positivity))
    linarith
  let H := Real.log (|s.im| + 2)
  let L := Real.log χ.modulus + H + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hH : 0 ≤ H := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hD0 : C0 ≤ D := by dsimp [D]; linarith
  have hDhalf : 1 / 2 ≤ D := by dsimp [D]; linarith
  have hDB0 : B0 ≤ D := by dsimp [D]; linarith
  have hDB12 : B1 + B2 ≤ D := by dsimp [D]; linarith
  have hbase : C0 + (1 / 2) * Real.log χ.modulus + B0 * H ≤ D * L := by
    have h1 := mul_le_mul_of_nonneg_right hDhalf hq
    have h2 := mul_le_mul_of_nonneg_right hDB0 hH
    dsimp [L]
    nlinarith
  have hrest : C0 + (B1 + B2) * H ≤ D * L := by
    have hh := mul_le_mul_of_nonneg_right hDB12 hH
    have hnon := mul_nonneg hD.le hq
    dsimp [L]
    nlinarith
  have hcost : 2 * (1 + 2 / δ) ≤ 4 * (1 + δ⁻¹) := by
    simp only [div_eq_mul_inv]
    linarith
  have hrest' : D * L ≤ D * L * (1 + δ⁻¹) := by
    have hh := mul_nonneg (mul_nonneg hD.le hLpos.le) (inv_nonneg.mpr hδ.le)
    nlinarith
  calc
    _ ≤ (2 * (1 + 2 / δ)) * (C0 + (1 / 2) * Real.log χ.modulus + B0 * H) +
        (C0 + (B1 + B2) * H) := by simpa only [H, add_assoc] using hbound
    _ ≤ (2 * (1 + 2 / δ)) * (D * L) + D * L :=
      add_le_add (mul_le_mul_of_nonneg_left hbase (by positivity)) hrest
    _ ≤ (4 * (1 + δ⁻¹)) * (D * L) + D * L * (1 + δ⁻¹) :=
      add_le_add (mul_le_mul_of_nonneg_right hcost (by positivity)) hrest'
    _ = _ := by dsimp [L, H]; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealCharacterPairZeroBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One zeta pole controls the two distinct real-character zero sums -/

namespace Ostmann

open Complex

theorem exists_distinct_real_zero_sum_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ ψ : PrimitiveRealCharacter), χ ≠ ψ → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      shiftedRealCharacterZeroSum χ (σ : ℂ) + shiftedRealCharacterZeroSum ψ (σ : ℂ) ≤
        1 / (σ - 1) + 4 * (Real.log χ.modulus + Real.log ψ.modulus) + C := by
  obtain ⟨B, hB, hb⟩ := exists_nonprincipal_logDeriv_real_lower
  obtain ⟨G, hG, hg⟩ := exists_low_height_zero_sum_error
  obtain ⟨R, hR, hr⟩ := exists_vonMangoldt_series_bound
  refine ⟨R + B * Real.log 2 + 2 * G, by positivity, ?_⟩
  intro χ ψ hne σ hσ hσ2
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let : NeZero ψ.modulus := ⟨ψ.positive.ne'⟩
  let N := χ.modulus * ψ.modulus
  let : NeZero N := ⟨Nat.mul_ne_zero χ.positive.ne' ψ.positive.ne'⟩
  have hχN : χ.modulus ∣ N := Nat.dvd_mul_right _ _
  have hψN : ψ.modulus ∣ N := Nat.dvd_mul_left _ _
  let a := DirichletCharacter.changeLevel hχN χ.complexCharacter
  let b := DirichletCharacter.changeLevel hψN ψ.complexCharacter
  have hab : a * b ≠ 1 := distinct_real_lifts_product_nonprincipal χ ψ hne hχN hψN
  have hp := real_character_pair_logDeriv_le a b (χ.lift_inverse_eq hχN)
    (ψ.lift_inverse_eq hψN) σ hσ
  have hprod := hb N (a * b) hab (σ : ℂ) hσ hσ2
  simp only [Complex.ofReal_im, abs_zero, zero_add] at hprod
  have hvr := (Complex.re_le_norm _).trans (hr σ hσ hσ2)
  have hχdiff := logDeriv_changeLevel_bound χ.complexCharacter hχN (σ : ℂ) hσ
  have hψdiff := logDeriv_changeLevel_bound ψ.complexCharacter hψN (σ : ℂ) hσ
  have hχre := Complex.re_le_norm (-(logDeriv (DirichletCharacter.LFunction a) (σ : ℂ) - logDeriv χ.L (σ : ℂ)))
  have hψre := Complex.re_le_norm (-(logDeriv (DirichletCharacter.LFunction b) (σ : ℂ) - logDeriv ψ.L (σ : ℂ)))
  simp only [Complex.neg_re, Complex.sub_re, norm_neg] at hχre hψre
  have hx := hg χ (σ : ℂ) hσ hσ2 (by simp)
  have hy := hg ψ (σ : ℂ) hσ hσ2 (by simp)
  have hlog : Real.log N = Real.log χ.modulus + Real.log ψ.modulus := by
    rw [show (N : ℝ) = (χ.modulus : ℝ) * ψ.modulus by simp [N], Real.log_mul]
    · exact_mod_cast χ.positive.ne'
    · exact_mod_cast ψ.positive.ne'
  change ‖logDeriv (DirichletCharacter.LFunction a) (σ : ℂ) - logDeriv χ.L (σ : ℂ)‖ ≤ _ at hχdiff
  change ‖logDeriv (DirichletCharacter.LFunction b) (σ : ℂ) - logDeriv ψ.L (σ : ℂ)‖ ≤ _ at hψdiff
  rw [hlog] at hχdiff hψdiff hprod
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealZeroPairExclusion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real Page exclusion from one-pole bounds -/

namespace Ostmann

open Complex

theorem real_zero_pair_exclusion (e f : PrimitiveRealZero) (δ R S : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : δ * R ≤ 1 / 10) (hS : δ * S ≤ 1 / 10)
    (he : 1 - δ / 20 ≤ e.beta) (hf : 1 - δ / 20 ≤ f.beta)
    (hsingle : shiftedRealCharacterZeroSum e.asRealCharacter ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + R)
    (hpair : e.asRealCharacter ≠ f.asRealCharacter →
      shiftedRealCharacterZeroSum e.asRealCharacter ((1 + δ : ℝ) : ℂ) +
        shiftedRealCharacterZeroSum f.asRealCharacter ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + S) : e = f := by
  have hme := near_real_zero_inverse_mass δ e.beta hδ e.beta_lt_one he
  have hmf := near_real_zero_inverse_mass δ f.beta hδ f.beta_lt_one hf
  have heterm := e.kernel_le_zero_sum (1 + δ) (by linarith) (by linarith)
  have hfterm := f.kernel_le_zero_sum (1 + δ) (by linarith) (by linarith)
  have hcancel (C : ℝ) : δ * (1 / δ + C) = 1 + δ * C := by field_simp
  by_cases hχ : e.asRealCharacter = f.asRealCharacter
  · apply PrimitiveRealZero.eq_of_character_beta hχ
    by_contra hβ
    obtain ⟨i, hi⟩ := e.has_actual_index
    obtain ⟨j, hj⟩ := f.has_actual_index
    rw [← hχ] at hj
    have hij : i ≠ j := by
      intro hij
      apply hβ
      apply Complex.ofReal_injective
      rw [← hi, ← hj, hij]
    have hh := shifted_real_zero_pair_le e.asRealCharacter ((1 + δ : ℝ) : ℂ)
      (by simp; linarith) (by simp; linarith) i j hij
    rw [hi, hj, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
      ← Complex.ofReal_inv, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re] at hh
    have hp := mul_le_mul_of_nonneg_left (hh.trans hsingle) hδ.le
    rw [hcancel] at hp
    simp only [one_div] at hme hmf
    nlinarith
  · have hh := (add_le_add heterm hfterm).trans (hpair hχ)
    have hp := mul_le_mul_of_nonneg_left hh hδ.le
    rw [hcancel] at hp
    nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualPageUniqueness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Page uniqueness for the actual primitive real zeros

The one-pole bound for two distinct characters and positivity of the actual
zero sums give an absolute Landau–Page constant. No uniqueness input is used.
-/

namespace Ostmann

open Complex

theorem exists_actual_page_uniqueness : ∃ κ : ℝ, 0 < κ ∧
    ∀ Q : ℕ, 2 ≤ Q → ∀ e f : PrimitiveRealZero,
      e.modulus ≤ Q → f.modulus ≤ Q →
      1 - κ / Real.log (4 * (Q : ℝ)) ≤ e.beta →
      1 - κ / Real.log (4 * (Q : ℝ)) ≤ f.beta → e = f := by
  obtain ⟨R, hR, hsingle⟩ := exists_real_zero_sum_upper
  obtain ⟨S, hS, hpair⟩ := exists_distinct_real_zero_sum_bound
  let D : ℝ := R + S + 10
  have hD : 0 < D := by dsimp [D]; positivity
  let κ : ℝ := 1 / (2000 * D)
  refine ⟨κ, by dsimp [κ]; positivity, ?_⟩
  intro Q hQ e f he hf hbe hbf
  let H : ℝ := Real.log (4 * (Q : ℝ))
  have hQr : 2 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hH : 1 ≤ H := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < 4 * (Q : ℝ))).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hHpos : 0 < H := by linarith
  have heLog : Real.log e.modulus ≤ H := by
    apply Real.log_le_log (by exact_mod_cast e.positive)
    have hh : (e.modulus : ℝ) ≤ Q := by exact_mod_cast he
    linarith
  have hfLog : Real.log f.modulus ≤ H := by
    apply Real.log_le_log (by exact_mod_cast f.positive)
    have hh : (f.modulus : ℝ) ≤ Q := by exact_mod_cast hf
    linarith
  let δ : ℝ := 1 / (100 * D * H)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one (by positivity : 0 < 100 * D * H)).mpr
    have hh := mul_le_mul_of_nonneg_left hH hD.le
    dsimp [D] at *
    nlinarith
  have hRerr : δ * ((1 / 2) * Real.log e.modulus + R) ≤ 1 / 10 := by
    rw [show δ * ((1 / 2) * Real.log e.modulus + R) =
      ((1 / 2) * Real.log e.modulus + R) / (100 * D * H) by dsimp [δ]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 100 * D * H)).mpr
    have hrh := mul_le_mul_of_nonneg_left hH hR.le
    have hsh := mul_nonneg hS.le hHpos.le
    dsimp [D]
    nlinarith
  have hSerr : δ * (4 * (Real.log e.modulus + Real.log f.modulus) + S) ≤ 1 / 10 := by
    rw [show δ * (4 * (Real.log e.modulus + Real.log f.modulus) + S) =
      (4 * (Real.log e.modulus + Real.log f.modulus) + S) / (100 * D * H) by
        dsimp [δ]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 100 * D * H)).mpr
    have hsh := mul_le_mul_of_nonneg_left hH hS.le
    have hrh := mul_nonneg hR.le hHpos.le
    dsimp [D]
    nlinarith
  have hgap : κ / H = δ / 20 := by
    dsimp [κ, δ]
    field_simp
    ring
  apply real_zero_pair_exclusion e f δ
    ((1 / 2) * Real.log e.modulus + R)
    (4 * (Real.log e.modulus + Real.log f.modulus) + S)
    hδ hδ1 hRerr hSerr
  · change 1 - κ / H ≤ e.beta at hbe
    rwa [hgap] at hbe
  · change 1 - κ / H ≤ f.beta at hbf
    rwa [hgap] at hbf
  · simpa only [add_sub_cancel_left, add_assoc, PrimitiveRealZero.asRealCharacter] using
      hsingle e.asRealCharacter (1 + δ) (by linarith) (by linarith)
  · intro hne
    simpa only [add_sub_cancel_left, add_assoc, PrimitiveRealZero.asRealCharacter] using
      hpair e.asRealCharacter f.asRealCharacter hne (1 + δ) (by linarith) (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualLocalZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical local exceptional zeros

An actual near-one zero is selected when one exists. Its uniqueness and
completeness follow from the proved Page theorem, not an analytic input.
-/

namespace Ostmann

noncomputable def actualPageConstant : ℝ := Classical.choose exists_actual_page_uniqueness

theorem actualPageConstant_pos : 0 < actualPageConstant :=
  (Classical.choose_spec exists_actual_page_uniqueness).1

theorem actualPage_unique (Q : ℕ) (hQ : 2 ≤ Q) (e f : PrimitiveRealZero)
    (he : e.modulus ≤ Q) (hf : f.modulus ≤ Q)
    (hbe : 1 - actualPageConstant / Real.log (4 * (Q : ℝ)) ≤ e.beta)
    (hbf : 1 - actualPageConstant / Real.log (4 * (Q : ℝ)) ≤ f.beta) : e = f :=
  (Classical.choose_spec exists_actual_page_uniqueness).2 Q hQ e f he hf hbe hbf

noncomputable def actualLocalZero (q : ℕ) : Option PrimitiveRealZero := by
  classical
  exact if h : ∃ e : PrimitiveRealZero, e.modulus ∣ q ∧
      1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤ e.beta then
    some (Classical.choose h) else none

theorem actualLocalZero_spec (q : ℕ) (e : PrimitiveRealZero)
    (he : actualLocalZero q = some e) :
    e.modulus ∣ q ∧ 1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤ e.beta := by
  classical
  unfold actualLocalZero at he
  split at he
  next h =>
    have hh := Classical.choose_spec h
    have heq : Classical.choose h = e := Option.some.inj he
    rwa [heq] at hh
  next => simp at he

theorem actualLocalZero_complete (q : ℕ) (hq : 1 ≤ q) (e : PrimitiveRealZero)
    (he : e.modulus ∣ q)
    (hbe : 1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤ e.beta) :
    actualLocalZero q = some e := by
  classical
  have hq2 : 2 ≤ q := by
    by_contra hn
    have hq1 : q = 1 := by omega
    have he1 : e.modulus = 1 := Nat.eq_one_of_dvd_one (hq1 ▸ he)
    exact e.modulus_ne_one he1
  unfold actualLocalZero
  rw [dite_eq_left ⟨e, he, hbe⟩]
  apply congrArg some
  have hh := Classical.choose_spec (show ∃ f : PrimitiveRealZero, f.modulus ∣ q ∧
      1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤ f.beta from ⟨e, he, hbe⟩)
  exact actualPage_unique q hq2 _ e (Nat.le_of_dvd (by omega) hh.1)
    (Nat.le_of_dvd (by omega) he) hh.2 hbe

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterNearZeroUnique
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unique simple real zero that can enter a character's Riesz rectangle -/

namespace Ostmann

theorem character_near_zero_unique : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : PrimitiveComplexCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 2) + 1
      (∀ i : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
          χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0) ∧
      (∀ i j : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T →
        |((actualCharacterZeros χ).zeros j).im| ≤ T →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros j).re → i = j) := by
  obtain ⟨cn, hcn, hn⟩ := exists_nonquadratic_zero_free_region
  obtain ⟨cr, hcr, hr⟩ := exists_full_height_real_region
  let c := min (cn / 2) (cr / 2)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcnc : c < cn := by
    have hh := min_le_left (cn / 2) (cr / 2)
    dsimp [c]
    linarith
  have hcrc : c ≤ cr := by
    have hh := min_le_right (cn / 2) (cr / 2)
    dsimp [c]
    linarith
  refine ⟨c, hc, ?_⟩
  intro χ T hT
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 2) + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have hHp : 0 < H := by
    have ht : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    dsimp [H]
    linarith
  by_cases hsq : χ.character ^ 2 = 1
  · have hreal := hr (χ.asReal hsq) T hT
    dsimp only at hreal
    simp only [realCharacterActualZeros] at hreal
    rw [χ.asReal_asComplex hsq] at hreal
    have hcut : c / H ≤ cr / H := div_le_div_of_nonneg_right hcrc hHp.le
    constructor
    · intro i hi hnear
      refine ⟨hsq, ?_⟩
      apply hreal.1 i
      · exact hi
      · change 1 - cr / H ≤ _
        linarith
    · intro i j hi hj hni hnj
      apply hreal.2 i j
      · exact hi
      · exact hj
      · change 1 - cr / H ≤ _
        linarith
      · change 1 - cr / H ≤ _
        linarith
  · have hnone (i : ℕ) (hi : |((actualCharacterZeros χ).zeros i).im| ≤ T)
        (hnear : 1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re) : False := by
      let V := Real.log χ.modulus + Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) + 1
      have hVp : 0 < V := by
        have ht : 0 ≤ Real.log (|((actualCharacterZeros χ).zeros i).im| + 2) :=
          Real.log_nonneg (by linarith [abs_nonneg ((actualCharacterZeros χ).zeros i).im])
        dsimp [V]
        linarith
      have hVH : V ≤ H := by
        have hh := Real.log_le_log (by positivity : 0 < |((actualCharacterZeros χ).zeros i).im| + 2)
          (show |((actualCharacterZeros χ).zeros i).im| + 2 ≤ T + 2 by linarith)
        dsimp [V, H]
        linarith
      have hm : cn / H ≤ cn / V := div_le_div_of_nonneg_left hcn.le hVp hVH
      have hs : c / H < cn / H := (div_lt_div_iff_of_pos_right hHp).mpr hcnc
      have hz := hn χ hsq i
      change cn / V ≤ _ at hz
      linarith
    exact ⟨fun i hi hnear => (hnone i hi hnear).elim,
      fun i _ hi _ hnear _ => (hnone i hi hnear).elim⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterNearZeroSimple
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique near-one indices have analytic multiplicity one -/

namespace Ostmann

open scoped Classical

theorem actual_character_zero_simple (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hunique : ∀ j : ℕ, (actualCharacterZeros χ).zeros j = (actualCharacterZeros χ).zeros i → j = i) :
    analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1 := by
  let Z := actualCharacterZeros χ
  let z := Z.zeros i
  let T := |z.im|
  have hz : z ∈ criticalZerosUpTo χ T := by
    apply mem_criticalZerosUpTo.mpr
    exact ⟨⟨(Z.in_strip i).1, (Z.in_strip i).2, Z.actual_zero i⟩, le_rfl⟩
  have hf := characterZeroEnumeration_fiber_card χ (faithfulCharacterZeroEquiv χ) T z hz
  change ((Z.heightIndices T).filter (fun j => Z.zeros j = z)).card = analyticOrderNatAt χ.L z at hf
  have hsingle : (Z.heightIndices T).filter (fun j => Z.zeros j = z) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hj
      exact hunique j hj.2
    · intro hj
      subst j
      exact ⟨(Z.mem_heightIndices T i).mpr le_rfl, rfl⟩
  rw [hsingle, Finset.card_singleton] at hf
  exact hf.symm

theorem character_near_zero_simple : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : PrimitiveComplexCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 2) + 1
      (∀ i : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
          χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
            analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1) ∧
      (∀ i j : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T →
        |((actualCharacterZeros χ).zeros j).im| ≤ T →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros j).re → i = j) := by
  obtain ⟨c, hc, hdata⟩ := character_near_zero_unique
  refine ⟨c, hc, ?_⟩
  intro χ T hT
  obtain ⟨hreal, huniq⟩ := hdata χ T hT
  refine ⟨?_, huniq⟩
  intro i hi hnear
  obtain ⟨hsq, him⟩ := hreal i hi hnear
  refine ⟨hsq, him, actual_character_zero_simple χ i ?_⟩
  intro j hj
  apply huniq j i _ hi _ hnear
  · simpa only [hj] using hi
  · simpa only [hj] using hnear

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszVerticalWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The absolutely convergent Riesz contour weight -/

namespace Ostmann

open Complex MeasureTheory

theorem characterMangoldt_riesz_term_norm (χ : PrimitiveComplexCharacter)
    (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term (characterMangoldtCoefficient χ) (rieszMellinLine σ t) n‖ =
      ‖LSeries.term (characterMangoldtCoefficient χ) (σ : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

theorem characterMangoldt_riesz_term_continuous (χ : PrimitiveComplexCharacter)
    (σ : ℝ) (n : ℕ) :
    Continuous (fun t => LSeries.term (characterMangoldtCoefficient χ) (rieszMellinLine σ t) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    exact continuous_const.div ((rieszMellinLine_continuous σ).const_cpow
      (.inl (by exact_mod_cast hn))) (fun _ => Complex.cpow_ne_zero_iff.mpr
        (.inl (by exact_mod_cast hn)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszContourRectangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Riesz contour displacement when the rectangle is zero-free -/

namespace Ostmann

open Complex Set
open scoped Interval

theorem rieszContour_rectangle_zero (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hne : ∀ s ∈ uIcc a b ×ℂ uIcc c d, χ.L s ≠ 0) :
    rectangleBoundaryIntegral (fun s => -logDeriv χ.L s * rieszContourWeight X s)
      a b c d = 0 := by
  apply rectangleBoundaryIntegral_eq_zero
  intro s hs
  have hspos : 0 < s.re := ha.trans_le ((uIcc_of_le hab) ▸ hs.1).1
  have hl : AnalyticAt ℂ (fun s => -logDeriv χ.L s) s := by
    exact ((χ.L_analytic s).deriv.div (χ.L_analytic s) (hne s hs)).neg
  exact hl.mul (rieszContourWeight_analyticAt X hX s hspos)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszSingleZeroRectangle
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual one-zero contribution to a character Riesz rectangle -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Interval

theorem rieszContour_regular_part (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (z : ℂ) (hz : 0 < z.re) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R z ∧
      (fun s => -logDeriv χ.L s * rieszContourWeight X s +
        (analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z / (s - z)) =ᶠ[𝓝[≠] z] R := by
  obtain ⟨g, hg, hgne, hsplit⟩ := χ.logDeriv_local_split z
  let W := rieszContourWeight X
  have hW : AnalyticAt ℂ W z := rieszContourWeight_analyticAt X hX z hz
  have hds := rieszWeight_dslope_analytic X hX z hz z hz
  have hlog : AnalyticAt ℂ (logDeriv g) z := hg.deriv.div hg hgne
  let R : ℂ → ℂ := fun s => -(analyticOrderNatAt χ.L z : ℂ) * dslope W z s - logDeriv g s * W s
  refine ⟨R, (analyticAt_const.mul hds).sub (hlog.mul hW), ?_⟩
  filter_upwards [hsplit, self_mem_nhdsWithin] with s hs hsz
  rw [hs]
  dsimp only [R]
  rw [dslope_of_ne W hsz]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  ring

theorem rieszContour_single_regularization (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (K : Set ℂ) (z : ℂ) (hz : 0 < z.re)
    (hK : ∀ s ∈ K, 0 < s.re) (hzeros : ∀ s ∈ K, χ.L s = 0 → s = z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F K ∧ ∀ s ≠ z,
      F s = -logDeriv χ.L s * rieszContourWeight X s +
        (analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z / (s - z) := by
  classical
  obtain ⟨R, hR, heR⟩ := rieszContour_regular_part χ X hX z hz
  let f : ℂ → ℂ := fun s => -logDeriv χ.L s * rieszContourWeight X s +
    (analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z / (s - z)
  let F : ℂ → ℂ := fun s => if s = z then R z else f s
  refine ⟨F, ?_, fun s hs => by simp [F, hs, f]⟩
  intro s hsK
  by_cases hs : s = z
  · subst s
    apply hR.congr
    have he : ∀ᶠ s in 𝓝 z, s ≠ z → f s = R s := by
      simpa only [mem_compl_iff, mem_singleton_iff, f] using (eventually_nhdsWithin_iff.mp heR)
    filter_upwards [he] with s hs
    by_cases hsz : s = z
    · simp [F, hsz]
    · simpa only [F, ite_eq_right hsz] using (hs hsz).symm
  · have hn : χ.L s ≠ 0 := fun he => hs (hzeros s hsK he)
    have hf : AnalyticAt ℂ f s := by
      apply (((χ.L_analytic s).deriv.div (χ.L_analytic s) hn).neg.mul
        (rieszContourWeight_analyticAt X hX s (hK s hsK))).add
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)
    apply hf.congr
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    simp [F, ht]

theorem rieszContour_single_zero_rectangle (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (a b c d : ℝ) (z : ℂ)
    (ha : 0 < a) (haz : a < z.re) (hzb : z.re < b) (hcz : c < z.im) (hzd : z.im < d)
    (hzeros : ∀ s ∈ uIcc a b ×ℂ uIcc c d, χ.L s = 0 → s = z) :
    rectangleBoundaryIntegral (fun s => -logDeriv χ.L s * rieszContourWeight X s) a b c d =
      -(2 * (Real.pi : ℂ) * I) *
        ((analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z) := by
  let f : ℂ → ℂ := fun s => -logDeriv χ.L s * rieszContourWeight X s
  let v : ℂ := (analyticOrderNatAt χ.L z : ℂ) * rieszContourWeight X z
  let p : ℂ → ℂ := fun s => v * (s - z)⁻¹
  have hpos (s : ℂ) (hs : s ∈ uIcc a b ×ℂ uIcc c d) : 0 < s.re :=
    ha.trans_le ((uIcc_of_le (haz.trans hzb).le) ▸ hs.1).1
  obtain ⟨F, hF, heF⟩ := rieszContour_single_regularization χ X hX
    (uIcc a b ×ℂ uIcc c d) z (ha.trans haz) hpos hzeros
  have hnot (s : ℂ) (hs : s ∈ contourRectangleBoundary a b c d) : s ≠ z :=
    contourBoundary_ne_interior ⟨haz, hzb, hcz, hzd⟩ hs
  have hf : RectangleIntegrable f a b c d := by
    apply rectangleIntegrable_of_continuousOn
    intro s hs
    have hn : χ.L s ≠ 0 := fun he => hnot s hs (hzeros s ⟨hs.1, hs.2.1⟩ he)
    exact ((((χ.L_analytic s).deriv.div (χ.L_analytic s) hn).neg).mul
      (rieszContourWeight_analyticAt X hX s (hpos s ⟨hs.1, hs.2.1⟩))).continuousAt.continuousWithinAt
  have hp : RectangleIntegrable p a b c d :=
    (rectangleIntegrable_sub_inv ⟨haz, hzb, hcz, hzd⟩).const_mul v
  have he : rectangleBoundaryIntegral F a b c d =
      rectangleBoundaryIntegral (fun s => f s + p s) a b c d := by
    apply rectangleBoundaryIntegral_congr
    intro s hs
    simpa only [f, p, v, div_eq_mul_inv] using heF s (hnot s hs)
  have hzero := rectangleBoundaryIntegral_eq_zero hF
  have hpval : rectangleBoundaryIntegral p a b c d = (2 * (Real.pi : ℂ) * I) * v := by
    rw [show p = (fun s => v * (s - z)⁻¹) from rfl, rectangleBoundaryIntegral_const_mul,
      rectangleBoundaryIntegral_sub_inv z a b c d haz hzb hcz hzd]
    ring
  rw [he, rectangleBoundaryIntegral_add hf hp, hpval] at hzero
  change rectangleBoundaryIntegral f a b c d = -(2 * (Real.pi : ℂ) * I) * v
  linear_combination hzero

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterRieszZeroSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unique actual zero contribution selected by a Riesz rectangle -/

namespace Ostmann

open Complex Set
open scoped Interval

noncomputable def characterRieszZeroTerm (χ : PrimitiveComplexCharacter) (X : ℝ)
    (e : Option ℕ) : ℂ :=
  match e with
  | none => 0
  | some i => -rieszContourWeight X ((actualCharacterZeros χ).zeros i)

theorem character_zero_enumerated_of_re_pos (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 0 < s.re) (hz : χ.L s = 0) :
    ∃ i, (actualCharacterZeros χ).zeros i = s := by
  apply actualCharacterZeros_complete
  refine ⟨hs, ?_, hz⟩
  by_contra hn
  exact χ.L_ne_zero_one_le_re s (not_lt.mp hn) hz

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterIndexedRealZero
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual indexed real zero as the canonical Page-zero datum -/

namespace Ostmann

noncomputable def indexedRealZero (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0) :
    PrimitiveRealZero where
  modulus := χ.modulus
  positive := χ.positive
  character := (χ.asReal hsq).character
  primitive := (χ.asReal hsq).primitive
  nontrivial := (χ.asReal hsq).nontrivial
  beta := ((actualCharacterZeros χ).zeros i).re
  beta_pos := ((actualCharacterZeros χ).in_strip i).1
  beta_lt_one := ((actualCharacterZeros χ).in_strip i).2
  zero := by
    change (χ.asReal hsq).asComplex.L (((actualCharacterZeros χ).zeros i).re : ℂ) = 0
    rw [χ.asReal_asComplex hsq]
    have he : (((actualCharacterZeros χ).zeros i).re : ℂ) = (actualCharacterZeros χ).zeros i := by
      apply Complex.ext <;> simp [him]
    rw [he]
    exact (actualCharacterZeros χ).actual_zero i

@[simp] theorem indexedRealZero_modulus (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0) :
    (indexedRealZero χ i hsq him).modulus = χ.modulus := rfl

@[simp] theorem indexedRealZero_beta (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0) :
    (indexedRealZero χ i hsq him).beta = ((actualCharacterZeros χ).zeros i).re := rfl

@[simp] theorem indexedRealZero_character (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0) :
    (indexedRealZero χ i hsq him).asRealCharacter.asComplex = χ := χ.asReal_asComplex hsq

theorem indexedRealZero_canonical (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hsq : χ.character ^ 2 = 1) (him : ((actualCharacterZeros χ).zeros i).im = 0)
    (q : ℕ) (hq : 1 ≤ q) (hdvd : χ.modulus ∣ q)
    (hnear : 1 - actualPageConstant / Real.log (4 * (q : ℝ)) ≤
      ((actualCharacterZeros χ).zeros i).re) :
    actualLocalZero q = some (indexedRealZero χ i hsq him) :=
  actualLocalZero_complete q hq _ hdvd hnear

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterRieszBoundary
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniformly controlled Riesz boundary, including exceptional characters -/

namespace Ostmann

open Complex

theorem character_riesz_boundary_data : ∃ c C : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ c ≤ actualPageConstant / 10 ∧ 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 4) + 1
      (∀ i : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T + 2 →
        1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros i).re →
        χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
          analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1) ∧
      (∀ i j : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T + 2 →
        |((actualCharacterZeros χ).zeros j).im| ≤ T + 2 →
        1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros i).re →
        1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros j).re → i = j) ∧
      ∃ a : ℝ, 1 - 2 * c / H ≤ a ∧ a ≤ 1 - c / H ∧
        ∀ s : ℂ, ((s.re = a ∧ |s.im| ≤ T) ∨
          (a ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| = T)) →
          χ.L s ≠ 0 ∧ ‖logDeriv χ.L s‖ ≤ C * H ^ 2 := by
  obtain ⟨c0, hc0, hnear⟩ := character_near_zero_simple
  obtain ⟨C0, hC0, hbound⟩ := character_logDeriv_logarithmic_separation
  let c := min (c0 / 4) (min (1 / 4) (actualPageConstant / 10))
  have hc : 0 < c := lt_min (by positivity) (lt_min (by norm_num)
    (div_pos actualPageConstant_pos (by norm_num)))
  have hc4 : c ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcp : c ≤ actualPageConstant / 10 := (min_le_right _ _).trans (min_le_right _ _)
  have hcc : 4 * c ≤ c0 := by
    have hh := min_le_left (c0 / 4) (min (1 / 4) (actualPageConstant / 10))
    dsimp [c]
    linarith
  refine ⟨c, C0 * (1 + 2 / c), hc, hc4, hcp, by positivity, ?_⟩
  intro χ T hT
  dsimp only
  let H := Real.log χ.modulus + Real.log (T + 4) + 1
  have hq : 0 ≤ Real.log χ.modulus := Real.log_nonneg (by exact_mod_cast χ.positive)
  have htlog : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hHp : 0 < H := by linarith
  let δ := c / H
  have hδ : 0 < δ := div_pos hc hHp
  have hδ4 : δ ≤ 1 / 4 := calc
    c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
    _ ≤ 1 / 4 := by simpa using hc4
  obtain ⟨hr, hu⟩ := hnear χ (T + 2) (by linarith)
  rw [show T + 2 + 2 = T + 4 by ring] at hr hu
  have hfrac : 4 * c / H ≤ c0 / H := div_le_div_of_nonneg_right hcc hHp.le
  have hr' (i : ℕ) (hi : |((actualCharacterZeros χ).zeros i).im| ≤ T + 2)
      (hn : 1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros i).re) :
      χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
        analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1 := by
    apply hr i hi
    change 1 - c0 / H ≤ _
    linarith
  have hu' (i j : ℕ) (hi : |((actualCharacterZeros χ).zeros i).im| ≤ T + 2)
      (hj : |((actualCharacterZeros χ).zeros j).im| ≤ T + 2)
      (hni : 1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros i).re)
      (hnj : 1 - 4 * c / H ≤ ((actualCharacterZeros χ).zeros j).re) : i = j := by
    apply hu i j hi hj <;> change 1 - c0 / H ≤ _ <;> linarith
  refine ⟨hr', hu', ?_⟩
  obtain ⟨a, ha, ha', hsep⟩ := one_zero_boundary_cut (actualCharacterZeros χ).zeros δ T
    hδ hδ4 hT (fun i hi hn => (hr' i hi (by simpa [δ, mul_div_assoc] using hn)).2.1)
    (fun i j hi hj hni hnj => hu' i j hi hj
      (by simpa [δ, mul_div_assoc] using hni) (by simpa [δ, mul_div_assoc] using hnj))
  refine ⟨a, by simpa [δ, mul_div_assoc] using ha, ha', ?_⟩
  intro s hs
  have hsa : a ≤ s.re := by
    rcases hs with hs | hs
    · exact hs.1.ge
    · exact hs.1
  have hs2 : s.re ≤ 2 := by
    rcases hs with hs | hs
    · rw [hs.1]; linarith
    · exact hs.2.1
  have hst : |s.im| ≤ T := by
    rcases hs with hs | hs
    · exact hs.2
    · exact hs.2.2.le
  have hspos : 1 / 2 ≤ s.re := by linarith
  have hdist := hsep s hs
  have hne : χ.L s ≠ 0 := by
    have hcn : χ.completed s ≠ 0 := by
      intro hz
      obtain ⟨i, hi⟩ := actualCharacterZeros_complete χ s ((χ.completed_zero_iff s).mp hz)
      have hh := hdist i
      rw [hi, sub_self, norm_zero] at hh
      linarith
    rw [χ.L_eq_completed_mul_all]
    exact mul_ne_zero hcn (χ.gammaInverse_ne_zero s (by linarith))
  refine ⟨hne, ?_⟩
  have hb := hbound χ s (δ / 2) hspos hs2 (by positivity) hdist
  have hlogs : Real.log χ.modulus + Real.log (|s.im| + 2) + 1 ≤ H := by
    have hh := Real.log_le_log (by positivity : 0 < |s.im| + 2)
      (show |s.im| + 2 ≤ T + 4 by linarith)
    dsimp [H]
    linarith
  have hinv : (δ / 2)⁻¹ = 2 * H / c := by dsimp [δ]; field_simp
  have hcost : 1 + (δ / 2)⁻¹ ≤ H * (1 + 2 / c) := by
    rw [hinv]
    calc
      1 + 2 * H / c ≤ H + 2 * H / c := add_le_add hH le_rfl
      _ = H * (1 + 2 / c) := by ring
  calc
    _ ≤ C0 * H * (H * (1 + 2 / c)) := hb.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hlogs hC0.le) hcost
        (by positivity) (by positivity))
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszDirichletIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact starting contour for the integrated Chebyshev sum -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

noncomputable def characterRieszMean (χ : PrimitiveComplexCharacter) (X : ℝ) : ℂ :=
  ∑' n : ℕ, characterMangoldtCoefficient χ n * rieszPrimeTest (n / X)

noncomputable def characterRieszVerticalTerm (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (characterMangoldtCoefficient χ) (rieszMellinLine σ t) n *
    rieszVerticalWeight X σ t

theorem characterRieszVerticalTerm_norm (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (n : ℕ) (t : ℝ) :
    ‖characterRieszVerticalTerm χ X σ n t‖ =
      ‖LSeries.term (characterMangoldtCoefficient χ) (σ : ℂ) n‖ *
        ‖rieszVerticalWeight X σ t‖ := by
  rw [characterRieszVerticalTerm, norm_mul, characterMangoldt_riesz_term_norm]

theorem characterRieszVerticalTerm_integrable (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) (n : ℕ) :
    Integrable (characterRieszVerticalTerm χ X σ n) := by
  apply ((rieszVerticalWeight_integrable X σ hX hσ).norm.const_mul
    ‖LSeries.term (characterMangoldtCoefficient χ) (σ : ℂ) n‖).mono'
  · exact ((characterMangoldt_riesz_term_continuous χ σ n).mul
      (rieszVerticalWeight_continuous X σ hX (by linarith))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => (characterRieszVerticalTerm_norm χ X σ n t).le)

theorem characterRieszVerticalTerm_summable_norm (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n => ∫ t : ℝ, ‖characterRieszVerticalTerm χ X σ n t‖) := by
  have hsum : LSeriesSummable (characterMangoldtCoefficient χ) (σ : ℂ) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by simpa using hσ)
  have hs := hsum.norm.mul_right (∫ t : ℝ, ‖rieszVerticalWeight X σ t‖)
  apply hs.congr
  intro n
  simp only [characterRieszVerticalTerm_norm, integral_const_mul]

theorem characterMangoldt_riesz_term_inversion (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, characterRieszVerticalTerm χ X σ n t) =
      characterMangoldtCoefficient χ n * rieszPrimeTest (n / X) := by
  by_cases hn : n = 0
  · subst n
    simp [characterRieszVerticalTerm, characterMangoldtCoefficient]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hkernel (t : ℝ) : characterRieszVerticalTerm χ X σ n t =
      characterMangoldtCoefficient χ n *
        (((n : ℝ) / X : ℝ) : ℂ) ^ (-rieszMellinLine σ t) *
          rieszMellinKernel (rieszMellinLine σ t) := by
    rw [characterRieszVerticalTerm, LSeries.term_of_ne_zero hn, rieszVerticalWeight,
      Complex.cpow_neg, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg hnR.le hX.le, inv_div]
    push_cast
    ring
  simp_rw [hkernel, mul_assoc]
  rw [integral_const_mul]
  have hinv := rieszPrimeTest_mellin_inversion σ ((n : ℝ) / X) hσ (div_pos hnR hX)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
    (((n : ℝ) / X : ℝ) : ℂ) ^ (-rieszMellinLine σ t) *
      rieszMellinKernel (rieszMellinLine σ t)) = _ at hinv
  rw [← hinv]
  ring

theorem characterRieszMean_eq_vertical_logDerivative (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 < σ) :
    characterRieszMean χ X =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (-logDeriv χ.L (rieszMellinLine σ t)) * rieszVerticalWeight X σ t := by
  unfold characterRieszMean
  calc
    _ = ∑' n : ℕ, ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, characterRieszVerticalTerm χ X σ n t :=
      tsum_congr (fun n => (characterMangoldt_riesz_term_inversion χ X σ hX hσ.le n).symm)
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∑' n : ℕ, ∫ t : ℝ, characterRieszVerticalTerm χ X σ n t := tsum_mul_left
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, ∑' n : ℕ, characterRieszVerticalTerm χ X σ n t := by
      rw [integral_tsum_of_summable_integral_norm
        (characterRieszVerticalTerm_integrable χ X σ hX hσ.le)
        (characterRieszVerticalTerm_summable_norm χ X σ hσ)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [show (∑' n : ℕ, characterRieszVerticalTerm χ X σ n t) =
        LSeries (characterMangoldtCoefficient χ) (rieszMellinLine σ t) * rieszVerticalWeight X σ t from tsum_mul_right]
      rw [χ.mangoldt_LSeries_eq _ (by simpa using hσ)]
      simp only [logDeriv_apply, neg_div]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszTailEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit right-contour tails for the Riesz integral -/

namespace Ostmann

open Complex MeasureTheory Set

noncomputable def rightRieszIntegrand (χ : PrimitiveComplexCharacter)
    (X σ t : ℝ) : ℂ :=
  -logDeriv χ.L (rieszMellinLine σ t) * rieszVerticalWeight X σ t

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterRieszResidueBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Character Riesz bounds retaining the exact rectangle residue -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem character_logDeriv_right_continuous (χ : PrimitiveComplexCharacter)
    (b : ℝ) (hb : 1 < b) :
    Continuous (fun t : ℝ => -logDeriv χ.L (rieszMellinLine b t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hn := χ.L_ne_zero_one_le_re (rieszMellinLine b t) (by simpa using hb.le)
  exact (((χ.L_analytic _).deriv.div (χ.L_analytic _) hn).neg.continuousAt).comp
    (rieszMellinLine_continuous b).continuousAt

theorem characterRieszMean_residue_rectangle_bound : ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (X a b T M : ℝ) (v : ℂ),
      1 ≤ X → 1 / 2 ≤ a → a ≤ b → 1 < b → b ≤ 2 → 0 < T → 0 ≤ M →
      rectangleBoundaryIntegral (fun s => -logDeriv χ.L s * rieszContourWeight X s)
        a b (-T) T = I * (((2 * Real.pi : ℝ) : ℂ) * v) →
      (∀ s : ℂ, ((s.re = a ∧ |s.im| ≤ T) ∨
        (a ≤ s.re ∧ s.re ≤ b ∧ |s.im| = T)) → ‖logDeriv χ.L s‖ ≤ M) →
      ‖characterRieszMean χ X - v‖ ≤ K * M * X ^ a +
        2 * (M * X ^ b / T ^ 2) * (b - a) +
        2 * (1 / (b - 1) + C) * X ^ b / T := by
  obtain ⟨K, hK, hleft⟩ := weightedRiesz_left_segment_bound
  obtain ⟨C, hC, hright⟩ := character_logDeriv_right_pole_bound
  refine ⟨K, C, hK, hC, ?_⟩
  intro χ X a b T M v hX ha hab hb hb2 hT hM hres hedge
  have hXp : 0 < X := by linarith
  have hlow (t : ℝ) (ht : t ∈ Icc (-T) T) :
      ‖-logDeriv χ.L (rieszMellinLine a t)‖ ≤ M := by
    rw [norm_neg]
    apply hedge
    left
    exact ⟨rieszMellinLine_re _ _, by simpa [rieszMellinLine] using abs_le.mpr ht⟩
  have he (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : |t| = T) :
      ‖-logDeriv χ.L ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M := by
    rw [norm_neg]
    apply hedge
    right
    simpa using And.intro hσ.1 (And.intro hσ.2 ht)
  have hl := hleft (fun s => -logDeriv χ.L s) X a T M hXp ha hM hlow
  have hl' : ‖∫ t in -T..T, rightRieszIntegrand χ X a t‖ ≤ K * M * X ^ a := by
    simpa only [intervalIntegral.integral_of_le (show -T ≤ T by linarith),
      integral_Icc_eq_integral_Ioc, rightRieszIntegrand] using hl
  have hu := weightedRiesz_horizontal_segment_bound (fun s => -logDeriv χ.L s)
    X a b T M hX hab (by simpa [abs_of_pos hT]) hM
    (fun σ hσ => he σ T hσ (abs_of_pos hT))
  have hd := weightedRiesz_horizontal_segment_bound (fun s => -logDeriv χ.L s)
    X a b (-T) M hX hab (by simpa [abs_neg, abs_of_pos hT]) hM
    (fun σ hσ => he σ (-T) hσ (by rw [abs_neg, abs_of_pos hT]))
  rw [neg_sq] at hd
  have hv := rectangle_vertical_shift_residue_norm_bound _ a b (-T) T _ hres
  have hrightBound (t : ℝ) : ‖-logDeriv χ.L (rieszMellinLine b t)‖ ≤ 1 / (b - 1) + C := by
    simpa only [norm_neg, rieszMellinLine_re] using hright χ (rieszMellinLine b t)
      (by simpa using hb) (by simpa using hb2)
  have ht := riesz_residue_truncation (fun s => -logDeriv χ.L s) X b
    (1 / (b - 1) + C) T v hXp hb.le (by positivity) hT
    (character_logDeriv_right_continuous χ b hb) hrightBound
  rw [← characterRieszMean_eq_vertical_logDerivative χ X b hXp hb] at ht
  change ‖(∫ t in -T..T, rightRieszIntegrand χ X b t) - _‖ ≤
    ‖∫ t in -T..T, rightRieszIntegrand χ X a t‖ + _ + _ at hv
  change ‖characterRieszMean χ X - v‖ ≤
    ‖(∫ t in -T..T, rightRieszIntegrand χ X b t) - ((2 * Real.pi : ℝ) : ℂ) * v‖ + _ at ht
  change ‖∫ σ in a..b, -logDeriv χ.L ((σ : ℂ) + (T : ℂ) * I) *
    rieszContourWeight X ((σ : ℂ) + (T : ℂ) * I)‖ ≤ _ at hu
  change ‖∫ σ in a..b, -logDeriv χ.L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) *
    rieszContourWeight X ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ _ at hd
  change ‖∫ t in -T..T, rightRieszIntegrand χ X a t‖ ≤ _ at hl'
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPageComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the selected actual Riesz zero with the canonical Page zero -/

namespace Ostmann

open Complex

noncomputable def canonicalCharacterRieszTerm (χ : PrimitiveComplexCharacter)
    (q : ℕ) (X : ℝ) : ℂ := by
  classical
  exact match actualLocalZero q with
  | none => 0
  | some e => if e.asRealCharacter.asComplex = χ then
      -rieszContourWeight X (e.beta : ℂ) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveCharacterReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduction to the actual primitive character, without multiplicities

At a fixed ambient modulus, passage to primitive characters is injective.
Thus grouping the sparse expansion introduces no coefficient multiplicity.
-/
namespace Ostmann
open scoped Classical

noncomputable def primitiveCharacterReduction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Option PrimitiveComplexCharacter :=
  if hχ : χ = 1 then none else some
    { modulus := χ.conductor
      positive := Nat.pos_of_ne_zero χ.conductor_ne_zero
      character := χ.primitiveCharacter
      primitive := χ.primitiveCharacter_isPrimitive
      nontrivial := primitiveCharacter_nontrivial χ hχ }

noncomputable def liftPrimitiveCharacter (N : ℕ)
    (e : Option PrimitiveComplexCharacter) : DirichletCharacter ℂ N :=
  match e with
  | none => 1
  | some χ => if h : χ.modulus ∣ N then DirichletCharacter.changeLevel h χ.character else 1

theorem lift_primitiveCharacterReduction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    liftPrimitiveCharacter N (primitiveCharacterReduction χ) = χ := by
  unfold primitiveCharacterReduction
  split_ifs with hχ
  · simpa only [liftPrimitiveCharacter] using hχ.symm
  · simp only [liftPrimitiveCharacter, χ.conductor_dvd_level, dite_true]
    exact χ.changeLevel_primitiveCharacter

theorem primitiveCharacterReduction_modulus {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (ρ : PrimitiveComplexCharacter)
    (hρ : primitiveCharacterReduction χ = some ρ) : ρ.modulus = χ.conductor := by
  unfold primitiveCharacterReduction at hρ
  split_ifs at hρ
  have he := Option.some.inj hρ
  exact (congrArg PrimitiveComplexCharacter.modulus he).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CanonicalRieszKernelBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform kernel bounds for the canonical exceptional zeros

For large conductors the Page cutoff is to the right of one half. The
remaining finitely many moduli contribute a finite constant.
-/

namespace Ostmann

open Complex

noncomputable def pageRieszKernelNorm (q : ℕ) : ℝ :=
  ‖rieszMellinKernel (pageBeta (actualLocalZero q) : ℂ)‖

theorem page_beta_half_for_large_modulus : ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
    1 / 2 ≤ pageBeta (actualLocalZero q) := by
  let N := ⌈Real.exp (2 * actualPageConstant)⌉₊ + 1
  refine ⟨N, ?_⟩
  intro q hq
  have hqpos : 1 ≤ q := by dsimp [N] at hq; omega
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have he : Real.exp (2 * actualPageConstant) ≤ (q : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp (2 * actualPageConstant)⌉₊ ≤ q by dsimp [N] at hq; omega))
  have hL : 2 * actualPageConstant ≤ Real.log (4 * (q : ℝ)) :=
    (Real.le_log_iff_exp_le (by linarith : 0 < 4 * (q : ℝ))).mpr (he.trans (by linarith))
  have hLp : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
  have hfrac : actualPageConstant / Real.log (4 * (q : ℝ)) ≤ 1 / 2 :=
    (div_le_iff₀ hLp).mpr (by linarith)
  cases heq : actualLocalZero q with
  | none => norm_num [pageBeta]
  | some e =>
    have hb := (actualLocalZero_spec q e heq).2
    change 1 / 2 ≤ e.beta
    linarith

theorem canonical_riesz_kernel_bound : ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, pageRieszKernelNorm q ≤ C := by
  classical
  obtain ⟨N, hN⟩ := page_beta_half_for_large_modulus
  let S := ∑ q ∈ Finset.range N, pageRieszKernelNorm q
  have hS : 0 ≤ S := Finset.sum_nonneg (fun q _ => norm_nonneg _)
  refine ⟨10 + S, by positivity, ?_⟩
  intro q
  by_cases hq : N ≤ q
  · have hh := rieszMellinKernel_half_strip (pageBeta (actualLocalZero q) : ℂ)
      (by simpa using hN q hq)
    have hk : pageRieszKernelNorm q ≤ 9 := by
      simpa [pageRieszKernelNorm, rieszLineMajorant] using hh
    linarith
  · have hs : pageRieszKernelNorm q ≤ S := Finset.single_le_sum (f := pageRieszKernelNorm) (a := q)
      (fun k _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_of_not_ge hq))
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimitiveRieszComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Riesz means after passage to the actual primitive character -/

namespace Ostmann

noncomputable def reducedRieszMean (e : Option PrimitiveComplexCharacter) (X : ℝ) : ℂ :=
  match e with
  | none => principalRieszMean X
  | some χ => characterRieszMean χ X

theorem primitiveReduction_divides {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ρ : PrimitiveComplexCharacter) (hρ : primitiveCharacterReduction χ = some ρ) : ρ.modulus ∣ q := by
  rw [primitiveCharacterReduction_modulus χ ρ hρ]
  exact χ.conductor_dvd_level

theorem primitiveReduction_agrees {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ρ : PrimitiveComplexCharacter) (hρ : primitiveCharacterReduction χ = some ρ)
    (n : ℕ) (hn : n.Coprime q) : χ (n : ZMod q) = ρ.character (n : ZMod ρ.modulus) := by
  have hd := primitiveReduction_divides χ ρ hρ
  have he := lift_primitiveCharacterReduction χ
  rw [hρ] at he
  simp only [liftPrimitiveCharacter, dite_eq_left hd] at he
  rw [← he]
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime n q).mpr hn
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_natCast hd]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveLiftReduction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The primitive label of a lifted primitive character -/

namespace Ostmann

theorem primitiveCharacterReduction_lift (q : ℕ) [NeZero q]
    (ρ : PrimitiveComplexCharacter) (hd : ρ.modulus ∣ q) :
    primitiveCharacterReduction (DirichletCharacter.changeLevel hd ρ.character) = some ρ := by
  let χ := DirichletCharacter.changeLevel hd ρ.character
  have hne : χ ≠ 1 := by
    change DirichletCharacter.changeLevel hd ρ.character ≠ 1
    exact mt (DirichletCharacter.changeLevel_eq_one_iff hd).mp ρ.nontrivial
  cases he : primitiveCharacterReduction χ with
  | none =>
    have hh := lift_primitiveCharacterReduction χ
    rw [he] at hh
    exact (hne hh.symm).elim
  | some τ =>
    have hτ := primitiveReduction_divides χ τ he
    have hh := lift_primitiveCharacterReduction χ
    rw [he] at hh
    simp only [liftPrimitiveCharacter, dite_eq_left hτ] at hh
    have hτρ : τ = ρ := τ.eq_of_changeLevel_eq ρ hτ hd hh
    simp only [hτρ]

theorem primitiveCharacterReduction_eq_some_iff (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : PrimitiveComplexCharacter) (hd : ρ.modulus ∣ q) :
    primitiveCharacterReduction χ = some ρ ↔
      χ = DirichletCharacter.changeLevel hd ρ.character := by
  constructor
  · intro he
    have hh := lift_primitiveCharacterReduction χ
    rw [he] at hh
    simpa only [liftPrimitiveCharacter, dite_eq_left hd] using hh.symm
  · rintro rfl
    exact primitiveCharacterReduction_lift q ρ hd

theorem primitiveCharacterReduction_eq_none_iff (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) : primitiveCharacterReduction χ = none ↔ χ = 1 := by
  constructor
  · intro he
    have hh := lift_primitiveCharacterReduction χ
    rw [he] at hh
    exact hh.symm
  · intro he
    simp [primitiveCharacterReduction, he]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledNodeSources
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete ancestor-source environments at every scheduled tree node -/

namespace Ostmann
open scoped Classical

abbrev scheduledNodeLevel (n : ℕ) (j : Fin (2 ^ n - 1)) : ℕ :=
  n - ((preorderNodePath n j).length + 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_DivisorPowerBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary divisor bound needed for the frequency moduli

For every fixed power `k`, the `k`th power of the divisor count is bounded
by a constant times `n`. The constant is independent of the modulus.
-/

namespace Ostmann

open scoped BigOperators Classical
open Filter

theorem prime_power_divisor_budget (k C p e : ℕ)
    (hbound : ∀ e : ℕ, (e + 1) ^ k ≤ C * 2 ^ e) (hp : p.Prime) :
    (e + 1) ^ k ≤ (if p < 2 ^ k then C else 1) * p ^ e := by
  by_cases hsmall : p < 2 ^ k
  · rw [ite_eq_left hsmall]
    exact (hbound e).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hp.two_le e))
  · rw [ite_eq_right hsmall, one_mul]
    calc
      _ ≤ (2 ^ e) ^ k := Nat.pow_le_pow_left (successor_le_two_pow e) k
      _ = (2 ^ k) ^ e := by rw [← pow_mul, Nat.mul_comm e k, pow_mul]
      _ ≤ p ^ e := Nat.pow_le_pow_left (by omega) e

/-- A concrete power version of `tau(n) = n^o(1)`, proved by separating
the finitely many primes below `2^k` in the factorization. -/
theorem exists_divisors_power_bound (k : ℕ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ n : ℕ, n ≠ 0 → n.divisors.card ^ k ≤ D * n := by
  obtain ⟨C, hC, hbound⟩ := exists_successor_power_bound k
  refine ⟨C ^ (2 ^ k), Nat.one_le_pow _ _ hC, fun n hn => ?_⟩
  have hsmall : (n.primeFactors.filter fun p => p < 2 ^ k).card ≤ 2 ^ k := by
    calc
      _ ≤ (Finset.range (2 ^ k)).card := Finset.card_le_card fun p hp =>
        Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = _ := Finset.card_range _
  have hcost : (∏ p ∈ n.primeFactors, if p < 2 ^ k then C else 1) ≤ C ^ (2 ^ k) := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const]
    exact Nat.pow_le_pow_right hC hsmall
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < 2 ^ k then C else 1) * p ^ n.factorization p := by
      apply Finset.prod_le_prod'
      intro p hp
      exact prime_power_divisor_budget k C p (n.factorization p) hbound
        (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, if p < 2 ^ k then C else 1) * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ _ := Nat.mul_le_mul_right n hcost

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualProgressionInput
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-progression estimate with constructed exceptional zeros

This is the theta estimate of Montgomery–Vaughan, Corollary 11.20. The actual
exceptional-zero family records divisibility, completeness and Page uniqueness.
-/

namespace Ostmann

def ActualProgressionTheta : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ q : ℕ, 1 ≤ q → ∀ a : ℕ, a.Coprime q → ∀ x : ℝ, 2 ≤ x →
      |primeProgressionTheta q a x -
        thetaMainTerm (Nat.totient q) (pageCoefficient (actualLocalZero q) a)
          (pageBeta (actualLocalZero q)) x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_InducedCharacterRieszDecay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Riesz estimates for all characters at the ambient modulus -/

namespace Ostmann

open Filter

noncomputable def reducedRieszMain (q : ℕ) (e : Option PrimitiveComplexCharacter) (X : ℝ) : ℂ :=
  match e with
  | none => (X / 2 : ℝ)
  | some χ => canonicalCharacterRieszTerm χ q X

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszCharacterMainSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact principal and exceptional terms after character summation -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem reducedRieszMain_no_exception (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℝ) (he : actualLocalZero q = none) :
    reducedRieszMain q (primitiveCharacterReduction χ) X =
      if χ = 1 then ((X / 2 : ℝ) : ℂ) else 0 := by
  classical
  cases hr : primitiveCharacterReduction χ with
  | none =>
    have hχ := (primitiveCharacterReduction_eq_none_iff q χ).mp hr
    simp only [reducedRieszMain, hχ, ↓reduceIte]
  | some ρ =>
    have hχ : χ ≠ 1 := by
      intro h
      have hn := (primitiveCharacterReduction_eq_none_iff q χ).mpr h
      rw [hr] at hn
      cases hn
    simp only [reducedRieszMain, canonicalCharacterRieszTerm, he, hχ, ↓reduceIte]

theorem reducedRieszMain_exception (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (X : ℝ) (e : PrimitiveRealZero) (he : actualLocalZero q = some e) :
    let hd := (actualLocalZero_spec q e he).1
    let τ := DirichletCharacter.changeLevel hd e.asRealCharacter.asComplex.character
    reducedRieszMain q (primitiveCharacterReduction χ) X =
      (if χ = 1 then ((X / 2 : ℝ) : ℂ) else 0) -
        (if χ = τ then rieszContourWeight X (e.beta : ℂ) else 0) := by
  classical
  dsimp only
  let R := e.asRealCharacter.asComplex
  let hd := (actualLocalZero_spec q e he).1
  let τ := DirichletCharacter.changeLevel hd R.character
  have hτ : τ ≠ 1 := mt (DirichletCharacter.changeLevel_eq_one_iff hd).mp R.nontrivial
  change reducedRieszMain q (primitiveCharacterReduction χ) X =
    (if χ = 1 then ((X / 2 : ℝ) : ℂ) else 0) -
      (if χ = τ then rieszContourWeight X (e.beta : ℂ) else 0)
  cases hr : primitiveCharacterReduction χ with
  | none =>
    have hχ := (primitiveCharacterReduction_eq_none_iff q χ).mp hr
    simp only [reducedRieszMain, hχ, ↓reduceIte, Ne.symm hτ, sub_zero]
  | some ρ =>
    have hχ : χ ≠ 1 := by
      intro h
      have hn := (primitiveCharacterReduction_eq_none_iff q χ).mpr h
      rw [hr] at hn
      cases hn
    by_cases hρ : ρ = R
    · have hχτ : χ = τ := by
        apply (primitiveCharacterReduction_eq_some_iff q χ R hd).mp
        simpa only [hρ] using hr
      simp only [reducedRieszMain, canonicalCharacterRieszTerm, he, hρ, R, hχτ, hτ,
        ↓reduceIte, zero_sub]
    · have hχτ : χ ≠ τ := by
        intro h
        have hh := primitiveCharacterReduction_lift q R hd
        change primitiveCharacterReduction τ = some R at hh
        rw [← h, hr] at hh
        exact hρ (Option.some.inj hh)
      simp only [reducedRieszMain, canonicalCharacterRieszTerm, he,
        show e.asRealCharacter.asComplex ≠ ρ from Ne.symm hρ, hχ, hχτ, ↓reduceIte, sub_zero]

theorem rieszCharacterMainSum_no_exception (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X : ℝ) (he : actualLocalZero q = none) :
    (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * reducedRieszMain q (primitiveCharacterReduction χ) X) =
      (X / 2 : ℝ) := by
  classical
  simp_rw [reducedRieszMain_no_exception q _ X he]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    principal_character_inverse_value q a ha, one_mul]

theorem rieszCharacterMainSum_exception (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (X : ℝ) (e : PrimitiveRealZero) (he : actualLocalZero q = some e) :
    let hd := (actualLocalZero_spec q e he).1
    let τ := DirichletCharacter.changeLevel hd e.asRealCharacter.asComplex.character
    (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * reducedRieszMain q (primitiveCharacterReduction χ) X) =
      (X / 2 : ℝ) - τ a⁻¹ * rieszContourWeight X (e.beta : ℂ) := by
  classical
  dsimp only
  simp_rw [reducedRieszMain_exception q _ X e he]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, principal_character_inverse_value q a ha, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszCanonicalResidueMain
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The canonical Page correction in the actual residue-class Riesz mean -/

namespace Ostmann

open Complex Filter
open scoped BigOperators

theorem real_zero_lift_inverse_nat (e : PrimitiveRealZero) (q a : ℕ) [NeZero q]
    (hd : e.modulus ∣ q) (ha : a.Coprime q) :
    (DirichletCharacter.changeLevel hd e.asRealCharacter.asComplex.character) (a : ZMod q)⁻¹ =
      (e.character (a : ZMod e.modulus) : ℂ) := by
  let τ := DirichletCharacter.changeLevel hd e.asRealCharacter.asComplex.character
  have hself : τ⁻¹ = τ := e.asRealCharacter.lift_inverse_eq hd
  have hi : τ (a : ZMod q)⁻¹ = τ (a : ZMod q) := by
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr ha
    have hh := congrArg (fun χ : DirichletCharacter ℂ q => χ (u : ZMod q)) hself
    rw [MulChar.inv_apply, Ring.inverse_unit] at hh
    rw [← hu, ZMod.inv_coe_unit]
    exact hh
  change τ (a : ZMod q)⁻¹ = _
  rw [hi]
  have hr := primitiveCharacterReduction_lift q e.asRealCharacter.asComplex hd
  exact primitiveReduction_agrees τ e.asRealCharacter.asComplex hr a ha

theorem rieszCharacterMainSum_canonical (q a : ℕ) [NeZero q] (ha : a.Coprime q) (X : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ *
      reducedRieszMain q (primitiveCharacterReduction χ) X) =
      (X / 2 : ℝ) - (pageCoefficient (actualLocalZero q) a : ℂ) *
        rieszContourWeight X (pageBeta (actualLocalZero q) : ℂ) := by
  have hua := (ZMod.isUnit_iff_coprime a q).mpr ha
  cases he : actualLocalZero q with
  | none =>
    rw [rieszCharacterMainSum_no_exception q _ hua X he]
    simp [pageCoefficient]
  | some e =>
    rw [rieszCharacterMainSum_exception q _ hua X e he]
    rw [real_zero_lift_inverse_nat e q a (actualLocalZero_spec q e he).1 ha]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ResiduePrimePowerRemoval
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing higher prime powers from sharp residue sums -/

namespace Ostmann

open scoped BigOperators

theorem primeProgressionLog_bounds (q a n : ℕ) :
    0 ≤ primeProgressionLog q a n ∧
      primeProgressionLog q a n ≤ residueMangoldtWeight q a n := by
  by_cases hp : n.Prime ∧ Nat.ModEq q n a
  · have he : (n : ZMod q) = (a : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff n a q).mpr hp.2
    rw [primeProgressionLog, ite_eq_left hp, residueMangoldtWeight, ite_eq_left he,
      ArithmeticFunction.vonMangoldt_apply_prime hp.1]
    exact ⟨Real.log_nonneg (by exact_mod_cast hp.1.one_le), le_rfl⟩
  · rw [primeProgressionLog, ite_eq_right hp]
    exact ⟨le_rfl, residueMangoldtWeight_nonneg q a n⟩

theorem primeProgressionTheta_bounds (q a : ℕ) (X : ℝ) :
    0 ≤ primeProgressionTheta q a X ∧ primeProgressionTheta q a X ≤ residuePsi q a X := by
  constructor
  · exact Finset.sum_nonneg (fun n _ => (primeProgressionLog_bounds q a n).1)
  · exact Finset.sum_le_sum (fun n _ => (primeProgressionLog_bounds q a n).2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TotientSqrtBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A sufficient reciprocal-totient bound for the large-modulus range -/

namespace Ostmann

theorem reciprocal_totient_sqrt_bound : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q →
    1 / (q.totient : ℝ) ≤ C / Real.sqrt q := by
  obtain ⟨D, hD, hdiv⟩ := exists_divisors_power_bound 2
  refine ⟨Real.sqrt D, Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < D by omega)), ?_⟩
  intro q hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hτ : (q : ℝ) ≤ q.divisors.card * (q.totient : ℝ) := by
    exact_mod_cast le_divisors_card_mul_totient q hq.ne'
  have hdiv' : (q.divisors.card : ℝ) ^ 2 ≤ D * (q : ℝ) := by exact_mod_cast hdiv q hq.ne'
  have hq2 : (q : ℝ) ^ 2 ≤ (D : ℝ) * q * (q.totient : ℝ) ^ 2 := by
    have hs : (q : ℝ) ^ 2 ≤ (q.divisors.card * (q.totient : ℝ)) ^ 2 := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hdiv' (sq_nonneg (q.totient : ℝ))
    nlinarith
  have hqD : (q : ℝ) ≤ (D : ℝ) * (q.totient : ℝ) ^ 2 := by nlinarith
  have hs := Real.sqrt_le_sqrt hqD
  rw [Real.sqrt_mul (Nat.cast_nonneg D), Real.sqrt_sq_eq_abs,
    abs_of_pos hφ] at hs
  exact (div_le_div_iff₀ hφ (Real.sqrt_pos.mpr hqpos)).mpr (by simpa using hs)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CanonicalThetaSize
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary size of the canonical progression main term -/

namespace Ostmann

open Complex

theorem canonical_page_beta_inverse_bound : ∃ B : ℝ, 0 < B ∧
    ∀ q : ℕ, (pageBeta (actualLocalZero q))⁻¹ ≤ B := by
  obtain ⟨C, hC, hbound⟩ := canonical_riesz_kernel_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro q
  let β := pageBeta (actualLocalZero q)
  have hβ : 0 < β := pageBeta_pos _
  have hβ1 : β ≤ 1 := pageBeta_le_one _
  have he : pageRieszKernelNorm q = 1 / (β * (β + 1)) := by
    change ‖(1 : ℂ) / ((β : ℂ) * ((β : ℂ) + 1))‖ = _
    rw [show (β : ℂ) + 1 = ((β + 1 : ℝ) : ℂ) by push_cast; rfl,
      norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hβ, abs_of_pos (by linarith : 0 < β + 1)]
  have hb := hbound q
  rw [he] at hb
  have hid : β⁻¹ = (β + 1) * (1 / (β * (β + 1))) := by field_simp
  change β⁻¹ ≤ _
  rw [hid]
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ β + 1 by linarith)
  nlinarith

theorem canonical_theta_sqrt_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (q a : ℕ) (X : ℝ), 0 < q → 1 ≤ X →
      |thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
        (pageBeta (actualLocalZero q)) X| ≤ C * X / Real.sqrt q := by
  obtain ⟨B, hB, hβ⟩ := canonical_page_beta_inverse_bound
  obtain ⟨D, hD, hφ⟩ := reciprocal_totient_sqrt_bound
  refine ⟨(1 + B) * D, by positivity, ?_⟩
  intro q a X hq hX
  have hφp : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have ht := thetaMainTerm_size (q.totient : ℝ) (pageCoefficient (actualLocalZero q) a)
    (pageBeta (actualLocalZero q)) X B hφp (pageCoefficient_abs_le_one _ _)
    (pageBeta_pos _) (pageBeta_le_one _) hX hB.le (hβ q)
  have hh := mul_le_mul_of_nonneg_left (hφ q hq) (show 0 ≤ (1 + B) * X by positivity)
  calc
    _ ≤ (1 + B) * X / q.totient := ht
    _ ≤ (1 + B) * X * (D / Real.sqrt q) := by simpa only [div_eq_mul_inv, mul_one, one_mul] using hh
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ResiduePsiLargeModulus
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary control of the complementary large-modulus range -/

namespace Ostmann

open Filter

theorem residuePsi_large_modulus_bound_log : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ y : ℝ in atTop, ∀ q : ℕ, 0 < q → Real.exp (y / 2) ≤ (q : ℝ) →
      ∀ a : ℕ,
        |residuePsi q a (Real.exp (y ^ 2)) - thetaMainTerm q.totient
          (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q))
            (Real.exp (y ^ 2))| ≤
          C * Real.exp (y ^ 2) * Real.exp (-(1 / 4 : ℝ) * y) := by
  obtain ⟨D, hD, hmain⟩ := canonical_theta_sqrt_bound
  refine ⟨D + 2, by positivity, ?_⟩
  filter_upwards [riesz_polynomial_absorption 1 (1 / 4) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with y hp hy
  intro q hq hqy a
  let X := Real.exp (y ^ 2)
  have hX : 1 ≤ X := Real.one_le_exp (sq_nonneg y)
  have hXp : 0 < X := Real.exp_pos _
  have hpoly : y ^ 2 ≤ Real.exp (y / 4) := by
    rw [show (1 / 4 : ℝ) * y = y / 4 by ring] at hp
    linarith
  have hquot : y ^ 2 / q ≤ Real.exp (-y / 4) := by
    calc
      _ ≤ Real.exp (y / 4) / Real.exp (y / 2) :=
        div_le_div₀ (Real.exp_nonneg _) hpoly (Real.exp_pos _) hqy
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  have hpoly' : y ^ 2 ≤ X * Real.exp (-y / 4) := by
    calc
      _ ≤ Real.exp (y / 4) := hpoly
      _ ≤ Real.exp (y ^ 2 - y / 4) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by
        dsimp [X]
        rw [Real.exp_sub, show -y / 4 = -(y / 4) by ring, Real.exp_neg]
        rfl
  have hcount := residuePsi_counting_bound q a X hq hX
  have hlog : Real.log X = y ^ 2 := Real.log_exp _
  rw [hlog] at hcount
  have hcount' : residuePsi q a X ≤ 2 * X * Real.exp (-y / 4) := by
    have hm := mul_le_mul_of_nonneg_left hquot hXp.le
    have hid : (X / (q : ℝ) + 1) * y ^ 2 = X * (y ^ 2 / q) + y ^ 2 := by ring
    rw [hid] at hcount
    linarith
  have hsqrt : Real.exp (y / 4) ≤ Real.sqrt q := by
    have hh := Real.sqrt_le_sqrt hqy
    rw [← Real.exp_half] at hh
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
  have hm := hmain q a X hq hX
  have hmain' : |thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
      (pageBeta (actualLocalZero q)) X| ≤ D * X * Real.exp (-y / 4) := by
    calc
      _ ≤ D * X / Real.sqrt q := hm
      _ ≤ D * X / Real.exp (y / 4) :=
        div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hsqrt
      _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring
  have htri := abs_sub (residuePsi q a X)
    (thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
      (pageBeta (actualLocalZero q)) X)
  rw [abs_of_nonneg (residuePsi_nonneg q a X)] at htri
  have he : -(1 / 4 : ℝ) * y = -y / 4 := by ring
  rw [he]
  change |residuePsi q a X - thetaMainTerm q.totient
    (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤ _
  nlinarith

theorem residuePsi_large_modulus_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 0 < q →
      Real.exp (Real.sqrt (Real.log X) / 2) ≤ (q : ℝ) → ∀ a : ℕ,
        |residuePsi q a X - thetaMainTerm q.totient
          (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
          C * X * Real.exp (-(1 / 4 : ℝ) * Real.sqrt (Real.log X)) := by
  obtain ⟨C, hC, hbound⟩ := residuePsi_large_modulus_bound_log
  refine ⟨C, hC, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually hbound, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have he : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log (by linarith)]
  dsimp only [Function.comp_apply] at hX
  simpa only [he] using hX

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualThetaEstimate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual prime-progression estimate, with no analytic input hypotheses -/

namespace Ostmann

open Filter

theorem actual_theta_bounded_range : ∃ D : ℝ, 0 < D ∧
    ∀ (q a : ℕ) (X L : ℝ), 1 ≤ q → 1 ≤ X → X ≤ L →
      |primeProgressionTheta q a X - thetaMainTerm q.totient
        (pageCoefficient (actualLocalZero q) a) (pageBeta (actualLocalZero q)) X| ≤
          (2 * Real.log L + D) * X := by
  obtain ⟨D, hD, hmain⟩ := canonical_theta_sqrt_bound
  refine ⟨D, hD, ?_⟩
  intro q a X L hq hX hXL
  have hXp : 0 ≤ X := by linarith
  have hqp : 0 < q := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hroot : 1 ≤ Real.sqrt q := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hqR)
  have hm := (hmain q a X hqp hX).trans
    (div_le_self (show 0 ≤ D * X by positivity) hroot)
  have hcount := residuePsi_counting_bound q a X hqp hX
  have hlog : Real.log X ≤ Real.log L := Real.log_le_log (by linarith) hXL
  have hdiv : X / q ≤ X := div_le_self hXp hqR
  have hb : residuePsi q a X ≤ 2 * X * Real.log L := by
    calc
      _ ≤ (X / q + 1) * Real.log X := hcount
      _ ≤ (2 * X) * Real.log L := mul_le_mul (by linarith) hlog
        (Real.log_nonneg hX) (by positivity)
  have hp := primeProgressionTheta_bounds q a X
  have ht := abs_sub (primeProgressionTheta q a X)
    (thetaMainTerm q.totient (pageCoefficient (actualLocalZero q) a)
      (pageBeta (actualLocalZero q)) X)
  rw [abs_of_nonneg hp.1] at ht
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterContourDiskZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Zeros in the enlarged contour disk still lie in the critical strip -/

namespace Ostmann

open Complex Metric

theorem PrimitiveComplexCharacter.L_ne_zero_negative_small (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : -1 < z.re) (hz' : z.re ≤ 0) (hne : z ≠ 0) : χ.L z ≠ 0 := by
  rw [χ.L_eq_completed_mul z hne]
  apply mul_ne_zero (χ.completed_ne_zero_left z hz')
  classical
  unfold PrimitiveComplexCharacter.gammaInverse DirichletCharacter.gammaFactor
  split_ifs
  · rw [gammaReal_inverse_factor]
    apply mul_ne_zero hne
    apply mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
    apply inv_ne_zero
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re]
    norm_num
    linarith
  · apply inv_ne_zero
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityZeroBins
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual zero indices, unit ordinate bins and separated representatives -/

namespace Ostmann

open scoped BigOperators Classical

abbrev DensityZeroIndex := Σ _ : PrimitiveComplexCharacter, ℕ
abbrev DensityZeroBin := Σ _ : PrimitiveComplexCharacter, ℤ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_MertensFromProgression
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens estimates from the progression estimate

The conductor-one theta bound implies the first Mertens estimate.
-/

namespace Ostmann

open Finset MeasureTheory
open scoped BigOperators Interval

noncomputable def PublishedProgressionInput.mertensConstant (P : PublishedProgressionInput) : ℝ :=
  |1 - Real.log 2| + P.errorConstant +
    P.errorConstant * (-thetaErrorPrimitive P.decay 2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ProgressionConstantRestriction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decreasing the common exceptional-zero constant -/

namespace Ostmann

/-- Completeness and Page uniqueness persist when the exceptional strip is
narrowed. The prime-progression estimate and its actual zero are unchanged. -/
noncomputable def PublishedProgressionInput.restrictKappa (P : PublishedProgressionInput)
    (κ : ℝ) (hκ : 0 < κ) (hκP : κ ≤ P.kappa) : PublishedProgressionInput where
  kappa := κ
  decay := P.decay
  errorConstant := P.errorConstant
  kappa_pos := hκ
  decay_pos := P.decay_pos
  errorConstant_nonneg := P.errorConstant_nonneg
  localZero := P.localZero
  divides := P.divides
  complete := by
    intro q hq e he hβ
    apply P.complete q hq e he
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hl : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
    have hh := div_le_div_of_nonneg_right hκP hl.le
    linarith
  unique := by
    intro Q hQ e f he hf hβ hγ
    apply P.unique Q hQ e f he hf
    all_goals
      have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hl : 0 < Real.log (4 * (Q : ℝ)) := Real.log_pos (by linarith)
      have hh := div_le_div_of_nonneg_right hκP hl.le
      linarith
  theta := P.theta

end Ostmann

end OAI
end


