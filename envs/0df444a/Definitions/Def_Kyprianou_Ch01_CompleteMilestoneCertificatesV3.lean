-- Prove2me | Definitions.Def_Kyprianou_Ch01_CompleteMilestoneCertificatesV3
-- name    : Kyprianou_Ch01_CompleteMilestoneCertificatesV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:37:07.314203+00:00
-- url     : https://prove2.me/theorems/cc13fdc5-e5c2-4bad-8c06-1ea004e36873
-- title:
--   Complete Chapter 1 milestone certificates with qualified Brownian model
-- statement:
--   Exact quantified propositions matching seven Proved foundational milestone declarations and the corrected Lévy–Khintchine sign-bridge theorem. These close the gap between the cumulative root and all 60 mandatory milestone statements.
-- source:
--   Kyprianou (2006) Chapter 1, §§1.1–1.3; authoritative statement types of the referenced LeanLevy, MarkovProcess and LevyFoundations theorems.

import Definitions.Def_Kyprianou_Ch01_ReviewCorrectionsNonexplosive
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_PoissonProcess
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Definitions.Def_MarkovProcess_V3H_Examples_BrownianMotion_c88465db
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Mathlib
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 MarkovProcess Real Complex Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u u_1 u_2 u_3
namespace Kyprianou.Ch01

/-! Full source proposition for ProbabilityTheory.IsLevyProcess.isInfinitelyDivisible_marginal. -/
noncomputable def certificate_reuse_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal : Prop :=
  ∀ {Ω : Type u_2} [inst : MeasurableSpace Ω] {E : Type u_3} [inst_1 : NormedAddCommGroup E]
  [@InnerProductSpace Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)]
  [inst_3 : MeasurableSpace E]
  [@BorelSpace E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      inst_3]
  [@SecondCountableTopology E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))]
  [@MeasurableAdd₂ E inst_3
      (@AddCommMagma.toAdd E
        (@AddCommSemigroup.toAddCommMagma E
          (@AddCommMonoid.toAddCommSemigroup E
            (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst_1)))))]
  {X : NNReal → Ω → E} {μ : @MeasureTheory.Measure Ω inst} [@MeasureTheory.IsProbabilityMeasure Ω inst μ],
  @ProbabilityTheory.IsLevyProcess Ω E inst inst_3
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst_1)) X μ →
    (∀ (t : NNReal), @Measurable Ω E inst inst_3 (X t)) →
      ∀ (t : NNReal),
        @ProbabilityTheory.IsInfinitelyDivisible E
          (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst_1)) inst_3
          (@MeasureTheory.Measure.map Ω E inst inst_3 (X t) μ)

/-! Full source proposition for ProbabilityTheory.IsLevyProcess.charFun_eq_exp_mul. -/
noncomputable def certificate_reuse_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul : Prop :=
  ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {E : Type u_3} [inst_1 : NormedAddCommGroup E]
  [inst_2 : @InnerProductSpace Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)]
  [inst_3 : MeasurableSpace E]
  [@BorelSpace E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      inst_3]
  [@SecondCountableTopology E
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))]
  [@MeasurableAdd₂ E inst_3
      (@AddCommMagma.toAdd E
        (@AddCommSemigroup.toAddCommMagma E
          (@AddCommMonoid.toAddCommSemigroup E
            (@AddCommGroup.toAddCommMonoid E (@NormedAddCommGroup.toAddCommGroup E inst_1)))))]
  {X : NNReal → Ω → E} {μ : @MeasureTheory.Measure Ω inst} [@MeasureTheory.IsProbabilityMeasure Ω inst μ]
  (h :
    @ProbabilityTheory.IsLevyProcess Ω E inst inst_3
      (@UniformSpace.toTopologicalSpace E
        (@PseudoMetricSpace.toUniformSpace E
          (@SeminormedAddCommGroup.toPseudoMetricSpace E (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
      (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst_1)) X μ),
  (∀ (t : NNReal), @Measurable Ω E inst inst_3 (X t)) →
    ∀ (t : NNReal) (ξ : E),
      @Eq Complex
        (@MeasureTheory.charFun E inst_3
          (@InnerProductSpace.toInner Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)
            inst_2)
          (@MeasureTheory.Measure.map Ω E inst inst_3 (X t) μ) ξ)
        (Complex.exp
          (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) (↑↑t)
            (@ProbabilityTheory.IsLevyProcess.charExponent Ω E inst inst_3
              (@UniformSpace.toTopologicalSpace E
                (@PseudoMetricSpace.toUniformSpace E
                  (@SeminormedAddCommGroup.toPseudoMetricSpace E
                    (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1))))
              (@AddCommGroup.toAddGroup E (@NormedAddCommGroup.toAddCommGroup E inst_1))
              (@InnerProductSpace.toInner Real E Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup E inst_1)
                inst_2)
              X μ h ξ)))

/-! Full source proposition for ProbabilityTheory.IsPoissonProcess.isLevyProcess. -/
noncomputable def certificate_reuse_ProbabilityTheory_IsPoissonProcess_isLevyProcess : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {N : NNReal → Ω → ℕ} {rate : NNReal} {μ : Measure Ω},
∀ (h : IsPoissonProcess N rate μ)
    (hcadlag : ∀ᵐ ω ∂μ, IsCadlag (fun t => (N t ω : ℤ))),
IsLevyProcess (fun t ω => (N t ω : ℤ)) μ

/-! Full source proposition for levy_foundations_poissonLaw_infinitelyDivisible. -/
noncomputable def certificate_reuse_levy_foundations_poissonLaw_infinitelyDivisible : Prop :=
  ∀ (r : ℝ≥0),
LevyFoundations.isInfinitelyDivisibleLaw
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ))

/-! Full source proposition for ProbabilityTheory.compoundPoisson_ae_isCadlag. -/
noncomputable def certificate_reuse_ProbabilityTheory_compoundPoisson_ae_isCadlag : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {b : ℝ} {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r),
∀ᵐ ω ∂μ, IsCadlag (fun t => compoundPoisson b τ Y t ω)

/-! Full source proposition for levy_foundations_compoundPoissonMarginalInfinitelyDivisible. -/
noncomputable def certificate_reuse_levy_foundations_compoundPoissonMarginalInfinitelyDivisible : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν']
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0) (b : ℝ) (t : ℝ≥0),
LevyFoundations.isInfinitelyDivisible
      (μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ)))

/-! Full source proposition for MarkovProcess.isBrownianReal_brownianMotion. -/
noncomputable def certificate_reuse_MarkovProcess_isBrownianReal_brownianMotion : Prop :=
  ∀ (x : ℝ),
MarkovProcess.IsBrownianReal (fun (t : NNReal) (omega : ContinuousPath ℝ) ↦ omega t - x)
      (MarkovProcess.brownianMotion x)

/-! Full source proposition for Kyprianou.Ch01.levyTripletExponentSignBridgeReviewed. -/
noncomputable def certificate_levyTripletExponentSignBridgeReviewed : Prop :=
  ∀ (T : ProbabilityTheory.LevyKhintchineTriple) (xi : ℝ),
-levyTripleExponent T xi =
      -(Complex.I * (((T.drift * xi : ℝ) : ℂ))) +
      (((T.gaussianVariance : ℝ) * xi ^ 2 / 2 : ℝ) : ℂ) -
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure)

end Kyprianou.Ch01


