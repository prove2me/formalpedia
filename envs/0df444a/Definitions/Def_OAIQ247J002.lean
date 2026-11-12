-- Prove2me | Definitions.Def_OAIQ247J002
-- name    : OAIQ247J002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:41:44.754648+00:00
-- url     : https://prove2.me/theorems/0278e142-9694-4706-a60f-da942894b5c1
-- title:
--   Definitions bundle OAIQ247J002 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 305 declarations of OpenAI's Lean: 85 definitions, 4 instances and 216 theorems. The definitions and types are `OAI.Erdos970.Erdos970Dependency.DensityComparison.dominationConstant`, `OAI.Erdos970.Erdos970Dependency.InitialDensityFormulas.regThreeDensity`, `OAI.Erdos970.Erdos970Dependency.InitialDensityFormulas.regTwoDensity`, `OAI.Erdos970.Erdos970Dependency.InvariantCostBound.evenMajor`, `OAI.Erdos970.Erdos970Dependency.InvariantCostBound.oddMajor`, `OAI.Erdos970.Erdos970Dependency.InvariantDensities.beta`, `OAI.Erdos970.Erdos970Dependency.InvariantDensities.evenDensity`, `OAI.Erdos970.Erdos970Dependency.InvariantDensities.oddDensity`, `OAI.Erdos970.Erdos970Dependency.InvariantDensities.oddFactor`, `OAI.Erdos970.Erdos970Dependency.InvariantFiniteness.evenMeasure`, `OAI.Erdos970.Erdos970Dependency.InvariantFiniteness.oddMeasure`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.costOutsideFilter`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.costTransform`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.costWindowFilter`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.gapAt`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.kernelScale`, `OAI.Erdos970.Erdos970Dependency.MarkedVisits.stateFilter`, `OAI.Erdos970.Erdos970Dependency.MaximalCoupling.common`, `OAI.Erdos970.Erdos970Dependency.MaximalCoupling.leftRemainder`, `OAI.Erdos970.Erdos970Dependency.MaximalCoupling.matrix`, `OAI.Erdos970.Erdos970Dependency.MaximalCoupling.residual`, `OAI.Erdos970.Erdos970Dependency.MaximalCoupling.rightRemainder`, `OAI.Erdos970.Erdos970Dependency.MeshStationary.mesh`, `OAI.Erdos970.Erdos970Dependency.MeshStationary.point`, `OAI.Erdos970.Erdos970Dependency.MeshStationary.weight`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.absoluteZetaTwo`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.characterPhase`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.characterRieszIntegrand`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.cubeHeight`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.dirichletCenter`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.dirichletDiskEnvelope`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.dirichletDiskPoint`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.localEulerFactor`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.mellinFactor`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.modulusEulerProduct`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.normalizedDirichlet`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.primeIntervalFlags`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.primeMultiplesIn` and 45 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Erdos970_PNT5_Strong`, `Jacobsthal_Analysis_DensityComparison`, `Jacobsthal_Analysis_RieszIntegralRepresentation`, `Jacobsthal_Analysis_WeightFutureIntegrals`, `Jacobsthal_Analysis_WeightIntegrals`, `Jacobsthal_Estimates_InvariantFiniteness`, `Jacobsthal_Estimates_InverseWeightGrowth`, `Jacobsthal_Estimates_NonquadraticZeroFree`, `Jacobsthal_Estimates_OnePairCost`, `Jacobsthal_Estimates_PVIdentity`, `Jacobsthal_Estimates_PairedDeficitPositivity`, `Jacobsthal_Estimates_RieszIntegrand`, `Jacobsthal_Harmonic_CharacterPositivity`, `Jacobsthal_Partitions_MeshStationary`, `Jacobsthal_Partitions_NestedCoordinates`, `Jacobsthal_Primes_DirichletZeroPenalty`, `Jacobsthal_Primes_IntervalPrimesDefinition`, `Jacobsthal_Primes_PrimeCountAbel`, `Jacobsthal_Primes_PrimeIntervalFlags`, `Jacobsthal_Primes_PrincipalPrimePowers`, `Jacobsthal_Primes_RieszMellinKernel`, `Jacobsthal_Primes_UniformDirichletBasepoint`, `Jacobsthal_Primes_WeightedPrimeMultiplePairs`, `Jacobsthal_Primes_ZetaPoleBounds`, `Jacobsthal_Probability_ActualCouplingUpdates`, `Jacobsthal_Probability_FirstHitKernels`, `Jacobsthal_Probability_GeometricCostLaws`, `Jacobsthal_Probability_MarkedCostHitReduction`, `Jacobsthal_Probability_MarkedVisitGeometry`, `Jacobsthal_Probability_OrdinaryMarkedWindow`, `Jacobsthal_Probability_PairedDrift`, `Jacobsthal_Probability_SigmaFamilyKernel`, `Jacobsthal_Probability_TransitionKernels`, `Jacobsthal_Renewal_DickmanFiniteDecay`, `Jacobsthal_Renewal_KernelPotential`, `Jacobsthal_Renewal_LaplaceODE`, `Jacobsthal_Renewal_RegenerationDrift`, `Jacobsthal_Renewal_WeightDickmanComparison`, `Jacobsthal_Sieve_AlignedPrimeCongruence`, `Jacobsthal_Sieve_BuchstabBridge`, `Jacobsthal_Sieve_CompactExponentialMoments`, `Jacobsthal_Sieve_ExponentialIntegral`, `Jacobsthal_Sieve_LargeModulusSiegelWalfisz`, `Jacobsthal_Sieve_LinearSieveFunctions`, `Jacobsthal_Sieve_PrincipalEulerCorrection`, `Jacobsthal_Sieve_ResidueSqrtSplit`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ247J007`; the statements `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.moving_signed_prime_multiple_lower_jb247`, `OAI.Erdos970.ErdosStoppedArithmetic.moving_subbin_actual_pair_lower_jb247`, `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_divisibility_jb247` and `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_full_local_bounds_jb247`; the proofs of `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_primitive_real_zero_free_disk_jb247`, `OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error_jb247`, `OAI_Erdos970_ErdosRandomVariance_stable_source_chebyshev_jb247`, `OAI_Erdos970_EulerWeightedLower_weightedSmallSum_eventually_uniform_jb247`, `OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247`, `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_divisibility_jb247` and `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_full_local_bounds_jb247`.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit adc7f12

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice

section
-- module Solutions.OAIQ247_JB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT5_Strong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)

local notation "Λ" => vonMangoldt

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

theorem SmoothedChebyshevClose_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2) (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X) (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) → Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
  ‖(↑((∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X))) : ℂ) -
        ↑((Finset.range ⌊X + 1⌋₊).sum ⇑ArithmeticFunction.vonMangoldt)‖ ≤
    C * ε * X * Real.log X := by
  norm_cast

  let F := Smooth1 SmoothingF ε

  let n₀ := ⌈X * (1 - c₁ * ε)⌉₊

  have n₀_pos : 0 < n₀ := by
    simp only [Nat.ceil_pos, n₀]
    subst C_eq
    simp_all only [mem_Ioo, and_imp, ge_iff_le, implies_true, mul_pos_iff_of_pos_left, sub_pos]
    exact (mul_le_of_le_one_right c₁_pos.le ε_lt_one.le).trans_lt c₁_lt

  have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg_left _ X_pos.le
    apply sub_le_self
    positivity

  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
    simp only [n₀]
    apply le_of_lt
    exact Nat.ceil_lt_add_one (by bound)

  have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
    simp only [n₀]
    exact Nat.le_ceil (X * (1 - c₁ * ε))

  have sumΛ : Summable (fun (n : ℕ) ↦ Λ n * F (n / X)) := by
    exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
    (hc₂ _ _ (by trivial) ((le_div_iff₀ X_pos).2 (Nat.ceil_le.1 (not_lt.1
    (s ∘ Finset.mem_range.2))))))

  have sumΛn₀ (n₀ : ℕ) : Summable (fun n ↦ Λ (n + n₀) * F ((n + n₀) / X)) := by exact_mod_cast sumΛ.comp_injective fun Q=>by valid

  rw[← Summable.sum_add_tsum_nat_add' (k := n₀) (mod_cast sumΛn₀ n₀)]

  let n₁ := ⌊X * (1 + c₂ * ε)⌋₊

  have n₁_pos : 0 < n₁ := by
      dsimp only [n₁]
      apply Nat.le_floor
      rw[Nat.succ_eq_add_one, zero_add]
      norm_cast
      apply one_le_mul_of_one_le_of_one_le (by linarith)
      apply le_add_of_nonneg_right
      positivity

  have n₁_ge : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
    simp only [tsub_le_iff_right, n₁]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))

  have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
    simp only [n₁]
    exact Nat.floor_le (by bound)

  have n₁_ge_n₀ : n₀ ≤ n₁ := by
    have hn : (n₀ : ℝ) ≤ (n₁ : ℝ) := by linarith
    exact_mod_cast hn

  have n₁_sub_n₀ : (n₁ : ℝ) - n₀ ≤ X * ε * (c₂ + c₁) := by
    calc
      (n₁ : ℝ) - n₀ ≤ X * (1 + c₂ * ε) - n₀ := by
                        exact sub_le_sub_right n₁_le ↑n₀
       _            ≤ X * (1 + c₂ * ε) - (X * (1 - c₁ * ε)) := by
          exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε))
       _            = X * ε * (c₂ + c₁) := by ring

  have : (∑' (n : ℕ), Λ (n + n₀ : ) * F ((n + n₀ : ) / X)) =
    (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((n + n₀) / X)) +
    (∑' (n : ℕ), Λ (n + n₁ : ) * F ((n + n₁ : ) / X)) := by
    rw[← Summable.sum_add_tsum_nat_add' (k := n₁ - n₀)]
    congr! 5
    · simp only [Nat.cast_add]
    · omega
    · congr! 1
      norm_cast
      omega
    · convert (preTransparency := .instances) sumΛn₀ ((n₁ - n₀) + n₀) using 4
      · omega
      · congr! 1
        norm_cast
        omega

  rw [this]
  clear this

  have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = Λ (n₁) * F (↑n₁ / X) := by
    have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = Λ (n₁) * F (↑n₁ / X) + (∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X)) := by
      let fTemp := fun n ↦ Λ (n + n₁) * F ((↑n + ↑n₁) / X)
      have sum_fTemp : Summable fTemp := by exact sumΛn₀ n₁
      have hTemp (n : ℕ): fTemp n = Λ (n + n₁) * F (↑(n + n₁) / X) := by rw[Nat.cast_add]
      have : ∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X) = ∑' (n : ℕ), fTemp n := by exact Eq.symm (tsum_congr hTemp)
      rw[this]
      have (n : ℕ): fTemp (n + 1) = Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X) := by exact hTemp (n + 1)
      have : ∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X) = ∑' (n : ℕ), fTemp (n + 1) := by exact Eq.symm (tsum_congr this)
      rw[this]
      have : Λ n₁ * F (↑n₁ / X) = fTemp 0 := by
        dsimp only [fTemp]
        rw[← Nat.cast_add, zero_add]
      rw[this]
      exact Summable.tsum_eq_zero_add (sumΛn₀ n₁)
    rw[this]
    apply add_eq_left.mpr
    convert (preTransparency := .instances) tsum_zero with n
    have : n₁ ≤ n + (n₁) := by exact Nat.le_add_left (n₁) n
    convert (preTransparency := .instances) mul_zero _
    convert (preTransparency := .instances) smoothIs0 (n + 1 + n₁) ?_
    rw[← mul_le_mul_iff_left₀ X_pos]
    have : ↑(n + 1 + n₁) / X * X = ↑(n + 1 + n₁) := by field_simp
    rw[this]
    have : (1 + c₂ * ε) * X = 1 + (X * (1 + c₂ * ε) - 1) := by ring
    rw[this, Nat.cast_add, Nat.cast_add]
    exact add_le_add (by bound) n₁_ge

  rw [this]
  clear this

  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw[Nat.floor_add_one, Nat.cast_add, Nat.cast_one]
    have temp : X ≤ ↑⌈X⌉₊ := by exact Nat.le_ceil X
    have : (⌈X⌉₊ : ℝ) ≤ ↑⌊X⌋₊ + 1 := by exact_mod_cast Nat.ceil_le_floor_add_one X
    exact Preorder.le_trans X (↑⌈X⌉₊) (↑⌊X⌋₊ + 1) temp this
    positivity

  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := by exact Nat.floor_le (by positivity)

  have : ∑ x ∈ Finset.range ⌊X + 1⌋₊, Λ x =
      (∑ x ∈ Finset.range n₀, Λ x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + ↑n₀) := by
    simp only [add_comm _ n₀]
    rw [← Finset.sum_range_add, Nat.add_sub_of_le]
    dsimp only [n₀]
    refine Nat.ceil_le.mpr ?_
    exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X X_le_floor_add_one
  rw [this]
  clear this

  have : ∑ n ∈ Finset.range n₀, Λ n * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, Λ n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases n_zero : n = 0
    · rw [n_zero]
      simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    · convert (preTransparency := .instances) mul_one _
      convert (preTransparency := .instances) smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range, n₀] at hn
      have : (n < ⌈X * (1 - c₁ * ε)⌉₊) → (n ≤ ⌊X * (1 - c₁ * ε)⌋₊) := by
        intro n_lt
        by_contra hcontra

        rw[not_le] at hcontra

        have temp1: (⌊X * (1 - c₁ * ε)⌋₊).succ.succ ≤ n.succ := by
          apply Nat.succ_le_succ
          exact Nat.succ_le_of_lt hcontra
        have : n.succ ≤ ⌈X * (1 - c₁ * ε)⌉₊ := by exact Nat.succ_le_of_lt hn
        have temp2: ⌊X * (1 - c₁ * ε)⌋₊ + 2 = (⌊X * (1 - c₁ * ε)⌋₊ + 1) + 1 := by ring
        have : ⌊X * (1 - c₁ * ε)⌋₊ + 2 ≤ ⌈X * (1 - c₁ * ε)⌉₊ := by
          rw[temp2, ← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one]
          exact Nat.le_trans temp1 hn
        rw[← and_not_self_iff (⌊X * (1 - c₁ * ε)⌋₊ + 2 ≤ ⌈X * (1 - c₁ * ε)⌉₊), not_le]
        apply And.intro
        exact this
        rw[temp2, ← Nat.succ_eq_add_one, Nat.lt_succ_iff]
        exact Nat.ceil_le_floor_add_one (X * (1 - c₁ * ε))
      exact (Nat.le_floor_iff' n_zero).mp (this hn)

  rw [this, sub_eq_add_neg, add_assoc, add_assoc]
  nth_rewrite 3 [add_comm]
  nth_rewrite 2 [← add_assoc]
  rw [← add_assoc, ← add_assoc, ← sub_eq_add_neg]
  clear this

  have :
    ∑ n ∈ Finset.range n₀, Λ n + (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X)) -
      (∑ x ∈ Finset.range n₀, Λ x + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀))
      =
      (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X)) -
      (∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀)) := by
    ring
  rw [this]
  clear this

  have :
    ‖∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X) - ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀) + Λ n₁ * F (↑n₁ / X)‖
    ≤
    (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
      ‖Λ n₁‖ * ‖F (↑n₁ / X)‖:= by
    apply norm_add_le_of_le
    apply norm_sub_le_of_le
    apply norm_sum_le_of_le
    intro b hb
    exact norm_mul_le_of_le (by rfl) (by rfl)
    apply norm_sum_le_of_le
    intro b hb
    rfl
    exact_mod_cast norm_mul_le_of_le (by rfl) (by rfl)

  refine this.trans ?_

  clear this

  have vonBnd1 :
    ∀ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    intro n hn
    have n_add_n0_le_n1: (n : ℝ) + n₀ ≤ n₁ := by
      apply le_of_lt
      rw[Finset.mem_range] at hn
      rw[← add_lt_add_iff_right (-↑n₀), add_neg_cancel_right, add_comm, ← sub_eq_neg_add]
      exact_mod_cast hn
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
      apply ArithmeticFunction.vonMangoldt_nonneg
    have inter2: Real.log (↑n + ↑n₀) ≤ Real.log (↑n₁) := by exact_mod_cast Real.log_le_log (by positivity) n_add_n0_le_n1
    have inter3: Real.log (↑n₁) ≤ Real.log (X * (1 + c₂ * ε)) := by exact Real.log_le_log (by bound) (by linarith)
    exact inter1.trans (inter2.trans inter3)

  have bnd1 :
    ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖
    ≤ (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) := by
    have : (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) = (∑ n ∈ Finset.range (n₁ - n₀), Real.log (X * (1 + c₂ * ε))) := by
      rw[← Nat.cast_sub]
      nth_rewrite 1 [← Finset.card_range (n₁ - n₀)]
      rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
      exact Eq.symm (Finset.sum_const (Real.log (X * (1 + c₂ * ε))))
      exact n₁_ge_n₀
    rw [this]
    apply Finset.sum_le_sum
    intro n hn
    rw [← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul (vonBnd1 _ hn) _ (norm_nonneg _) (log_nonneg (by bound))
    rw[Real.norm_of_nonneg, ← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddAbove
    bound
    rw[← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound

  have bnd2 :
    ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤ (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) := by
    have : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) = (∑ n ∈ Finset.range (⌊X + 1⌋₊ - n₀), Real.log (X + 1)) := by
      rw[← Nat.cast_sub]
      nth_rewrite 1 [← Finset.card_range (⌊X + 1⌋₊ - n₀)]
      rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
      exact Eq.symm (Finset.sum_const (Real.log (X + 1)))
      simp only [Nat.ceil_le, n₀]
      exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X X_le_floor_add_one
    rw[this]
    apply Finset.sum_le_sum
    intro n hn
    have n_add_n0_le_X_add_one: (n : ℝ) + n₀ ≤ X + 1 := by
      rw[Finset.mem_range] at hn
      rw[← add_le_add_iff_right (-↑n₀), add_assoc, ← sub_eq_add_neg, sub_self, add_zero, ← sub_eq_add_neg]
      have temp: (n : ℝ) < ⌊X + 1⌋₊ - n₀ := by
        rw[← Nat.cast_sub, Nat.cast_lt]
        exact hn
        simp only [Nat.ceil_le, n₀]
        exact le_trans n₀_inside_le_X X_le_floor_add_one
      have : ↑⌊X + 1⌋₊ - ↑n₀ ≤ X + 1 - ↑n₀ := by
        apply sub_le_sub_right floor_X_add_one_le_self
      exact le_of_lt (lt_of_le_of_lt' this temp)
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
      apply ArithmeticFunction.vonMangoldt_nonneg
    apply le_trans inter1
    exact_mod_cast Real.log_le_log (by positivity) (n_add_n0_le_X_add_one)

  have largeSumBound := add_le_add bnd1 bnd2

  clear vonBnd1 bnd1 bnd2

  have inter1 : Real.log (X * (1 + c₂ * ε)) ≤ Real.log (3 * X) := by
    apply Real.log_le_log (by positivity)
    have const_le_2: 1 + c₂ * ε ≤ 3 := by
      have : (3 : ℝ) = 1 + 2 := by ring
      rw[this]
      apply add_le_add_right
      rw[← mul_one 2]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    rw[mul_comm]
    exact mul_le_mul const_le_2 (by rfl) (by positivity) (by positivity)

  have inter2 : (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) ≤ (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) := by
    apply mul_le_mul n₁_sub_n₀ _ (log_nonneg (by linarith)) (by positivity)
    rw[← Real.log_mul (by positivity) (by positivity)]
    nth_rewrite 3 [mul_comm]
    exact inter1

  have inter3 : (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) ≤ 2 * (X * ε * (c₂ + c₁)) * (Real.log (X)) := by
    nth_rewrite 3 [mul_assoc]
    rw[two_mul, mul_add]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by positivity) (by linarith)

  have inter4 : (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) ≤ 2 * (X * ε * (c₁ + c₂)) * (Real.log (X)) := by
    nth_rewrite 2 [add_comm]
    exact le_trans inter2 inter3

  clear inter2 inter3

  have inter6 : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) ≤ 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) := by
    apply mul_le_mul _ _ (log_nonneg (by linarith)) (by positivity)
    have : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)) := by ring
    rw[this]
    apply sub_le_sub
    have : X + 1 ≤ X * (1 + ε * c₁) := by
      ring_nf
      rw[add_comm, add_le_add_iff_left]
      exact X_bound_1
    exact le_trans floor_X_add_one_le_self this
    nth_rewrite 2 [mul_comm]
    exact n₀_gt
    rw[← Real.log_mul (by positivity) (by norm_num), mul_comm]
    exact Real.log_le_log (by positivity) (by linarith)

  have inter7: 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) ≤ 4 * (X * ε * c₁) * Real.log (X) := by
    have : (4 : ℝ) = 2 + 2 := by ring
    rw[this, mul_add]
    nth_rewrite 5 [mul_assoc]
    rw[add_mul]
    apply add_le_add
    nth_rewrite 1 [mul_assoc]
    rfl
    nth_rewrite 1 [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left <| Real.log_le_log (by positivity) (by linarith)
    positivity

  have inter9: (↑n₁ - ↑n₀) * Real.log (X * (1 + c₂ * ε)) + (↑⌊X + 1⌋₊ - ↑n₀) * Real.log (X + 1) ≤
    2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by
    have : 2 * (X * ε * (3 * c₁ + c₂)) = 2 * (X * ε * (c₁ + c₂)) + 4 * (X * ε * c₁) := by ring
    rw[this, add_mul]
    exact add_le_add inter4 <| le_trans inter6 inter7

  have largeSumBound2 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤
    2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by
    exact le_trans largeSumBound inter9

  clear largeSumBound inter4 inter9

  have inter2 : ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    rw[← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul _ _ (norm_nonneg _) (log_nonneg (by bound))
    rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact le_trans ArithmeticFunction.vonMangoldt_le_log <| Real.log_le_log (mod_cast n₁_pos) n₁_le
    rw[Real.norm_of_nonneg]
    apply smooth1BddAbove _ n₁_pos
    apply smooth1BddBelow _ n₁_pos

  have largeSumBound3 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) := by exact add_le_add largeSumBound2 (le_trans inter2 inter1)
  clear inter1 inter2 largeSumBound2

  have largeSumBound4 : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * (2 * Real.log X + Real.log (3)) := by
    nth_rewrite 2 [two_mul, add_assoc]
    rw [← Real.log_mul (by positivity) (by positivity), mul_comm X 3]
    apply le_trans largeSumBound3
    nth_rewrite 2 [mul_add]
    apply add_le_add_right
    nth_rewrite 1 [← one_mul (Real.log (3 * X))]
    apply mul_le_mul_of_nonneg_right _ (log_nonneg (by linarith))
    linarith

  clear largeSumBound3

  have largeSumBoundFinal : ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖ + ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
    ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ ≤ (6 * (X * ε * (3 * c₁ + c₂))) * Real.log (X) := by
    apply le_trans largeSumBound4
    rw[mul_add]
    have : (6 : ℝ) = 4 + 2 := by ring
    rw[this, add_mul, add_mul]
    apply add_le_add
    ring_nf
    rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by positivity) (by linarith)

  clear largeSumBound4

  rw[C_eq]
  linear_combination largeSumBoundFinal

open _root_.Filter Topology

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PairedDeficitPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedDeficitPositivity

open Filter Set
open scoped Topology

theorem mass_lower_bound {b : ℝ → ℝ} {l u m : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hc : ContinuousOn b (Icc l u)) (hbl : m ≤ b l)
    (hd : ∀ t ∈ Ioo l u, ∃ v, HasDerivAt (fun s => s * b s) v t ∧ m ≤ v) :
    m ≤ b u := by
  have hcM : ContinuousOn (fun s => s * b s) (Icc l u) := continuousOn_id.mul hc
  have hdM : DifferentiableOn ℝ (fun s => s * b s) (interior (Icc l u)) := by
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨v, hv, _⟩ := hd t ht
    exact hv.differentiableAt.differentiableWithinAt
  have hder : ∀ t ∈ interior (Icc l u), m ≤ deriv (fun s => s * b s) t := by
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨v, hv, hm⟩ := hd t ht
    simpa only [hv.deriv] using hm
  have h := (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv hcM hdM hder
    l ⟨le_rfl, hlu⟩ u ⟨hlu, le_rfl⟩ hlu
  have hbase : l * m ≤ l * b l := mul_le_mul_of_nonneg_left hbl hl.le
  have hu : 0 < u := lt_of_lt_of_le hl hlu
  nlinarith

theorem feedback_lower_bound_upto {b : ℝ → ℝ} {r m : ℝ} (hr : 0 < r)
    (hc : ContinuousOn b (Ici r))
    (hi : ∀ s ∈ Icc r (r + 1), m ≤ b s)
    (hd : ∀ s, r + 1 < s →
      ∃ v, HasDerivAt (fun t => t * b t) v s ∧ b (s - 1) ≤ v)
    (n : ℕ) : ∀ s ∈ Icc r (r + 1 + n), m ≤ b s := by
  induction n with
  | zero => simpa using hi
  | succ n ih =>
    intro s hs
    by_cases hsn : s ≤ r + 1 + n
    · exact ih s ⟨hs.1, hsn⟩
    · have hbase : r + 1 + n < s := lt_of_not_ge hsn
      apply mass_lower_bound (l := r + 1 + n) (by positivity) hbase.le
      · exact hc.mono (fun t ht => by change r ≤ t; linarith [ht.1])
      · exact ih _ ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], le_rfl⟩
      · intro t ht
        obtain ⟨v, hv, hvb⟩ := hd t (by linarith [ht.1, Nat.cast_nonneg (α := ℝ) n])
        refine ⟨v, hv, le_trans (ih (t - 1) ⟨?_, ?_⟩) hvb⟩
        · linarith [ht.1, Nat.cast_nonneg (α := ℝ) n]
        · push_cast at hs
          linarith [ht.2, hs.2]

theorem feedback_lower_bound {b : ℝ → ℝ} {r m : ℝ} (hr : 0 < r)
    (hc : ContinuousOn b (Ici r))
    (hi : ∀ s ∈ Icc r (r + 1), m ≤ b s)
    (hd : ∀ s, r + 1 < s →
      ∃ v, HasDerivAt (fun t => t * b t) v s ∧ b (s - 1) ≤ v)
    {s : ℝ} (hs : r ≤ s) : m ≤ b s := by
  obtain ⟨n, hn⟩ := exists_nat_ge (s - r - 1)
  exact feedback_lower_bound_upto hr hc hi hd n s ⟨hs, by linarith⟩

theorem feedback_not_tendsto_zero {b d : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn b (Ici r)) (hz : b r = 0)
    (hi : ∀ s ∈ Ioc r (r + 1), 0 < b s)
    (hp : ∀ s, r < s → 0 < d s)
    (hd : ∀ s, r + 1 < s →
      HasDerivAt (fun t => t * b t) (b (s - 1) + d (s - 1)) s) :
    ¬ Tendsto b atTop (𝓝 0) := by
  have hder : ∀ s, r + 1 < s →
      ∃ v, HasDerivAt (fun t => t * b t) v s ∧ b (s - 1) ≤ v := by
    intro s hs
    exact ⟨_, hd s hs, by linarith [hp (s - 1) (by linarith)]⟩
  have hn : ∀ s, r ≤ s → 0 ≤ b s := by
    apply fun s hs => feedback_lower_bound hr hc ?_ hder hs
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · simp [← h, hz]
    · exact (hi s ⟨h, hs.2⟩).le
  have hpos : ∀ s ∈ Icc (r + 1) (r + 2), 0 < b s := by
    intro s hs
    have hmono : StrictMonoOn (fun t => t * b t) (Icc (r + 1) s) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (continuousOn_id.mul (hc.mono (by intro t ht; change r ≤ t; linarith [ht.1])))
      intro t ht
      rw [interior_Icc] at ht
      change 0 < deriv (fun t => t * b t) t
      rw [(hd t ht.1).deriv]
      exact add_pos_of_nonneg_of_pos (hn _ (by linarith [ht.1])) (hp _ (by linarith [ht.1]))
    have hmass : (r + 1) * b (r + 1) ≤ s * b s :=
      hmono.monotoneOn ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
    have hfirst : 0 < b (r + 1) := hi _ ⟨by linarith, le_rfl⟩
    have hstart : 0 < (r + 1) * b (r + 1) := mul_pos (by linarith) hfirst
    have hspos : 0 < s := by linarith [hs.1]
    nlinarith
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_forall_le'
    (hc.mono (by intro t ht; change r ≤ t; linarith [ht.1])) hpos
  have htail : ∀ s, r + 1 ≤ s → m ≤ b s := by
    intro s hs
    apply feedback_lower_bound (r := r + 1) (by linarith)
      (hc.mono (by intro t ht; change r ≤ t; exact le_trans (by linarith) ht)) ?_ ?_ hs
    · simpa only [add_assoc, one_add_one_eq_two] using hmin
    · intro t ht
      exact hder t (by linarith)
  intro hlim
  have hevent : ∀ᶠ s in atTop, b s < m := (tendsto_order.mp hlim).2 m hm
  obtain ⟨s, hs, hsm⟩ := (hevent.and (eventually_ge_atTop (r + 1))).exists
  exact (not_lt_of_ge (htail s hsm)) hs

theorem first_zero_of_nonpos {z : ℝ → ℝ} (hc : ContinuousOn z (Ici 1))
    (hi : ∀ s ∈ Icc 1 2, 0 < z s) {S : ℝ} (hS : 1 ≤ S) (hzS : z S ≤ 0) :
    ∃ r, 2 < r ∧ z r = 0 ∧ ∀ s ∈ Ico 1 r, 0 < z s := by
  have h2 : 0 < z 2 := hi _ ⟨by norm_num, le_rfl⟩
  have hS2 : 2 < S := by
    by_contra h
    exact (not_lt_of_ge hzS) (hi S ⟨hS, le_of_not_gt h⟩)
  let Z : Set ℝ := Icc 2 S ∩ z ⁻¹' {0}
  have hcont : ContinuousOn z (Icc 2 S) := hc.mono (by intro t ht; change 1 ≤ t; linarith [ht.1])
  have hcompact : IsCompact Z := isCompact_Icc.of_isClosed_subset
    (hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨t, ht, hzt⟩ := intermediate_value_Icc' hS2.le hcont ⟨hzS, h2.le⟩
  have hne : Z.Nonempty := ⟨t, ht, hzt⟩
  obtain ⟨r, hr⟩ := hcompact.exists_isLeast hne
  have hr2 : 2 ≤ r := hr.1.1.1
  have hrS : r ≤ S := hr.1.1.2
  have hzr : z r = 0 := hr.1.2
  have hr2' : 2 < r := lt_of_le_of_ne hr2 (by intro h; subst r; linarith)
  refine ⟨r, hr2', hzr, ?_⟩
  intro s hs
  by_cases hs2 : s ≤ 2
  · exact hi s ⟨hs.1, hs2⟩
  · by_contra h
    have hz : z s ≤ 0 := le_of_not_gt h
    have hcs : ContinuousOn z (Icc 2 s) := hc.mono (by intro t ht; change 1 ≤ t; linarith [ht.1])
    obtain ⟨t, ht, hzt⟩ := intermediate_value_Icc' (le_of_not_ge hs2) hcs ⟨hz, h2.le⟩
    have htr : r ≤ t := hr.2 ⟨⟨ht.1, by linarith [ht.2, hs.2]⟩, hzt⟩
    linarith [ht.2, hs.2]

theorem no_first_zero {a c : ℝ → ℝ} {r : ℝ} (hr : 2 < r)
    (ha : ContinuousOn a (Ici 1)) (har : a r = 0)
    (hcprev : ∀ s ∈ Ico 1 r, 0 < c s)
    (hsum : ∀ s, 1 ≤ s → 0 < a s + c s)
    (hd : ∀ s, 2 < s → HasDerivAt (fun t => t * a t) (-c (s - 1)) s)
    (hlim : Tendsto a atTop (𝓝 0)) : False := by
  let b : ℝ → ℝ := fun s => -a s
  have hbc : ContinuousOn b (Ici r) := ha.neg.mono (by intro t ht; change 1 ≤ t; exact le_trans (by linarith) ht)
  have hbder : ∀ s, 2 < s → HasDerivAt (fun t => t * b t) (c (s - 1)) s := by
    intro s hs
    convert! (hd s hs).neg using 1 <;> simp [b]
    rfl
  have hbi : ∀ s ∈ Ioc r (r + 1), 0 < b s := by
    intro s hs
    have hm : StrictMonoOn (fun t => t * b t) (Icc r s) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (continuousOn_id.mul (hbc.mono (fun _ ht => ht.1)))
      intro t ht
      rw [interior_Icc] at ht
      change 0 < deriv (fun t => t * b t) t
      rw [(hbder t (by linarith [ht.1])).deriv]
      exact hcprev _ ⟨by linarith [ht.1], by linarith [ht.2, hs.2]⟩
    have hmass := hm ⟨le_rfl, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ hs.1
    have hbr : b r = 0 := by simp [b, har]
    change r * b r < s * b s at hmass
    rw [hbr, mul_zero] at hmass
    exact (mul_pos_iff_of_pos_left (by linarith [hs.1] : 0 < s)).mp hmass
  apply feedback_not_tendsto_zero (d := fun s => a s + c s) (by linarith) hbc
    (by simp [b, har]) hbi (fun s hs => hsum s (by linarith)) ?_
  · simpa only [b, neg_zero] using hlim.neg
  · intro s hs
    convert! hbder s (by linarith) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [b]
    ring

theorem paired_pos {a c : ℝ → ℝ}
    (ha : ContinuousOn a (Ici 1)) (hc : ContinuousOn c (Ici 1))
    (hai : ∀ s ∈ Icc 1 2, 0 < a s) (hci : ∀ s ∈ Icc 1 2, 0 < c s)
    (hsum : ∀ s, 1 ≤ s → 0 < a s + c s)
    (hda : ∀ s, 2 < s → HasDerivAt (fun t => t * a t) (-c (s - 1)) s)
    (hdc : ∀ s, 2 < s → HasDerivAt (fun t => t * c t) (-a (s - 1)) s)
    (hla : Tendsto a atTop (𝓝 0)) (hlc : Tendsto c atTop (𝓝 0)) :
    ∀ s, 1 ≤ s → 0 < a s ∧ 0 < c s := by
  intro S hS
  by_contra h
  have hbad : min (a S) (c S) ≤ 0 := by
    exact le_of_not_gt (fun hpos => h (lt_min_iff.mp hpos))
  obtain ⟨r, hr, hzero, hpre⟩ := first_zero_of_nonpos (ha.inf hc)
    (fun s hs => lt_min (hai s hs) (hci s hs)) hS hbad
  by_cases harc : a r ≤ c r
  · have har : a r = 0 := by simpa only [min_eq_left harc] using hzero
    exact no_first_zero hr ha har (fun s hs => (lt_min_iff.mp (hpre s hs)).2) hsum hda hla
  · have hcr : c r = 0 := by simpa only [min_eq_right (le_of_not_ge harc)] using hzero
    exact no_first_zero hr hc hcr (fun s hs => (lt_min_iff.mp (hpre s hs)).1)
      (fun s hs => by simpa only [add_comm] using hsum s hs) hdc hlc

end NumberTheoryLean.PairedDeficitPositivity

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PVIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Real Set MeasureTheory Filter Topology Finset
open scoped NNReal ENNReal

lemma integrableOn_one_sub_exp_neg_div :
    IntegrableOn (fun t => (1 - exp (-t)) / t) (Ioc 0 1) := by

  have h_bound : ∀ t ∈ Set.Ioc 0 1, (1 - Real.exp (-t)) / t ≤ 1 := by
    exact fun t ht => by rw [ div_le_iff₀ ht.1 ] ; linarith [ Real.add_one_le_exp ( -t ) ] ;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  exacts [ fun t => 1, by norm_num, by exact Measurable.aestronglyMeasurable ( by exact Measurable.div ( measurable_const.sub ( Real.continuous_exp.measurable.comp ( measurable_neg ) ) ) measurable_id' ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun t ht => by rw [ Real.norm_of_nonneg ( div_nonneg ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by linarith [ ht.1, ht.2 ] ) ht.1.le ) ] ; exact h_bound t ht ]

lemma integrableOn_exp_neg_div_Ioi :
    IntegrableOn (fun t => exp (-t) / t) (Ioi 1) := by

  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 1) := by
    exact MeasureTheory.IntegrableOn.mono_set ( by exact MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero ) ) ( Set.Ioi_subset_Ioi zero_le_one );
  refine' h_integrable.mono' _ _;
  · exact ContinuousOn.aestronglyMeasurable ( fun t ht => ContinuousAt.continuousWithinAt ( by exact ContinuousAt.div ( ContinuousAt.rexp ( continuousAt_id.neg ) ) continuousAt_id ( by linarith [ ht.out ] ) ) ) measurableSet_Ioi;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( Real.exp_pos _ |> le_of_lt ) ( by linarith [ hx.out ] ) ) ] ; exact div_le_self ( Real.exp_pos _ |> le_of_lt ) ( by linarith [ hx.out ] ) ;

lemma tendsto_integral_one_sub_exp_neg_div :
    Tendsto (fun ε => ∫ t in ε..1, (1 - exp (-t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in (0:ℝ)..1, (1 - exp (-t)) / t)) := by

  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Set.Ioc 0 1) := by
    exact integrableOn_one_sub_exp_neg_div;

  have h_cont : ContinuousOn (fun ε => ∫ t in (ε)..1, (1 - Real.exp (-t)) / t) (Set.Icc 0 1) := by
    have h_cont : ContinuousOn (fun ε => ∫ t in (1 : ℝ)..ε, (1 - Real.exp (-t)) / t) (Set.Icc 0 1) := by
      intro ε hε; apply_rules [ intervalIntegral.continuousWithinAt_primitive ] ; aesop;
      rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le ] <;> aesop;
    exact ContinuousOn.congr ( h_cont.fun_neg ) fun x hx => by rw [ ← intervalIntegral.integral_symm ] ;
  have := h_cont 0 ( by norm_num );
  convert this.tendsto.mono_left _ using 2 <;> first | (with_reducible_and_instances rfl) | (norm_num [ Set.Ioi_subset_Ici_self ];)
  exact nhdsWithin_mono _ <| Set.Ioi_subset_Ici_self

lemma eulerMascheroni_eq_integral :
    eulerMascheroniConstant =
      (∫ t in (0:ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1:ℝ), exp (-t) / t := by

  have h_gamma_deriv : Real.eulerMascheroniConstant = -∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t := by
    have h_gamma_deriv : deriv Real.Gamma 1 = ∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t := by

      have h_gamma_deriv : deriv Real.Gamma 1 = ∫ t in Set.Ioi 0, t^0 * Real.exp (-t) * Real.log t := by
        have h_def : ∀ s > 0, Real.Gamma s = ∫ t in Set.Ioi 0, t^(s-1) * Real.exp (-t) := by
          exact fun s hs => by rw [ Real.Gamma_eq_integral hs ] ; congr; ext; ring;

        have h_dominated : Filter.Tendsto (fun h => ∫ t in Set.Ioi 0, (t^h - 1) / h * Real.exp (-t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t in Set.Ioi 0, Real.log t * Real.exp (-t))) := by

          have h_dominate : ∀ h ∈ Set.Ioo 0 1, ∀ t ∈ Set.Ioi 0, abs ((t^h - 1) / h * Real.exp (-t)) ≤ abs (Real.log t) * Real.exp (-t) * (t + 1) := by
            intros h hh t ht
            have h_abs : abs ((t^h - 1) / h) ≤ abs (Real.log t) * (t + 1) := by

              obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 h, t^h - 1 = h * t^c * Real.log t := by

                have h_mean_value : ∃ c ∈ Set.Ioo 0 h, deriv (fun x => t^x) c = (t^h - 1) / h := by
                  have := exists_deriv_eq_slope ( f := fun x => t ^ x ) hh.1;
                  simpa using this ( continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow continuousAt_const continuousAt_id <| Or.inl <| by linarith [ ht.out ] ) ( fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by exact DifferentiableAt.rpow ( differentiableAt_const _ ) differentiableAt_id <| by linarith [ ht.out ] );
                norm_num [ Real.rpow_def_of_pos ht, mul_assoc, mul_comm, mul_left_comm ] at *;
                exact h_mean_value.imp fun x hx => ⟨ hx.1, by rw [ hx.2, mul_div_cancel₀ _ hh.1.ne' ] ⟩;
              by_cases h_zero : h = 0 <;> simp_all +decide [ abs_mul, mul_assoc, mul_comm ];
              by_cases h₂ : t ≤ 1;
              · exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.rpow_nonneg ht.le _ ) ] ; exact le_trans ( Real.rpow_le_one ht.le h₂ ( by linarith ) ) ( by linarith ) ) ( abs_nonneg _ );
              · exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.rpow_nonneg ht.le _ ) ] ; exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show c ≤ 1 by linarith ) ) ( by norm_num ) ) ( abs_nonneg _ );
            rw [ abs_mul, abs_of_nonneg ( Real.exp_pos _ |> LT.lt.le ) ] ; nlinarith [ Real.exp_pos ( -t ) ];

          have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t) * (t + 1)) (Set.Ioi 0) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t) * t) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t) * abs (Real.log t)) (Set.Ioi 0) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t) * abs (Real.log t)) (Set.Ioc 0 1) := by
                  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * abs (Real.log t)) (Set.Ioc 0 1) := by
                    have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.log t) (Set.Ioc 0 1) := by
                      exact Continuous.integrableOn_Ioc ( Real.continuous_mul_log );
                    refine' h_integrable.norm.congr _;
                    filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1.le ] ;
                  refine' h_integrable.mono' _ _;
                  · exact MeasureTheory.AEStronglyMeasurable.mul ( MeasureTheory.AEStronglyMeasurable.mul ( measurable_id.aestronglyMeasurable ) ( Real.continuous_exp.comp_aestronglyMeasurable ( measurable_neg.aestronglyMeasurable ) ) ) ( Real.measurable_log.norm.aestronglyMeasurable );
                  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg ht.1.le ( Real.exp_nonneg _ ) ) ( abs_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_right ( mul_le_of_le_one_right ht.1.le ( Real.exp_le_one_iff.mpr ( neg_nonpos.mpr ht.1.le ) ) ) ( abs_nonneg _ ) ;
                have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t) * abs (Real.log t)) (Set.Ioi 1) := by
                  have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t) * t) (Set.Ioi 1) := by
                    have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t^2 * Real.exp (-t)) (Set.Ioi 1) := by
                      have h_gamma : ∫ t in Set.Ioi 0, t^2 * Real.exp (-t) = Real.Gamma 3 := by
                        rw [ h_def ] <;> norm_num;
                      exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_gamma; rw [ MeasureTheory.integral_undef h_gamma ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one );
                    exact h_integrable.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
                  refine' h_integrable.mono' _ _;
                  · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( measurable_id.mul ( Real.continuous_exp.measurable.comp measurable_neg ) ) ( Real.measurable_log.norm ) );
                  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg ( by linarith [ ht.out ] ) ( Real.exp_nonneg _ ) ) ( abs_nonneg _ ) ) ] ; exact mul_le_mul_of_nonneg_left ( by rw [ abs_of_nonneg ( Real.log_nonneg ( by linarith [ ht.out ] ) ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ ht.out ] ) ) ( by linarith [ ht.out ] ) ) ( mul_nonneg ( by linarith [ ht.out ] ) ( Real.exp_nonneg _ ) ) ;
                convert MeasureTheory.IntegrableOn.union ‹IntegrableOn ( fun t : ℝ => t * Real.exp ( -t ) * |log t| ) ( Set.Ioc 0 1 ) volume› ‹IntegrableOn ( fun t : ℝ => t * Real.exp ( -t ) * |log t| ) ( Set.Ioi 1 ) volume› using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num;)
              exact h_integrable.congr_fun ( fun x hx => by ring ) measurableSet_Ioi;
            have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t)) (Set.Ioi 0) := by
              have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t)) (Set.Ioc 0 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t)) (Set.Ioc 0 1) := by
                  have h_integrable : ∫ t in Set.Ioc 0 1, abs (Real.log t) = 1 := by
                    rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => abs_of_nonpos ( Real.log_nonpos hx.1.le hx.2 ), ← intervalIntegral.integral_of_le ] <;> norm_num;
                  exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; norm_num );
                refine' h_integrable.mono' _ _;
                · exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable.aestronglyMeasurable ) ( Continuous.aestronglyMeasurable ( by continuity ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( Real.exp_le_one_iff.mpr <| neg_nonpos.mpr ht.1.le ) <| abs_nonneg <| Real.log t;
              have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => abs (Real.log t) * Real.exp (-t)) (Set.Ioi 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Set.Ioi 1) := by
                  have := @integral_rpow_mul_exp_neg_rpow 1;
                  specialize @this 1 ; norm_num at this;
                  exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; norm_num ) ) ) ) ) ) ( Set.Ioi_subset_Ioi zero_le_one );
                refine' h_integrable.mono' _ _;
                · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Real.measurable_log.norm ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_right ( by rw [ abs_of_nonneg ( Real.log_nonneg ht.out.le ) ] ; exact le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ ht.out ] ) ) ( by linarith [ ht.out ] ) ) ( by positivity ) ;
              convert MeasureTheory.IntegrableOn.union ‹IntegrableOn ( fun t : ℝ => |Real.log t| * Real.exp ( -t ) ) ( Set.Ioc 0 1 ) volume› ‹IntegrableOn ( fun t : ℝ => |Real.log t| * Real.exp ( -t ) ) ( Set.Ioi 1 ) volume› using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num;)
            simp_all +decide [ mul_add ];
            exact MeasureTheory.Integrable.add ‹_› ‹_›;
          refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
          refine' fun t => |Real.log t| * Real.exp ( -t ) * ( t + 1 );
          · filter_upwards [ self_mem_nhdsWithin ] with n hn using Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Measurable.div_const ( by exact Measurable.sub ( measurable_id.pow_const _ ) measurable_const ) _ ) ( Real.continuous_exp.measurable.comp measurable_neg ) );
          · filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with h hh using Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) fun t ht => h_dominate h hh t ht;
          · exact h_integrable;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;
            refine' Filter.Tendsto.mul _ tendsto_const_nhds;
            simpa [ div_eq_inv_mul, Real.rpow_def_of_pos ht ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.sub ( HasDerivAt.exp ( HasDerivAt.const_mul ( Real.log t ) ( hasDerivAt_id 0 ) ) ) ( hasDerivAt_const 0 1 ) );

        have h_deriv : Filter.Tendsto (fun h => (Real.Gamma (1 + h) - Real.Gamma 1) / h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv Real.Gamma 1)) := by
          have h_deriv : HasDerivAt Real.Gamma (deriv Real.Gamma 1) 1 := by
            exact DifferentiableAt.hasDerivAt ( Real.differentiableAt_Gamma fun m => by linarith );
          simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero_right;

        have h_gamma_def : ∀ h > 0, (Real.Gamma (1 + h) - Real.Gamma 1) / h = ∫ t in Set.Ioi 0, (t^h - 1) / h * Real.exp (-t) := by
          intro h hh; rw [ h_def ( 1 + h ) ( by linarith ), h_def 1 zero_lt_one ] ; simp +decide [ sub_mul, div_mul_eq_mul_div, MeasureTheory.integral_div ] ;
          rw [ MeasureTheory.integral_sub ] <;> norm_num [ integral_exp_Iic ];
          · have := @integral_rpow_mul_exp_neg_rpow 1;
            exact ( by have := @this h ( by norm_num ) ( by linarith ) ; exact ( by contrapose! this; rw [ MeasureTheory.integral_undef ( by aesop ) ] ; positivity ) );
          · exact MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero );
        simpa [ mul_assoc, mul_comm, mul_left_comm ] using tendsto_nhds_unique h_deriv ( h_dominated.congr' <| Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => h_gamma_def x hx ▸ rfl );
      aesop;
    rw [ ← h_gamma_deriv, Real.eulerMascheroniConstant_eq_neg_deriv ];

  have h_split : ∫ t in Set.Ioi 0, Real.exp (-t) * Real.log t = (∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t) + (∫ t in Set.Ioi 1, Real.exp (-t) * Real.log t) := by
    rw [ ← MeasureTheory.setIntegral_union ] <;> norm_num;
    · have h_integrable : MeasureTheory.IntegrableOn (fun t => Real.log t) (Set.Ioc 0 1) := by
        rw [ ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one ];
        norm_num +zetaDelta at *;
      refine' h_integrable.norm.mono' _ _;
      · exact MeasureTheory.AEStronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) ) h_integrable.aestronglyMeasurable;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ norm_mul, Real.norm_of_nonneg ( Real.exp_pos _ |> le_of_lt ) ] ; exact mul_le_of_le_one_left ( norm_nonneg _ ) ( Real.exp_le_one_iff.mpr <| by linarith [ hx.1, hx.2 ] ) ;
    ·
      have h_conv : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t) * t) (Set.Ioi 1) := by
        have h_integrable : ∫ t in Set.Ioi 0, Real.exp (-t) * t = Real.Gamma 2 := by
          rw [ Real.Gamma_eq_integral ] <;> norm_num;
        exact MeasureTheory.IntegrableOn.mono_set ( by exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity ) ) ( Set.Ioi_subset_Ioi zero_le_one );
      refine' h_conv.mono' _ _;
      · exact ContinuousOn.aestronglyMeasurable ( fun t ht => ContinuousAt.continuousWithinAt ( by exact ContinuousAt.mul ( ContinuousAt.rexp ( continuousAt_id.neg ) ) ( Real.continuousAt_log ( by linarith [ ht.out ] ) ) ) ) measurableSet_Ioi;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_eq_abs, abs_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( Real.log_nonneg ht.out.le ) ) ] ; exact mul_le_mul_of_nonneg_left ( le_trans ( Real.log_le_sub_one_of_pos ( zero_lt_one.trans ht.out ) ) ( by linarith ) ) ( Real.exp_pos _ |> le_of_lt ) ;

  have h_log_zero_one : ∫ t in Set.Ioc 0 1, Real.exp (-t) * Real.log t = -∫ t in Set.Ioc 0 1, ∫ s in t..1, Real.exp (-t) / s := by
    have h_log_zero_one : ∀ t ∈ Set.Ioc 0 1, Real.log t = -∫ s in t..1, 1 / s := by
      intro t ht; rw [ integral_one_div_of_pos ] <;> aesop;
    rw [ ← MeasureTheory.integral_neg ] ; exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ h_log_zero_one x hx ] ; simp +decide [ div_eq_mul_inv, mul_comm ] ;

  have h_fubini : ∫ t in Set.Ioc 0 1, ∫ s in t..1, Real.exp (-t) / s = ∫ s in Set.Ioc 0 1, ∫ t in Set.Ioc 0 s, Real.exp (-t) / s := by
    have h_fubini : ∫ t in Set.Ioc 0 1, ∫ s in t..1, Real.exp (-t) / s = ∫ t in Set.Ioc 0 1, ∫ s in Set.Ioc 0 1, (if t ≤ s then Real.exp (-t) / s else 0) := by
      refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => _;
      rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
      rw [ intervalIntegral.integral_of_le ht.2 ];
      rw [ ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
      grind;
    rw [ h_fubini, ← MeasureTheory.integral_integral_swap ];
    · norm_num [ ← MeasureTheory.integral_indicator, Set.indicator_apply ];
      grind +splitImp;
    · rw [ MeasureTheory.integrable_prod_iff ];
      · field_simp;
        constructor;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx;
          refine' MeasureTheory.Integrable.indicator _ _;
          · exact Continuous.integrableOn_Ioc ( by exact Continuous.div_const ( Real.continuous_exp.comp <| ContinuousNeg.continuous_neg ) _ );
          · exact measurableSet_Iic;
        · refine' MeasureTheory.Integrable.congr _ _;
          use fun x => ∫ y in Set.Ioc 0 x, Real.exp ( -y ) / x;
          ·
            have h_inner : ∀ x ∈ Set.Ioc 0 1, ∫ y in Set.Ioc 0 x, Real.exp (-y) / x = (1 - Real.exp (-x)) / x := by
              intro x hx; rw [ ← intervalIntegral.integral_of_le hx.1.le ] ; norm_num [ intervalIntegral.integral_comp_neg ] ;
            rw [ MeasureTheory.integrable_congr ( Filter.eventuallyEq_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun x hx => h_inner x hx ) ];
            refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun x => 1;
            · norm_num;
            · exact ContinuousOn.aestronglyMeasurable ( fun x hx => ContinuousAt.continuousWithinAt ( by exact ContinuousAt.div ( continuousAt_const.sub ( Real.continuous_exp.continuousAt.comp ( ContinuousAt.neg continuousAt_id ) ) ) continuousAt_id ( ne_of_gt hx.1 ) ) ) measurableSet_Ioc;
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using by rw [ Real.norm_of_nonneg ( div_nonneg ( sub_nonneg.2 <| Real.exp_le_one_iff.2 <| by linarith [ hx.1, hx.2 ] ) hx.1.le ) ] ; exact div_le_one_of_le₀ ( by linarith [ hx.1, hx.2, Real.add_one_le_exp ( -x ) ] ) hx.1.le;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx;
            rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
            congr with y ; split_ifs <;> norm_num;
            · rw [ abs_of_nonneg ( div_nonneg ( Real.exp_nonneg _ ) hx.1.le ) ];
            · grind +revert;
            · grind;
            · aesop;
      · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ( measurableSet_le measurable_snd measurable_fst ) ( by exact Measurable.div ( Real.continuous_exp.measurable.comp ( measurable_neg.comp measurable_snd ) ) measurable_fst ) measurable_const );

  have h_log_one_infty : ∫ t in Set.Ioi 1, Real.exp (-t) * Real.log t = ∫ t in Set.Ioi 1, ∫ s in (1 : ℝ)..t, Real.exp (-t) / s := by
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
    norm_num [ div_eq_mul_inv, ht.out.le ];

  have h_fubini_one_infty : ∫ t in Set.Ioi 1, ∫ s in (1 : ℝ)..t, Real.exp (-t) / s = ∫ s in Set.Ioi 1, ∫ t in Set.Ioi s, Real.exp (-t) / s := by
    have h_fubini_one_infty : ∫ t in Set.Ioi 1, ∫ s in (1 : ℝ)..t, Real.exp (-t) / s = ∫ s in Set.Ioi 1, ∫ t in Set.Ioi 1, Real.exp (-t) / s * (if s ≤ t then 1 else 0) := by
      rw [ ← MeasureTheory.integral_integral_swap ];
      · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => _;
        rw [ intervalIntegral.integral_of_le ht.out.le, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        simp only [ ← ite_and ];
      · rw [ MeasureTheory.integrable_prod_iff ];
        · constructor;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht;

            have h_integrable : MeasureTheory.IntegrableOn (fun y => Real.exp (-t) / y) (Set.Ioc 1 t) := by
              exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const continuousAt_id <| by linarith [ hx.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
            rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ioc ) ] at h_integrable;
            rw [ MeasureTheory.integrable_congr ];
            convert h_integrable.restrict;
            filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with y hy using by rw [ Set.indicator_apply ] ; aesop;
          · refine' MeasureTheory.Integrable.congr _ _;
            use fun x => ∫ y in Set.Ioc 1 x, Real.exp ( -x ) / y;
            ·
              have h_inner : ∀ x ∈ Set.Ioi 1, ∫ y in Set.Ioc 1 x, Real.exp (-x) / y = Real.exp (-x) * Real.log x := by
                intro x hx; rw [ ← intervalIntegral.integral_of_le hx.out.le ] ; norm_num [ div_eq_mul_inv, hx.out.le ] ;
              rw [ MeasureTheory.integrable_congr ( Filter.eventuallyEq_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioi ) h_inner ) ];
              have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * x) (Set.Ioi 1) := by
                have h_integrable : MeasureTheory.IntegrableOn (fun x => Real.exp (-x) * x) (Set.Ioi 0) := by
                  have h_integrable : ∫ x in Set.Ioi 0, Real.exp (-x) * x = Real.Gamma 2 := by
                    rw [ Real.Gamma_eq_integral ] <;> norm_num;
                  exact ( by contrapose! h_integrable; rw [ MeasureTheory.integral_undef h_integrable ] ; positivity );
                exact h_integrable.mono_set <| Set.Ioi_subset_Ioi zero_le_one;
              refine' h_integrable.mono' _ _;
              · exact MeasureTheory.AEStronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) ) ( Real.measurable_log.aestronglyMeasurable );
              · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx using by rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( Real.log_nonneg hx.out.le ) ) ] ; exact mul_le_mul_of_nonneg_left ( le_trans ( Real.log_le_sub_one_of_pos ( zero_lt_one.trans hx.out ) ) ( by linarith ) ) ( Real.exp_pos _ |> le_of_lt ) ;
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with x hx;
              rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
              congr with y ; split_ifs <;> norm_num;
              · rw [ abs_of_nonneg ( div_nonneg ( Real.exp_nonneg _ ) ( by linarith ) ) ];
              · linarith;
              · grind +revert;
              · grind +qlia;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( by exact Measurable.mul ( Real.continuous_exp.measurable.comp ( measurable_neg.comp measurable_fst ) ) ( measurable_snd.inv ) ) ( by exact Measurable.ite ( measurableSet_le measurable_snd measurable_fst ) measurable_const measurable_const ) );
    rw [ h_fubini_one_infty ];
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s hs => _;
    rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ];
    simp +decide [ Set.indicator ];
    rw [ ← MeasureTheory.integral_congr_ae ];
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton s ) ] with x hx using by split_ifs <;> cases lt_or_gt_of_ne hx <;> linarith [ hs.out ] ;
  simp_all +decide [ div_eq_mul_inv, ← intervalIntegral.integral_of_le zero_le_one ];
  rw [ intervalIntegral.integral_of_le zero_le_one ] ; norm_num [ MeasureTheory.integral_mul_const, integral_exp_neg_Ioi ] ; ring_nf;
  norm_num [ integral_exp_Iic, ← intervalIntegral.integral_of_le zero_le_one ] ; ring_nf;
  rw [ intervalIntegral.integral_of_le zero_le_one ] ; rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by rw [ ← intervalIntegral.integral_of_le hx.1.le ] ] ; norm_num [ intervalIntegral.integral_comp_neg ] ; ring_nf;
  rw [ intervalIntegral.integral_of_le zero_le_one ]

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ExponentialIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Real Set MeasureTheory Filter Topology
open scoped Interval

namespace ErdosAverageCertificates

noncomputable section

theorem exponentialIntegral_log_limit :
    Tendsto
      (fun s : ℝ ↦ Real.log s +
        ∫ t in Set.Ioi s, Real.exp (-t) / t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-Real.eulerMascheroniConstant)) := by
  have hbase := tendsto_integral_one_sub_exp_neg_div
  have htail : Tendsto
      (fun _s : ℝ ↦ ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t)) :=
    tendsto_const_nhds
  have hlim := hbase.neg.add htail
  have htarget :
      -(∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) +
          ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t =
        -Real.eulerMascheroniConstant := by
    rw [eulerMascheroni_eq_integral]
    ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with s hs0 hs1
  have hs : 0 < s := hs0
  have hsle : s ≤ 1 := hs1.le
  have hfinite : IntervalIntegrable
      (fun t : ℝ ↦ Real.exp (-t) / t) volume s 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact (continuous_exp.comp continuous_neg).continuousOn
    · exact continuousOn_id
    · intro t ht
      have ht' := Set.mem_uIcc.mp ht
      rcases ht' with ht' | ht'
      · change t ≠ 0
        linarith
      · change t ≠ 0
        linarith
  have hone : IntervalIntegrable (fun t : ℝ ↦ 1 / t) volume s 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    have ht' := Set.mem_uIcc.mp ht
    rcases ht' with ht' | ht'
    · change t ≠ 0
      linarith
    · change t ≠ 0
      linarith
  have hsplitSet : Set.Ioi s = Set.Ioc s 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi hsle).symm
  have hdisj : Disjoint (Set.Ioc s 1) (Set.Ioi 1) :=
    Set.Ioc_disjoint_Ioi_same
  have htailInt : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-t) / t) (Set.Ioi 1) :=
    integrableOn_exp_neg_div_Ioi
  have hfiniteOn : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-t) / t) (Set.Ioc s 1) := by
    rwa [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsle]
  rw [hsplitSet, setIntegral_union hdisj measurableSet_Ioi hfiniteOn htailInt]
  have hlog : (∫ t in s..1, (1 : ℝ) / t) = -Real.log s := by
    simp_rw [one_div]
    rw [integral_inv_of_pos hs one_pos]
    rw [Real.log_div one_ne_zero hs.ne']
    simp
  have hsub :
      (∫ t in s..1, (1 - Real.exp (-t)) / t) =
        (∫ t in s..1, (1 : ℝ) / t) -
          ∫ t in s..1, Real.exp (-t) / t := by
    rw [← intervalIntegral.integral_sub hone hfinite]
    congr 1
    funext t
    ring
  rw [hsub, hlog]
  rw [← intervalIntegral.integral_of_le hsle]
  ring

theorem exponentialIntegral_exp_limit :
    Tendsto
      (fun s : ℝ ↦ s * Real.exp
        (∫ t in Set.Ioi s, Real.exp (-t) / t))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := (continuous_exp.tendsto
    (-Real.eulerMascheroniConstant)).comp exponentialIntegral_log_limit
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  change Real.exp (Real.log s +
      ∫ t in Set.Ioi s, Real.exp (-t) / t) = _
  rw [Real.exp_add, Real.exp_log hs]

theorem laplace_final_value_of_tendsto
    (f : ℝ → ℝ) (L C : ℝ)
    (hf : Measurable f) (hC : 0 ≤ C)
    (hbound : ∀ u : ℝ, 1 ≤ u → |f u| ≤ C)
    (hlim : Tendsto f atTop (nhds L)) :
    Tendsto
      (fun s : ℝ ↦ s * ∫ u in Set.Ioi 1, f u * Real.exp (-s * u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  let F : ℝ → ℝ → ℝ := fun s t ↦
    (Set.Ioi s).indicator (fun t ↦ f (t / s) * Real.exp (-t)) t
  let G : ℝ → ℝ := fun t ↦
    (Set.Ioi (0 : ℝ)).indicator (fun t ↦ L * Real.exp (-t)) t
  let B : ℝ → ℝ := fun t ↦
    (Set.Ioi (0 : ℝ)).indicator (fun t ↦ C * Real.exp (-t)) t
  have hBint : Integrable B := by
    have hexp : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Set.Ioi 0) :=
      integrableOn_exp_neg_Ioi 0
    have hmul : IntegrableOn (fun t : ℝ ↦ C * Real.exp (-t)) (Set.Ioi 0) :=
      hexp.const_mul C
    simpa [B, integrable_indicator_iff measurableSet_Ioi] using hmul
  have hFmeas : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable (F s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hcomp : Measurable (fun t : ℝ ↦ f (t / s)) :=
      hf.comp (measurable_id.div_const s)
    have hprod : Measurable (fun t : ℝ ↦
        f (t / s) * Real.exp (-t)) :=
      hcomp.mul ((continuous_exp.comp continuous_neg).measurable)
    exact hprod.aestronglyMeasurable.indicator measurableSet_Ioi
  have hFbound : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ᵐ t : ℝ, ‖F s t‖ ≤ B t := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards with t
    by_cases hst : s < t
    · have hs0 : 0 < s := hs
      have ht0 : 0 < t := hs0.trans hst
      have hratio : 1 ≤ t / s := by
        rw [le_div_iff₀ hs0]
        simpa using hst.le
      have hfC := hbound (t / s) hratio
      have hstmem : t ∈ Set.Ioi s := hst
      have htmem : t ∈ Set.Ioi (0 : ℝ) := ht0
      change ‖(Set.Ioi s).indicator
          (fun v ↦ f (v / s) * Real.exp (-v)) t‖ ≤
        (Set.Ioi 0).indicator (fun v ↦ C * Real.exp (-v)) t
      rw [Set.indicator_of_mem hstmem, Set.indicator_of_mem htmem]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right hfC (Real.exp_pos _).le
    · have hnot : t ∉ Set.Ioi s := hst
      change ‖(Set.Ioi s).indicator
          (fun v ↦ f (v / s) * Real.exp (-v)) t‖ ≤
        (Set.Ioi 0).indicator (fun v ↦ C * Real.exp (-v)) t
      rw [Set.indicator_of_notMem hnot, norm_zero]
      by_cases ht0 : 0 < t
      · have htmem : t ∈ Set.Ioi (0 : ℝ) := ht0
        rw [Set.indicator_of_mem htmem]
        positivity
      · have htmem : t ∉ Set.Ioi (0 : ℝ) := ht0
        rw [Set.indicator_of_notMem htmem]
  have hFlim : ∀ᵐ t : ℝ,
      Tendsto (fun s : ℝ ↦ F s t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (G t)) := by
    filter_upwards with t
    by_cases ht : 0 < t
    · have hevent : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0), s < t :=
        nhdsWithin_le_nhds (Iio_mem_nhds ht)
      have hratio : Tendsto (fun s : ℝ ↦ t / s)
          (nhdsWithin 0 (Set.Ioi 0)) atTop := by
        simpa [div_eq_mul_inv] using
          tendsto_const_nhds.pos_mul_atTop ht tendsto_inv_nhdsGT_zero
      have hfpart := hlim.comp hratio
      have hconst : Tendsto (fun _s : ℝ ↦ Real.exp (-t))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-t))) :=
        tendsto_const_nhds
      have hprod := hfpart.mul hconst
      have hprod' : Tendsto
          (fun s : ℝ ↦ f (t / s) * Real.exp (-t))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (L * Real.exp (-t))) := hprod
      have hG : G t = L * Real.exp (-t) := by simp [G, ht]
      rw [hG]
      apply hprod'.congr'
      filter_upwards [hevent] with s hst
      simp [F, hst]
    · have ht0 : t ≤ 0 := le_of_not_gt ht
      have hevent : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < s :=
        self_mem_nhdsWithin
      have hzero : Tendsto (fun _s : ℝ ↦ (0 : ℝ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds
      have hzero' : G t = 0 := by simp [G, ht]
      rw [hzero']
      apply hzero.congr'
      filter_upwards [hevent] with s hs
      have hnot : ¬s < t := by linarith
      simp [F, hnot]
  have hint := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    B hFmeas hFbound hBint hFlim
  have hGint : (∫ t : ℝ, G t) = L := by
    have hGset : (∫ t : ℝ, G t) =
        ∫ t in Set.Ioi (0 : ℝ), L * Real.exp (-t) := by
      rw [← integral_indicator measurableSet_Ioi]
    rw [hGset, integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [hGint] at hint
  refine hint.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0 < s := hs
  have hsne : s ≠ 0 := hs0.ne'
  have hscale := integral_comp_mul_left_Ioi
    (fun t : ℝ ↦ f (t / s) * Real.exp (-t)) 1 hs0
  have hscale' :
      (∫ u in Set.Ioi (1 : ℝ), f u * Real.exp (-s * u)) =
        s⁻¹ * ∫ t in Set.Ioi s, f (t / s) * Real.exp (-t) := by
    simpa [hsne, smul_eq_mul] using hscale
  have hFset : (∫ t : ℝ, F s t) =
      ∫ t in Set.Ioi s, f (t / s) * Real.exp (-t) := by
    rw [← integral_indicator measurableSet_Ioi]
  rw [hFset]
  rw [hscale']
  simp [hsne]

end

end ErdosAverageCertificates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_LaplaceODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Real Set MeasureTheory Filter Topology

namespace ErdosAverageCertificates

noncomputable section

theorem laplace_ode_solution
    {F : ℝ → ℝ}
    (hF : DifferentiableOn ℝ F (Set.Ioi 0))
    (hpos : ∀ s : ℝ, 0 < s → 0 < 1 + F s)
    (hode : ∀ s : ℝ, 0 < s →
      s * deriv F s + Real.exp (-s) * (1 + F s) = 0)
    (hinfty : Tendsto F atTop (nhds 0)) :
    ∀ s : ℝ, 0 < s →
      1 + F s = Real.exp
        (∫ t in Set.Ioi s, Real.exp (-t) / t) := by
  intro s hs
  have hlogDeriv : ∀ x ∈ Set.Ici s,
      HasDerivAt (fun y : ℝ ↦ Real.log (1 + F y))
        (-Real.exp (-x) / x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hs hx
    have hFx : DifferentiableAt ℝ F x :=
      hF.differentiableAt (Ioi_mem_nhds hx0)
    have hinner : HasDerivAt (fun y : ℝ ↦ 1 + F y) (deriv F x) x :=
      hFx.hasDerivAt.const_add 1
    have hlog := (Real.hasDerivAt_log (hpos x hx0).ne').comp x hinner
    have hxne : x ≠ 0 := hx0.ne'
    have hHne : 1 + F x ≠ 0 := (hpos x hx0).ne'
    have hratio : (1 + F x)⁻¹ * deriv F x = -Real.exp (-x) / x := by
      rw [inv_mul_eq_div]
      field_simp [hxne, hHne]
      nlinarith [hode x hx0]
    exact hlog.congr_deriv hratio
  have hlogLim : Tendsto (fun x : ℝ ↦ Real.log (1 + F x))
      atTop (nhds 0) := by
    have hinner : Tendsto (fun x : ℝ ↦ 1 + F x) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.add hinfty)
    change Tendsto (Real.log ∘ fun x : ℝ ↦ 1 + F x) atTop (nhds 0)
    simpa only [Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hinner
  have hneg : ∀ x ∈ Set.Ioi s, -Real.exp (-x) / x ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := hs.trans hx
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hx0.le
  have hint := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos'
    hlogDeriv hneg hlogLim
  have hlogEq : Real.log (1 + F s) =
      ∫ t in Set.Ioi s, Real.exp (-t) / t := by
    have hrewrite : (fun x : ℝ ↦ -Real.exp (-x) / x) =
        fun x : ℝ ↦ -(Real.exp (-x) / x) := by
      funext x
      ring
    rw [hrewrite, integral_neg] at hint
    linarith
  rw [← hlogEq, Real.exp_log (hpos s hs)]

end

end ErdosAverageCertificates

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_DickmanFiniteDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DelayConstruction

open MeasureTheory Filter
open scoped Topology

noncomputable def kernel (f : ℝ → ℝ) (t : ℝ) : ℝ := f (t - 1) / max 1 t

theorem kernel_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (kernel f) := by
  apply Continuous.div (hf.comp (continuous_id.sub continuous_const)) (continuous_const.max continuous_id)
  intro t
  change max (1 : ℝ) t ≠ 0
  have h := le_max_left (1 : ℝ) t
  linarith

noncomputable def stepApprox (σ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun u => 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t

theorem stepApprox_continuous (σ : ℝ) (n : ℕ) : Continuous (stepApprox σ n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have hk := kernel_continuous ih
      have hInt : Continuous (fun u : ℝ => ∫ t in (1 : ℝ)..u, kernel (stepApprox σ n) t) :=
        (intervalIntegral.differentiable_integral_of_continuous hk).continuous
      exact continuous_const.add (continuous_const.mul (hInt.comp (continuous_const.max continuous_id)))

theorem stepApprox_succ_stable (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ (n : ℝ) + 1) :
    stepApprox σ (n + 1) u = stepApprox σ n u := by
  induction n generalizing u with
  | zero => simp only [Nat.cast_zero, zero_add] at hu; simp [stepApprox, max_eq_left hu]
  | succ n ih =>
      change 1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ (n + 1)) t) =
        1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t)
      apply congrArg (fun I : ℝ => 1 + σ * I)
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (le_max_left (1 : ℝ) u)] at ht
      have hmax : max 1 u ≤ (n : ℝ) + 2 := by
        apply max_le
        · have hn0 := Nat.cast_nonneg (α := ℝ) n
          linarith
        · push_cast at hu
          linarith
      have htbound : t - 1 ≤ (n : ℝ) + 1 := by linarith [ht.2]
      unfold kernel
      rw [ih htbound]

theorem stepApprox_stable (σ : ℝ) {n m : ℕ} (hnm : n ≤ m) {u : ℝ}
    (hu : u ≤ (n : ℝ) + 1) : stepApprox σ m u = stepApprox σ n u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [stepApprox_succ_stable σ m, ih]
      have hcast : (n : ℝ) ≤ m := by exact_mod_cast hm
      linarith

noncomputable def delay (σ u : ℝ) : ℝ := stepApprox σ ⌈u⌉₊ u

theorem delay_eq_stepApprox (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ (n : ℝ) + 1) :
    delay σ u = stepApprox σ n u := by
  unfold delay
  have hceil : u ≤ (⌈u⌉₊ : ℝ) + 1 := by have h := Nat.le_ceil u; linarith
  rcases le_total n ⌈u⌉₊ with h | h
  · exact stepApprox_stable σ h hu
  · exact (stepApprox_stable σ h hceil).symm

theorem delay_continuous (σ : ℝ) : Continuous (delay σ) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  let n := ⌈u⌉₊ + 1
  have hu : u < (n : ℝ) + 1 := by have h := Nat.le_ceil u; dsimp [n]; push_cast <;> linarith
  have heq : delay σ =ᶠ[𝓝 u] stepApprox σ n := by
    filter_upwards [Iio_mem_nhds hu] with x hx
    exact delay_eq_stepApprox σ n hx.le
  exact (continuousAt_congr heq).mpr (stepApprox_continuous σ n).continuousAt

theorem delay_initial (σ : ℝ) {u : ℝ} (hu : u ≤ 1) : delay σ u = 1 := by
  rw [delay_eq_stepApprox σ 0 (by simpa using hu)]
  rfl

theorem delay_integral (σ u : ℝ) :
    delay σ u = 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (delay σ) t := by
  let n := ⌈u⌉₊
  have hu : u ≤ (n : ℝ) := Nat.le_ceil u
  rw [delay_eq_stepApprox σ (n + 1) (by push_cast <;> linarith)]
  change 1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t) = _
  apply congrArg (fun I : ℝ => 1 + σ * I)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (le_max_left (1 : ℝ) u)] at ht
  have hmax : max 1 u ≤ (n : ℝ) + 1 := max_le (by have hn0 := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)
  have htbound : t - 1 ≤ (n : ℝ) + 1 := by linarith [ht.2]
  unfold kernel
  rw [delay_eq_stepApprox σ n htbound]

theorem delay_integral_of_one_le (σ : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    delay σ u = 1 + σ * ∫ t in (1 : ℝ)..u, delay σ (t - 1) / t := by
  rw [delay_integral σ u, max_eq_right hu]
  apply congrArg (fun I : ℝ => 1 + σ * I)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hu] at ht
  simp only [kernel, max_eq_right ht.1]

theorem delay_hasDerivAt (σ : ℝ) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (delay σ) (σ * delay σ (u - 1) / u) u := by
  have hk := kernel_continuous (delay_continuous σ)
  have hInt := intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 1 u)
    hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hPrim := (hInt.const_mul σ).const_add 1
  have heq : delay σ =ᶠ[𝓝 u] (fun x => 1 + σ * ∫ t in (1 : ℝ)..x, kernel (delay σ) t) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    rw [delay_integral σ x, max_eq_right hx.le]
  have hD := hPrim.congr_of_eventuallyEq heq
  simpa only [kernel, max_eq_right hu.le, mul_div_assoc] using hD

end NumberTheoryLean.DelayConstruction

end

section

namespace NumberTheoryLean.DelayUniqueness

theorem shifted_unique_upto (σ : ℝ) (F G : ℝ → ℝ)
    (hFinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → F u = 1)
    (hGinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → G u = 1)
    (hFrec : ∀ u : ℝ, 2 < u → F u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, F t / t)
    (hGrec : ∀ u : ℝ, 2 < u → G u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, G t / t)
    (n : ℕ) : ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ) + 2 → F u = G u := by
  induction n with
  | zero =>
      intro u hu1 hu2
      have hu : u ≤ 2 := by simpa only [Nat.cast_zero, zero_add] using hu2
      rw [hFinit u hu1 hu, hGinit u hu1 hu]
  | succ n ih =>
      intro u hu1 hun
      by_cases hu2 : u ≤ 2
      · rw [hFinit u hu1 hu2, hGinit u hu1 hu2]
      · have hu : 2 < u := lt_of_not_ge hu2
        rw [hFrec u hu, hGrec u hu]
        apply congrArg (fun I : ℝ => 1 + σ * I)
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
        change F t / t = G t / t
        rw [ih t ht.1 (by push_cast at hun <;> linarith [ht.2])]

theorem shifted_unique (σ : ℝ) (F G : ℝ → ℝ)
    (hFinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → F u = 1)
    (hGinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → G u = 1)
    (hFrec : ∀ u : ℝ, 2 < u → F u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, F t / t)
    (hGrec : ∀ u : ℝ, 2 < u → G u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, G t / t)
    {u : ℝ} (hu : 1 ≤ u) : F u = G u := by
  apply shifted_unique_upto σ F G hFinit hGinit hFrec hGrec ⌈u⌉₊ u hu
  have h := Nat.le_ceil u
  linarith

end NumberTheoryLean.DelayUniqueness

end

section

namespace NumberTheoryLean.Dickman

open MeasureTheory Filter
open scoped Topology

noncomputable def rho : ℝ → ℝ := DelayConstruction.delay (-1)

theorem rho_continuous : Continuous rho := DelayConstruction.delay_continuous (-1)

theorem rho_initial {u : ℝ} (hu : u ≤ 1) : rho u = 1 := DelayConstruction.delay_initial (-1) hu

theorem rho_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt rho (-rho (u - 1) / u) u := by
  simpa only [rho, neg_one_mul] using DelayConstruction.delay_hasDerivAt (-1) hu

theorem rho_integral {u : ℝ} (hu : 1 ≤ u) :
    rho u = 1 - ∫ t in (1 : ℝ)..u, rho (t - 1) / t := by
  simpa only [rho, neg_one_mul, sub_eq_add_neg] using DelayConstruction.delay_integral_of_one_le (-1) hu

theorem rho_first_interval {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) : rho u = 1 - Real.log u := by
  rw [rho_integral hu1]
  have hInt : (∫ t in (1 : ℝ)..u, rho (t - 1) / t) = ∫ t in (1 : ℝ)..u, 1 / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hu1] at ht
    change rho (t - 1) / t = 1 / t
    rw [rho_initial (by linarith [ht.2])]
  rw [hInt, integral_one_div_of_pos (by norm_num) (by linarith), div_one]

noncomputable def primitive (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, rho t

theorem primitive_continuous : Continuous primitive :=
  (intervalIntegral.differentiable_integral_of_continuous rho_continuous).continuous

theorem primitive_hasDerivAt (u : ℝ) : HasDerivAt primitive (rho u) u :=
  intervalIntegral.integral_hasDerivAt_right (rho_continuous.intervalIntegrable 0 u)
    rho_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter rho_continuous.continuousAt

noncomputable def identityDifference (u : ℝ) : ℝ := u * rho u - (primitive u - primitive (u - 1))

theorem identityDifference_continuous : Continuous identityDifference :=
  (continuous_id.mul rho_continuous).sub (primitive_continuous.sub
    (primitive_continuous.comp (continuous_id.sub continuous_const)))

theorem identityDifference_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt identityDifference 0 u := by
  have hProd := (hasDerivAt_id u).mul (rho_hasDerivAt hu)
  have hShift := (primitive_hasDerivAt (u - 1)).comp u ((hasDerivAt_id u).sub_const 1)
  have hDiff := hProd.sub ((primitive_hasDerivAt u).sub hShift)
  have hvalue : (1 * rho u + id u * (-rho (u - 1) / u) - (rho u - rho (u - 1) * 1)) = 0 := by
    dsimp only [id_eq]
    field_simp
    ring
  rw [hvalue] at hDiff
  convert! hDiff using 1
  all_goals try with_reducible_and_instances rfl

theorem identityDifference_one : identityDifference 1 = 0 := by
  have hp1 : primitive 1 = 1 := by
    unfold primitive
    calc
      (∫ t in (0 : ℝ)..1, rho t) = ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact rho_initial ht.2
      _ = 1 := by simp
  have hp0 : primitive 0 = 0 := by simp [primitive]
  simp only [identityDifference, rho_initial (le_refl 1), one_mul, sub_self, hp1, hp0, sub_zero]

theorem rho_unit_integral {u : ℝ} (hu : 1 ≤ u) :
    u * rho u = ∫ t in u - 1..u, rho t := by
  have hzero : identityDifference u = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu
      identityDifference_continuous.continuousOn
      (fun x hx => identityDifference_hasDerivAt hx.1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 1 u)
    simpa only [intervalIntegral.integral_zero, identityDifference_one, sub_zero] using hFTC.symm
  have hInt := intervalIntegral.integral_add_adjacent_intervals
    (rho_continuous.intervalIntegrable (μ := volume) 0 (u - 1)) (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
  change primitive (u - 1) + (∫ t in u - 1..u, rho t) = primitive u at hInt
  unfold identityDifference at hzero
  linarith

theorem rho_antitone_segment (b : ℝ)
    (hprev : ∀ t : ℝ, 0 ≤ t → t ≤ b - 1 → 0 ≤ rho t) : AntitoneOn rho (Set.Icc 1 b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 1 b) rho_continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (rho_hasDerivAt hx.1).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(rho_hasDerivAt hx.1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hprev (x - 1) (by linarith [hx.1])
      (by linarith [hx.2]))) (by linarith [hx.1])

theorem rho_nonneg_upto (n : ℕ) : ∀ u : ℝ, 0 ≤ u → u ≤ (n : ℝ) + 1 → 0 ≤ rho u := by
  induction n with
  | zero =>
      intro u _ hu
      rw [rho_initial (by simpa only [Nat.cast_zero, zero_add] using hu)]
      norm_num
  | succ n ih =>
      intro u hu0 hu
      have hub : u ≤ (n : ℝ) + 2 := by push_cast at hu <;> linarith
      have hmono : AntitoneOn rho (Set.Icc 1 ((n : ℝ) + 2)) :=
        rho_antitone_segment _ (fun t ht0 htb => ih t ht0 (by linarith))
      by_cases hu1 : u ≤ 1
      · rw [rho_initial hu1]; norm_num
      · have hu1' : 1 < u := lt_of_not_ge hu1
        have hpoint : ∀ t ∈ Set.Icc (u - 1) u, rho u ≤ rho t := by
          intro t ht
          by_cases ht1 : 1 ≤ t
          · exact hmono ⟨ht1, ht.2.trans hub⟩ ⟨hu1'.le, hub⟩ ht.2
          · rw [rho_initial (le_of_not_ge ht1)]
            have h := hmono ⟨le_rfl, by linarith⟩ ⟨hu1'.le, hub⟩ hu1'.le
            simpa only [rho_initial (le_refl 1)] using h
        have hint := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho u) volume (u - 1) u)
          (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u) hpoint
        have hconst : (∫ _t in u - 1..u, rho u) = rho u := by simp
        rw [hconst, ← rho_unit_integral hu1'.le] at hint
        have hprod : 0 ≤ (u - 1) * rho u := by nlinarith
        exact nonneg_of_mul_nonneg_right hprod (by linarith)

theorem rho_nonneg (u : ℝ) : 0 ≤ rho u := by
  by_cases hu : u ≤ 1
  · rw [rho_initial hu]; norm_num
  · apply rho_nonneg_upto ⌈u⌉₊ u (by linarith)
    have h := Nat.le_ceil u
    linarith

theorem rho_antitone : Antitone rho := by
  intro x y hxy
  by_cases hy : y ≤ 1
  · rw [rho_initial hy, rho_initial (hxy.trans hy)]
  · have hy1 : 1 < y := lt_of_not_ge hy
    have hmono := rho_antitone_segment y (fun t _ _ => rho_nonneg t)
    by_cases hx : x ≤ 1
    · rw [rho_initial hx]
      have h := hmono ⟨le_rfl, hy1.le⟩ ⟨hy1.le, le_rfl⟩ hy1.le
      simpa only [rho_initial (le_refl 1)] using h
    · exact hmono ⟨le_of_not_ge hx, hxy⟩ ⟨hy1.le, le_rfl⟩ hxy

theorem rho_half_step {u : ℝ} (hu : 1 ≤ u) : rho (u - 1 / 2) ≤ 2 * u * rho u := by
  have hconst := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u - 1 / 2)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho (u - 1 / 2)) volume (u - 1) (u - 1 / 2))
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) (u - 1 / 2))
    (fun t ht => rho_antitone ht.2)
  have hvalue : (∫ _t in u - 1..u - 1 / 2, rho (u - 1 / 2)) = (1 / 2 : ℝ) * rho (u - 1 / 2) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hvalue] at hconst
  have hsub := intervalIntegral.integral_mono_interval (μ := volume)
    (a := u - 1) (b := u - 1 / 2) (c := u - 1) (d := u)
    le_rfl (by linarith) (by linarith)
    (Filter.Eventually.of_forall (fun t => rho_nonneg t))
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
  rw [← rho_unit_integral hu] at hsub
  nlinarith

theorem rho_lower_comparison {u : ℝ} (hu : 2 ≤ u) : rho (u - 1) ≤ 4 * u ^ 2 * rho u := by
  have h1 := rho_half_step (u := u) (by linarith)
  have h2 := rho_half_step (u := u - 1 / 2) (by linarith)
  have harg : u - 1 / 2 - 1 / 2 = u - 1 := by ring
  rw [harg] at h2
  calc
    rho (u - 1) ≤ 2 * (u - 1 / 2) * rho (u - 1 / 2) := h2
    _ ≤ 2 * (u - 1 / 2) * (2 * u * rho u) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (4 * u * (u - 1 / 2)) * rho u := by ring
    _ ≤ 4 * u ^ 2 * rho u := mul_le_mul_of_nonneg_right (by nlinarith) (rho_nonneg u)

theorem rho_pos_initial {u : ℝ} (hu : u ≤ 2) : 0 < rho u := by
  by_cases hu1 : u ≤ 1
  · rw [rho_initial hu1]; norm_num
  · have hu1' : 1 < u := lt_of_not_ge hu1
    rw [rho_first_interval hu1'.le hu]
    have hlog2 : Real.log 2 < 1 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) Real.exp_one_gt_two
      simpa only [Real.log_exp] using h
    have hlogu := Real.log_le_log (show 0 < u by linarith) hu
    linarith

theorem rho_pos_upto (n : ℕ) : ∀ u : ℝ, u ≤ (n : ℝ) + 2 → 0 < rho u := by
  induction n with
  | zero => intro u hu; exact rho_pos_initial (by simpa only [Nat.cast_zero, zero_add] using hu)
  | succ n ih =>
      intro u hu
      by_cases hu2 : u ≤ 2
      · exact rho_pos_initial hu2
      · have hu2' : 2 < u := lt_of_not_ge hu2
        have hprev : 0 < rho (u - 1) := ih (u - 1) (by push_cast at hu <;> linarith)
        have hbound := rho_lower_comparison hu2'.le
        by_contra hnot
        have hnonpos : rho u ≤ 0 := le_of_not_gt hnot
        have hprod := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4 * u ^ 2 by positivity) hnonpos
        linarith

theorem rho_pos (u : ℝ) : 0 < rho u := by
  apply rho_pos_upto ⌈u⌉₊ u
  have h := Nat.le_ceil u
  linarith

theorem rho_upper_comparison {u : ℝ} (hu : 1 ≤ u) : u * rho u ≤ rho (u - 1) := by
  have hInt := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho (u - 1)) volume (u - 1) u)
    (fun t ht => rho_antitone ht.1)
  have hconst : (∫ _t in u - 1..u, rho (u - 1)) = rho (u - 1) := by simp
  rw [hconst, ← rho_unit_integral hu] at hInt
  exact hInt

end NumberTheoryLean.Dickman

end

section

namespace NumberTheoryLean.DickmanDecay

open MeasureTheory Filter
open scoped Topology
open Dickman

noncomputable def hazard (u : ℝ) : ℝ := rho (u - 1) / (u * rho u)

theorem hazard_eq_neg_deriv {u : ℝ} (hu : 1 < u) : hazard u = -deriv rho u / rho u := by
  rw [(rho_hasDerivAt hu).deriv]
  unfold hazard
  field_simp

theorem hazard_ge_one {u : ℝ} (hu : 2 ≤ u) : 1 ≤ hazard u := by
  unfold hazard
  apply (le_div_iff₀ (mul_pos (show 0 < u by linarith) (rho_pos u))).mpr
  simpa only [one_mul] using rho_upper_comparison (u := u) (by linarith)

theorem deriv_le_of_hazard {u rate : ℝ} (hu : 1 < u) (hrate : rate ≤ hazard u) :
    deriv rho u ≤ -rate * rho u := by
  rw [hazard_eq_neg_deriv hu] at hrate
  have h := (le_div_iff₀ (rho_pos u)).mp hrate
  linarith

theorem rho_exponential_comparison (T rate a b : ℝ) (hT : 2 ≤ T)
    (htail : ∀ t : ℝ, T ≤ t → rate ≤ hazard t) (ha : T ≤ a) (hab : a ≤ b) :
    rho b ≤ rho a * Real.exp (-rate * (b - a)) := by
  let H : ℝ → ℝ := fun t => Real.exp (rate * t) * rho t
  have hCont : Continuous H :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul rho_continuous
  have hDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt H (Real.exp (rate * t) * (deriv rho t + rate * rho t)) t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hExp := ((hasDerivAt_id t).const_mul rate).exp
    have hRho := (rho_hasDerivAt ht1).differentiableAt.hasDerivAt
    have hProd := hExp.mul hRho
    convert! hProd using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq, mul_one]
    ring
  have hMono : AntitoneOn H (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hCont.continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (hDeriv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hDeriv t ht).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hd := deriv_le_of_hazard (u := t) (rate := rate) (by linarith [ht.1]) (htail t (by linarith [ht.1]))
      linarith
  have hHb : H b ≤ H a := hMono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hQ : rho b ≤ Real.exp (rate * a) * rho a / Real.exp (rate * b) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    dsimp [H] at hHb
    nlinarith
  calc
    rho b ≤ Real.exp (rate * a) * rho a / Real.exp (rate * b) := hQ
    _ = rho a * (Real.exp (rate * a) / Real.exp (rate * b)) := by ring
    _ = rho a * Real.exp (-rate * (b - a)) := by rw [← Real.exp_sub]; congr 1; congr 1; ring

theorem unit_exponential_integral (rate u : ℝ) (hrate : rate ≠ 0) :
    (∫ t in u - 1..u, Real.exp (-rate * (t - (u - 1)))) = (1 - Real.exp (-rate)) / rate := by
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => Real.exp (-rate * t)) (u - 1)]
  simp only [sub_self, sub_sub_cancel]
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hrate), integral_exp]
  simp only [mul_zero, mul_one, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

theorem hazard_bootstrap (T rate u : ℝ) (hT : 2 ≤ T) (hrate : 0 < rate)
    (htail : ∀ t : ℝ, T ≤ t → rate ≤ hazard t) (hu : T + 1 ≤ u) :
    rate / (1 - Real.exp (-rate)) ≤ hazard u := by
  have hu1 : 1 ≤ u := by linarith
  have hcomp : ∀ t ∈ Set.Icc (u - 1) u,
      rho t ≤ rho (u - 1) * Real.exp (-rate * (t - (u - 1))) := by
    intro t ht
    exact rho_exponential_comparison T rate (u - 1) t hT htail (by linarith) ht.1
  have hCont : Continuous (fun t : ℝ => rho (u - 1) * Real.exp (-rate * (t - (u - 1)))) := by fun_prop
  have hInt := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
    (hCont.intervalIntegrable (μ := volume) (u - 1) u) hcomp
  rw [← rho_unit_integral hu1, intervalIntegral.integral_const_mul,
    unit_exponential_integral rate u (ne_of_gt hrate)] at hInt
  have he : 0 < 1 - Real.exp (-rate) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  unfold hazard
  apply (div_le_div_iff₀ he (mul_pos (show 0 < u by linarith) (rho_pos u))).mpr
  rw [← mul_div_assoc] at hInt
  have hmul := (le_div_iff₀ hrate).mp hInt
  nlinarith

theorem bootstrap_uniform_gain (L rate : ℝ) (hrate1 : 1 ≤ rate) (hrateL : rate ≤ L) :
    rate + Real.exp (-L) ≤ rate / (1 - Real.exp (-rate)) := by
  have hrate0 : 0 < rate := by linarith
  have he0 : 0 < Real.exp (-rate) := Real.exp_pos _
  have hd0 : 0 < Real.exp (-L) := Real.exp_pos _
  have hle : Real.exp (-L) ≤ Real.exp (-rate) := Real.exp_le_exp.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-rate) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  apply (le_div_iff₀ hden).mpr
  nlinarith [mul_nonneg (show 0 ≤ rate - 1 by linarith) he0.le, mul_nonneg hd0.le he0.le]

theorem hazard_step_bound (L : ℝ) (hL : 1 ≤ L) (n : ℕ) :
    ∀ u : ℝ, (n : ℝ) + 2 ≤ u →
      min L (1 + (n : ℝ) * Real.exp (-L)) ≤ hazard u := by
  induction n with
  | zero =>
      intro u hu
      simp only [Nat.cast_zero, zero_mul, add_zero, min_eq_right hL]
      exact hazard_ge_one (by simpa only [Nat.cast_zero, zero_add] using hu)
  | succ n ih =>
      intro u hu
      let d := Real.exp (-L)
      let rate := min L (1 + (n : ℝ) * d)
      have hd : 0 < d := Real.exp_pos _
      have hr1 : 1 ≤ rate := le_min hL (by have hn := Nat.cast_nonneg (α := ℝ) n; nlinarith)
      have hrL : rate ≤ L := min_le_left _ _
      have htail : ∀ t : ℝ, (n : ℝ) + 2 ≤ t → rate ≤ hazard t := fun t ht => ih t ht
      have hboost := hazard_bootstrap ((n : ℝ) + 2) rate u
        (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith) htail
        (by push_cast at hu <;> linarith)
      have hgain := bootstrap_uniform_gain L rate hr1 hrL
      have hstep : min L (1 + ((n + 1 : ℕ) : ℝ) * d) ≤ rate + d := by
        by_cases hcase : L ≤ 1 + (n : ℝ) * d
        · have hr : rate = L := min_eq_left hcase
          rw [hr]
          exact (min_le_left _ _).trans (by linarith)
        · have hr : rate = 1 + (n : ℝ) * d := min_eq_right (le_of_not_ge hcase)
          rw [hr]
          have hm := min_le_right L (1 + ((n + 1 : ℕ) : ℝ) * d)
          push_cast at hm ⊢
          linarith
      exact hstep.trans (hgain.trans hboost)

theorem exists_hazard_tail (rate : ℝ) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u → rate ≤ hazard u := by
  let L := max 1 rate
  let d := Real.exp (-L)
  have hL : 1 ≤ L := le_max_left _ _
  have hd : 0 < d := Real.exp_pos _
  obtain ⟨n, hn⟩ := exists_nat_ge ((L - 1) / d)
  have hreach : L ≤ 1 + (n : ℝ) * d := by
    have h := (div_le_iff₀ hd).mp hn
    linarith
  refine ⟨(n : ℝ) + 2, by have h := Nat.cast_nonneg (α := ℝ) n; linarith, ?_⟩
  intro u hu
  have h := hazard_step_bound L hL n u hu
  rw [min_eq_left hreach] at h
  exact (le_max_right 1 rate).trans h

theorem rho_exponential_majorant (rate : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u →
      rho u ≤ C * Real.exp (-rate * u) := by
  obtain ⟨T, hT, htail⟩ := exists_hazard_tail rate
  refine ⟨rho T * Real.exp (rate * T), mul_pos (rho_pos T) (Real.exp_pos _), T, hT, ?_⟩
  intro u hu
  have h := rho_exponential_comparison T rate T u hT htail le_rfl hu
  have heq : Real.exp (-rate * (u - T)) = Real.exp (rate * T) * Real.exp (-rate * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at h
  simpa only [mul_assoc] using h

theorem rho_faster_than_exponential (rate : ℝ) :
    Tendsto (fun u : ℝ => Real.exp (rate * u) * rho u) atTop (𝓝 0) := by
  obtain ⟨C, hC, T, _, hbound⟩ := rho_exponential_majorant (rate + 1)
  have hUpper : (fun u : ℝ => Real.exp (rate * u) * rho u) ≤ᶠ[atTop]
      (fun u => C * Real.exp (-u)) := by
    apply eventually_atTop.mpr
    refine ⟨T, ?_⟩
    intro u hu
    have h := mul_le_mul_of_nonneg_left (hbound u hu) (Real.exp_pos (rate * u)).le
    have heq : Real.exp (rate * u) * (C * Real.exp (-(rate + 1) * u)) = C * Real.exp (-u) := by
      calc
        _ = C * (Real.exp (rate * u) * Real.exp (-(rate + 1) * u)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; ring
    rw [heq] at h
    exact h
  have hLower : (0 : ℝ → ℝ) ≤ᶠ[atTop] (fun u : ℝ => Real.exp (rate * u) * rho u) :=
    Filter.Eventually.of_forall (fun u => mul_nonneg (Real.exp_pos _).le (rho_nonneg u))
  have hLimit : Tendsto (fun u : ℝ => C * Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  exact squeeze_zero' hLower hUpper hLimit

theorem rho_tendsto_zero : Tendsto rho atTop (𝓝 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using rho_faster_than_exponential 0

end NumberTheoryLean.DickmanDecay

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LinearSieveFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LinearSieveFunctions

open MeasureTheory Filter
open scoped Topology

noncomputable def plus : ℝ → ℝ := DelayConstruction.delay 1

theorem plus_continuous : Continuous plus := DelayConstruction.delay_continuous 1

theorem plus_initial {u : ℝ} (hu : u ≤ 1) : plus u = 1 := DelayConstruction.delay_initial 1 hu

noncomputable def f (A s : ℝ) : ℝ :=
  if s ≤ 2 then 0 else A * (plus (s - 1) - Dickman.rho (s - 1)) / (2 * s)

noncomputable def F (A s : ℝ) : ℝ :=
  A * (plus (s - 1) + Dickman.rho (s - 1)) / (2 * s)

theorem f_initial (A : ℝ) {s : ℝ} (hs : s ≤ 2) : f A s = 0 := by simp only [f, ite_eq_left hs]

theorem f_eq_difference (A s : ℝ) :
    f A s = A * (plus (s - 1) - Dickman.rho (s - 1)) / (2 * s) := by
  by_cases hs : s ≤ 2
  · rw [f_initial A hs, plus_initial (by linarith), Dickman.rho_initial (by linarith)]
    simp
  · simp only [f, ite_eq_right hs]

theorem plus_add_rho_initial {u : ℝ} (hu : u ≤ 2) : plus u + Dickman.rho u = 2 := by
  change DelayConstruction.delay 1 u + DelayConstruction.delay (-1) u = 2
  rw [DelayConstruction.delay_eq_stepApprox 1 1 (by norm_num; exact hu),
    DelayConstruction.delay_eq_stepApprox (-1) 1 (by norm_num; exact hu)]
  simp only [DelayConstruction.stepApprox, DelayConstruction.kernel, one_mul, neg_one_mul]
  ring

theorem mass_f (A : ℝ) {s : ℝ} (hs : s ≠ 0) :
    s * f A s = (A / 2) * (plus (s - 1) - Dickman.rho (s - 1)) := by
  rw [f_eq_difference]
  field_simp

theorem mass_F (A : ℝ) {s : ℝ} (hs : s ≠ 0) :
    s * F A s = (A / 2) * (plus (s - 1) + Dickman.rho (s - 1)) := by
  unfold F
  field_simp

theorem F_initial (A : ℝ) {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3) : F A s = A / s := by
  unfold F
  rw [plus_add_rho_initial (by linarith)]
  field_simp

theorem f_continuousAt_of_ne_zero (A : ℝ) {s : ℝ} (hs : s ≠ 0) : ContinuousAt (f A) s := by
  have hnum : Continuous (fun x : ℝ => A * (plus (x - 1) - Dickman.rho (x - 1))) :=
    continuous_const.mul ((plus_continuous.comp (continuous_id.sub continuous_const)).sub
      (Dickman.rho_continuous.comp (continuous_id.sub continuous_const)))
  have hraw : ContinuousAt (fun x : ℝ => A * (plus (x - 1) - Dickman.rho (x - 1)) / (2 * x)) s :=
    hnum.continuousAt.div (continuous_const.mul continuous_id).continuousAt (by exact mul_ne_zero (by norm_num) hs)
  exact (continuousAt_congr (Filter.Eventually.of_forall (f_eq_difference A))).mpr hraw

theorem f_continuous (A : ℝ) : Continuous (f A) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s = 0
  · subst s
    have heq : f A =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 2)] with x hx
      exact f_initial A hx.le
    exact (continuousAt_congr heq).mpr continuous_const.continuousAt
  · exact f_continuousAt_of_ne_zero A hs

theorem F_continuousAt (A : ℝ) {s : ℝ} (hs : s ≠ 0) : ContinuousAt (F A) s := by
  have hnum : Continuous (fun x : ℝ => A * (plus (x - 1) + Dickman.rho (x - 1))) :=
    continuous_const.mul ((plus_continuous.comp (continuous_id.sub continuous_const)).add
      (Dickman.rho_continuous.comp (continuous_id.sub continuous_const)))
  exact hnum.continuousAt.div (continuous_const.mul continuous_id).continuousAt (mul_ne_zero (by norm_num) hs)

theorem gap_identity (A : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    F A s - f A s = A * Dickman.rho (s - 1) / s := by
  rw [f_eq_difference]
  unfold F
  have hs0 : s ≠ 0 := by linarith
  field_simp
  ring

theorem mass_f_hasDerivAt (A : ℝ) {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x * f A x) (F A (s - 1)) s := by
  have hp : HasDerivAt plus (plus (s - 1 - 1) / (s - 1)) (s - 1) := by
    simpa only [plus, one_mul] using DelayConstruction.delay_hasDerivAt 1 (u := s - 1) (by linarith)
  have hpShift := hp.comp s ((hasDerivAt_id s).sub_const 1)
  have hrShift := (Dickman.rho_hasDerivAt (u := s - 1) (by linarith)).comp s ((hasDerivAt_id s).sub_const 1)
  have hraw := (hpShift.sub hrShift).const_mul (A / 2)
  have heq : (fun x => x * f A x) =ᶠ[𝓝 s]
      (fun x => (A / 2) * (plus (x - 1) - Dickman.rho (x - 1))) := by
    filter_upwards [Ioi_mem_nhds (show 0 < s by linarith)] with x hx
    exact mass_f A (ne_of_gt hx)
  have hd := hraw.congr_of_eventuallyEq heq
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  unfold F
  field_simp
  ring

theorem mass_F_hasDerivAt (A : ℝ) {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x * F A x) (f A (s - 1)) s := by
  have hp : HasDerivAt plus (plus (s - 1 - 1) / (s - 1)) (s - 1) := by
    simpa only [plus, one_mul] using DelayConstruction.delay_hasDerivAt 1 (u := s - 1) (by linarith)
  have hpShift := hp.comp s ((hasDerivAt_id s).sub_const 1)
  have hrShift := (Dickman.rho_hasDerivAt (u := s - 1) (by linarith)).comp s ((hasDerivAt_id s).sub_const 1)
  have hraw := (hpShift.add hrShift).const_mul (A / 2)
  have heq : (fun x => x * F A x) =ᶠ[𝓝 s]
      (fun x => (A / 2) * (plus (x - 1) + Dickman.rho (x - 1))) := by
    filter_upwards [Ioi_mem_nhds (show 0 < s by linarith)] with x hx
    exact mass_F A (ne_of_gt hx)
  have hd := hraw.congr_of_eventuallyEq heq
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  rw [f_eq_difference]
  field_simp
  ring

theorem F_continuousOn (A : ℝ) : ContinuousOn (F A) (Set.Ioi 0) := by
  intro s hs
  exact (F_continuousAt A (ne_of_gt hs)).continuousWithinAt

theorem mass_f_integral (A : ℝ) {s : ℝ} (hs : 2 ≤ s) :
    s * f A s = ∫ t in (2 : ℝ)..s, F A (t - 1) := by
  have hInt : IntervalIntegrable (fun t : ℝ => F A (t - 1)) volume 2 s := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hs] at ht
    have hF := F_continuousAt A (s := t - 1) (by linarith [ht.1])
    have hshift : ContinuousAt (fun x : ℝ => x - 1) t := (continuous_id.sub continuous_const).continuousAt
    exact (hF.comp (f := fun x : ℝ => x - 1) (x := t) hshift).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
    (continuous_id.mul (f_continuous A)).continuousOn
    (fun t ht => mass_f_hasDerivAt A ht.1) hInt
  simpa only [Pi.mul_apply, id_eq, f_initial A (le_refl 2), mul_zero, sub_zero] using hFTC.symm

theorem f_first_formula (A : ℝ) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    f A s = A * Real.log (s - 1) / s := by
  have hMass := mass_f_integral A hs2
  have hInt : (∫ t in (2 : ℝ)..s, F A (t - 1)) = A * Real.log (s - 1) := by
    calc
      (∫ t in (2 : ℝ)..s, F A (t - 1)) = ∫ t in (2 : ℝ)..s, A / (t - 1) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hs2] at ht
        change F A (t - 1) = A / (t - 1)
        exact F_initial A (by linarith [ht.1]) (by linarith [ht.2])
      _ = ∫ t in (1 : ℝ)..s - 1, A / t := by
        simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
          intervalIntegral.integral_comp_sub_right (fun t : ℝ => A / t) 1 (a := 2) (b := s)
      _ = A * ∫ t in (1 : ℝ)..s - 1, 1 / t := by
        simp only [div_eq_mul_inv, one_mul, intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_one_div_of_pos (by norm_num) (by linarith), div_one]
  rw [hInt] at hMass
  apply (eq_div_iff (show s ≠ 0 by linarith)).mpr
  nlinarith

theorem gap_pos {A s : ℝ} (hA : 0 < A) (hs : 1 ≤ s) : 0 < F A s - f A s := by
  rw [gap_identity A hs]
  exact div_pos (mul_pos hA (Dickman.rho_pos _)) (by linarith)

end NumberTheoryLean.LinearSieveFunctions

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_BuchstabBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped Interval
open MeasureTheory
open Filter

namespace ErdosAverageCertificates

noncomputable section

noncomputable def buchstabStage : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, u =>
      if u ≤ 2 then 1
      else 1 + ∫ t in 1..u - 1, buchstabStage n t / t

@[simp] theorem buchstabStage_zero (u : ℝ) : buchstabStage 0 u = 1 := rfl

theorem buchstabStage_succ_eq_integral {n : ℕ} {u : ℝ} (hu : 2 < u) :
    buchstabStage (n + 1) u =
      1 + ∫ t in 1..u - 1, buchstabStage n t / t := by
  rw [buchstabStage, ite_eq_right (not_le_of_gt hu)]

theorem buchstabStage_succ_eq_stage {n : ℕ} {u : ℝ}
    (hu1 : 1 ≤ u) (hun : u ≤ n + 2) :
    buchstabStage (n + 1) u = buchstabStage n u := by
  induction n generalizing u with
  | zero =>
      have hu2 : u ≤ 2 := by simpa using hun
      simp [buchstabStage, hu2]
  | succ n ih =>
      by_cases hu2 : u ≤ 2
      · simp [buchstabStage, hu2]
      · have hu2' : 2 < u := lt_of_not_ge hu2
        rw [buchstabStage_succ_eq_integral hu2',
          buchstabStage_succ_eq_integral hu2']
        congr 1
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc (1 : ℝ) (u - 1) := by
          simpa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] using ht
        have htupper : t ≤ n + 2 := by
          norm_num at hun ⊢
          linarith [ht'.2]
        change buchstabStage (n + 1) t / t = buchstabStage n t / t
        rw [ih ht'.1 htupper]

theorem buchstabStage_eq_of_le {m n : ℕ} {u : ℝ}
    (hu1 : 1 ≤ u) (hum : u ≤ m + 2) (hmn : m ≤ n) :
    buchstabStage n u = buchstabStage m u := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      have hun : u ≤ n + 2 := by
        exact hum.trans (by exact_mod_cast Nat.add_le_add_right hmn 2)
      rw [buchstabStage_succ_eq_stage hu1 hun, ih]

noncomputable def buchstabAux (u : ℝ) : ℝ :=
  if u < 1 then 0 else buchstabStage ⌈u⌉₊ u

noncomputable def buchstabFunction (u : ℝ) : ℝ :=
  if u < 1 then 0 else buchstabAux u / u

theorem buchstabAux_eq_stage {n : ℕ} {u : ℝ}
    (hu1 : 1 ≤ u) (hun : u ≤ n + 2) :
    buchstabAux u = buchstabStage n u := by
  rw [buchstabAux, ite_eq_right (not_lt_of_ge hu1)]
  let k : ℕ := max ⌈u⌉₊ n
  have huceil : u ≤ (⌈u⌉₊ : ℝ) + 2 :=
    (Nat.le_ceil u).trans (by norm_num)
  have hceilk : ⌈u⌉₊ ≤ k := le_max_left _ _
  have hnk : n ≤ k := le_max_right _ _
  calc
    buchstabStage ⌈u⌉₊ u = buchstabStage k u :=
      (buchstabStage_eq_of_le hu1 huceil hceilk).symm
    _ = buchstabStage n u := buchstabStage_eq_of_le hu1 hun hnk

theorem buchstabFunction_eq_aux_div {u : ℝ} (hu : 1 ≤ u) :
    buchstabFunction u = buchstabAux u / u := by
  rw [buchstabFunction, ite_eq_right (not_lt_of_ge hu)]

theorem buchstabAux_eq_one {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    buchstabAux u = 1 := by
  simpa using buchstabAux_eq_stage (n := 0) hu1 (by simpa using hu2)

theorem buchstabFunction_eq_inv {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    buchstabFunction u = u⁻¹ := by
  rw [buchstabFunction_eq_aux_div hu1, buchstabAux_eq_one hu1 hu2]
  exact one_div u

theorem mul_buchstabFunction {u : ℝ} (hu : 1 ≤ u) :
    u * buchstabFunction u = buchstabAux u := by
  rw [buchstabFunction_eq_aux_div hu]
  field_simp [show u ≠ 0 by linarith]

theorem buchstabAux_eq_one_add_integral {u : ℝ} (hu : 2 < u) :
    buchstabAux u = 1 + ∫ t in 1..u - 1, buchstabFunction t := by
  let n : ℕ := ⌈u⌉₊
  have hu1 : 1 ≤ u := by linarith
  have hun : u ≤ ((n + 1 : ℕ) : ℝ) + 2 := by
    dsimp [n]
    have hceil := Nat.le_ceil u
    norm_num at hceil ⊢
    linarith
  rw [buchstabAux_eq_stage hu1 hun,
    buchstabStage_succ_eq_integral hu]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (1 : ℝ) (u - 1) := by
    simpa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] using ht
  have htn : t ≤ (n : ℝ) + 2 := by
    dsimp [n]
    have hceil := Nat.le_ceil u
    linarith [ht'.2]
  change buchstabStage n t / t = buchstabFunction t
  rw [← buchstabAux_eq_stage ht'.1 htn,
    ← buchstabFunction_eq_aux_div ht'.1]

noncomputable def buchstabStageIntegrand (n : ℕ) (t : ℝ) : ℝ :=
  buchstabStage n (max t 1) / max t 1

theorem integral_buchstabStageIntegrand_eq {n : ℕ} {u : ℝ}
    (hu : 2 ≤ u) :
    (∫ t in 1..u - 1, buchstabStageIntegrand n t) =
      ∫ t in 1..u - 1, buchstabStage n t / t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (1 : ℝ) (u - 1) := by
    simpa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] using ht
  simp [buchstabStageIntegrand, max_eq_left ht'.1]

theorem continuous_buchstabStage : ∀ n : ℕ,
    Continuous (buchstabStage n)
  | 0 => by exact continuous_const
  | n + 1 => by
      have hstage := continuous_buchstabStage n
      have hmax : Continuous (fun t : ℝ ↦ max t 1) :=
        continuous_id.max continuous_const
      have hmax0 : ∀ t : ℝ, max t 1 ≠ 0 := fun t ↦ by
        have : (1 : ℝ) ≤ max t 1 := le_max_right _ _
        linarith
      have hint : Continuous (buchstabStageIntegrand n) := by
        unfold buchstabStageIntegrand
        exact (hstage.comp hmax).div hmax (hmax0)
      have hright : Continuous (fun u : ℝ ↦
          1 + ∫ t in 1..u - 1, buchstabStageIntegrand n t) := by
        have hprimitive : Continuous (fun v : ℝ ↦
            ∫ t in 1..v, buchstabStageIntegrand n t) :=
          (intervalIntegral.differentiable_integral_of_continuous hint).continuous
        exact continuous_const.add
          (hprimitive.comp (continuous_id.sub continuous_const))
      rw [show buchstabStage (n + 1) = fun u : ℝ ↦
          if u ≤ 2 then 1
          else 1 + ∫ t in 1..u - 1, buchstabStageIntegrand n t by
        funext u
        by_cases hu : u ≤ 2
        · simp [buchstabStage, hu]
        · rw [buchstabStage, ite_eq_right hu,
            integral_buchstabStageIntegrand_eq (le_of_not_ge hu)]
          simp [hu] ]
      apply continuous_if_le continuous_id continuous_const
      · exact continuous_const.continuousOn
      · exact hright.continuousOn
      · rintro u rfl
        norm_num

theorem continuousOn_buchstabAux : ContinuousOn buchstabAux (Set.Ici 1) := by
  intro u hu
  let n : ℕ := ⌈u⌉₊
  have huBound : u < (n : ℝ) + 2 := by
    dsimp [n]
    have hceil := Nat.le_ceil u
    linarith
  have hlocal : ∀ᶠ v in nhdsWithin u (Set.Ici (1 : ℝ)),
      buchstabAux v = buchstabStage n v := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds huBound),
      eventually_mem_nhdsWithin] with v hvBound hv1
    exact buchstabAux_eq_stage hv1 hvBound.le
  exact (continuous_buchstabStage n).continuousAt.continuousWithinAt.congr_of_eventuallyEq
    hlocal (buchstabAux_eq_stage hu huBound.le)

theorem continuousOn_buchstabFunction :
    ContinuousOn buchstabFunction (Set.Ici 1) := by
  have hdiv : ContinuousOn (fun u ↦ buchstabAux u / u) (Set.Ici (1 : ℝ)) :=
    continuousOn_buchstabAux.div continuousOn_id fun u hu ↦ by
      change 1 ≤ u at hu
      linarith
  exact hdiv.congr fun u hu ↦ buchstabFunction_eq_aux_div hu

noncomputable def buchstabContinuousExtension (t : ℝ) : ℝ :=
  buchstabFunction (max t 1)

theorem continuous_buchstabContinuousExtension :
    Continuous buchstabContinuousExtension := by
  have hmax : Continuous (fun t : ℝ ↦ max t 1) :=
    continuous_id.max continuous_const
  unfold buchstabContinuousExtension
  simpa only [Function.comp_def] using
    continuousOn_buchstabFunction.comp_continuous hmax
      (fun t ↦ le_max_right t 1)

theorem integral_buchstabContinuousExtension_eq {u : ℝ} (hu : 2 ≤ u) :
    (∫ t in 1..u - 1, buchstabContinuousExtension t) =
      ∫ t in 1..u - 1, buchstabFunction t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (1 : ℝ) (u - 1) := by
    simpa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] using ht
  simp [buchstabContinuousExtension, max_eq_left ht'.1]

theorem hasDerivAt_buchstabAux {u : ℝ} (hu : 2 < u) :
    HasDerivAt buchstabAux (buchstabFunction (u - 1)) u := by
  have hext := continuous_buchstabContinuousExtension
  have hprim := intervalIntegral.integral_hasDerivAt_right
    (a := (1 : ℝ)) (b := u - 1)
    (hext.intervalIntegrable _ _)
    hext.aestronglyMeasurable.stronglyMeasurableAtFilter hext.continuousAt
  have hcomp := hprim.comp u ((hasDerivAt_id u).sub_const 1)
  have hright : HasDerivAt
      (fun v : ℝ ↦ 1 + ∫ t in 1..v - 1, buchstabContinuousExtension t)
      (buchstabContinuousExtension (u - 1)) u := by
    have h := hcomp.const_add 1
    change HasDerivAt
      (fun v : ℝ ↦ 1 + ∫ t in 1..v - 1, buchstabContinuousExtension t)
      (buchstabContinuousExtension (u - 1) * 1) u at h
    simpa only [mul_one] using h
  have heq : buchstabAux =ᶠ[nhds u]
      fun v : ℝ ↦ 1 + ∫ t in 1..v - 1, buchstabContinuousExtension t := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    rw [buchstabAux_eq_one_add_integral hv,
      integral_buchstabContinuousExtension_eq hv.le]
  have h := hright.congr_of_eventuallyEq heq
  simpa [buchstabContinuousExtension, max_eq_left (by linarith : (1 : ℝ) ≤ u - 1)] using h

theorem hasDerivAt_mul_buchstabFunction {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun v ↦ v * buchstabFunction v)
      (buchstabFunction (u - 1)) u := by
  have heq : (fun v : ℝ ↦ v * buchstabFunction v) =ᶠ[nhds u] buchstabAux := by
    filter_upwards [Ioi_mem_nhds (show 1 < u by linarith)] with v hv
    exact mul_buchstabFunction hv.le
  exact (hasDerivAt_buchstabAux hu).congr_of_eventuallyEq heq

theorem hasDerivAt_buchstabFunction {u : ℝ} (hu : 2 < u) :
    HasDerivAt buchstabFunction
      ((buchstabFunction (u - 1) - buchstabFunction u) / u) u := by
  have hu0 : u ≠ 0 := by linarith
  have hquot := (hasDerivAt_buchstabAux hu).div (hasDerivAt_id u) hu0
  have hEq : ∀ᶠ v in nhds u, buchstabFunction v = buchstabAux v / v := by
    filter_upwards [Ioi_mem_nhds (show 1 < u by linarith)] with v hv
    exact buchstabFunction_eq_aux_div hv.le
  have h := hquot.congr_of_eventuallyEq hEq
  apply h.congr_deriv
  dsimp only [id_eq, one_mul]
  rw [← mul_buchstabFunction (show 1 ≤ u by linarith)]
  field_simp

theorem buchstabStage_nonneg : ∀ n : ℕ, ∀ {u : ℝ}, 1 ≤ u →
    0 ≤ buchstabStage n u
  | 0, _, _ => by simp [buchstabStage]
  | n + 1, u, hu => by
      by_cases hu2 : u ≤ 2
      · simp [buchstabStage, hu2]
      · rw [buchstabStage_succ_eq_integral (lt_of_not_ge hu2)]
        have hInt : 0 ≤ ∫ t in 1..u - 1, buchstabStage n t / t := by
          apply intervalIntegral.integral_nonneg (by linarith)
          intro t ht
          have ht1 : 1 ≤ t := by linarith [ht.1]
          exact div_nonneg (buchstabStage_nonneg n ht1) (by linarith)
        linarith

theorem buchstabStage_one_le : ∀ n : ℕ, ∀ {u : ℝ}, 1 ≤ u →
    1 ≤ buchstabStage n u
  | 0, _, _ => by simp [buchstabStage]
  | n + 1, u, hu => by
      by_cases hu2 : u ≤ 2
      · simp [buchstabStage, hu2]
      · rw [buchstabStage_succ_eq_integral (lt_of_not_ge hu2)]
        have hInt : 0 ≤ ∫ t in 1..u - 1, buchstabStage n t / t := by
          apply intervalIntegral.integral_nonneg (by linarith)
          intro t ht
          have ht1 : 1 ≤ t := by linarith [ht.1]
          exact div_nonneg (buchstabStage_nonneg n ht1) (by linarith)
        linarith

theorem buchstabAux_one_le {u : ℝ} (hu : 1 ≤ u) :
    1 ≤ buchstabAux u := by
  rw [buchstabAux_eq_stage (n := ⌈u⌉₊) hu
    ((Nat.le_ceil u).trans (by norm_num))]
  exact buchstabStage_one_le _ hu

theorem buchstabFunction_nonneg {u : ℝ} (hu : 1 ≤ u) :
    0 ≤ buchstabFunction u := by
  rw [buchstabFunction_eq_aux_div hu]
  exact div_nonneg (buchstabAux_one_le hu |>.trans' zero_le_one) (by linarith)

theorem buchstabFunction_le_one_induction : ∀ n : ℕ,
    ∀ {u : ℝ}, 1 ≤ u → u ≤ n + 2 → buchstabFunction u ≤ 1
  | 0, u, hu1, hu2 => by
      rw [buchstabFunction_eq_inv hu1 (by simpa using hu2)]
      exact inv_le_one_of_one_le₀ hu1
  | n + 1, u, hu1, huN => by
      by_cases hu2 : u ≤ 2
      · rw [buchstabFunction_eq_inv hu1 hu2]
        exact inv_le_one_of_one_le₀ hu1
      · have hu2' : 2 < u := lt_of_not_ge hu2
        rw [buchstabFunction_eq_aux_div hu1,
          buchstabAux_eq_one_add_integral hu2']
        rw [div_le_iff₀ (by linarith : 0 < u)]
        have hInt : (∫ t in 1..u - 1, buchstabFunction t) ≤ u - 2 := by
          have hcont : ContinuousOn buchstabFunction (Set.Icc (1 : ℝ) (u - 1)) :=
            continuousOn_buchstabFunction.mono (by
              intro t ht
              exact ht.1)
          calc
            (∫ t in 1..u - 1, buchstabFunction t) ≤
                ∫ _t in 1..u - 1, (1 : ℝ) := by
              apply intervalIntegral.integral_mono_on (by linarith)
              · exact ContinuousOn.intervalIntegrable (by
                  rwa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)])
              · exact continuousOn_const.intervalIntegrable
              · intro t ht
                have ht1 : 1 ≤ t := ht.1
                have htu : t ≤ n + 2 := by
                  norm_num at huN ⊢
                  linarith [ht.2]
                exact buchstabFunction_le_one_induction n ht1 htu
            _ = u - 2 := by simp <;> ring
        linarith

theorem buchstabFunction_le_one {u : ℝ} (hu : 1 ≤ u) :
    buchstabFunction u ≤ 1 := by
  let n : ℕ := ⌈u⌉₊
  apply buchstabFunction_le_one_induction n hu
  dsimp [n]
  exact (Nat.le_ceil u).trans (by norm_num)

theorem abs_buchstabFunction_le_one {u : ℝ} (hu : 1 ≤ u) :
    |buchstabFunction u| ≤ 1 := by
  rw [abs_of_nonneg (buchstabFunction_nonneg hu)]
  exact buchstabFunction_le_one hu

theorem abs_deriv_buchstabFunction_le_two_div {u : ℝ} (hu : 2 < u) :
    |deriv buchstabFunction u| ≤ 2 / u := by
  rw [(hasDerivAt_buchstabFunction hu).deriv, abs_div,
    abs_of_pos (by linarith : 0 < u)]
  have hnum : |buchstabFunction (u - 1) - buchstabFunction u| ≤ 2 := by
    calc
      |buchstabFunction (u - 1) - buchstabFunction u| ≤
          |buchstabFunction (u - 1)| + |buchstabFunction u| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add
        (abs_buchstabFunction_le_one (by linarith))
        (abs_buchstabFunction_le_one (by linarith))
      _ = 2 := by norm_num
  exact div_le_div_of_nonneg_right hnum (by linarith)

theorem abs_buchstabFunction_sub_shift_le_two_div {u : ℝ} (hu : 3 < u) :
    |buchstabFunction u - buchstabFunction (u - 1)| ≤ 2 / (u - 1) := by
  have hdiff : ∀ x ∈ Set.Icc (u - 1) u,
      DifferentiableAt ℝ buchstabFunction x := by
    intro x hx
    exact (hasDerivAt_buchstabFunction (by linarith [hx.1])).differentiableAt
  have hbound : ∀ x ∈ Set.Icc (u - 1) u,
      ‖deriv buchstabFunction x‖ ≤ 2 / (u - 1) := by
    intro x hx
    rw [Real.norm_eq_abs]
    calc
      |deriv buchstabFunction x| ≤ 2 / x :=
        abs_deriv_buchstabFunction_le_two_div (by linarith [hx.1])
      _ ≤ 2 / (u - 1) := by
        exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hx.1
  have hmv := (convex_Icc (u - 1) u).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (Set.left_mem_Icc.mpr (by linarith))
      (Set.right_mem_Icc.mpr (by linarith))
  convert hmv using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

theorem abs_deriv_buchstabFunction_le_two_div_mul_sub_one {u : ℝ}
    (hu : 3 < u) :
    |deriv buchstabFunction u| ≤ 2 / (u * (u - 1)) := by
  rw [(hasDerivAt_buchstabFunction (by linarith)).deriv, abs_div,
    abs_of_pos (by linarith : 0 < u)]
  have h := abs_buchstabFunction_sub_shift_le_two_div hu
  rw [abs_sub_comm] at h
  calc
    |buchstabFunction (u - 1) - buchstabFunction u| / u ≤
        (2 / (u - 1)) / u :=
      div_le_div_of_nonneg_right h (by linarith)
    _ = 2 / (u * (u - 1)) := by
      field_simp [show u ≠ 0 by linarith, show u - 1 ≠ 0 by linarith]

theorem continuousOn_deriv_buchstabFunction :
    ContinuousOn (deriv buchstabFunction) (Set.Ioi 2) := by
  have hω : ContinuousOn buchstabFunction (Set.Ioi (2 : ℝ)) :=
    continuousOn_buchstabFunction.mono (Set.Ioi_subset_Ici_self.trans
      (Set.Ici_subset_Ici.mpr (by norm_num)))
  have hshift : ContinuousOn (fun u : ℝ ↦ buchstabFunction (u - 1))
      (Set.Ioi 2) := by
    apply continuousOn_buchstabFunction.comp
      (continuousOn_id.sub continuousOn_const)
    intro u hu
    change 1 ≤ u - 1
    linarith [Set.mem_Ioi.mp hu]
  have hformula : ContinuousOn
      (fun u : ℝ ↦ (buchstabFunction (u - 1) - buchstabFunction u) / u)
      (Set.Ioi 2) :=
    (hshift.sub hω).div continuousOn_id fun u hu ↦ by
      exact ne_of_gt (by linarith [Set.mem_Ioi.mp hu])
  exact hformula.congr fun u hu ↦
    (hasDerivAt_buchstabFunction (Set.mem_Ioi.mp hu)).deriv

theorem integrableOn_deriv_buchstabFunction :
    IntegrableOn (deriv buchstabFunction) (Set.Ioi 3) := by
  have hmodel : IntegrableOn
      (fun x : ℝ ↦ 2 * (x + (-1)) ^ (-2 : ℝ)) (Set.Ioi 3) :=
    (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := (3 : ℝ))
      (m := (-1 : ℝ)) (by norm_num) (by norm_num)).const_mul 2
  apply hmodel.mono'
  · exact (continuousOn_deriv_buchstabFunction.mono
      (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx3 : 3 < x := Set.mem_Ioi.mp hx
    rw [Real.norm_eq_abs]
    calc
      |deriv buchstabFunction x| ≤ 2 / (x * (x - 1)) :=
        abs_deriv_buchstabFunction_le_two_div_mul_sub_one hx3
      _ ≤ 2 / ((x - 1) * (x - 1)) := by
        exact div_le_div_of_nonneg_left (by norm_num)
          (mul_pos (by linarith) (by linarith))
          (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
      _ = 2 * (x + (-1)) ^ (-2 : ℝ) := by
        rw [show x + (-1) = x - 1 by ring,
          show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num,
          Real.rpow_intCast]
        norm_num [div_eq_mul_inv, zpow_neg]
        field_simp [show x - 1 ≠ 0 by linarith]

noncomputable def buchstabLimit : ℝ :=
  limUnder atTop buchstabFunction

theorem tendsto_buchstabFunction_atTop :
    Tendsto buchstabFunction atTop (nhds buchstabLimit) := by
  exact tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (a := (3 : ℝ))
    (fun x hx ↦ ((hasDerivAt_buchstabFunction
      (by linarith [Set.mem_Ioi.mp hx])).differentiableAt).hasDerivAt)
    integrableOn_deriv_buchstabFunction

noncomputable def buchstabLaplace (s : ℝ) : ℝ :=
  ∫ u in Set.Ioi (1 : ℝ), buchstabFunction u * Real.exp (-s * u)

theorem measurable_buchstabFunction : Measurable buchstabFunction := by
  have hlow : ContinuousOn buchstabFunction (Set.Iio (1 : ℝ)) := by
    have hz : ∀ u ∈ Set.Iio (1 : ℝ), buchstabFunction u = 0 := by
      intro u hu
      rw [buchstabFunction, ite_eq_left (Set.mem_Iio.mp hu)]
    exact continuousOn_const.congr fun u hu ↦ hz u hu
  have hhigh : ContinuousOn buchstabFunction (Set.Ici (1 : ℝ)) :=
    continuousOn_buchstabFunction
  have hpiece : buchstabFunction = (Set.Ici (1 : ℝ)).piecewise
      buchstabFunction (fun _ ↦ 0) := by
    funext u
    by_cases hu : 1 ≤ u
    · simp [hu]
    · simp [Set.piecewise, hu, buchstabFunction, lt_of_not_ge hu]
  rw [hpiece]
  exact hhigh.measurable_piecewise
    (continuousOn_const.mono (by
      intro u hu
      exact Set.mem_Iio.mpr (lt_of_not_ge hu))) measurableSet_Ici

theorem integrableOn_buchstabLaplace_integrand {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦
      buchstabFunction u * Real.exp (-s * u)) (Set.Ioi 1) := by
  have hexp : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u)) (Set.Ioi 1) :=
    exp_neg_integrableOn_Ioi 1 hs
  apply hexp.mono'
  · have hprod : Measurable (fun u : ℝ ↦
        buchstabFunction u * Real.exp (-s * u)) :=
      measurable_buchstabFunction.mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -s * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hprod.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (abs_buchstabFunction_le_one (Set.mem_Ioi.mp hu).le)

theorem integrableOn_id_mul_exp_neg_mul {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦ u * Real.exp (-s * u)) (Set.Ioi 1) := by
  let f : ℝ → ℝ := fun t ↦ Real.exp (-t) * t
  have hf : IntegrableOn f (Set.Ioi 0) := by
    have h := Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    norm_num [f, Real.rpow_one, mul_comm]
  have hcomp : IntegrableOn (fun u : ℝ ↦ f (s * u)) (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff f 0 hs).mpr (by simpa using hf)
  have hscaled : IntegrableOn (fun u : ℝ ↦ s⁻¹ * f (s * u)) (Set.Ioi 0) :=
    Integrable.const_mul hcomp s⁻¹
  have htarget : IntegrableOn (fun u : ℝ ↦
      u * Real.exp (-s * u)) (Set.Ioi 0) := by
    apply hscaled.congr_fun _ measurableSet_Ioi
    intro u hu
    dsimp [f]
    field_simp [hs.ne']
  exact htarget.mono_set (Set.Ioi_subset_Ioi (by norm_num))

theorem integrableOn_buchstabLaplace_deriv_integrand {s : ℝ}
    (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦
      -u * buchstabFunction u * Real.exp (-s * u)) (Set.Ioi 1) := by
  have hmodel := integrableOn_id_mul_exp_neg_mul hs
  apply hmodel.mono'
  · have hm : Measurable (fun u : ℝ ↦
        -u * buchstabFunction u * Real.exp (-s * u)) :=
      (measurable_id.neg.mul measurable_buchstabFunction).mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -s * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := (Set.mem_Ioi.mp hu).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_neg, abs_of_pos (by linarith : 0 < u)]
    calc
      u * |buchstabFunction u| * Real.exp (-s * u) ≤
          u * 1 * Real.exp (-s * u) := by
        gcongr
        exact abs_buchstabFunction_le_one hu1
      _ = u * Real.exp (-s * u) := by ring

theorem hasDerivAt_buchstabLaplace {s : ℝ} (hs : 0 < s) :
    HasDerivAt buchstabLaplace
      (∫ u in Set.Ioi (1 : ℝ),
        -(u * buchstabFunction u * Real.exp (-s * u))) s := by
  let P : ℝ → ℝ → ℝ := fun x u ↦
    buchstabFunction u * Real.exp (-x * u)
  let P' : ℝ → ℝ → ℝ := fun x u ↦
    -u * buchstabFunction u * Real.exp (-x * u)
  let b : ℝ → ℝ := fun u ↦
    u * Real.exp (-(s / 2) * u)
  have hsHalf : 0 < s / 2 := by linarith
  have hnhds : Set.Ioi (s / 2) ∈ nhds s := Ioi_mem_nhds (by linarith)
  have hPmeas : ∀ᶠ x in nhds s,
      AEStronglyMeasurable (P x) (volume.restrict (Set.Ioi 1)) := by
    filter_upwards with x
    have hm : Measurable (P x) := by
      unfold P
      exact measurable_buchstabFunction.mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -x * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hm.aestronglyMeasurable
  have hPint : Integrable (P s) (volume.restrict (Set.Ioi 1)) := by
    change IntegrableOn (P s) (Set.Ioi 1)
    simpa [P] using integrableOn_buchstabLaplace_integrand hs
  have hP'meas : AEStronglyMeasurable (P' s)
      (volume.restrict (Set.Ioi 1)) := by
    have hm : Measurable (P' s) := by
      unfold P'
      exact (measurable_id.neg.mul measurable_buchstabFunction).mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -s * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hm.aestronglyMeasurable
  have hbint : Integrable b (volume.restrict (Set.Ioi 1)) := by
    change IntegrableOn b (Set.Ioi 1)
    simpa [b] using integrableOn_id_mul_exp_neg_mul hsHalf
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi 1)),
      ∀ x ∈ Set.Ioi (s / 2), ‖P' x u‖ ≤ b u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro x hx
    have hu1 : 1 ≤ u := (Set.mem_Ioi.mp hu).le
    have hu0 : 0 ≤ u := zero_le_one.trans hu1
    have hexp : Real.exp (-x * u) ≤ Real.exp (-(s / 2) * u) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Set.mem_Ioi.mp hx]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg hu0, abs_of_pos (Real.exp_pos _)]
    dsimp [P', b]
    calc
      u * |buchstabFunction u| * Real.exp (-x * u) ≤
          u * 1 * Real.exp (-x * u) := by
        gcongr
        exact abs_buchstabFunction_le_one hu1
      _ ≤ u * Real.exp (-(s / 2) * u) := by
        simpa using mul_le_mul_of_nonneg_left hexp hu0
  have hdiff : ∀ᵐ u ∂(volume.restrict (Set.Ioi 1)),
      ∀ x ∈ Set.Ioi (s / 2), HasDerivAt (P · u) (P' x u) x := by
    filter_upwards with u
    intro x hx
    have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (-y * u))
        (-u * Real.exp (-x * u)) x := by
      have hinner : HasDerivAt (fun y : ℝ ↦ -y * u) (-u) x := by
        simpa [mul_neg, neg_mul] using (hasDerivAt_id x).mul_const (-u)
      apply hinner.exp.congr_deriv
      ring
    dsimp [P, P']
    have hc := hexp.const_mul (buchstabFunction u)
    apply hc.congr_deriv
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := P) (x₀ := s) (s := Set.Ioi (s / 2)) (bound := b)
    hnhds hPmeas hPint hP'meas hbound hbint hdiff
  change HasDerivAt
    (fun n : ℝ ↦ ∫ u in Set.Ioi (1 : ℝ),
      buchstabFunction u * Real.exp (-n * u))
    (∫ u in Set.Ioi (1 : ℝ),
      -(u * buchstabFunction u * Real.exp (-s * u))) s
  simpa [P, P'] using hmain.2

theorem differentiableOn_buchstabLaplace :
    DifferentiableOn ℝ buchstabLaplace (Set.Ioi 0) := by
  intro s hs
  exact DifferentiableAt.differentiableWithinAt
    (hasDerivAt_buchstabLaplace (Set.mem_Ioi.mp hs)).differentiableAt

theorem integrableOn_buchstabShift_mul_exp {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦
      buchstabFunction (u - 1) * Real.exp (-s * u)) (Set.Ioi 2) := by
  have hexp : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u)) (Set.Ioi 2) :=
    exp_neg_integrableOn_Ioi 2 hs
  apply hexp.mono'
  · have hm : Measurable (fun u : ℝ ↦
        buchstabFunction (u - 1) * Real.exp (-s * u)) :=
      (measurable_buchstabFunction.comp
        (measurable_id.sub measurable_const)).mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -s * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u - 1 := by linarith [Set.mem_Ioi.mp hu]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (abs_buchstabFunction_le_one hu1)

theorem integrableOn_mul_buchstab_mul_exp_deriv {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦
      (u * buchstabFunction u) * (-s * Real.exp (-s * u))) (Set.Ioi 2) := by
  have hbase := integrableOn_buchstabLaplace_deriv_integrand hs
  have hscaled : IntegrableOn (fun u : ℝ ↦
      s * (-u * buchstabFunction u * Real.exp (-s * u))) (Set.Ioi 1) :=
    Integrable.const_mul hbase s
  have hcongr : IntegrableOn (fun u : ℝ ↦
      (u * buchstabFunction u) * (-s * Real.exp (-s * u))) (Set.Ioi 1) := by
    apply hscaled.congr_fun _ measurableSet_Ioi
    intro u hu
    ring
  exact hcongr.mono_set (Set.Ioi_subset_Ioi (by norm_num))

theorem integral_mul_buchstab_mul_exp_Ioi_two {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Ioi (2 : ℝ),
      (u * buchstabFunction u) * Real.exp (-s * u)) =
      Real.exp (-s * 2) / s +
        (1 / s) * ∫ u in Set.Ioi (2 : ℝ),
          buchstabFunction (u - 1) * Real.exp (-s * u) := by
  let g : ℝ → ℝ := fun u ↦ u * buchstabFunction u
  let g' : ℝ → ℝ := fun u ↦ buchstabFunction (u - 1)
  let e : ℝ → ℝ := fun u ↦ Real.exp (-s * u)
  let e' : ℝ → ℝ := fun u ↦ -s * Real.exp (-s * u)
  have hg : ∀ u ∈ Set.Ioi (2 : ℝ), HasDerivAt g (g' u) u := by
    intro u hu
    exact hasDerivAt_mul_buchstabFunction (Set.mem_Ioi.mp hu)
  have he : ∀ u ∈ Set.Ioi (2 : ℝ), HasDerivAt e (e' u) u := by
    intro u hu
    dsimp [e, e']
    have hinner : HasDerivAt (fun x : ℝ ↦ -s * x) (-s) u := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul (-s)
    apply hinner.exp.congr_deriv
    ring
  have hge' : IntegrableOn (g * e') (Set.Ioi (2 : ℝ)) := by
    change IntegrableOn (fun u : ℝ ↦
      (u * buchstabFunction u) * (-s * Real.exp (-s * u))) (Set.Ioi 2)
    exact integrableOn_mul_buchstab_mul_exp_deriv hs
  have hg'e : IntegrableOn (g' * e) (Set.Ioi (2 : ℝ)) := by
    change IntegrableOn (fun u : ℝ ↦
      buchstabFunction (u - 1) * Real.exp (-s * u)) (Set.Ioi 2)
    exact integrableOn_buchstabShift_mul_exp hs
  have hzero : Tendsto (g * e) (nhdsWithin 2 (Set.Ioi 2))
      (nhds (Real.exp (-s * 2))) := by
    have hω2 : ContinuousAt buchstabFunction 2 :=
      continuousOn_buchstabFunction.continuousAt
        (Ici_mem_nhds (by norm_num))
    have hprod : ContinuousAt (fun u : ℝ ↦
        (u * buchstabFunction u) * Real.exp (-s * u)) 2 :=
      (continuousAt_id.mul hω2).mul
        (Real.continuous_exp.continuousAt.comp
          ((continuousAt_const.mul continuousAt_id)))
    have ht : Tendsto (fun u : ℝ ↦
        (u * buchstabFunction u) * Real.exp (-s * u))
        (nhdsWithin 2 (Set.Ioi 2))
        (nhds ((2 * buchstabFunction 2) * Real.exp (-s * 2))) :=
      hprod.tendsto.mono_left inf_le_left
    change Tendsto (fun u : ℝ ↦
      (u * buchstabFunction u) * Real.exp (-s * u))
      (nhdsWithin 2 (Set.Ioi 2)) (nhds (Real.exp (-s * 2)))
    simpa [buchstabFunction_eq_inv (u := (2 : ℝ))
      (by norm_num) (by norm_num)] using ht
  have hinfty : Tendsto (g * e) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun u : ℝ ↦
      u ^ (1 : ℝ) * Real.exp (-s * u))
    · filter_upwards with u
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      have hu0 : 0 ≤ u := zero_le_one.trans hu
      change ‖(u * buchstabFunction u) * Real.exp (-s * u)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hu0, abs_of_pos (Real.exp_pos _)]
      calc
        u * |buchstabFunction u| * Real.exp (-s * u) ≤
            u * 1 * Real.exp (-s * u) := by
          gcongr
          exact abs_buchstabFunction_le_one hu
        _ = u ^ (1 : ℝ) * Real.exp (-s * u) := by
          rw [Real.rpow_one, mul_one]
    · exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 s hs
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    hg he hge' hg'e hzero hinfty
  have hleft : (∫ u in Set.Ioi (2 : ℝ), g u * e' u) =
      -s * ∫ u in Set.Ioi (2 : ℝ), g u * e u := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp [e']
    ring
  rw [hleft] at hibp
  dsimp [g, g', e] at hibp ⊢
  have hs0 : s ≠ 0 := hs.ne'
  let A := ∫ u in Set.Ioi (2 : ℝ),
    u * buchstabFunction u * Real.exp (-s * u)
  let B := ∫ u in Set.Ioi (2 : ℝ),
    buchstabFunction (u - 1) * Real.exp (-s * u)
  let E := Real.exp (-s * 2)
  have hAB : s * A = E + B := by
    dsimp [A, B, E]
    linarith [hibp]
  change A = E / s + (1 / s) * B
  calc
    A = (E + B) / s := (eq_div_iff hs0).2 (by simpa [mul_comm] using hAB)
    _ = E / s + (1 / s) * B := by field_simp [hs0]

theorem integral_buchstabShift_mul_exp_Ioi_two {s : ℝ} :
    (∫ u in Set.Ioi (2 : ℝ),
      buchstabFunction (u - 1) * Real.exp (-s * u)) =
      Real.exp (-s) * buchstabLaplace s := by
  let h : ℝ → ℝ := fun u ↦
    buchstabFunction (u - 1) * Real.exp (-s * u)
  calc
    (∫ u in Set.Ioi (2 : ℝ),
        buchstabFunction (u - 1) * Real.exp (-s * u)) =
        ∫ u : ℝ, (Set.Ioi (2 : ℝ)).indicator h u := by
      rw [integral_indicator measurableSet_Ioi]
    _ = ∫ v : ℝ, (Set.Ioi (2 : ℝ)).indicator h (v + 1) := by
      rw [integral_add_right_eq_self]
    _ = ∫ v : ℝ, (Set.Ioi (1 : ℝ)).indicator
        (fun v ↦ Real.exp (-s) *
          (buchstabFunction v * Real.exp (-s * v))) v := by
      apply integral_congr_ae
      filter_upwards with v
      by_cases hv : 1 < v
      · rw [Set.indicator_of_mem (show v + 1 ∈ Set.Ioi (2 : ℝ) by
            exact Set.mem_Ioi.mpr (by linarith)),
          Set.indicator_of_mem (Set.mem_Ioi.mpr hv)]
        dsimp [h]
        rw [show v + 1 - 1 = v by ring,
          show -s * (v + 1) = -s + (-s * v) by ring, Real.exp_add]
        ring_nf
      · rw [Set.indicator_of_notMem (show v + 1 ∉ Set.Ioi (2 : ℝ) by
            intro hv'
            exact hv (by linarith [Set.mem_Ioi.mp hv'])),
          Set.indicator_of_notMem (show v ∉ Set.Ioi (1 : ℝ) by exact hv)]
    _ = ∫ v in Set.Ioi (1 : ℝ), Real.exp (-s) *
          (buchstabFunction v * Real.exp (-s * v)) := by
      rw [integral_indicator measurableSet_Ioi]
    _ = Real.exp (-s) * buchstabLaplace s := by
      rw [integral_const_mul]
      rfl

theorem integral_mul_buchstab_mul_exp_Ioi_one {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Ioi (1 : ℝ),
      (u * buchstabFunction u) * Real.exp (-s * u)) =
      (Real.exp (-s) / s) * (1 + buchstabLaplace s) := by
  let q : ℝ → ℝ := fun u ↦
    (u * buchstabFunction u) * Real.exp (-s * u)
  have hq1 : IntegrableOn q (Set.Ioi (1 : ℝ)) := by
    have h := (integrableOn_buchstabLaplace_deriv_integrand hs).neg
    apply h.congr_fun _ measurableSet_Ioi
    intro u hu
    dsimp [q]
    ring
  have hq2 : IntegrableOn q (Set.Ioi (2 : ℝ)) :=
    hq1.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hq1 hq2
  have hfinite : (∫ u in (1 : ℝ)..2, q u) =
      ∫ u in (1 : ℝ)..2, Real.exp (-s * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (1 : ℝ) 2 := by
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hu
    dsimp [q]
    rw [buchstabFunction_eq_inv hu'.1 hu'.2]
    have hu0 : u ≠ 0 := ne_of_gt (zero_lt_one.trans_le hu'.1)
    field_simp [hu0]
  have hexp1 : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u))
      (Set.Ioi 1) := exp_neg_integrableOn_Ioi 1 hs
  have hexp2 : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u))
      (Set.Ioi 2) := exp_neg_integrableOn_Ioi 2 hs
  have hexpSplit := intervalIntegral.integral_interval_add_Ioi hexp1 hexp2
  have hexpTail (c : ℝ) :
      (∫ u in Set.Ioi c, Real.exp (-s * u)) = Real.exp (-s * c) / s := by
    have h := integral_exp_mul_Ioi (a := -s) (by linarith) c
    rw [h]
    field_simp [hs.ne']
  rw [hexpTail 1, hexpTail 2] at hexpSplit
  rw [hfinite] at hsplit
  have htail := integral_mul_buchstab_mul_exp_Ioi_two hs
  rw [integral_buchstabShift_mul_exp_Ioi_two] at htail
  dsimp [q] at hsplit ⊢
  rw [htail] at hsplit
  have hs0 : s ≠ 0 := hs.ne'
  field_simp [hs0] at hexpSplit hsplit ⊢
  nlinarith [hsplit, hexpSplit]

theorem buchstabLaplace_nonneg {s : ℝ} : 0 ≤ buchstabLaplace s := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact mul_nonneg
    (buchstabFunction_nonneg (Set.mem_Ioi.mp hu).le)
    (Real.exp_pos _).le

theorem buchstabLaplace_ode {s : ℝ} (hs : 0 < s) :
    s * deriv buchstabLaplace s +
      Real.exp (-s) * (1 + buchstabLaplace s) = 0 := by
  have hd := (hasDerivAt_buchstabLaplace hs).deriv
  rw [integral_neg] at hd
  have htotal := integral_mul_buchstab_mul_exp_Ioi_one hs
  rw [hd, htotal]
  field_simp [hs.ne']
  ring

theorem tendsto_buchstabLaplace_atTop :
    Tendsto buchstabLaplace atTop (nhds 0) := by
  apply squeeze_zero' (g := fun s : ℝ ↦ Real.exp (-s))
  · filter_upwards with s
    exact buchstabLaplace_nonneg
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs1
    have hs : 0 < s := zero_lt_one.trans_le hs1
    have hFint := integrableOn_buchstabLaplace_integrand hs
    have hexp : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u))
        (Set.Ioi 1) := exp_neg_integrableOn_Ioi 1 hs
    have hle : buchstabLaplace s ≤
        ∫ u in Set.Ioi (1 : ℝ), Real.exp (-s * u) := by
      apply setIntegral_mono_on hFint hexp measurableSet_Ioi
      intro u hu
      exact mul_le_of_le_one_left (Real.exp_pos _).le
        (buchstabFunction_le_one (Set.mem_Ioi.mp hu).le)
    have heval : (∫ u in Set.Ioi (1 : ℝ), Real.exp (-s * u)) =
        Real.exp (-s) / s := by
      have h := integral_exp_mul_Ioi (a := -s) (by linarith) 1
      rw [h]
      field_simp [hs.ne']
    rw [heval] at hle
    exact hle.trans (div_le_self (Real.exp_pos _).le hs1)
  · exact Real.tendsto_exp_neg_atTop_nhds_zero

theorem one_add_buchstabLaplace_eq_exponentialIntegral {s : ℝ} (hs : 0 < s) :
    1 + buchstabLaplace s = Real.exp
      (∫ t in Set.Ioi s, Real.exp (-t) / t) := by
  exact laplace_ode_solution differentiableOn_buchstabLaplace
    (fun x hx ↦ by linarith [buchstabLaplace_nonneg (s := x)])
    (fun x hx ↦ buchstabLaplace_ode hx)
    tendsto_buchstabLaplace_atTop s hs

theorem buchstabLimit_eq_exp_neg_eulerMascheroniConstant :
    buchstabLimit = Real.exp (-Real.eulerMascheroniConstant) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hzero : Tendsto (fun s : ℝ ↦ s) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hleft : Tendsto (fun s : ℝ ↦
      s * (1 + buchstabLaplace s)) l (nhds buchstabLimit) := by
    have hab : Tendsto (fun s : ℝ ↦ s * buchstabLaplace s) l
        (nhds buchstabLimit) :=
      laplace_final_value_of_tendsto buchstabFunction buchstabLimit 1
        measurable_buchstabFunction (by norm_num)
        (fun u hu ↦ abs_buchstabFunction_le_one hu)
        tendsto_buchstabFunction_atTop
    have hsum := hzero.add hab
    simpa [mul_add] using hsum
  have hright : Tendsto (fun s : ℝ ↦
      s * (1 + buchstabLaplace s)) l
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    apply exponentialIntegral_exp_limit.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [one_add_buchstabLaplace_eq_exponentialIntegral hs]
  exact tendsto_nhds_unique hleft hright

end

end ErdosAverageCertificates

end

section

namespace NumberTheoryLean.BuchstabBridge

open MeasureTheory Filter
open scoped Topology
open LinearSieveFunctions

theorem plus_eq_buchstabAux {s : ℝ} (hs : 1 ≤ s) :
    plus (s - 1) = ErdosAverageCertificates.buchstabAux s := by
  apply DelayUniqueness.shifted_unique 1 (fun u => plus (u - 1)) ErdosAverageCertificates.buchstabAux
  · intro u _ hu2
    exact plus_initial (by linarith)
  · intro u hu1 hu2
    exact ErdosAverageCertificates.buchstabAux_eq_one hu1 hu2
  · intro u hu
    simpa only [plus, one_mul] using
      DelayConstruction.delay_integral_of_one_le 1 (u := u - 1) (by linarith)
  · intro u hu
    rw [ErdosAverageCertificates.buchstabAux_eq_one_add_integral hu, one_mul]
    apply congrArg (fun I : ℝ => 1 + I)
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
    exact ErdosAverageCertificates.buchstabFunction_eq_aux_div ht.1
  · exact hs

theorem plus_div_eq_buchstabFunction {s : ℝ} (hs : 1 ≤ s) :
    plus (s - 1) / s = ErdosAverageCertificates.buchstabFunction s := by
  rw [plus_eq_buchstabAux hs]
  exact (ErdosAverageCertificates.buchstabFunction_eq_aux_div hs).symm

theorem pair_sum_eq_buchstab (A : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    F A s + f A s = A * ErdosAverageCertificates.buchstabFunction s := by
  rw [← plus_div_eq_buchstabFunction hs, f_eq_difference]
  unfold F
  have hs0 : s ≠ 0 := by linarith
  field_simp
  ring

noncomputable def sieveA : ℝ := 2 * Real.exp Real.eulerMascheroniConstant

theorem sieveA_pos : 0 < sieveA := by unfold sieveA; positivity

theorem sieveA_gt_two : 2 < sieveA := by
  have hgamma : 0 < Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hexp : 1 < Real.exp Real.eulerMascheroniConstant := Real.one_lt_exp_iff.mpr hgamma
  unfold sieveA
  linarith

theorem sieveA_normalization : sieveA * Real.exp (-Real.eulerMascheroniConstant) = 2 := by
  unfold sieveA
  rw [mul_assoc, ← Real.exp_add]
  simp

theorem normalized_pair_sum_tendsto_two :
    Tendsto (fun s : ℝ => F sieveA s + f sieveA s) atTop (𝓝 2) := by
  have hlim := ErdosAverageCertificates.tendsto_buchstabFunction_atTop.const_mul sieveA
  rw [ErdosAverageCertificates.buchstabLimit_eq_exp_neg_eulerMascheroniConstant,
    sieveA_normalization] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  exact (pair_sum_eq_buchstab sieveA hs).symm

theorem pair_gap_tendsto_zero (A : ℝ) :
    Tendsto (fun s : ℝ => F A s - f A s) atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b + 1, fun s hs => by linarith⟩
  have hrho := DickmanDecay.rho_tendsto_zero.comp hshift
  have hlim := (hrho.const_mul A).mul (tendsto_inv_atTop_zero : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0))
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  rw [gap_identity A hs, div_eq_mul_inv]
  rfl

theorem normalized_F_tendsto_one : Tendsto (F sieveA) atTop (𝓝 1) := by
  have hlim := (normalized_pair_sum_tendsto_two.add (pair_gap_tendsto_zero sieveA)).div_const 2
  norm_num at hlim
  apply hlim.congr
  intro s
  ring

theorem normalized_f_tendsto_one : Tendsto (f sieveA) atTop (𝓝 1) := by
  have hlim := (normalized_pair_sum_tendsto_two.sub (pair_gap_tendsto_zero sieveA)).div_const 2
  norm_num at hlim
  apply hlim.congr
  intro s
  ring

end NumberTheoryLean.BuchstabBridge

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightFutureIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.NormalizedDeficits

open Filter Set
open scoped Topology
open LinearSieveFunctions BuchstabBridge

noncomputable def lowerDeficit (s : ℝ) : ℝ := 1 - f sieveA s
noncomputable def upperDeficit (s : ℝ) : ℝ := F sieveA s - 1
noncomputable def gap (s : ℝ) : ℝ := F sieveA s - f sieveA s

theorem deficit_sum (s : ℝ) : lowerDeficit s + upperDeficit s = gap s := by
  unfold lowerDeficit upperDeficit gap
  ring

theorem gap_eq_rho {s : ℝ} (hs : 1 ≤ s) : gap s = sieveA * Dickman.rho (s - 1) / s :=
  gap_identity sieveA hs

theorem lowerDeficit_continuous : Continuous lowerDeficit :=
  continuous_const.sub (f_continuous sieveA)

theorem upperDeficit_continuousOn : ContinuousOn upperDeficit (Ici 1) :=
  ((F_continuousOn sieveA).mono (by intro s hs; change 0 < s; exact lt_of_lt_of_le zero_lt_one hs)).sub continuousOn_const

theorem gap_continuousOn : ContinuousOn gap (Ici 1) := by
  have h := lowerDeficit_continuous.continuousOn.add upperDeficit_continuousOn
  have heq : gap = fun s => lowerDeficit s + upperDeficit s := funext (fun s => (deficit_sum s).symm)
  rw [heq]
  exact h

theorem gap_pos {s : ℝ} (hs : 1 ≤ s) : 0 < gap s :=
  LinearSieveFunctions.gap_pos sieveA_pos hs

theorem lowerDeficit_mass_deriv {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun t => t * lowerDeficit t) (-upperDeficit (s - 1)) s := by
  convert! (hasDerivAt_id s).sub (mass_f_hasDerivAt sieveA hs) using 1
  · ext t
    change t * (1 - f sieveA t) = t - t * f sieveA t
    ring
  · simp only [upperDeficit]
    ring

theorem upperDeficit_mass_deriv {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun t => t * upperDeficit t) (-lowerDeficit (s - 1)) s := by
  convert! (mass_F_hasDerivAt sieveA hs).sub (hasDerivAt_id s) using 1
  · ext t
    change t * (F sieveA t - 1) = t * F sieveA t - t
    ring
  · simp only [lowerDeficit]
    ring

theorem gap_mass_deriv {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun t => t * gap t) (-gap (s - 1)) s := by
  convert! (mass_F_hasDerivAt sieveA hs).sub (mass_f_hasDerivAt sieveA hs) using 1
  · ext t
    change t * (F sieveA t - f sieveA t) = t * F sieveA t - t * f sieveA t
    ring
  · simp only [gap]
    ring

theorem lowerDeficit_tendsto_zero : Tendsto lowerDeficit atTop (𝓝 0) := by
  convert! normalized_f_tendsto_one.const_sub 1 using 1
  all_goals try with_reducible_and_instances rfl
  simp

theorem upperDeficit_tendsto_zero : Tendsto upperDeficit atTop (𝓝 0) := by
  convert! normalized_F_tendsto_one.sub_const 1 using 1
  all_goals try with_reducible_and_instances rfl
  simp

theorem gap_tendsto_zero : Tendsto gap atTop (𝓝 0) := pair_gap_tendsto_zero sieveA

theorem deficits_pos {s : ℝ} (hs : 1 ≤ s) : 0 < lowerDeficit s ∧ 0 < upperDeficit s := by
  apply PairedDeficitPositivity.paired_pos lowerDeficit_continuous.continuousOn
    upperDeficit_continuousOn ?_ ?_ ?_ (fun _ h => lowerDeficit_mass_deriv h)
    (fun _ h => upperDeficit_mass_deriv h) lowerDeficit_tendsto_zero upperDeficit_tendsto_zero s hs
  · intro t ht
    simp only [lowerDeficit, f_initial sieveA ht.2, sub_zero, zero_lt_one]
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    change 0 < F sieveA t - 1
    rw [F_initial sieveA ht0 (by linarith [ht.2])]
    have h := (lt_div_iff₀ ht0).mpr (show 1 * t < sieveA by linarith [sieveA_gt_two, ht.2])
    linarith
  · intro t ht
    rw [deficit_sum]
    exact gap_pos ht

theorem deficit_offsets_pos {δ : ℝ} (hhalf : δ < 1 / 2)
    (hδA : δ * sieveA < 1) (hδA2 : δ * sieveA < sieveA - 2)
    {s : ℝ} (hs : 1 ≤ s) :
    0 < lowerDeficit s - δ * gap s ∧ 0 < upperDeficit s - δ * gap s := by
  let a : ℝ → ℝ := fun t => lowerDeficit t - δ * gap t
  let c : ℝ → ℝ := fun t => upperDeficit t - δ * gap t
  have ha : ContinuousOn a (Ici 1) :=
    lowerDeficit_continuous.continuousOn.sub (continuousOn_const.mul gap_continuousOn)
  have hc : ContinuousOn c (Ici 1) :=
    upperDeficit_continuousOn.sub (continuousOn_const.mul gap_continuousOn)
  have hginit : ∀ t ∈ Icc 1 2, gap t = sieveA / t := by
    intro t ht
    simp only [gap, f_initial sieveA ht.2, sub_zero,
      F_initial sieveA (s := t) (by linarith [ht.1]) (by linarith [ht.2])]
  have hai : ∀ t ∈ Icc 1 2, 0 < a t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hdiv : δ * sieveA / t < 1 := (div_lt_one ht0).mpr (lt_of_lt_of_le hδA ht.1)
    dsimp [a, lowerDeficit]
    rw [f_initial sieveA ht.2, hginit t ht]
    have heq : δ * (sieveA / t) = δ * sieveA / t := by ring
    rw [heq]
    linarith
  have hci : ∀ t ∈ Icc 1 2, 0 < c t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hdiv : 0 < (sieveA - δ * sieveA - t) / t :=
      div_pos (by linarith [ht.2]) ht0
    dsimp [c, upperDeficit]
    rw [F_initial sieveA ht0 (by linarith [ht.2]), hginit t ht]
    convert! hdiv using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have hsum : ∀ t, 1 ≤ t → 0 < a t + c t := by
    intro t ht
    have heq : a t + c t = (1 - 2 * δ) * gap t := by
      dsimp [a, c]
      rw [← deficit_sum t]
      ring
    rw [heq]
    exact mul_pos (by linarith) (gap_pos ht)
  have hda : ∀ t, 2 < t → HasDerivAt (fun u => u * a u) (-c (t - 1)) t := by
    intro t ht
    convert! (lowerDeficit_mass_deriv ht).sub ((gap_mass_deriv ht).const_mul δ) using 1
    · ext u
      change u * (lowerDeficit u - δ * gap u) = u * lowerDeficit u - δ * (u * gap u)
      ring
    · dsimp [c]
      ring
  have hdc : ∀ t, 2 < t → HasDerivAt (fun u => u * c u) (-a (t - 1)) t := by
    intro t ht
    convert! (upperDeficit_mass_deriv ht).sub ((gap_mass_deriv ht).const_mul δ) using 1
    · ext u
      change u * (upperDeficit u - δ * gap u) = u * upperDeficit u - δ * (u * gap u)
      ring
    · dsimp [a]
      ring
  have hla : Tendsto a atTop (𝓝 0) := by
    simpa only [mul_zero, sub_zero] using lowerDeficit_tendsto_zero.sub (gap_tendsto_zero.const_mul δ)
  have hlc : Tendsto c atTop (𝓝 0) := by
    simpa only [mul_zero, sub_zero] using upperDeficit_tendsto_zero.sub (gap_tendsto_zero.const_mul δ)
  exact PairedDeficitPositivity.paired_pos ha hc hai hci hsum hda hdc hla hlc s hs

theorem deficits_uniform_comparison : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
    ∀ s : ℝ, 1 ≤ s →
      δ * gap s < lowerDeficit s ∧ lowerDeficit s < (1 - δ) * gap s ∧
      δ * gap s < upperDeficit s ∧ upperDeficit s < (1 - δ) * gap s := by
  let δ : ℝ := min 1 (sieveA - 2) / (4 * sieveA)
  have hδpos : 0 < δ := div_pos (lt_min zero_lt_one (sub_pos.mpr sieveA_gt_two))
    (mul_pos (by norm_num) sieveA_pos)
  have heq : δ * sieveA = min 1 (sieveA - 2) / 4 := by
    dsimp [δ]
    field_simp [ne_of_gt sieveA_pos]
  have hδA : δ * sieveA < 1 := by rw [heq]; linarith [min_le_left (1 : ℝ) (sieveA - 2)]
  have hδA2 : δ * sieveA < sieveA - 2 := by
    rw [heq]
    linarith [min_le_right (1 : ℝ) (sieveA - 2), sieveA_gt_two]
  have hhalf : δ < 1 / 2 := by nlinarith [sieveA_gt_two]
  refine ⟨δ, hδpos, hhalf, ?_⟩
  intro s hs
  obtain ⟨ha, hc⟩ := deficit_offsets_pos hhalf hδA hδA2 hs
  have hsum := deficit_sum s
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · linarith
  · nlinarith

end NumberTheoryLean.NormalizedDeficits

end

section

namespace NumberTheoryLean.DeficitFutureIntegrals

open Filter Set MeasureTheory
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits

theorem deficit_mass_bounds {s : ℝ} (hs : 1 ≤ s) :
    (0 ≤ s * lowerDeficit s ∧ s * lowerDeficit s ≤ sieveA * Dickman.rho (s - 1)) ∧
    (0 ≤ s * upperDeficit s ∧ s * upperDeficit s ≤ sieveA * Dickman.rho (s - 1)) := by
  obtain ⟨ha, hc⟩ := deficits_pos hs
  have hsum := deficit_sum s
  have hg : s * gap s = sieveA * Dickman.rho (s - 1) := by
    rw [gap_eq_rho hs]
    field_simp
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hbA : s * lowerDeficit s ≤ s * gap s :=
    mul_le_mul_of_nonneg_left (by linarith) hs0.le
  have hbC : s * upperDeficit s ≤ s * gap s :=
    mul_le_mul_of_nonneg_left (by linarith) hs0.le
  exact ⟨⟨mul_nonneg hs0.le ha.le, by simpa only [hg] using hbA⟩,
    ⟨mul_nonneg hs0.le hc.le, by simpa only [hg] using hbC⟩⟩

theorem lowerDeficit_mass_tendsto_zero :
    Tendsto (fun s => s * lowerDeficit s) atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v + 1, fun s hs => by linarith⟩
  have hlim := (DickmanDecay.rho_tendsto_zero.comp hshift).const_mul sieveA
  simp only [mul_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (deficit_mass_bounds hs).1.1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (deficit_mass_bounds hs).1.2

theorem upperDeficit_mass_tendsto_zero :
    Tendsto (fun s => s * upperDeficit s) atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v + 1, fun s hs => by linarith⟩
  have hlim := (DickmanDecay.rho_tendsto_zero.comp hshift).const_mul sieveA
  simp only [mul_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (deficit_mass_bounds hs).2.1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    exact (deficit_mass_bounds hs).2.2

theorem upperDeficit_mass_deriv_of_one_lt {s : ℝ} (hs : 1 < s) :
    HasDerivAt (fun t => t * upperDeficit t) (-lowerDeficit (s - 1)) s := by
  by_cases hs2 : 2 < s
  · exact upperDeficit_mass_deriv hs2
  · have heq : (fun t => t * upperDeficit t) =ᶠ[𝓝 s] (fun t => sieveA - t) := by
      filter_upwards [Ioo_mem_nhds (show 0 < s by linarith) (show s < 3 by linarith)] with t ht
      change t * (F sieveA t - 1) = sieveA - t
      rw [F_initial sieveA ht.1 ht.2.le]
      field_simp [ne_of_gt ht.1]
    have h := ((hasDerivAt_const s sieveA).sub (hasDerivAt_id s)).congr_of_eventuallyEq heq
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [lowerDeficit, f_initial sieveA (s := s - 1) (by linarith), sub_zero, zero_sub]

end NumberTheoryLean.DeficitFutureIntegrals

end

section

namespace NumberTheoryLean.DerivativeWeights

open Filter Set MeasureTheory
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits DeficitFutureIntegrals

noncomputable def evenInitial (s : ℝ) : ℝ :=
  sieveA * (s / (s - 1) - Real.log (s - 1))

noncomputable def phiEven (s : ℝ) : ℝ :=
  if s ≤ 2 then evenInitial s else s * (lowerDeficit s + upperDeficit (s - 1))

noncomputable def phiOdd (s : ℝ) : ℝ :=
  if s ≤ 3 then sieveA else s * (upperDeficit s + lowerDeficit (s - 1))

noncomputable def W (t : ℝ) : ℝ := (t + 1) / t ^ 2

theorem phiOdd_initial {s : ℝ} (hs : s ≤ 3) : phiOdd s = sieveA := by
  simp only [phiOdd, ite_eq_left hs]

theorem phiEven_initial {s : ℝ} (hs : s ≤ 2) : phiEven s = evenInitial s := by
  simp only [phiEven, ite_eq_left hs]

theorem phiEven_eq_deficits {s : ℝ} (hs : 2 ≤ s) :
    phiEven s = s * (lowerDeficit s + upperDeficit (s - 1)) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst s
    norm_num [phiEven, evenInitial, lowerDeficit, upperDeficit,
      f_initial, F_initial sieveA (s := 1) (by norm_num) (by norm_num)]
    ring
  · exact ite_eq_right (not_le_of_gt h)

theorem phiOdd_eq_deficits {s : ℝ} (hs : 1 ≤ s) :
    phiOdd s = s * (upperDeficit s + lowerDeficit (s - 1)) := by
  by_cases hs3 : s ≤ 3
  · rw [phiOdd_initial hs3]
    simp only [upperDeficit, lowerDeficit, f_initial sieveA (s := s - 1) (by linarith),
      F_initial sieveA (s := s) (by linarith) hs3]
    field_simp
    ring
  · exact ite_eq_right hs3

theorem phiEven_explicit {s : ℝ} (hs : 1 < s) (hs4 : s ≤ 4) :
    phiEven s = evenInitial s := by
  by_cases hs2 : s ≤ 2
  · exact phiEven_initial hs2
  · rw [phiEven_eq_deficits (by linarith)]
    unfold lowerDeficit upperDeficit evenInitial
    rw [f_first_formula sieveA (by linarith) hs4,
      F_initial sieveA (s := s - 1) (by linarith) (by linarith)]
    field_simp
    ring

theorem hasDerivAt_of_mass {g : ℝ → ℝ} {s v : ℝ} (hs : s ≠ 0)
    (hm : HasDerivAt (fun t => t * g t) v s) :
    HasDerivAt g ((v - g s) / s) s := by
  have heq : g =ᶠ[𝓝 s] (fun t => (t * g t) / t) := by
    filter_upwards [eventually_ne_nhds hs] with t ht
    field_simp
  have h := (hm.div (hasDerivAt_id s) hs).congr_of_eventuallyEq heq
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq, mul_one]
  field_simp

theorem lowerDeficit_hasDerivAt {s : ℝ} (hs : 2 < s) :
    HasDerivAt lowerDeficit (-phiEven s / s ^ 2) s := by
  have h := hasDerivAt_of_mass (by linarith : s ≠ 0) (lowerDeficit_mass_deriv hs)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  rw [phiEven_eq_deficits hs.le]
  field_simp
  ring

theorem upperDeficit_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt upperDeficit (-phiOdd s / s ^ 2) s := by
  have h := hasDerivAt_of_mass (by linarith : s ≠ 0) (upperDeficit_mass_deriv_of_one_lt hs)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  rw [phiOdd_eq_deficits hs.le]
  field_simp
  ring

theorem evenInitial_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt evenInitial (-s / (s - 1) ^ 2 * sieveA) s := by
  have hn : s - 1 ≠ 0 := by linarith
  have h := (((hasDerivAt_id s).div ((hasDerivAt_id s).sub_const 1) hn).sub
    (((hasDerivAt_id s).sub_const 1).log hn)).const_mul sieveA
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq, one_mul, mul_one]
  field_simp
  ring

theorem phiEven_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt phiEven (-s / (s - 1) ^ 2 * phiOdd (s - 1)) s := by
  by_cases hs3 : s < 3
  · have heq : phiEven =ᶠ[𝓝 s] evenInitial := by
      filter_upwards [Ioo_mem_nhds hs hs3] with t ht
      exact phiEven_explicit ht.1 (by linarith [ht.2])
    rw [phiOdd_initial (s := s - 1) (by linarith)]
    exact (evenInitial_hasDerivAt hs).congr_of_eventuallyEq heq
  · have hs2 : 2 < s := by linarith
    have hU := (upperDeficit_hasDerivAt (s := s - 1) (by linarith)).comp s
      ((hasDerivAt_id s).sub_const 1)
    have h := (hasDerivAt_id s).mul ((lowerDeficit_hasDerivAt hs2).add hU)
    have heq : phiEven =ᶠ[𝓝 s] (fun t => t * (lowerDeficit t + upperDeficit (t - 1))) := by
      filter_upwards [Ioi_mem_nhds hs2] with t ht
      exact phiEven_eq_deficits ht.le
    have hd := h.congr_of_eventuallyEq heq
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq, Pi.add_apply, Function.comp_apply, one_mul, mul_one]
    rw [phiEven_eq_deficits hs2.le]
    field_simp
    ring

theorem phiOdd_hasDerivAt {s : ℝ} (hs : 3 < s) :
    HasDerivAt phiOdd (-s / (s - 1) ^ 2 * phiEven (s - 1)) s := by
  have hA := (lowerDeficit_hasDerivAt (s := s - 1) (by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have h := (hasDerivAt_id s).mul ((upperDeficit_hasDerivAt (by linarith : 1 < s)).add hA)
  have heq : phiOdd =ᶠ[𝓝 s] (fun t => t * (upperDeficit t + lowerDeficit (t - 1))) := by
    filter_upwards [Ioi_mem_nhds (show 1 < s by linarith)] with t ht
    exact phiOdd_eq_deficits ht.le
  have hd := h.congr_of_eventuallyEq heq
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq, Pi.add_apply, Function.comp_apply, one_mul, mul_one]
  rw [phiOdd_eq_deficits (by linarith)]
  field_simp
  ring

theorem phiEven_pos {s : ℝ} (hs : 1 < s) : 0 < phiEven s := by
  by_cases hs2 : 2 ≤ s
  · rw [phiEven_eq_deficits hs2]
    exact mul_pos (by linarith) (add_pos (deficits_pos (by linarith)).1
      (deficits_pos (s := s - 1) (by linarith)).2)
  · rw [phiEven_initial (by linarith)]
    unfold evenInitial
    have hlog : Real.log (s - 1) < 0 := Real.log_neg (by linarith) (by linarith)
    exact mul_pos sieveA_pos (sub_pos.mpr (lt_trans hlog (div_pos (by linarith) (by linarith))))

theorem phiOdd_pos (s : ℝ) : 0 < phiOdd s := by
  by_cases hs3 : s ≤ 3
  · rw [phiOdd_initial hs3]
    exact sieveA_pos
  · rw [phiOdd_eq_deficits (by linarith)]
    exact mul_pos (by linarith) (add_pos (deficits_pos (by linarith)).2
      (deficits_pos (s := s - 1) (by linarith)).1)

theorem phiEven_continuousAt {s : ℝ} (hs : 1 < s) : ContinuousAt phiEven s :=
  (phiEven_hasDerivAt hs).continuousAt

theorem phiOdd_continuous : Continuous phiOdd := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs3 : s < 3
  · have heq : phiOdd =ᶠ[𝓝 s] (fun _ => sieveA) := by
      filter_upwards [Iio_mem_nhds hs3] with t ht
      exact phiOdd_initial ht.le
    exact continuousAt_const.congr_of_eventuallyEq heq
  · have heq : phiOdd =ᶠ[𝓝 s] (fun t => t * (upperDeficit t + lowerDeficit (t - 1))) := by
      filter_upwards [Ioi_mem_nhds (show 1 < s by linarith)] with t ht
      exact phiOdd_eq_deficits ht.le
    have hcU : ContinuousAt upperDeficit s :=
      (F_continuousAt sieveA (by linarith)).sub continuousAt_const
    have hcA : ContinuousAt (fun t => lowerDeficit (t - 1)) s :=
      (lowerDeficit_continuous.comp (continuous_id.sub continuous_const)).continuousAt
    exact (continuousAt_id.mul (hcU.add hcA)).congr_of_eventuallyEq heq

theorem phiEven_strictAntiOn : StrictAntiOn phiEven (Ioi 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  · intro s hs
    exact (phiEven_continuousAt hs).continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    change 1 < s at hs
    rw [(phiEven_hasDerivAt hs).deriv]
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith)
      (sq_pos_of_pos (by linarith))) (phiOdd_pos _)

theorem phiOdd_antitone : Antitone phiOdd := by
  have htail : AntitoneOn phiOdd (Ici 3) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 3) phiOdd_continuous.continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      exact (phiOdd_hasDerivAt hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      change 3 < s at hs
      rw [(phiOdd_hasDerivAt hs).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
        (phiEven_pos (by linarith)).le
  intro x y hxy
  by_cases hy : y ≤ 3
  · rw [phiOdd_initial hy, phiOdd_initial (le_trans hxy hy)]
  · by_cases hx : x ≤ 3
    · rw [phiOdd_initial hx, ← phiOdd_initial (s := 3) le_rfl]
      exact htail (by simp) (le_of_not_ge hy) (le_of_not_ge hy)
    · exact htail (le_of_not_ge hx) (le_of_not_ge hy) hxy

end NumberTheoryLean.DerivativeWeights

end

section

namespace NumberTheoryLean.WeightFutureIntegrals

open Filter Set MeasureTheory
open scoped Topology
open NormalizedDeficits DeficitFutureIntegrals DerivativeWeights

theorem phiEven_tendsto_zero : Tendsto phiEven atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v + 1, fun s hs => by linarith⟩
  have hl := lowerDeficit_mass_tendsto_zero.add
    ((upperDeficit_mass_tendsto_zero.comp hshift).add (upperDeficit_tendsto_zero.comp hshift))
  simp only [add_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  rw [phiEven_eq_deficits hs]
  simp only [Function.comp_apply]
  ring

theorem phiOdd_tendsto_zero : Tendsto phiOdd atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v + 1, fun s hs => by linarith⟩
  have hl := upperDeficit_mass_tendsto_zero.add
    ((lowerDeficit_mass_tendsto_zero.comp hshift).add (lowerDeficit_tendsto_zero.comp hshift))
  simp only [add_zero] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  rw [phiOdd_eq_deficits hs]
  simp only [Function.comp_apply]
  ring

theorem W_pos {t : ℝ} (ht : 0 < t) : 0 < W t := by
  unfold W
  positivity

theorem future_integral_of_shifted_deriv {P B : ℝ → ℝ} {s : ℝ}
    (hc : ContinuousAt P s)
    (hd : ∀ t, s < t → HasDerivAt P (-B (t - 1)) t)
    (hb : ∀ t, s - 1 < t → 0 ≤ B t)
    (hl : Tendsto P atTop (𝓝 0)) :
    IntegrableOn B (Ioi (s - 1)) ∧ P s = ∫ t in Ioi (s - 1), B t := by
  let H : ℝ → ℝ := fun t => P (t + 1)
  have hc' : ContinuousWithinAt H (Ici (s - 1)) (s - 1) := by
    have hcs : ContinuousAt P ((s - 1) + 1) := by simpa only [sub_add_cancel] using hc
    exact (hcs.comp (f := fun t : ℝ => t + 1) (x := s - 1)
      (continuous_id.add continuous_const).continuousAt).continuousWithinAt
  have hder : ∀ t ∈ Ioi (s - 1), HasDerivAt H (-B t) t := by
    intro t ht
    have h := (hd (t + 1) (by change s - 1 < t at ht; linarith)).comp t
      ((hasDerivAt_id t).add_const 1)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hn : ∀ t ∈ Ioi (s - 1), -B t ≤ 0 := fun t ht => neg_nonpos.mpr (hb t ht)
  have hshift : Tendsto (fun t : ℝ => t + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro v
    exact eventually_atTop.mpr ⟨v - 1, fun t ht => by linarith⟩
  have hlim : Tendsto H atTop (𝓝 0) := hl.comp hshift
  have hint := integrableOn_Ioi_deriv_of_nonpos hc' hder hn hlim
  have heq := integral_Ioi_of_hasDerivAt_of_nonpos hc' hder hn hlim
  constructor
  · exact integrable_neg_iff.mp hint
  · simp only [integral_neg, H, sub_add_cancel, zero_sub] at heq
    linarith

theorem phiEven_future_integral {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t => W t * phiOdd t) (Ioi (s - 1)) ∧
      phiEven s = ∫ t in Ioi (s - 1), W t * phiOdd t := by
  apply future_integral_of_shifted_deriv (phiEven_continuousAt hs) ?_ ?_ phiEven_tendsto_zero
  · intro t ht
    convert! phiEven_hasDerivAt (lt_trans hs ht) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [W, sub_add_cancel]
    ring
  · intro t ht
    exact (mul_pos (W_pos (by linarith)) (phiOdd_pos t)).le

theorem phiOdd_future_integral (s : ℝ) :
    IntegrableOn (fun t => W t * phiEven t) (Ioi (max 2 (s - 1))) ∧
      phiOdd s = ∫ t in Ioi (max 2 (s - 1)), W t * phiEven t := by
  have hc := phiOdd_continuous.continuousAt (x := max 3 s)
  have hder : ∀ t, max 3 s < t →
      HasDerivAt phiOdd (-(W (t - 1) * phiEven (t - 1))) t := by
    intro t ht
    convert! phiOdd_hasDerivAt (lt_of_le_of_lt (le_max_left _ _) ht) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [W, sub_add_cancel]
    ring
  have hn : ∀ t, max 3 s - 1 < t → 0 ≤ W t * phiEven t := by
    intro t ht
    have ht1 : 1 < t := by linarith [le_max_left (3 : ℝ) s]
    exact (mul_pos (W_pos (by linarith)) (phiEven_pos ht1)).le
  have h := future_integral_of_shifted_deriv hc hder hn phiOdd_tendsto_zero
  have hmax : max 3 s - 1 = max 2 (s - 1) := by
    by_cases hs : s ≤ 3
    · rw [max_eq_left hs, max_eq_left (by linarith)]
      norm_num
    · rw [max_eq_right (le_of_not_ge hs), max_eq_right (by linarith)]
  have heq : phiOdd (max 3 s) = phiOdd s := by
    by_cases hs : s ≤ 3
    · rw [max_eq_left hs, phiOdd_initial le_rfl, phiOdd_initial hs]
    · rw [max_eq_right (le_of_not_ge hs)]
  simpa only [hmax, heq] using h

end NumberTheoryLean.WeightFutureIntegrals

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_TransitionKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TransitionKernels

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open LinearSieveFunctions BuchstabBridge NormalizedDeficits
open DerivativeWeights WeightFutureIntegrals

noncomputable def tailDensity (left mass : ℝ) (B : ℝ → ℝ) : ℝ → ℝ :=
  (Ici left).indicator (fun t => B t / mass)

theorem tailDensity_nonneg {left mass : ℝ} {B : ℝ → ℝ} (hm : 0 < mass)
    (hB : ∀ t, left ≤ t → 0 ≤ B t) (t : ℝ) : 0 ≤ tailDensity left mass B t := by
  unfold tailDensity
  by_cases ht : left ≤ t
  · rw [indicator_of_mem (show t ∈ Ici left from ht)]
    exact div_nonneg (hB t ht) hm.le
  · rw [indicator_of_notMem (show t ∉ Ici left from ht)]

theorem tailDensity_integrable {left mass : ℝ} {B : ℝ → ℝ}
    (hB : IntegrableOn B (Ioi left)) : Integrable (tailDensity left mass B) := by
  unfold tailDensity
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hB).div_const mass

theorem tailDensity_integral {left mass : ℝ} {B : ℝ → ℝ} (hm : 0 < mass)
    (hB : mass = ∫ t in Ioi left, B t) : ∫ t, tailDensity left mass B t = 1 := by
  unfold tailDensity
  rw [integral_indicator measurableSet_Ici, integral_div, integral_Ici_eq_integral_Ioi, ← hB]
  exact div_self (ne_of_gt hm)

theorem phiEven_measurable : Measurable phiEven := by
  have hF : Measurable (F sieveA) := by
    unfold F
    exact (measurable_const.mul
      (((plus_continuous.comp (continuous_id.sub continuous_const)).add
        (Dickman.rho_continuous.comp (continuous_id.sub continuous_const))).measurable)).div
      (measurable_const.mul measurable_id)
  unfold phiEven
  apply Measurable.ite measurableSet_Iic
  · unfold evenInitial
    exact measurable_const.mul ((measurable_id.div (measurable_id.sub measurable_const)).sub
      (Real.measurable_log.comp (measurable_id.sub measurable_const)))
  · exact measurable_id.mul (lowerDeficit_continuous.measurable.add
      ((hF.sub measurable_const).comp (measurable_id.sub measurable_const)))

theorem W_measurable : Measurable W := by
  unfold W
  exact (measurable_id.add measurable_const).div (measurable_id.pow_const 2)

end NumberTheoryLean.TransitionKernels

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_WeightIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TwoStepDensityBounds

open Set
open DerivativeWeights WeightFutureIntegrals

theorem W_lower {t M : ℝ} (ht : 0 < t) (htM : t ≤ M) : 1 / M ≤ W t := by
  have hM : 0 < M := lt_of_lt_of_le ht htM
  unfold W
  apply (div_le_div_iff₀ hM (sq_pos_of_pos ht)).mpr
  nlinarith

end NumberTheoryLean.TwoStepDensityBounds

end

section

open Set MeasureTheory
namespace Erdos970Dependency.WeightIntegrals
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals

noncomputable def wPrimitive (t : ℝ) : ℝ := Real.log t - 1 / t
noncomputable def wMass (a b : ℝ) : ℝ := ∫ t in a..b, W t

noncomputable def tailW (u : ℝ) : ℝ := wPrimitive (u + 1) - wPrimitive 2

noncomputable def regIntegral (t : ℝ) : ℝ := ∫ u in (1 : ℝ)..t + 1, W u * tailW u

end Erdos970Dependency.WeightIntegrals

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_WeightDickmanComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.WeightDickmanComparison

open Filter Set
open scoped Topology
open LinearSieveFunctions BuchstabBridge NormalizedDeficits
open DerivativeWeights WeightFutureIntegrals

theorem deficits_le_gap {s : ℝ} (hs : 1 ≤ s) :
    lowerDeficit s ≤ gap s ∧ upperDeficit s ≤ gap s := by
  have h := deficit_sum s
  obtain ⟨ha, hc⟩ := deficits_pos hs
  constructor <;> linarith

theorem weights_dickman_bounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ s : ℝ, 2 ≤ s →
      (c * Dickman.rho (s - 2) ≤ phiEven s ∧ phiEven s ≤ C * Dickman.rho (s - 2)) ∧
      (c * Dickman.rho (s - 2) ≤ phiOdd s ∧ phiOdd s ≤ C * Dickman.rho (s - 2)) := by
  obtain ⟨δ, hδ, _, hcomp⟩ := deficits_uniform_comparison
  refine ⟨δ * sieveA, 3 * sieveA, mul_pos hδ sieveA_pos,
    mul_pos (by norm_num) sieveA_pos, ?_⟩
  intro s hs
  have hs1 : 1 ≤ s := by linarith
  have hp1 : 1 ≤ s - 1 := by linarith
  have hs0 : 0 < s := by linarith
  have hg : 0 < gap (s - 1) := gap_pos hp1
  have hgprev : (s - 1) * gap (s - 1) = sieveA * Dickman.rho (s - 2) := by
    rw [gap_eq_rho hp1, show s - 1 - 1 = s - 2 by ring]
    field_simp
  have hgcur : s * gap s = sieveA * Dickman.rho (s - 1) := by
    rw [gap_eq_rho hs1]
    field_simp
  have hlow : (δ * sieveA) * Dickman.rho (s - 2) ≤ s * (δ * gap (s - 1)) := by
    calc
      _ = δ * ((s - 1) * gap (s - 1)) := by rw [hgprev]; ring
      _ = (s - 1) * (δ * gap (s - 1)) := by ring
      _ ≤ s * (δ * gap (s - 1)) := mul_le_mul_of_nonneg_right (by linarith) (mul_pos hδ hg).le
  have hlowE : s * (δ * gap (s - 1)) ≤ phiEven s := by
    rw [phiEven_eq_deficits hs]
    apply mul_le_mul_of_nonneg_left _ hs0.le
    have hc := (hcomp (s - 1) hp1).2.2.1
    have ha := (deficits_pos hs1).1
    linarith
  have hlowO : s * (δ * gap (s - 1)) ≤ phiOdd s := by
    rw [phiOdd_eq_deficits hs1]
    apply mul_le_mul_of_nonneg_left _ hs0.le
    have ha := (hcomp (s - 1) hp1).1
    have hc := (deficits_pos hs1).2
    linarith
  have huppE : phiEven s ≤ s * (gap s + gap (s - 1)) := by
    rw [phiEven_eq_deficits hs]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (deficits_le_gap hs1).1 (deficits_le_gap hp1).2) hs0.le
  have huppO : phiOdd s ≤ s * (gap s + gap (s - 1)) := by
    rw [phiOdd_eq_deficits hs1]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (deficits_le_gap hs1).2 (deficits_le_gap hp1).1) hs0.le
  have hupp : s * (gap s + gap (s - 1)) ≤ (3 * sieveA) * Dickman.rho (s - 2) := by
    have h1 : sieveA * Dickman.rho (s - 1) ≤ sieveA * Dickman.rho (s - 2) :=
      mul_le_mul_of_nonneg_left (Dickman.rho_antitone (by linarith)) sieveA_pos.le
    have h2 : s * gap (s - 1) ≤ 2 * ((s - 1) * gap (s - 1)) := by
      nlinarith [mul_le_mul_of_nonneg_right (show s ≤ 2 * (s - 1) by linarith) hg.le]
    rw [hgprev] at h2
    rw [mul_add, hgcur]
    nlinarith
  exact ⟨⟨le_trans hlow hlowE, le_trans huppE hupp⟩,
    ⟨le_trans hlow hlowO, le_trans huppO hupp⟩⟩

end NumberTheoryLean.WeightDickmanComparison

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InverseWeightGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.WeightTailBounds

open Filter Set
open scoped Topology
open DerivativeWeights WeightDickmanComparison

theorem even_logDeriv_eq {s : ℝ} (hs : 1 < s) :
    -deriv phiEven s / phiEven s = s / (s - 1) ^ 2 * (phiOdd (s - 1) / phiEven s) := by
  rw [(phiEven_hasDerivAt hs).deriv]
  ring

theorem odd_logDeriv_eq {s : ℝ} (hs : 3 < s) :
    -deriv phiOdd s / phiOdd s = s / (s - 1) ^ 2 * (phiEven (s - 1) / phiOdd s) := by
  rw [(phiOdd_hasDerivAt hs).deriv]
  ring

theorem slope_lower_from_rho {s c C p q : ℝ} (hs : 4 ≤ s)
    (hc : 0 < c) (hC : 0 < C) (hp : 0 < p)
    (hpu : p ≤ C * Dickman.rho (s - 2)) (hql : c * Dickman.rho (s - 3) ≤ q) :
    (c / (2 * C)) * DickmanDecay.hazard (s - 2) ≤
      s / (s - 1) ^ 2 * (q / p) := by
  have hnum : 0 ≤ c * Dickman.rho (s - 3) := (mul_pos hc (Dickman.rho_pos _)).le
  have hratio : (c * Dickman.rho (s - 3)) / (C * Dickman.rho (s - 2)) ≤ q / p := by
    calc
      _ ≤ (c * Dickman.rho (s - 3)) / p := div_le_div_of_nonneg_left hnum hp hpu
      _ ≤ q / p := div_le_div_of_nonneg_right hql hp.le
  have hcoeff : 1 / (2 * (s - 2)) ≤ s / (s - 1) ^ 2 := by
    apply (div_le_div_iff₀ (by linarith : 0 < 2 * (s - 2)) (sq_pos_of_pos (by linarith))).mpr
    nlinarith
  have hbase : 0 ≤ (c * Dickman.rho (s - 3)) / (C * Dickman.rho (s - 2)) :=
    (div_pos (mul_pos hc (Dickman.rho_pos _)) (mul_pos hC (Dickman.rho_pos _))).le
  calc
    _ = (1 / (2 * (s - 2))) * ((c * Dickman.rho (s - 3)) / (C * Dickman.rho (s - 2))) := by
      unfold DickmanDecay.hazard
      rw [show s - 2 - 1 = s - 3 by ring]
      field_simp
    _ ≤ _ := mul_le_mul hcoeff hratio hbase (by positivity)

theorem weights_logDeriv_ge_hazard : ∃ k : ℝ, 0 < k ∧ ∀ s : ℝ, 4 ≤ s →
    k * DickmanDecay.hazard (s - 2) ≤ -deriv phiEven s / phiEven s ∧
    k * DickmanDecay.hazard (s - 2) ≤ -deriv phiOdd s / phiOdd s := by
  obtain ⟨c, C, hc, hC, hb⟩ := weights_dickman_bounds
  refine ⟨c / (2 * C), by positivity, ?_⟩
  intro s hs
  have hsp : 2 ≤ s - 1 := by linarith
  have he := (hb (s - 1) hsp).1.1
  have ho := (hb (s - 1) hsp).2.1
  rw [show s - 1 - 2 = s - 3 by ring] at he ho
  rw [even_logDeriv_eq (by linarith), odd_logDeriv_eq (by linarith)]
  exact ⟨slope_lower_from_rho hs hc hC (phiEven_pos (by linarith)) (hb s (by linarith)).1.2 ho,
    slope_lower_from_rho hs hc hC (phiOdd_pos s) (hb s (by linarith)).2.2 he⟩

theorem weights_logDeriv_growth (rate : ℝ) : ∃ U : ℝ, 4 ≤ U ∧ ∀ s : ℝ, U ≤ s →
    rate ≤ -deriv phiEven s / phiEven s ∧ rate ≤ -deriv phiOdd s / phiOdd s := by
  obtain ⟨k, hk, hkb⟩ := weights_logDeriv_ge_hazard
  obtain ⟨T, hT, ht⟩ := DickmanDecay.exists_hazard_tail (rate / k)
  refine ⟨T + 2, by linarith, ?_⟩
  intro s hs
  have h : rate ≤ k * DickmanDecay.hazard (s - 2) := by
    have ht' := mul_le_mul_of_nonneg_left (ht (s - 2) (by linarith)) hk.le
    have heq : k * (rate / k) = rate := by field_simp
    rwa [heq] at ht'
  exact ⟨le_trans h (hkb s (by linarith)).1, le_trans h (hkb s (by linarith)).2⟩

end NumberTheoryLean.WeightTailBounds

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_RegenerationDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.RegenerationTails

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open BuchstabBridge DerivativeWeights WeightFutureIntegrals WeightTailBounds
open TransitionKernels

theorem tailDensity_setIntegral {left right mass : ℝ} {B : ℝ → ℝ} (h : left ≤ right) :
    (∫ t in Ici right, tailDensity left mass B t) = (∫ t in Ici right, B t) / mass := by
  calc
    _ = ∫ t in Ici right, B t / mass := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro t ht
      exact indicator_of_mem (show t ∈ Ici left from le_trans h ht) _
    _ = _ := integral_div mass B

theorem exponential_comparison {P : ℝ → ℝ} {U rate a b : ℝ}
    (hp : ∀ t, U ≤ t → 0 < P t)
    (hd : ∀ t, U ≤ t → DifferentiableAt ℝ P t)
    (hl : ∀ t, U ≤ t → rate ≤ -deriv P t / P t)
    (ha : U ≤ a) (hab : a ≤ b) : P b ≤ P a * Real.exp (-rate * (b - a)) := by
  let H : ℝ → ℝ := fun t => Real.exp (rate * t) * P t
  have hder : ∀ t, U ≤ t → HasDerivAt H
      (Real.exp (rate * t) * (deriv P t + rate * P t)) t := by
    intro t ht
    have h := (((hasDerivAt_id t).const_mul rate).exp).mul (hd t ht).hasDerivAt
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq, mul_one]
    ring
  have hm : AntitoneOn H (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro t ht
      exact (hder t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htU : U ≤ t := by linarith [ht.1]
      rw [(hder t htU).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have h := (le_div_iff₀ (hp t htU)).mp (hl t htU)
      linarith
  have h := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hq : P b ≤ Real.exp (rate * a) * P a / Real.exp (rate * b) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa only [H, mul_comm] using h
  calc
    P b ≤ Real.exp (rate * a) * P a / Real.exp (rate * b) := hq
    _ = P a * (Real.exp (rate * a) / Real.exp (rate * b)) := by ring
    _ = _ := by rw [← Real.exp_sub]; congr 1; congr 1; ring

end NumberTheoryLean.RegenerationTails

end

section

namespace NumberTheoryLean.RegenerationDrift

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open TransitionKernels RegenerationTails

theorem exponential_moment_of_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (hsupport : ∀ᵐ x ∂μ, m ≤ x)
    (htail : ∀ h : ℝ, 0 ≤ h → μ (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) ≤ ENNReal.ofReal (2 * Real.exp m) := by
  have hnn : 0 ≤ᵐ[μ] (fun x : ℝ => x - m) := by
    filter_upwards [hsupport] with x hx
    exact sub_nonneg.mpr hx
  have hlc := lintegral_comp_eq_lintegral_meas_le_mul (f := fun x : ℝ => x - m)
    (g := Real.exp) μ hnn (measurable_id.sub measurable_const).aemeasurable
    (fun t _ => Real.continuous_exp.intervalIntegrable 0 t)
    (Eventually.of_forall (fun t => (Real.exp_pos t).le))
  simp only [integral_exp, Real.exp_zero] at hlc
  have hsmall : (∫⁻ x, ENNReal.ofReal (Real.exp (x - m) - 1) ∂μ) ≤ 1 := by
    rw [hlc]
    calc
      _ ≤ ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-h)) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with h hh
        have hset : {x : ℝ | h ≤ x - m} = Ici (m + h) := by ext x; simp only [mem_ofPred_eq, mem_Ici]; constructor <;> intro hx <;> linarith
        rw [hset]
        calc
          _ ≤ ENNReal.ofReal (Real.exp (-2 * h)) * ENNReal.ofReal (Real.exp h) :=
            mul_le_mul (htail h hh.le) le_rfl zero_le zero_le
          _ = _ := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            congr 2
            ring
      _ = 1 := by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
          (Eventually.of_forall (fun h => (Real.exp_pos (-h)).le)), integral_exp_neg_Ioi_zero]
        norm_num
  have hshiftMeas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (x - m) - 1)) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (measurable_id.sub measurable_const)).sub measurable_const)
  have heq : (fun x : ℝ => ENNReal.ofReal (Real.exp (x - m))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (Real.exp (x - m) - 1) + 1) := by
    filter_upwards [hsupport] with x hx
    have he : 1 ≤ Real.exp (x - m) := Real.one_le_exp_iff.mpr (sub_nonneg.mpr hx)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (sub_nonneg.mpr he) zero_le_one]
    congr 1
    ring
  have hshift : (∫⁻ x, ENNReal.ofReal (Real.exp (x - m)) ∂μ) ≤ 2 := by
    rw [lintegral_congr_ae heq, lintegral_add_left hshiftMeas]
    simp only [lintegral_const, measure_univ, mul_one]
    calc
      _ ≤ 1 + 1 := add_le_add hsmall le_rfl
      _ = 2 := by norm_num
  have hscale : ∀ x : ℝ, ENNReal.ofReal (Real.exp x) =
      ENNReal.ofReal (Real.exp m) * ENNReal.ofReal (Real.exp (x - m)) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [lintegral_congr hscale, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (Real.exp m) * 2 := mul_le_mul le_rfl hshift zero_le zero_le
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num <;> ring

theorem exponential_integrable_of_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (hsupport : ∀ᵐ x ∂μ, m ≤ x)
    (htail : ∀ h : ℝ, 0 ≤ h → μ (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) :
    Integrable Real.exp μ := by
  refine ⟨Real.continuous_exp.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => (Real.exp_pos x).le))).mpr
  exact lt_of_le_of_lt (exponential_moment_of_tail μ m hsupport htail) ENNReal.ofReal_lt_top

noncomputable def driftFactor : ℝ := 2 / Real.exp 1

theorem driftFactor_pos : 0 < driftFactor := by unfold driftFactor; positivity
theorem driftFactor_lt_one : driftFactor < 1 := by
  unfold driftFactor
  exact (div_lt_one (Real.exp_pos 1)).mpr Real.exp_one_gt_two

theorem drift_scale (s : ℝ) : 2 * Real.exp (s - 1) = driftFactor * Real.exp s := by
  unfold driftFactor
  rw [Real.exp_sub]
  ring

end NumberTheoryLean.RegenerationDrift

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_CompactExponentialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CompactExponentialMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open DerivativeWeights WeightFutureIntegrals WeightTailBounds
open TransitionKernels RegenerationTails RegenerationDrift

theorem exponential_moment_of_upper_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (htail : ∀ h : ℝ, 0 ≤ h → μ (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) ≤ ENNReal.ofReal (2 * Real.exp m) := by
  let q : ℝ → ℝ := fun x => max m x
  have hq : Measurable q := measurable_const.max measurable_id
  let ν := μ.map q
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (μ := μ) hq.aemeasurable).mpr inferInstance
  have hs : ∀ᵐ x ∂ν, m ≤ x := by
    apply (ae_map_iff hq.aemeasurable measurableSet_Ici).mpr
    exact Eventually.of_forall (fun x => le_max_left m x)
  have ht : ∀ h : ℝ, 0 ≤ h → ν (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h)) := by
    intro h hh
    by_cases h0 : h = 0
    · subst h
      simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one]
      exact le_trans (measure_mono (subset_univ _)) (by rw [measure_univ])
    · change μ.map q (Ici (m + h)) ≤ _
      rw [Measure.map_apply hq measurableSet_Ici]
      have hpre : q ⁻¹' Ici (m + h) = Ici (m + h) := by
        ext x
        change (m + h ≤ max m x) ↔ m + h ≤ x
        rw [le_max_iff]
        constructor
        · intro hx
          rcases hx with hx | hx
          · exfalso
            have hh0 : 0 < h := lt_of_le_of_ne hh (Ne.symm h0)
            linarith
          · exact hx
        · exact Or.inr
      rw [hpre]
      exact htail h hh
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (q x)) ∂μ := lintegral_mono (fun x =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_max_right m x)))
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp x) ∂ν :=
      (lintegral_map (ENNReal.measurable_ofReal.comp Real.measurable_exp) hq).symm
    _ ≤ _ := exponential_moment_of_tail ν m hs ht

theorem exponential_integrable_of_upper_tail (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (htail : ∀ h : ℝ, 0 ≤ h → μ (Ici (m + h)) ≤ ENNReal.ofReal (Real.exp (-2 * h))) :
    Integrable Real.exp μ := by
  refine ⟨Real.continuous_exp.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => (Real.exp_pos x).le))).mpr
  exact lt_of_le_of_lt (exponential_moment_of_upper_tail μ m htail) ENNReal.ofReal_lt_top

end NumberTheoryLean.CompactExponentialMoments

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_FirstHitKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.GoodPairTransitions

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open BuchstabBridge DerivativeWeights WeightFutureIntegrals TransitionKernels
open TwoStepDensityBounds

def goodPair (s : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc (max 2 (s - 1)) (max 2 (s - 1) + 1 / 4) ∧
    x.2 ∈ Icc (x.1 - 1) (x.1 - 3 / 4)}

theorem goodPair_measurable (s : ℝ) : MeasurableSet (goodPair s) := by
  exact ((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    ((measurableSet_le (measurable_fst.sub measurable_const) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.sub measurable_const)))

theorem goodPair_volume (s : ℝ) : ((volume : Measure ℝ).prod volume) (goodPair s) = ENNReal.ofReal (1 / 16 : ℝ) := by
  rw [Measure.prod_apply (goodPair_measurable s)]
  have heq : ∀ t : ℝ, volume (Prod.mk t ⁻¹' goodPair s) =
      (Icc (max 2 (s - 1)) (max 2 (s - 1) + 1 / 4)).indicator
        (fun _ => ENNReal.ofReal (1 / 4 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ Icc (max 2 (s - 1)) (max 2 (s - 1) + 1 / 4)
    · have hp : Prod.mk t ⁻¹' goodPair s = Icc (t - 1) (t - 3 / 4) := by
        ext u
        simp only [mem_preimage, goodPair, mem_ofPred_eq, ht, true_and]
      rw [hp, Real.volume_Icc, indicator_of_mem ht]
      congr 1
      ring
    · have hp : Prod.mk t ⁻¹' goodPair s = ∅ := by
        ext u
        simp only [mem_preimage, goodPair, mem_ofPred_eq, ht, false_and, mem_empty_iff_false]
      rw [hp, measure_empty, indicator_of_notMem ht]
  rw [lintegral_congr heq, lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
  rw [show max 2 (s - 1) + 1 / 4 - max 2 (s - 1) = (1 : ℝ) / 4 by ring]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  congr 1
  norm_num

theorem goodPair_bounds {s M t u : ℝ} (hM : 4 ≤ M) (hs : s ≤ M) (hg : (t, u) ∈ goodPair s) :
    2 ≤ t ∧ 1 ≤ u ∧ t ≤ M ∧ u ≤ M := by
  have ht2 : 2 ≤ t := le_trans (le_max_left _ _) hg.1.1
  have ha : max 2 (s - 1) ≤ M - 1 := max_le (by linarith) (by linarith)
  exact ⟨ht2, by linarith [hg.2.1], by linarith [hg.1.2], by linarith [hg.1.2, hg.2.2]⟩

theorem goodPair_terminal {s t u : ℝ} (hg : (t, u) ∈ goodPair s) :
    u ≤ max (3 / 2) (s - 3 / 2) := by
  by_cases hs : s ≤ 3
  · have ha : max 2 (s - 1) = 2 := max_eq_left (by linarith)
    have ht := hg.1.2
    rw [ha] at ht
    exact le_trans (show u ≤ 3 / 2 by linarith [hg.2.2]) (le_max_left _ _)
  · have ha : max 2 (s - 1) = s - 1 := max_eq_right (by linarith)
    have ht := hg.1.2
    rw [ha] at ht
    exact le_trans (show u ≤ s - 3 / 2 by linarith [hg.2.2]) (le_max_right _ _)

theorem phiOdd_le_A (s : ℝ) : phiOdd s ≤ sieveA := by
  by_cases hs : s ≤ 3
  · exact le_of_eq (phiOdd_initial hs)
  · have h := phiOdd_antitone (show 3 ≤ s by linarith)
    rwa [phiOdd_initial (s := 3) le_rfl] at h

noncomputable def goodPairDensityLower (M : ℝ) : ℝ := (1 / M) ^ 2 * (phiOdd M / sieveA)

theorem goodPairDensityLower_pos {M : ℝ} (hM : 4 ≤ M) : 0 < goodPairDensityLower M := by
  unfold goodPairDensityLower
  exact mul_pos (sq_pos_of_pos (one_div_pos.mpr (by linarith))) (div_pos (phiOdd_pos M) sieveA_pos)

noncomputable def goodPairProbability (M : ℝ) : ℝ := min (1 / 2) (goodPairDensityLower M / 16)

theorem goodPairProbability_pos {M : ℝ} (hM : 4 ≤ M) : 0 < goodPairProbability M :=
  lt_min (by norm_num) (div_pos (goodPairDensityLower_pos hM) (by norm_num))

theorem goodPairProbability_le_one (M : ℝ) : goodPairProbability M ≤ 1 :=
  le_trans (min_le_left _ _) (by norm_num)

end NumberTheoryLean.GoodPairTransitions

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_InvariantFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantDensities
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.TransitionKernels

noncomputable def oddFactor (s : ℝ) : ℝ := 1 - 1 / s ^ 2
noncomputable def evenDensity (s : ℝ) : ℝ := (Ici (2 : ℝ)).indicator phiEven s
noncomputable def oddDensity (s : ℝ) : ℝ := (Ici (1 : ℝ)).indicator (fun t ↦ oddFactor t * phiOdd t) s

noncomputable def beta : ℝ := ∫ s in (1 : ℝ)..3, oddDensity s

end Erdos970Dependency.InvariantDensities

end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantFiniteness
open NumberTheoryLean NumberTheoryLean.DerivativeWeights NumberTheoryLean.TransitionKernels
open Erdos970Dependency.InvariantDensities

noncomputable def evenMeasure : Measure ℝ := volume.withDensity (fun s ↦ ENNReal.ofReal (InvariantDensities.evenDensity s))
noncomputable def oddMeasure : Measure ℝ := volume.withDensity (fun s ↦ ENNReal.ofReal (InvariantDensities.oddDensity s))

end Erdos970Dependency.InvariantFiniteness

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_DensityComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InitialDensityFormulas
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.WeightFutureIntegrals NumberTheoryLean.TransitionKernels
open NumberTheoryLean.RegenerationTails NumberTheoryLean.TwoStepDensityBounds
open Erdos970Dependency.WeightIntegrals

noncomputable def regTwoDensity (u : ℝ) : ℝ :=
  (Ici (1 : ℝ)).indicator (fun u ↦ (W u * phiOdd u / sieveA) * tailW u) u

noncomputable def regThreeDensity (t : ℝ) : ℝ :=
  (Ici (2 : ℝ)).indicator (fun t ↦ (W t * phiEven t / sieveA) * regIntegral t) t

end Erdos970Dependency.InitialDensityFormulas

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.DensityComparison
open NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals
open NumberTheoryLean.TransitionKernels
open Erdos970Dependency.WeightIntegrals Erdos970Dependency.InitialDensityFormulas

noncomputable def dominationConstant : ℝ := 48 * sieveA / phiEven (23 / 10)

end Erdos970Dependency.DensityComparison

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_UniformDirichletBasepoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

noncomputable def absoluteZetaTwo : ℝ := ∑' n : ℕ, ‖LSeries.term (fun _ => 1) (2 : ℂ) n‖

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_DirichletZeroPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

noncomputable def dirichletCenter (t : ℝ) : ℂ := 3 + (t : ℂ) * Complex.I
noncomputable def dirichletDiskPoint (t : ℝ) (w : ℂ) : ℂ := dirichletCenter t + (5/2 : ℂ)*w
noncomputable def normalizedDirichlet {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) (w : ℂ) : ℂ :=
  DirichletCharacter.LFunction chi (dirichletDiskPoint t w) /
    DirichletCharacter.LFunction chi (dirichletCenter t)
noncomputable def dirichletDiskEnvelope (q : ℕ) (t : ℝ) : ℝ :=
  4 * absoluteZetaTwo * (|t|+6) * (q : ℝ)^(1/2:ℝ)

@[simp] theorem dirichletCenter_re (t : ℝ) : (dirichletCenter t).re = 3 := by
  simp [dirichletCenter]
@[simp] theorem dirichletDiskPoint_re (t : ℝ) (w : ℂ) :
    (dirichletDiskPoint t w).re = 3 + (5/2:ℝ)*w.re := by
  simp [dirichletDiskPoint]

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

@[simp] theorem dirichletDiskPoint_ofReal (sigma t : ℝ) :
    dirichletDiskPoint t ((2/5*(sigma-3):ℝ):ℂ) = (sigma:ℂ)+(t:ℂ)*Complex.I := by
  unfold dirichletDiskPoint dirichletCenter
  push_cast
  ring

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CharacterPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped ComplexOrder

noncomputable def characterPhase (n : ℕ) (t : ℝ) : ℂ := (n:ℂ)^(-(t:ℂ)*Complex.I)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_NonquadraticZeroFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

noncomputable def modulusHeight (q : ℕ) (t : ℝ) : ℝ := Real.log (q:ℝ)+Real.log (|t|+6)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_PrincipalEulerCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

noncomputable def localEulerFactor (alpha : ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  1-alpha*(p:ℂ)^(-s)

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

noncomputable def modulusEulerProduct (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, localEulerFactor 1 p s

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_ZetaPoleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex

noncomputable abbrev regularZeta := DirichletCharacter.LFunctionTrivChar₁ 1

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_RieszMellinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def rieszKernel (s : ℂ) : ℂ := 1/(s*(s+1))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Analysis_RieszIntegralRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Filter
open scoped Topology BigOperators

noncomputable def mellinFactor : ℂ := ((1/(2*Real.pi):ℝ):ℂ)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_PairedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedDrift

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels
open RegenerationDrift CompactExponentialMoments

theorem block_drift_algebra {a B p v e mass : ℝ} (ha : a ≤ 1 / 4) (hB : 0 ≤ B)
    (hp : 0 < p) (hp1 : p ≤ 1) (hv : 0 ≤ v) (he : e ≤ a * v + B) (hm : mass ≤ 1)
    (hcase : mass ≤ 1 - p ∨ 8 * B ≤ v) :
    e + (2 * B / p) * mass ≤ (1 - p / 2) * (v + 2 * B / p) := by
  let D := 2 * B / p
  have hD : 0 ≤ D := div_nonneg (by linarith) hp.le
  have hpD : p * D = 2 * B := by dsimp [D]; field_simp
  have hav : a * v ≤ v / 4 := by nlinarith [mul_le_mul_of_nonneg_right ha hv]
  have hrv : v / 2 ≤ (1 - p / 2) * v := by
    nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) / 2 ≤ 1 - p / 2 by linarith) hv]
  change e + D * mass ≤ (1 - p / 2) * (v + D)
  rcases hcase with hsmall | hlarge
  · have hmD := mul_le_mul_of_nonneg_left hsmall hD
    nlinarith
  · have hmD := mul_le_mul_of_nonneg_left hm hD
    nlinarith

end NumberTheoryLean.PairedDrift

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedVisitGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set
open scoped Topology
open NumberTheoryLean.TransitionKernels

noncomputable def gapAt (r T : ℝ) : ℝ := r*Real.exp (-T)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Renewal_KernelPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.KernelPotential

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

noncomputable def potential (B : Kernel α β) (K : Kernel α α) : Kernel α β :=
  Kernel.sum (fun n : ℕ => B ∘ₖ (K ^ n))

instance potential_isSFiniteKernel (B : Kernel α β) (K : Kernel α α)
    [IsSFiniteKernel B] [IsSFiniteKernel K] : IsSFiniteKernel (potential B K) := by
  have hp : ∀ n : ℕ, IsSFiniteKernel (K ^ n) := by
    intro n
    induction n with
    | zero => change IsSFiniteKernel (Kernel.id : Kernel α α); infer_instance
    | succ n ih =>
      rw [pow_succ]
      change IsSFiniteKernel ((K ^ n) ∘ₖ K)
      first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  unfold potential
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end NumberTheoryLean.KernelPotential

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_OnePairCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InvariantCostBound
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals
open Erdos970Dependency.InvariantDensities

noncomputable def evenMajor : ℝ → ℝ := (Ici (2 : ℝ)).indicator (fun s ↦ lowerDeficit s + upperDeficit (s - 1))
noncomputable def oddMajor : ℝ → ℝ := (Ici (1 : ℝ)).indicator (fun s ↦ upperDeficit s + lowerDeficit (s - 1))

end Erdos970Dependency.InvariantCostBound

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RieszIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Filter
open scoped Topology

noncomputable def characterRieszIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X : ℝ) (s : ℂ) : ℂ :=
  -logDeriv (DirichletCharacter.LFunction chi) s * rieszKernel s * (X:ℂ)^s

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_MeshStationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace Erdos970Dependency.MeshStationary

noncomputable def mesh (m : ℕ) : ℝ := 1/(m : ℝ)
noncomputable def point (m k : ℕ) : ℝ := (k : ℝ)*mesh m
noncomputable def weight (u : ℝ) : ℝ := (u+1)/u^2

end Erdos970Dependency.MeshStationary

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_NestedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

abbrev MV := MvPolynomial (Fin 2) R

end ErdosCriticalGeometry

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_IntervalPrimesDefinition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open Finset

noncomputable def intervalPrimes (x H : ℝ) (q : ℕ) (r : ℤ) : Finset ℕ :=
  (range (⌊max (x+H) 0⌋₊+1)).filter (fun p =>
    p.Prime ∧ x < (p:ℝ) ∧ (p:ℝ) ≤ x+H ∧ Int.ModEq (q:ℤ) (p:ℤ) r)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeCountAbel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.PrimeCountAbel

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology

noncomputable def mainKernel (t : ℝ) : ℝ := 1 / Real.log t ^ 2

end ErdosPrimeInputs.PrimeCountAbel

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrincipalPrimePowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def principalDifference (q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)-
    (ArithmeticFunction.vonMangoldt n:ℂ)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueSqrtSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

noncomputable def residuePsi {q : ℕ} (a : ZMod q) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊X⌋₊+1), ArithmeticFunction.vonMangoldt.residueClass a n

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

noncomputable def residuePrimeWeight {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  if n.Prime then ArithmeticFunction.vonMangoldt.residueClass a n else 0

noncomputable def residueTheta {q : ℕ} (a : ZMod q) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊X⌋₊+1), residuePrimeWeight a n

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory
open scoped Topology BigOperators
open ErdosPrimeInputs.PrimeCountAbel (mainKernel)

noncomputable def residueErrorKernel {q : ℕ} (a : ZMod q) (t : ℝ) : ℝ :=
  residueTheta a t/(t*Real.log t^2)-mainKernel t/(q.totient:ℝ)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_LargeModulusSiegelWalfisz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

noncomputable def cubeHeight (X : ℝ) : ℝ := (Real.log X)^((1:ℝ)/3)

end Erdos970Dependency.SiegelWalfisz



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimeIntervalFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset
open scoped Topology

noncomputable def primeIntervalFlags (includeLower includeUpper : Bool) (u v : ℝ) : Finset ℕ :=
  (range (⌊max v 0⌋₊+1)).filter (fun p:ℕ => p.Prime ∧
    (if includeLower then u ≤ (p:ℝ) else u < (p:ℝ)) ∧
    (if includeUpper then (p:ℝ) ≤ v else (p:ℝ) < v))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_WeightedPrimeMultiplePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset
open scoped Topology

noncomputable def primeMultiplesIn (d : ℕ) (P x y : ℝ) : Finset ℤ := by
  classical
  exact (Icc (⌈x⌉:ℤ) (⌊y⌋:ℤ)).filter (fun m:ℤ => x < (m:ℝ) ∧ (m:ℝ) < y ∧
    ∃ ell : ℕ, ell.Prime ∧ P < (ell:ℝ) ∧ (m=(d:ℤ)*ell ∨ m= -((d:ℤ)*ell)))

end Erdos970Dependency.SiegelWalfisz



open _root_.Filter


end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_AlignedPrimeCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped BigOperators

abbrev Vertex := Finset ℕ × Finset ℕ

end NumberTheoryLean.ResidueSieveTree

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_ActualCouplingUpdates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Finset
open scoped BigOperators
namespace Erdos970Dependency.MaximalCoupling

variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

noncomputable def common (a b : ι → ℝ) (i : ι) : ℝ := min (a i) (b i)
noncomputable def residual (a b : ι → ℝ) : ℝ := 1 - ∑ i, common a b i
noncomputable def leftRemainder (a b : ι → ℝ) (i : ι) : ℝ := a i - common a b i
noncomputable def rightRemainder (a b : ι → ℝ) (i : ι) : ℝ := b i - common a b i

noncomputable def matrix (a b : ι → ℝ) (i j : ι) : ℝ :=
  (if i = j then common a b i else 0) +
    if residual a b = 0 then 0 else leftRemainder a b i * rightRemainder a b j / residual a b

end Erdos970Dependency.MaximalCoupling

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_GeometricCostLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

noncomputable def costTransform (μ : Measure ℝ) (eta : ℝ) : ℝ≥0∞ :=
  ∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂μ

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_SigmaFamilyKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

lemma measurable_sigma_family {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {Z : Type*} [MeasurableSpace Z] {f : (Σ i, X i) → Z}
    (hf : ∀ i, Measurable (fun x => f (@Sigma.mk ι X i x))) : Measurable f := by
  intro S hS
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  exact hf i hS

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_OrdinaryMarkedWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.KernelPotential

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

noncomputable def stateFilter {S : Set α} (hS : MeasurableSet S) : Kernel α α := Kernel.id.restrict hS

instance stateFilter_isFiniteKernel {S : Set α} (hS : MeasurableSet S) : IsFiniteKernel (stateFilter hS) := by
  unfold stateFilter
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_MarkedCostHitReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.KernelPotential

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

noncomputable def kernelScale (p : ℝ≥0∞) (B : Kernel α β) [IsSFiniteKernel B] : Kernel α β :=
  B.withDensity (fun _ _ => p)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.KernelPotential

noncomputable def costWindowFilter (v H : ℝ) : Kernel ℝ ℝ :=
  stateFilter (S := Icc v (v+H)) measurableSet_Icc

noncomputable def costOutsideFilter (v H : ℝ) : Kernel ℝ ℝ :=
  stateFilter (S := (Icc v (v+H))ᶜ) measurableSet_Icc.compl

instance costWindowFilter_isFiniteKernel (v H : ℝ) : IsFiniteKernel (costWindowFilter v H) := by
  unfold costWindowFilter
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
instance costOutsideFilter_isFiniteKernel (v H : ℝ) : IsFiniteKernel (costOutsideFilter v H) := by
  unfold costOutsideFilter
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
end


