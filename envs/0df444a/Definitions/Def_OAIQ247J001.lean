-- Prove2me | Definitions.Def_OAIQ247J001
-- name    : OAIQ247J001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:41:56.671198+00:00
-- url     : https://prove2.me/theorems/0c5bce64-bf34-4382-af43-ba027e14b5ab
-- title:
--   Definitions bundle OAIQ247J001 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 495 declarations of OpenAI's Lean: 41 definitions, 1 inductive type or structure, 2 instances and 451 theorems. The definitions and types are `Erdos970.MellinInverseTransform`, `Erdos970.Mertens.E₁`, `Erdos970.Mertens.E₁p`, `Erdos970.Mertens.E₁Λ`, `Erdos970.Mertens.E₂p`, `Erdos970.Mertens.E₂Λ`, `Erdos970.Mertens.E₃`, `Erdos970.Mertens.M`, `Erdos970.Mertens.M_eq_f`, `Erdos970.Mertens.M_eq_summand`, `Erdos970.Mertens.γ`, `Erdos970.S_horiz`, `Erdos970.S_max`, `Erdos970.S_vert`, `Erdos970.VerticalIntegral`, `Erdos970.VerticalIntegral'`, `Erdos970.ballDR`, `Erdos970.f_M`, `Erdos970.logDerivZeta`, `Erdos970.zetaPartialSum`, `Erdos970.ℙ`, `Int.IsFundamentalDiscr`, `OAI.Erdos970.AdditiveLargeSieve.derivativeCoefficients`, `OAI.Erdos970.AdditiveLargeSieve.exponential`, `OAI.Erdos970.AdditiveLargeSieve.fractionValue`, `OAI.Erdos970.AdditiveLargeSieve.monomial`, `OAI.Erdos970.AdditiveLargeSieve.polynomial`, `OAI.Erdos970.AdditiveLargeSieve.reducedFractions`, `OAI.Erdos970.Erdos66Dependency.ResidueLifts.liftsOn`, `OAI.Erdos970.Erdos66Dependency.SingleResidueCount.residueClass`, `OAI.Erdos970.Erdos970Dependency.RawStateCost.stateCost`, `OAI.Erdos970.NumberTheoryLean.FinitePathGeometry.Side`, `OAI.Erdos970.NumberTheoryLean.FinitePathGeometry.cost`, `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.CostState`, `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.State`, `OAI.Erdos970.NumberTheoryLean.FinitePathMeasures.stateRatio`, `OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regenerationSet`, `OAI.Erdos970.NumberTheoryLean.FirstHitKernels.regenerationStateSet`, `OAI.Erdos970.NumberTheoryLean.PairedCostProcess.OddCost`, `OAI.Erdos970.NumberTheoryLean.RepresentativeAdmission.representativeGap` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Erdos970_Fourier`, `Erdos970_MertensClassical`, `Erdos970_PNT1_ComplexAnalysis`, `Erdos970_PNT2_LogDerivative`, `Erdos970_PNT3_RiemannZeta`, `Erdos970_PNT4_ZeroFreeRegion`, `Erdos970_PNT5_Strong`, `Erdos970_ResidueCalcOnRectangles`, `Erdos970_SmoothExistence`, `Erdos970_ZetaBounds`, `Erdos970_ZetaZeroFree`, `Jacobsthal_Estimates_OnePairCost`, `Jacobsthal_Estimates_ReducedFractions`, `Jacobsthal_Estimates_RepresentativeAdmission`, `Jacobsthal_Harmonic_FourierDerivative`, `Jacobsthal_Paths_FiniteHistorySupport`, `Jacobsthal_Probability_FirstHitKernels`, `Jacobsthal_Probability_MarkedVisitGeometry`, `Jacobsthal_Probability_TransitionKernels`, `Jacobsthal_Sieve_IntegerResidueVariance`, `Jacobsthal_Sieve_RealCoprimeResidueCount`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ247J006` and `OAIQ247J007`; the statements `Erdos970.Mertens.LogZetaInteg.log_zeta_eq_integ_aux_jb247`, `Erdos970.Mertens.sum_M_eq_summand_le_jb247`, `OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247` and `OAI.Erdos970.WeightedTorusJets.source_character_global_greedy_determinant_local_bounds_jb247`; the proofs of `Erdos970.Mertens.LogZetaInteg.log_zeta_eq_integ_aux_jb247`, `Erdos970.Mertens.sum_M_eq_summand_le_jb247`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_primitive_real_zero_free_disk_jb247`, `OAI.Erdos970.EulerWeightedLower.uniformLowerEnvelope_limit_jb247`, `OAI.Erdos970.WeightedTorusJets.characterField_changeLevel_discr_natAbs_jb247`, `OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247` and `OAI.Erdos970.WeightedTorusJets.source_character_global_greedy_determinant_local_bounds_jb247`.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit adc7f12

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.ZMod.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.Index
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
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
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Tactic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.ContinuousMap.Bounded.Basic
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
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul

/-- Mathlib d13f23b's `Int.IsFundamentalDiscr`: a fundamental discriminant is a squarefree `D ≡ 1 [4]`, or `4 * d`
with `d` squarefree and `d ≡ 2, 3 [4]`. -/
def _root_.Int.IsFundamentalDiscr (D : ℤ) : Prop :=
  (D % 4 = 1 ∧ Squarefree D) ∨ ∃ d : ℤ, D = 4 * d ∧ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3)

/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ247_JB.Erdos970_Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

open FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

section lemmas

local instance instCoeForallRealForallComplex_solutions_rd15514_1 {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

end lemmas

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_MertensClassical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.ArithmeticFunction hiding log

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

attribute [fun_prop] measurable_from_top

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

end Mertens

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT1_ComplexAnalysis
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


lemma lem_exprule (n : ℕ) (hn : n ≥ 1) (α β : ℂ) : (n : ℂ) ^ (α + β) = (n : ℂ) ^ α * (n : ℂ) ^ β := by
  apply Complex.cpow_add
                              
  rw [Nat.cast_ne_zero]
                        
  rw [← Nat.one_le_iff_ne_zero]
  exact hn

lemma lem_realbw (b : ℝ) (w : ℂ) : (b * w).re = b * w.re := by
  exact Complex.re_ofReal_mul b w

lemma lem_Euler (a : ℝ) : Complex.exp (a * Complex.I) = Real.cos a + Real.sin a * Complex.I := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma lem_Reecos (a : ℝ) : (Complex.exp (a * Complex.I)).re = Real.cos a := by
  rw [lem_Euler]
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex.re_ofReal_mul]
  rw [Complex.I_re]
  simp

lemma lem_coseven (a : ℝ) : Real.cos (-a) = Real.cos a := by
  exact Real.cos_neg a

lemma lem_coseveny (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : Real.cos (-y * Real.log (n : ℝ)) = Real.cos (y * Real.log (n : ℝ)) := by
  rw [neg_mul]
  exact lem_coseven (y * Real.log (n : ℝ))

lemma lem_niyelog (n : ℕ) (hn : n ≥ 1) (y : ℝ) : (n : ℂ) ^ (-y * Complex.I) = Complex.exp (-y * Complex.I * Real.log (n : ℝ)) := by
                                
  have h1 : (n : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rw [← Nat.one_le_iff_ne_zero]
    exact hn
                                                     
  rw [Complex.cpow_def_of_ne_zero h1]

  rw [← Complex.natCast_log]

  ring_nf

lemma lem_eacosalog (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : (Complex.exp (-y * Complex.I * Real.log (n : ℝ))).re = Real.cos (-y * Real.log (n : ℝ)) := by
                                  
  let a := -y * Real.log (n : ℝ)
                                               
  have h : -y * Complex.I * Real.log (n : ℝ) = a * Complex.I := by
    simp [a, mul_assoc, mul_comm Complex.I]
  rw [h]
                     
  exact lem_Reecos a

lemma lem_eacosalog2 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (-y * Real.log (n : ℝ)) := by
  rw [lem_niyelog n hn y]
  exact lem_eacosalog n hn y

lemma lem_eacosalog3 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (y * Real.log (n : ℝ)) := by
  rw [lem_eacosalog2 n hn y]
  exact lem_coseveny n hn y

lemma lem_cos2t (θ : ℝ) : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
  exact Real.cos_two_mul θ

lemma lem_cos2t2 (θ : ℝ) : 2 * Real.cos θ ^ 2 = 1 + Real.cos (2 * θ) := by
  rw [lem_cos2t]
  ring

lemma lem_cosSquare (θ : ℝ) : 2 * (1 + Real.cos θ)^2 = 2 + 4 * Real.cos θ + 2 * Real.cos θ^2 := by
  ring

lemma lem_cos2cos341 (θ : ℝ) : 2 * (1 + Real.cos θ) ^ 2 = 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [lem_cosSquare]
  rw [lem_cos2t2]
  ring

lemma lem_SquarePos (y : ℝ) : 0 ≤ y ^ 2 := by
  exact sq_nonneg y

lemma lem_SquarePos2 (y : ℝ) : 0 ≤ 2 * y ^ 2 := by
  apply mul_nonneg
  · norm_num
  · exact lem_SquarePos y

lemma lem_SquarePoscos (θ : ℝ) : 0 ≤ 2 * (1 + Real.cos θ) ^ 2 := by
  exact lem_SquarePos2 (1 + Real.cos θ)

lemma lem_postrig (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [← lem_cos2cos341]
  exact lem_SquarePoscos θ

lemma lem_postriglogn (n : ℕ) (_hn : n ≥ 1) (t : ℝ) : 0 ≤ 3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)) := by
  rw [mul_assoc]
  exact lem_postrig (t * Real.log (n : ℝ))

lemma real_part_of_diff (M : ℝ) (w : ℂ) : (2 * M - w).re = 2 * M - w.re := by
  simp [Complex.sub_re]

lemma real_part_of_diffz (M : ℝ) (f_z : ℂ) : (2 * M - f_z).re = 2 * M - f_z.re := real_part_of_diff M f_z

lemma inequality_reversal (x M : ℝ) (hxM : x ≤ M) : 2 * M - x ≥ M := by linarith

lemma real_part_lower_bound (w : ℂ) (M : ℝ) (_hM : M > 0) (h : w.re ≤ M) : 2 * M - w.re ≥ M := by apply inequality_reversal w.re M h

lemma real_part_lower_bound3 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w).re > 0 := by
  rw [real_part_of_diffz]
  apply lt_of_le_of_lt'
  apply real_part_lower_bound
  exact hM
  exact h
  exact hM

lemma nonzero_if_real_part_positive (w : ℂ) (hw_re_pos : w.re > 0) : w ≠ 0 := by
  by_contra h
  rw [h] at hw_re_pos
  exact lt_irrefl 0 hw_re_pos

lemma lem_real_part_lower_bound4 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w) ≠ 0 := by
  apply nonzero_if_real_part_positive
  exact real_part_lower_bound3 w M hM h

lemma lem_abspos (z : ℂ) : z ≠ 0 → norm z > 0 := by
  intro h_ne_zero
  apply Real.sqrt_pos.mpr
  exact Complex.normSq_pos.mpr h_ne_zero

lemma lem_real_part_lower_bound5 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : norm (2 * M - w) > 0 := by
  apply lem_abspos
  exact lem_real_part_lower_bound4 w M hM h

lemma lem_modulus_sq_ReImw (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := by
  simp_rw [Complex.sq_norm]
  simp_rw [Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma lem_modulus_sq_identity (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := lem_modulus_sq_ReImw M w

lemma lem_nonnegative_product (M x : ℝ) (hM : M > 0) (hxM : x ≤ M) : 4 * M * (M - x) ≥ 0 := by
  have h_four_M_nonneg : 4 * M ≥ 0 := by linarith [hM]
  have h_diff_nonneg : M - x ≥ 0 := by linarith [hxM]
  apply mul_nonneg h_four_M_nonneg h_diff_nonneg

lemma lem_nonnegative_product2 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : 4 * M * (M - w.re) ≥ 0 := by
  apply lem_nonnegative_product
  exact hM
  exact hw_re_le_M

lemma lem_nonnegative_product3 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 - norm w ^ 2 ≥ 0 := by
  rw [lem_modulus_sq_identity]
  apply lem_nonnegative_product2
  exact hM
  exact hw_re_le_M

lemma lem_nonnegative_product4 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 ≥ norm w ^ 2 := by
  have h := lem_nonnegative_product3 M w hM hw_re_le_M
  linarith

lemma lem_nonnegative_product5 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ≥ norm w := by
  have h_sq_ge : ‖2 * M - w‖ ^ 2 ≥ ‖w‖ ^ 2 := by
    apply lem_nonnegative_product4 M w hM hw_re_le_M
  rw [ge_iff_le] at h_sq_ge                                                

  apply (sq_le_sq₀ (norm_nonneg w) (norm_nonneg (2 * M - w))).mp
  exact h_sq_ge

lemma lem_nonnegative_product6 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm w ≤ norm (2 * M - w) := by apply lem_nonnegative_product5 M w hM hw_re_le_M

lemma lem_ineqmultr (a b c : ℝ) (hc : c > 0) (_ha : 0 ≤ a) (hab : a ≤ b) : a / c ≤ b / c := by
  apply div_le_div_of_nonneg_right
  exact hab
  linarith [hc]

lemma lem_ineqmultrbb (a b : ℝ) (hb : b > 0) (ha : 0 ≤ a) (hab : a ≤ b) : a / b ≤ 1 := by
  have h := lem_ineqmultr a b b hb ha hab
  rw [div_self (ne_of_gt hb)] at h
  exact h

lemma lem_nonnegative_product7 (M : ℝ) (w : ℂ) (_hM : M > 0) (h_abs_diff_pos : norm (2 * M - w) > 0) (h_abs_le_abs_diff : norm w ≤ norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 := by
                                                                                   
  have h_abs_w_nonneg : 0 ≤ ‖w‖ := norm_nonneg w

  apply lem_ineqmultrbb
  exact h_abs_diff_pos
  exact h_abs_w_nonneg
  exact h_abs_le_abs_diff

lemma lem_nonnegative_product8 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) (h_abs_le_abs_diff : norm w ≤
norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 := by
  apply lem_nonnegative_product7 M w
  exact hM
  apply lem_real_part_lower_bound5 w M hM hw_re_le_M
  exact h_abs_le_abs_diff

lemma lem_nonnegative_product9 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm w / norm (2 * M - w) ≤ 1 := by
  apply lem_nonnegative_product8
  exact hM
  exact hw_re_le_M
  apply lem_nonnegative_product6
  exact hM
  exact hw_re_le_M

lemma lem_triangle_ineq (N G : ℂ) : norm (N + G) ≤ norm N + norm G := by
  exact norm_add_le N G

lemma lem_triangleineqminus (N F : ℂ) : norm (N - F) ≤ norm N + norm F := by
  rw [sub_eq_add_neg]
  calc
    ‖N + (-F)‖ ≤ ‖N‖ + ‖-F‖ := by apply lem_triangle_ineq
    _ = ‖N‖ + ‖F‖ := by rw [norm_neg]

lemma lem_rtriangle (r : ℝ) (N F : ℂ) (hr : r > 0) : r * norm (N - F) ≤ r * (norm N + norm F) := by
  apply mul_le_mul_of_nonneg_left
  apply lem_triangleineqminus
  linarith

lemma rtriangle2 (r : ℝ) (N F : ℂ) (hr : r > 0) : r * norm (N - F) ≤ r * norm N + r * norm F := by
  have h := lem_rtriangle r N F hr
  linarith [h]

lemma lem_rtriangle3 (r R : ℝ) (N F : ℂ) (hr : r > 0) (_hR : r < R) (h : R * norm F ≤ r * norm (N - F)) : R * norm F ≤ r * norm N + r * norm F := by
  calc
    R * norm F ≤ r * norm (N - F) := by exact h
    _ ≤ r * norm N + r * norm F := by apply rtriangle2 r N F hr

lemma lem_rtriangle4 (r R : ℝ) (N F : ℂ) (hr : 0 < r) (hR : r < R) (h_hyp : R * norm F ≤ r * norm (N - F)) : (R - r) * norm F ≤ r * norm N := by
  have h_result_from_lem3 : R * norm F ≤ r * norm N + r * norm F := by
    apply lem_rtriangle3 r R N F hr hR h_hyp
  linarith [h_result_from_lem3]

lemma lem_rtriangle5 (r R M : ℝ) (F : ℂ) (hr : 0 < r) (hrR : r < R) (hM : M > 0)
    (h_hyp : R * norm F ≤ r * norm (2 * M - F)) :
(R - r) * norm F ≤ 2 * M * r := by
                                        
  have h1 : (R - r) * norm F ≤ r * norm (2 * M : ℂ) :=
    lem_rtriangle4 r R (2 * M : ℂ) F hr hrR h_hyp

  have h2 : norm (2 * M : ℂ) = 2 * M := by

    have h_pos : (2 * M : ℝ) > 0 := by linarith [hM]
                                                                        
    convert (preTransparency := .instances) Complex.norm_of_nonneg (le_of_lt h_pos) using 1
                                                             
    norm_cast
                             
  rw [h2] at h1
                                     
  rw [mul_comm r (2 * M)] at h1
  exact h1

lemma lem_RrFpos (r R : ℝ) (F : ℂ) (_hr : 0 < r) (hrR : r < R) : (R - r) * norm F ≥ 0 := by
  have h_R_minus_r_nonneg : R - r ≥ 0 := by linarith [hrR]
  have h_abs_F_nonneg : 0 ≤ norm F := by apply norm_nonneg
  apply mul_nonneg h_R_minus_r_nonneg h_abs_F_nonneg

lemma lem_rtriangle6 (r R M : ℝ) (F : ℂ) (hr : 0 < r) (hrR : r < R) (_hM : M > 0)
    (h_hyp : (R - r) * norm F ≤ 2 * M * r) :
norm F ≤ (2 * M * r) / (R - r) := by
  have h_R_minus_r_pos : R - r > 0 := by linarith [hrR]
  have h_numerator_nonneg : 0 ≤ (R - r) * ‖F‖ := by apply lem_RrFpos r R F hr hrR
                                                                          
  have h_ineq_with_denominators : ( (R - r) * ‖F‖ ) / (R - r) ≤ (2 * M * r) / (R - r) := by
    apply lem_ineqmultr
    exact h_R_minus_r_pos          
    exact h_numerator_nonneg          
    exact h_hyp          
                                                                        
  rw [mul_div_cancel_left₀ (‖F‖) (ne_of_gt h_R_minus_r_pos)] at h_ineq_with_denominators
                                                     
  exact h_ineq_with_denominators

lemma lem_rtriangle7 (r R M : ℝ) (F : ℂ)
    (hr : 0 < r) (hrR : r < R) (hM : M > 0)
    (h_hyp : R * norm F ≤ r * norm (2 * M - F)) :
norm F ≤ (2 * M * r) / (R - r) := by
  have h_step1 := lem_rtriangle5 r R M F hr hrR hM h_hyp
  apply lem_rtriangle6 r R M F hr hrR hM h_step1

def ballDR (R : ℝ) : Set ℂ := Metric.ball (0 : ℂ) R

theorem analyticWithinAt_to_analyticAt_aux {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ} (_hS : S ∈ nhds z)
  (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : ENNReal) (_h_conv_on_inter : r ≤ p.radius) (_hr_pos : 0 < r)
  (hasSumt : ∀ {y : ℂ}, z + y ∈ insert z S → y ∈ Metric.eball 0 r → HasSum (fun n => (p n) fun _x => y) (f (z + y)))
  (ε : ℝ) (hε_pos : ε > 0) (h_ball_subset_S : Metric.ball z ε ⊆ S) :
  let r' := min r (ENNReal.ofReal ε);
  ∀ {y : ℂ}, y ∈ Metric.eball 0 r' → HasSum (fun n => (p n) fun _x => y) (f (z + y)) := by
  intro r' y hy
  apply hasSumt
  ·                            

    right                                              
    apply h_ball_subset_S
    rw [Metric.mem_ball]
                                      
    simp
                               
    have : y ∈ Metric.eball 0 (ENNReal.ofReal ε) := by
      apply Metric.eball_subset_eball (min_le_right r (ENNReal.ofReal ε)) hy

    have ε_nn : ENNReal.ofReal ε = ↑(ε.toNNReal) := by
      simp [ENNReal.ofReal]
    rw [ε_nn] at this
    rw [@Metric.eball_coe] at this
    simpa [Metric.mem_ball, dist_self_add_right, Real.toNNReal_of_nonneg hε_pos.le]

  ·                              
    exact Metric.eball_subset_eball (min_le_left r (ENNReal.ofReal ε)) hy

theorem analyticWithinAt_to_analyticAt {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ}
    (hS : S ∈ nhds z) (h : AnalyticWithinAt ℂ f S z) : AnalyticAt ℂ f z := by
  rcases h with ⟨p, hp⟩

  use p

  rcases hp with ⟨r, h_conv_on_inter, hr_pos⟩

  rcases Metric.mem_nhds_iff.mp hS with ⟨ε, hε_pos, h_ball_subset_S⟩

  let r' := min r (ENNReal.ofReal ε)
  use r'

  constructor

  · exact inf_le_of_left_le h_conv_on_inter

  ·
    exact lt_min hr_pos (ENNReal.ofReal_pos.mpr hε_pos)
  rename_i hasSumt
  exact analyticWithinAt_to_analyticAt_aux hS p r h_conv_on_inter hr_pos hasSumt ε hε_pos h_ball_subset_S

lemma lem_1zanalDR (R : ℝ) (_hR_pos : 0 < R) :
    AnalyticOn ℂ (fun z ↦ z⁻¹) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by

  apply AnalyticOn.mono (analyticOn_inv)
                                                     
  intro z hz
                                                       
  exact hz.2

lemma lem_analprod {T : Set ℂ} {f1 f2 : ℂ → ℂ} (hf1 : AnalyticOn ℂ f1 T) (hf2 : AnalyticOn ℂ f2 T) :
    AnalyticOn ℂ (f1 * f2) T := by
  exact hf1.mul hf2

lemma lem_fzzTanal {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
                          
  rw [show (fun z ↦ f z / z) = (fun z ↦ f z) * (fun z ↦ z⁻¹) by ext; simp [div_eq_mul_inv]]
                                
  let T := {z : ℂ | norm z ≤ R ∧ z ≠ 0}
                                                            
  have hf_on_T : AnalyticOn ℂ f T := hf.mono (?_)
                         
  have h_inv_on_T : AnalyticOn ℂ (fun z ↦ z⁻¹) T := lem_1zanalDR R hR_pos
                                                                
  exact lem_analprod hf_on_T h_inv_on_T
  intro z hz
  have hT : T = {z | norm z ≤ R ∧ z ≠ 0} := rfl
  rw [hT] at hz
  simp only [Set.mem_ofPred_eq] at hz
  simp only [Metric.mem_closedBall]
  simp only [dist_zero_right]
  exact hz.1

lemma lem_AnalOntoWithin {V : Set ℂ} {h : ℂ → ℂ} (hh : AnalyticOn ℂ h V) (z : ℂ) (hz : z ∈ V) :
    AnalyticWithinAt ℂ h V z := by
  exact hh z hz

lemma lem_DR0T {R : ℝ} (hR : 0 < R) :
    Metric.closedBall 0 R = {0} ∪ {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
  ext z
  simp [Metric.closedBall, dist_zero_right]
  by_cases hz : z = 0
  · simp [hz, hR.le]
  · simp [hz]

lemma lem_analWWWithin {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    (AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0) →
    (∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) →
    (∀ z ∈ Metric.closedBall 0 R, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) := by
  intro h0 hT z hz
  rw [lem_DR0T hR_pos] at hz
  cases' hz with hz hz
  · simp at hz
    rw [hz]
    exact h0
  · exact hT z hz

lemma lem_analWWithinAtOn (R : ℝ) (hR_pos : 0 < R) (h : ℂ → ℂ)
    (h_at_0 : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0)
    (h_at_T : ∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) :
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  exact lem_analWWWithin hR_pos h h_at_0 h_at_T

lemma lem_AnalAttoWithin {h : ℂ → ℂ} {s : Set ℂ} (hh : AnalyticAt ℂ h 0) :
    AnalyticWithinAt ℂ h s 0 := by
  exact hh.analyticWithinAt

lemma analyticWithinAt_punctured_to_closedBall {R : ℝ} (_hR : 0 < R) {h : ℂ → ℂ} {z : ℂ} (hz : z ∈ {w : ℂ | norm w ≤ R ∧ w ≠ 0}) (h_within : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z) : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z := by
                                                                                                                   
  apply AnalyticWithinAt.mono_of_mem_nhdsWithin h_within

  have hz_ne_zero : z ≠ 0 := hz.2

  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]

  use Metric.ball z (‖z‖ / 2)

  constructor
  ·                                      
    exact Metric.ball_mem_nhds z (half_pos (norm_pos_iff.mpr hz_ne_zero))

  ·                                                                                       
    intro w hw
    constructor
    ·                   
      have w_in_closedball : w ∈ Metric.closedBall 0 R := hw.2
      simp only [Metric.mem_closedBall, dist_zero_right] at w_in_closedball
                                           
      simp [w_in_closedball]
    ·              
      intro hw_eq_zero
      have w_in_ball : w ∈ Metric.ball z (‖z‖ / 2) := hw.1
      rw [hw_eq_zero] at w_in_ball
      simp only [Metric.mem_ball] at w_in_ball

      rw [dist_comm] at w_in_ball
      simp at w_in_ball
      have pos_norm : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne_zero
      linarith [pos_norm]

lemma lem_analAtOnOn {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    AnalyticAt ℂ h 0 →
    AnalyticOn ℂ h {z : ℂ | norm z ≤ R ∧ z ≠ 0} →
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  intro h_at_0 h_on_punctured

  apply lem_analWWithinAtOn R hR_pos h

  · exact lem_AnalAttoWithin h_at_0

  · intro z hz
                                                       
    have h_within_punctured : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z :=
      lem_AnalOntoWithin h_on_punctured z hz
                                     
    exact analyticWithinAt_punctured_to_closedBall hR_pos hz h_within_punctured

lemma lem_orderne0 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) :
    analyticOrderAt f 0 ≠ 0 := by exact (AnalyticAt.analyticOrderAt_ne_zero hf).mpr hf0

lemma lem_ordernetop (f : ℂ → ℂ) (_hf : AnalyticAt ℂ f 0) (hf_ne_zero : ¬(∀ᶠ z in nhds 0, f z = 0)) :
    analyticOrderAt f 0 ≠ ⊤ := by
  intro h
  rw [analyticOrderAt_eq_top] at h
  exact hf_ne_zero h

lemma lem_ordernatcast (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) (hn : analyticOrderAt f 0 = n) :
    ∃ (g : ℂ → ℂ), AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧ ∀ᶠ (z : ℂ) in nhds 0, f z = z ^ n * g z := by

  rw [AnalyticAt.analyticOrderAt_eq_natCast] at hn
  · convert (preTransparency := .instances) hn
    aesop
  · exact hf

lemma lem_ordernatcast1 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) (hn : analyticOrderAt f 0 = n) (hn_ne_zero : n ≠ 0) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
                           
  rcases lem_ordernatcast f hf n hn with ⟨g, hg_analytic, _, hf_eq_g⟩
                              
  use fun z ↦ z ^ (n - 1) * g z
  constructor
  ·                                                    
    exact (analyticAt_id.pow (n - 1)).mul hg_analytic
  ·                        
    filter_upwards [hf_eq_g] with z h_eq
    rw [h_eq]
    ring_nf
    rw [← pow_succ' z (n - 1), Nat.sub_add_cancel (Nat.pos_of_ne_zero hn_ne_zero)]

lemma lem_ordernatcast2_old (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (h_not_eventually_zero : ¬ (∀ᶠ z in nhds 0, f z = 0)) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
                                 
  let n₀ := analyticOrderAt f 0
                                                                        
  have hn_ne_top : n₀ ≠ ⊤ := lem_ordernetop f hf h_not_eventually_zero
                                             
  lift n₀ to ℕ using hn_ne_top with n hn_eq
                                                  
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    rw [hn_zero] at hn_eq

    have t := (lem_orderne0 f hf hf0)
    have : n₀ = analyticOrderAt f 0 := rfl
    rw [←this] at t
    exact t (id (Eq.symm hn_eq))
                                                                       
  exact lem_ordernatcast1 f hf n (by aesop) hn_ne_zero

lemma lem_ordernatcast2 {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ) (hf0 : f 0 = 0)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticAt ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) 0 := by
                                                                            
  have hS : Metric.closedBall 0 R ∈ nhds (0 : ℂ) := by
                                                              
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hR_pos) ?subset
    exact Metric.ball_subset_closedBall
  have hf_within : AnalyticWithinAt ℂ f (Metric.closedBall 0 R) 0 := hf 0 (by
    simp [Metric.mem_closedBall, hR_pos.le])
  have hf_at0 : AnalyticAt ℂ f 0 := analyticWithinAt_to_analyticAt hS hf_within

  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  by_cases hEZ : (∀ᶠ z in nhds (0 : ℂ), f z = 0)
  ·                                                                                          
                                          
    have hU : {z : ℂ | f z = 0} ∈ nhds (0 : ℂ) := by simpa only [Filter.Eventually] using hEZ
                                        
    have hf_eq_zero : f =ᶠ[nhds (0 : ℂ)] (fun _ : ℂ => 0) := by
      refine (Filter.eventuallyEq_iff_exists_mem).2 ?_
      exact ⟨{z | f z = 0}, hU, by intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
                                                                    
    have h_fderiv_zero : (fderiv ℂ f 0) = 0 := by
      simpa using (Filter.EventuallyEq.fderiv_eq hf_eq_zero)

    have h_g_zero_on_U : ∀ z ∈ {z : ℂ | f z = 0}, g z = 0 := by
      intro z hzU
      by_cases hz0 : z = 0
      ·                                  
        simp [g, hz0, h_fderiv_zero]
      ·                                  
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hzU
        simp [g, hz0, this]
                                                                                  
    have h_const0_within : AnalyticWithinAt ℂ (fun _ : ℂ => (0 : ℂ)) {z : ℂ | f z = 0} 0 :=
      analyticAt_const.analyticWithinAt
    have h_g_within : AnalyticWithinAt ℂ g {z : ℂ | f z = 0} 0 := by
                                        
      apply h_const0_within.congr
      intro z hz
      by_cases hz0 : z = 0
      ·        
        simp [g, hz0, h_fderiv_zero]
      ·             
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hz
        simp [g, hz0, this]
                           
      simp [g, h_fderiv_zero]
    exact analyticWithinAt_to_analyticAt hU h_g_within

  ·                                                                
    have h_notEZ : ¬ (∀ᶠ z in nhds (0 : ℂ), f z = 0) := hEZ
                                                        
    rcases lem_ordernatcast2_old f hf_at0 hf0 h_notEZ with ⟨h0, h0_at0, hfac_ev⟩
                                                               
    have hV : {z : ℂ | f z = z * h0 z} ∈ nhds (0 : ℂ) := by simpa only [Filter.Eventually] using hfac_ev
    have h_eq_nhds : f =ᶠ[nhds (0 : ℂ)] (fun z => z * h0 z) :=
      (Filter.eventuallyEq_iff_exists_mem).2 ⟨{z : ℂ | f z = z * h0 z}, hV, by
        intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
                              
    have h_fderiv_prod : fderiv ℂ f 0 = fderiv ℂ (fun z => z * h0 z) 0 :=
      Filter.EventuallyEq.fderiv_eq h_eq_nhds
                                                                              
    have h_diff_id : DifferentiableAt ℂ (fun z : ℂ => z) 0 := differentiableAt_id
    have h_diff_h0 : DifferentiableAt ℂ h0 0 := h0_at0.differentiableAt
                             
    have h_val0 : (fderiv ℂ f 0) 1 = h0 0 := by
                                                           
      rw [h_fderiv_prod]
      rw [fderiv_fun_mul' h_diff_id h_diff_h0]
      simp only [add_apply, smul_apply]
      rw [fderiv_fun_id]
      simp only [ContinuousLinearMap.id_apply]
      simp only [zero_smul, zero_add]
      simp

    have h_geq_h0_on_V : ∀ z ∈ {z : ℂ | f z = z * h0 z}, g z = h0 z := by
      intro z hzU
      by_cases hz0 : z = 0
      ·        
        simpa [g, hz0] using h_val0
      ·                                    
        have : f z = z * h0 z := by simpa [Set.mem_ofPred_eq] using hzU
        simp only [g, if_neg hz0, this]
        exact mul_div_cancel_left₀ (h0 z) hz0
                                                                    
    have h0_within : AnalyticWithinAt ℂ h0 {z : ℂ | f z = z * h0 z} 0 := h0_at0.analyticWithinAt
    have hg_within : AnalyticWithinAt ℂ g {z : ℂ | f z = z * h0 z} 0 := by

      apply AnalyticWithinAt.congr h0_within
                                 
      intro z hz
      exact h_geq_h0_on_V z hz

      have h_0_in_V : (0 : ℂ) ∈ {z : ℂ | f z = z * h0 z} := by
        simp [hf0]
      exact h_geq_h0_on_V 0 h_0_in_V
    exact analyticWithinAt_to_analyticAt hV hg_within

lemma lem_ballDR (R : ℝ) (hR : R > 0) : closure (ballDR R) = Metric.closedBall (0 : ℂ) R := by
  unfold ballDR
  exact closure_ball 0 (ne_of_gt hR)

lemma lem_inDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw : w ∈ closure (ballDR R)) : norm w ≤ R := by
  rw [lem_ballDR R hR] at hw
  rw [Metric.mem_closedBall] at hw
  rw [Complex.dist_eq] at hw
  simp at hw
  exact hw

lemma lem_notinDR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw : w ∉ ballDR R) : norm w ≥ R := by
                               
  unfold ballDR at hw
                                                   
  rw [Metric.mem_ball] at hw
                                                              
  push Not at hw
                                                                     
  rw [Complex.dist_eq] at hw
                       
  simp at hw
  exact hw

lemma lem_legeR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw1 : norm w ≤ R) (hw2 : norm w ≥ R) : norm w = R := by
  linarith

lemma lem_circleDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw1 : w ∈ closure (ballDR R)) (hw2 : w ∉ ballDR R) : norm w = R := by
  have h1 : norm w ≤ R := lem_inDR R hR w hw1
  have h2 : norm w ≥ R := lem_notinDR R hR w hw2
  exact lem_legeR R hR w h1 h2

lemma lem_Rself (R : ℝ) (hR : R > 0) : |R| = R := by
  rw [abs_eq_self]
  linarith

lemma lem_Rself2 (R : ℝ) (hR : R > 0) : |R| ≤ R := by
  rw [lem_Rself R hR]

lemma lem_Rself3 (R : ℝ) (hR : R > 0) : (R : ℂ) ∈ closure (ballDR R) := by
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  simp
  exact lem_Rself2 R hR

lemma lem_DRcompact (R : ℝ) (hR : R > 0) : IsCompact (closure (ballDR R)) := by
  rw [lem_ballDR R hR]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact Metric.isClosed_closedBall
  · exact Metric.isBounded_closedBall

lemma lem_ExtrValThm {K : Set ℂ} (hK : IsCompact K) (hK_nonempty : K.Nonempty) (g : K → ℂ) (hg : Continuous g) :
∃ v : K, ∀ z : K, norm (g z) ≤ norm (g v) := by
                                       
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
                            
  have : Nonempty K := hK_nonempty.to_subtype
                                                             
  let f : K → ℝ := fun z => norm (g z)
                                
  have hf_cont : Continuous f := continuous_norm.comp hg
                                                       
  obtain ⟨v, hv_mem, hv_max⟩ := IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty hf_cont.continuousOn
  use v
  intro z
  exact hv_max (Set.mem_univ z)

lemma lem_ExtrValThmDR (R : ℝ) (hR : R > 0) (g : closure (ballDR R) → ℂ) (hg : Continuous g) :
∃ v : closure (ballDR R), ∀ z : closure (ballDR R), norm (g z) ≤ norm (g v) := by
                                                     
  have hK_compact : IsCompact (closure (ballDR R)) := lem_DRcompact R hR
                                             
  have hK_nonempty : (closure (ballDR R)).Nonempty := by
    rw [lem_ballDR R hR]
    rw [Metric.nonempty_closedBall]
    linarith
                                    
  exact lem_ExtrValThm hK_compact hK_nonempty g hg

lemma lem_AnalCont {R : ℝ} (_hR : R > 0) (H : ℂ → ℂ) (h_analytic : AnalyticOn ℂ H (closure (ballDR R))) :
Continuous (H ∘ (Subtype.val : closure (ballDR R) → ℂ)) := by
                                                                    
  have h_cont_on : ContinuousOn H (closure (ballDR R)) := AnalyticOn.continuousOn h_analytic
                              
  have h_val_cont : Continuous (Subtype.val : closure (ballDR R) → ℂ) := continuous_subtype_val

  exact ContinuousOn.comp_continuous h_cont_on h_val_cont (fun _ => Subtype.mem _)

lemma lem_ExtrValThmh {R : ℝ} (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ u : closure (ballDR R), ∀ z : closure (ballDR R), norm (h u) ≥ norm (h z) := by
                                                    
  have hg_continuous : Continuous (h ∘ Subtype.val : closure (ballDR R) → ℂ) :=
    lem_AnalCont hR h h_analytic
                                              
  obtain ⟨v, hv⟩ := lem_ExtrValThmDR R hR (h ∘ Subtype.val) hg_continuous
                   
  use v
                                        
  intro z
  have : norm ((h ∘ Subtype.val) z) ≤ norm ((h ∘ Subtype.val) v) := hv z
                             
  simp [Function.comp] at this
  exact this

lemma lem_MaxModP (R : ℝ) (_hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) := by
                                                             
  have h_preconnected : IsPreconnected (ballDR R) := by
    unfold ballDR
    apply Convex.isPreconnected
    exact convex_ball (0 : ℂ) R

  have h_open : IsOpen (ballDR R) := by
    unfold ballDR
    exact Metric.isOpen_ball

  have h_diff_cont : DiffContOnCl ℂ h (ballDR R) := by
    constructor
    ·                                   
      apply AnalyticOn.differentiableOn
      exact h_analytic.mono subset_closure
    ·                                         
      exact AnalyticOn.continuousOn h_analytic

  have h_max_on : IsMaxOn (norm ∘ h) (ballDR R) w := by
    intro z hz
    change ‖h z‖ ≤ ‖h w‖
    exact hw_max z hz

  have h_eq := Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn h_preconnected h_open h_diff_cont hw_in_DR h_max_on

  intro z hz
  have norm_eq := h_eq hz
  simp only [Function.comp_apply, Function.const_apply] at norm_eq
                                                                                   
  convert (preTransparency := .instances) norm_eq

lemma lem_MaxModR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : norm (h R) = norm (h w) := by
                                                                
  have h_const : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) :=
    lem_MaxModP R hR h h_analytic w hw_in_DR hw_max
                                                      
  have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
                                         
  exact h_const (R : ℂ) hR_in_closure

lemma lem_MaxModRR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) :
∀ z ∈ closure (ballDR R), norm (h R) ≥ norm (h z) := by
  intro z hz
                                                                            
  have h1 := lem_MaxModP R hR h h_analytic w hw_in_DR hw_max z hz
                                             
  have h2 := lem_MaxModR R hR h h_analytic w hw_in_DR hw_max
                                                                             
  rw [h2, h1]

theorem lem_MaxModv2 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : closure (ballDR R), norm (v : ℂ) = R ∧ ∀ z : closure (ballDR R), norm (h (v : ℂ)) ≥ norm (h (z : ℂ)) := by
                                                       
  obtain ⟨u, hu⟩ := lem_ExtrValThmh hR h h_analytic

  if h_case : (u : ℂ) ∈ ballDR R then
                                 
    have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
    let v : closure (ballDR R) := ⟨R, hR_in_closure⟩
    use v
    constructor
    ·                
                                                                             
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                                               
      have : norm (R : ℂ) = abs R := by
        simp [Complex.norm_real]
      rw [this, lem_Rself R hR]
    ·                                                     
      intro z
                                                                        
      have hw_max : ∀ w ∈ ballDR R, norm (h w) ≤ norm (h (u : ℂ)) := by
        intro w hw
                                                      
        have hw_closure : w ∈ closure (ballDR R) := subset_closure hw
                                              
        let w_sub : closure (ballDR R) := ⟨w, hw_closure⟩
        exact hu w_sub
                                             
      have h_result := lem_MaxModRR R hR h h_analytic (u : ℂ) h_case hw_max
                                                  
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                           
      exact h_result (z : ℂ) (Subtype.mem z)
  else
                                 
    use u
    constructor
    ·                                   
      exact lem_circleDR R hR (u : ℂ) (Subtype.mem u) h_case
    ·                                                                  
      exact hu

theorem lem_MaxModv3 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : ℂ, norm v = R ∧ ∀ z : ℂ, z ∈ closure (ballDR R) → norm (h v) ≥ norm (h z) := by
                                                                                   
  obtain ⟨v_sub, hv_abs, hv_max⟩ := lem_MaxModv2 R hR h h_analytic
                                                           
  let v := (v_sub : ℂ)
  use v
  constructor
  ·                
    exact hv_abs
  ·                            
    intro z hz
                                               
    have hz_sub : z ∈ closure (ballDR R) := hz
    let z_sub : closure (ballDR R) := ⟨z, hz_sub⟩
    have := hv_max z_sub
                             
    simp at this
    exact this

lemma lem_MaxModv4 (R B : ℝ) (hR : R > 0) (_hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∃ v : ℂ, norm v = R ∧ (∀ w : ℂ, w ∈ closure (ballDR R) → norm (h v) ≥ norm (h w)) ∧ norm (h v) ≤ B := by
                                                                             
  obtain ⟨v, hv_abs, hv_max⟩ := lem_MaxModv3 R hR h h_analytic
                         
  use v
  constructor
  ·           
    exact hv_abs
  constructor
  ·                                                  
    exact hv_max
  ·                                                  
    apply h_boundary_bound
    exact hv_abs

lemma lem_HardMMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B := by
  intro w hw
                                                                                            
  obtain ⟨v, hv_abs, hv_max, hv_bound⟩ := lem_MaxModv4 R B hR hB h h_analytic h_boundary_bound
                                
  have h1 : norm (h w) ≤ norm (h v) := hv_max w hw
  have h2 : norm (h v) ≤ B := hv_bound
                             
  linarith [h1, h2]

lemma lem_EasyMMP (R B : ℝ) (hR : R > 0) (_hB : B ≥ 0)
  (h : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_closure_bound : ∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B) :
∀ z : ℂ, norm z = R → norm (h z) ≤ B := by
  intro z hz
                                                  
  apply h_closure_bound z
                                     
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  rw [Complex.dist_eq]
  simp

  have : ‖z‖ = R := hz
  linarith

theorem lem_MMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
(∀ z : ℂ, z ∈ closure (ballDR R) → norm (h z) ≤ B) ↔ (∀ z : ℂ, norm z = R → norm (h z) ≤ B) := by
  constructor
  ·                                                     
    intro h_closure_bound
    exact lem_EasyMMP R B hR hB h h_analytic h_closure_bound
  ·                                                      
    intro h_boundary_bound
    exact lem_HardMMP R B hR hB h h_analytic h_boundary_bound

lemma lem_denominator_nonzero (R M : ℝ) (_hR : R > 0) (hM : M > 0)
  (f : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
  (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → (2 * M - f z) ≠ 0 := by
  intro z hz
                                                  
  apply lem_real_part_lower_bound4 (f z) M hM
                                   
  exact h_re_bound z hz

lemma lem_f_vs_2M_minus_f (R M : ℝ) (_hR : R > 0) (hM : M > 0)
  (f : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
  (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → norm (f z) / norm (2 * M - f z) ≤ 1 := by
  intro z hz
                                                 
  apply lem_nonnegative_product9 M (f z) hM
                                   
  exact h_re_bound z hz

lemma lem_removable_singularity (R : ℝ) (hR : R > 0) (f : ℂ → ℂ)
  (h_analytic : AnalyticOn ℂ f (closure (ballDR R))) (h_zero : f 0 = 0) :
AnalyticOn ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) (closure (ballDR R)) := by
                                                                             
  rw [lem_ballDR R hR] at h_analytic ⊢

  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  apply lem_analAtOnOn hR g

  ·                                
                                                   
    exact lem_ordernatcast2 hR f h_zero h_analytic

  ·                                                         

    have f_on_closedball : AnalyticOn ℂ f (Metric.closedBall 0 R) := h_analytic
    have quotient_analytic : AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | ‖z‖ ≤ R ∧ z ≠ 0} :=
      lem_fzzTanal hR f f_on_closedball

    apply AnalyticOn.congr quotient_analytic
    intro z hz
                                                                 
    simp [g, if_neg hz.2]

lemma lem_quotient_analytic {R : ℝ} (_hR : R > 0) (h1 h2 : ℂ → ℂ)
  (h_analytic1 : AnalyticOn ℂ h1 (closure (ballDR R)))
  (h_analytic2 : AnalyticOn ℂ h2 (closure (ballDR R)))
  (h_nonzero : ∀ z ∈ closure (ballDR R), h2 z ≠ 0) :
AnalyticOn ℂ (fun z ↦ h1 z / h2 z) (closure (ballDR R)) := by
  exact AnalyticOn.div h_analytic1 h_analytic2 h_nonzero

noncomputable def f_M (R M : ℝ) (_hR : R > 0) (_hM : M > 0)
    (f : ℂ → ℂ)
    (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (_h_zero : f 0 = 0)
    (_h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
ℂ → ℂ := fun z ↦ (if z = 0 then (fderiv ℂ f 0) 1 else f z / z) / (2 * M - f z)

lemma lem_g_analytic (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
AnalyticOn ℂ (f_M R M hR hM f h_analytic h_zero h_re_bound) (closure (ballDR R)) := by
                                                          
  let h₁ : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z
                              
  let h₂ : ℂ → ℂ := fun z ↦ 2 * M - f z

  have h_eq : f_M R M hR hM f h_analytic h_zero h_re_bound = fun z ↦ h₁ z / h₂ z := by
    ext z
    unfold f_M h₁ h₂
    simp

  rw [h_eq]

  apply lem_quotient_analytic hR

  · exact lem_removable_singularity R hR f h_analytic h_zero

  · have h₂_analytic : AnalyticOn ℂ h₂ (closure (ballDR R)) := by
      unfold h₂
      apply AnalyticOn.sub
      · exact analyticOn_const
      · exact h_analytic
    exact h₂_analytic

  · intro z hz
    unfold h₂
    exact lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz

lemma lem_absab (a b : ℂ) (_hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
  exact IsAbsoluteValue.abv_div norm a b

lemma lem_g_on_boundaryz (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_in_closure : z ∈ closure (ballDR R)) (hz_nonzero : z ≠ 0) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
norm (f z / z) / norm (2 * M - f z) := by
                              
  unfold f_M
                                                                
  simp only [if_neg hz_nonzero]

  have h_nonzero : (2 * M - f z) ≠ 0 := lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz_in_closure
                    
  exact lem_absab (f z / z) (2 * M - f z) h_nonzero

lemma lem_fzzR (R : ℝ) (hR : R > 0) (z w : ℂ) (hz : norm z = R) : norm (w / z) = norm w / R := by
                          
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz
    simp at hz
    linarith [hz, hR]
                    
  rw [lem_absab w z hz_nonzero]
                               
  rw [hz]

lemma lem_g_on_boundary (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_on_boundary : norm z = R) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
(norm (f z) / R) / norm (2 * M - f z) := by
                                            
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz_on_boundary
    simp at hz_on_boundary
    linarith [hz_on_boundary, hR]

  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    convert (preTransparency := .instances) le_of_eq hz_on_boundary

  have h1 : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    norm (f z / z) / norm (2 * M - f z) :=
    lem_g_on_boundaryz R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure hz_nonzero

  have h2 : norm (f z / z) = norm (f z) / R :=
    lem_fzzR R hR z (f z) hz_on_boundary

  rw [h1, h2]

lemma lem_f_vs_2M_minus_fR (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (_h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_in_closure : z ∈ closure (ballDR R)) :
(norm (f z) / R) / norm (2 * M - f z) ≤ 1 / R := by
                                               
  have h1 : norm (f z) / norm (2 * M - f z) ≤ 1 :=
    lem_f_vs_2M_minus_f R M hR hM f h_analytic h_re_bound z hz_in_closure

  rw [div_div]

  rw [mul_comm R]

  rw [← div_div]

  exact div_le_div_of_nonneg_right h1 (le_of_lt hR)

lemma lem_g_boundary_bound0 (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_on_boundary : norm z = R) :
norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R := by
                                                          
  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    convert (preTransparency := .instances) le_of_eq hz_on_boundary

  rw [lem_g_on_boundary R M hR hM f h_analytic h_zero h_re_bound z hz_on_boundary]

  exact lem_f_vs_2M_minus_fR R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure

lemma lem_g_interior_bound (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R := by
                      
  have hB : (1 / R : ℝ) ≥ 0 := div_nonneg zero_le_one (le_of_lt hR)
                                          
  have h_g_analytic : AnalyticOn ℂ (f_M R M hR hM f h_analytic h_zero h_re_bound) (closure (ballDR R)) :=
    lem_g_analytic R M hR hM f h_analytic h_zero h_re_bound
                                                                       
  apply (lem_MMP R (1 / R) hR hB (f_M R M hR hM f h_analytic h_zero h_re_bound) h_g_analytic).mpr
                                                                
  intro z hz_boundary
  exact lem_g_boundary_bound0 R M hR hM f h_analytic h_zero h_re_bound z hz_boundary

lemma lem_g_at_r (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
(norm (f z) / r) / norm (2 * M - f z) := by
                                            
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz_on_boundary
    simp at hz_on_boundary
    linarith [hz_on_boundary, hr_pos]

  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h1 : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    norm (f z / z) / norm (2 * M - f z) :=
    lem_g_on_boundaryz R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure hz_nonzero

  have h2 : norm (f z / z) = norm (f z) / r :=
    lem_fzzR r hr_pos z (f z) hz_on_boundary

  rw [h1, h2]

lemma lem_g_at_rR (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
(norm (f z) / r) / norm (2 * M - f z) ≤ 1 / R := by
                                                       
  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h_bound : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R :=
    lem_g_interior_bound R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure

  have h_eq : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    (norm (f z) / r) / norm (2 * M - f z) :=
    lem_g_at_r R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  rw [← h_eq]
  exact h_bound

lemma lem_fracs (a b r R : ℝ) (ha : a > 0) (hb : b > 0) (hr : r > 0) (hR : R > 0)
(h_le : (a / r) / b ≤ 1 / R) : R * a ≤ r * b := by
                                              
  have h1 : (a / r) / b = a / (r * b) := by
    field_simp
  rw [h1] at h_le

  have h_pos_rb : 0 < r * b := mul_pos hr hb
  rw [div_le_div_iff₀ h_pos_rb hR] at h_le
                                      
  simp only [one_mul] at h_le

  linarith

lemma lem_nonneg_product_with_real_abs (r M : ℝ) (hr : r > 0) (hM : M > 0) : 0 ≤ r * (2 * |M|) := by
                                 
  have h_abs_eq : |M| = M := abs_of_pos hM
                                         
  rw [h_abs_eq]

  have h_two_M_pos : (2 : ℝ) * M > 0 := by
    apply mul_pos
    norm_num
    exact hM
                              
  apply mul_nonneg
  linarith [hr]
  linarith [h_two_M_pos]

lemma lem_f_bound_rearranged (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
R * norm (f z) ≤ r * norm (2 * M - f z) := by
                                     
  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h_ineq : (norm (f z) / r) / norm (2 * M - f z) ≤ 1 / R :=
    lem_g_at_rR R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  have h_denom_nonzero : (2 * M - f z) ≠ 0 :=
    lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz_in_closure

  have h_denom_pos : norm (2 * M - f z) > 0 :=
    lem_abspos (2 * M - f z) h_denom_nonzero

  by_cases h_case : f z = 0
  ·                                                      
    rw [h_case]
    simp [mul_zero]
    exact lem_nonneg_product_with_real_abs r M hr_pos hM
  ·                                    
    have h_num_pos : norm (f z) > 0 :=
      lem_abspos (f z) h_case

    exact lem_fracs (norm (f z)) (norm (2 * M - f z)) r R
           h_num_pos h_denom_pos hr_pos hR h_ineq

lemma lem_final_bound_on_circle0 (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
                                                                                     
  have h_ineq : R * norm (f z) ≤ r * norm (2 * M - f z) :=
    lem_f_bound_rearranged R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  have h_bound : norm (f z) ≤ (2 * M * r) / (R - r) :=
    lem_rtriangle7 r R M (f z) hr_pos hr_lt_R hM h_ineq

  have h_rearrange : (2 * M * r) / (R - r) = (2 * r / (R - r)) * M := by
    field_simp

  rw [← h_rearrange]
  exact h_bound

lemma lem_final_bound_on_circle (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
  exact lem_final_bound_on_circle0 R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

lemma lem_BCI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_in_ball : norm z ≤ r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
                                  
  let B := (2 * r / (R - r)) * M

  have hB : B ≥ 0 := by
    unfold B
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · linarith [hr_pos]
      · linarith [hr_lt_R]
    · linarith [hM]

  have h_analytic_r : AnalyticOn ℂ f (closure (ballDR r)) := by
    apply AnalyticOn.mono h_analytic
                                                   
    apply closure_mono
    unfold ballDR
    exact Metric.ball_subset_ball (le_of_lt hr_lt_R)

  have hz_in_closure_r : z ∈ closure (ballDR r) := by
    rw [lem_ballDR r hr_pos]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    exact hz_in_ball

  have h_boundary : ∀ w : ℂ, norm w = r → norm (f w) ≤ B := by
    intro w hw_boundary
    exact lem_final_bound_on_circle R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R w hw_boundary

  have h_closure := (lem_MMP r B hr_pos hB f h_analytic_r).mpr h_boundary

  exact h_closure z hz_in_closure_r

theorem thm_BorelCaratheodoryI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R) :
sSup ((norm ∘ f) '' (closure (ballDR r))) ≤ (2 * r / (R - r)) * M := by
                                                                                               
  apply Real.sSup_le
  ·                                                                                                      
    intro x hx

    obtain ⟨z, hz_in_closure, hx_eq⟩ := hx
    rw [← hx_eq]

    have hz_bound : norm z ≤ r := by
      rw [lem_ballDR r hr_pos] at hz_in_closure
      rw [Metric.mem_closedBall] at hz_in_closure
      rw [Complex.dist_eq] at hz_in_closure
      simp at hz_in_closure
      exact hz_in_closure
                    
    exact lem_BCI R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_bound
  ·                                       
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · linarith [hr_pos]
      · linarith [hr_lt_R]
    · linarith [hM]

lemma deriv_ofReal_eq_one (t : ℝ) : deriv Complex.ofReal t = 1 := by

  have h : deriv Complex.ofReal t = Complex.ofReal 1 := by

    rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
    exact ContinuousLinearMap.deriv Complex.ofRealCLM
                                       
  rw [h]
  simp only [Complex.ofReal_one]

lemma differentiableAt_ofReal (t : ℝ) : DifferentiableAt ℝ Complex.ofReal t := by
                                                                                
  rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
                                                                                    
  apply ContinuousLinearMap.differentiableAt

lemma one_div_two_pi_pos : (1 : ℝ) / (2 * Real.pi) > 0 := by
                            
  have h_pi_pos : Real.pi > 0 := Real.pi_pos
                        
  have h_2pi_pos : 2 * Real.pi > 0 := by
    apply mul_pos
    · norm_num
    · exact h_pi_pos
                              
  apply div_pos
  · norm_num
  · exact h_2pi_pos

lemma abs_integral_le_integral_abs {a b : ℝ} {g : ℝ → ℂ} (_hab : a ≤ b) : norm (∫ (t : ℝ) in Set.Icc a b, g t) ≤ ∫ (t : ℝ) in Set.Icc a b, norm (g t) := by

  exact MeasureTheory.norm_integral_le_integral_norm g

lemma complex_abs_mul (a b : ℂ) : norm (a * b) = norm a * norm b :=
  Complex.norm_mul a b

lemma complex_abs_ofReal_nonneg (r : ℝ) (hr : r ≥ 0) : norm (↑r : ℂ) = r := by
                                          
  have h1 : norm (↑r * 1) = r * norm (1 : ℂ) := by simp; assumption
                                         
  simp only [mul_one] at h1
  have h2 : norm (1 : ℂ) = 1 := by simp
  rw [h2] at h1
  simp only [mul_one] at h1
  simp
  assumption

lemma abs_one_div_two_pi_complex : norm (1 / (2 * ↑Real.pi : ℂ)) = 1 / (2 * Real.pi) := by
                                                                              
  have h_eq : (1 / (2 * ↑Real.pi) : ℂ) = ↑(1 / (2 * Real.pi) : ℝ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]

  rw [h_eq]

  have h_nonneg : (1 / (2 * Real.pi) : ℝ) ≥ 0 := by
    apply div_nonneg
    · norm_num
    · apply mul_nonneg
      · norm_num
      · exact le_of_lt Real.pi_pos

  exact complex_abs_ofReal_nonneg (1 / (2 * Real.pi)) h_nonneg

lemma lem_e01 : Real.exp 0 = 1 := by
  exact Real.exp_zero

lemma lem_modulus_wz (w z : ℂ) : norm ((w - z) ^ 2) = (norm (w - z)) ^ 2 := by
                                     
  exact Complex.norm_pow (w - z) 2

lemma lem_reverse_triangle (w z : ℂ) : norm w - norm z ≤ norm (w - z) := by

  exact norm_sub_norm_le w z

lemma lem_zrr1 {R_analytic r_z r_int : ℝ}
    (_h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
0 < r_int - norm z := by
                                                      
  have h1 : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
                                        
  have h2 : dist z 0 = ‖z‖ := by
    rw [dist_eq_norm, sub_zero]
                 
  have h3 : ‖z‖ ≤ r_z := by rwa [← h2]
                                      
  have h4 : norm z = ‖z‖ := rfl
                    
  have h5 : norm z ≤ r_z := by rwa [h4]
                                                     
  have h6 : norm z < r_int := lt_of_le_of_lt h5 h_r_z_lt_r_int
                                 
  linarith

lemma lem_wposneq0 (w : ℂ) : norm w > 0 → w ≠ 0 := by
  intro h
                                                  
  by_contra h_eq_zero
                              
  have h_abs_zero : norm w = 0 := by
    rw [h_eq_zero]
    simp
                                        
  rw [h_abs_zero] at h
  exact lt_irrefl 0 h

lemma lem_absdiv {a b : ℂ} (_hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
                                             
  exact norm_div a b

lemma lem_integral_inequality_aux {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in a..b, g t ≤ ∫ _t in a..b, C := by

  have h_const_integrable : IntervalIntegrable (fun _ => C) MeasureTheory.volume a b :=
    intervalIntegrable_const
                                                                             
  have h_pointwise : ∀ x ∈ Set.Icc a b, g x ≤ (fun _ => C) x := by
    intro x hx
    simp
    exact h_bound x hx
                                   
  exact intervalIntegral.integral_mono_on hab h_integrable h_const_integrable h_pointwise

lemma lem_integral_inequality {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in Set.Icc a b, g t ≤ ∫ _t in Set.Icc a b, C := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact lem_integral_inequality_aux hab h_integrable h_bound

lemma integral_const_over_interval (C : ℝ) :
∫ _t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
                                                                             
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
                                                                                     
  have h_le : (0 : ℝ) ≤ 2 * Real.pi := by
    apply mul_nonneg
    · norm_num
    · exact Real.pi_pos.le
  rw [← intervalIntegral.integral_of_le h_le]
                                                 
  rw [intervalIntegral.integral_const]
                                                        
  simp [sub_zero, smul_eq_mul]

lemma lem_r_prime_lt_R {r R : ℝ}
    (_h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(r + R) / 2 < R := by
                                                                  
  rw [add_div_two_lt_right]
  exact h_r_lt_R

lemma lem_r_prime_is_intermediate {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
r < (r + R) / 2 ∧ (r + R) / 2 < R := by
  constructor
  ·                         
    rw [left_lt_add_div_two]
    exact h_r_lt_R
  ·                         
    exact lem_r_prime_lt_R h_r_pos h_r_lt_R

lemma lem_calc_R_minus_r_prime {r R : ℝ}
    (_h_r_pos : 0 < r)
    (_h_r_lt_R : r < R) :
R - ((r + R) / 2) = (R - r) / 2 := by
  field_simp <;> ring

lemma lem_calc_denominator_specific {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(R - ((r + R) / 2)) * (((r + R) / 2) - r) ^ 2 = ((R - r) ^ 3) / 8 := by
                                                           
  rw [lem_calc_R_minus_r_prime h_r_pos h_r_lt_R]
                                              
  have h_calc : ((r + R) / 2) - r = (R - r) / 2 := by
    field_simp <;> ring
                                
  rw [h_calc]

  ring

lemma lem_calc_numerator_specific {M r R : ℝ}
    (_hM_pos : 0 < M)
    (_hr_pos : 0 < r)
    (_hr_lt_R : r < R) :
2 * (((r + R) / 2) ^ 2) * M = ((R + r) ^ 2 * M) / 2 := by
                                                  
  ring

lemma lem_frac_simplify {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (((R + r) ^ 2 * M) / 2) / (((R - r) ^ 3) / 8) := by
                                     
  dsimp only
                              
  have h_num := lem_calc_numerator_specific hM_pos hr_pos hr_lt_R
                                
  have h_denom := lem_calc_denominator_specific hr_pos hr_lt_R
                              
  rw [← h_num, ← h_denom]

lemma lem_frac_simplify2 {M r R : ℝ}
    (hM_pos : 0 < M)
    (_hr_pos : 0 < r)
    (hr_lt_R : r < R) :
((R + r) ^ 2 * M / 2) / ((R - r) ^ 3 / 8) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by

  have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
  have h_eight_ne_zero : (8 : ℝ) ≠ 0 := by norm_num
  have h_R_minus_r_ne_zero : R - r ≠ 0 := by linarith [hr_lt_R]
  have h_R_minus_r_pow_ne_zero : (R - r) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    exact h_R_minus_r_ne_zero

  field_simp [h_two_ne_zero, h_eight_ne_zero, h_R_minus_r_pow_ne_zero] <;> ring

lemma lem_frac_simplify3 {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by
                              
  dsimp only
                                                         
  have h1 := lem_frac_simplify hM_pos hr_pos hr_lt_R
                                                            
  have h2 := lem_frac_simplify2 hM_pos hr_pos hr_lt_R
                          
  rw [h1, h2]

lemma lem_ineq_R_plus_r_lt_2R {r R : ℝ} (h_r_lt_R : r < R) :
R + r < 2 * R := by
                           
  rw [two_mul]
                                                                
  linarith [h_r_lt_R]

lemma lem_R_plus_r_is_positive {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
0 < R + r := by
                                         
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
                                       
  exact add_pos hR_pos hr_pos

lemma lem_square_inequality_strict {a b : ℝ}
    (h_a_pos : 0 < a)
    (h_a_lt_b : a < b) :
a ^ 2 < b ^ 2 := by
                             
  have h_a_nonneg : 0 ≤ a := le_of_lt h_a_pos
                                                    
  have h_b_pos : 0 < b := lt_trans h_a_pos h_a_lt_b
  have h_b_nonneg : 0 ≤ b := le_of_lt h_b_pos
                                   
  have h_squares := mul_self_lt_mul_self_iff h_a_nonneg h_b_nonneg
                                                     
  have h_mult : a * a < b * b := h_squares.mp h_a_lt_b
                                                   
  rw [← pow_two, ← pow_two] at h_mult
  exact h_mult

lemma lem_2R_sq_is_4R_sq {R : ℝ} (_hR_pos : 0 < R) : (2 * R) ^ 2 = 4 * R ^ 2 := by
                                                  
  ring

lemma lem_ineq_R_plus_r_sq {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(R + r) ^ 2 < 4 * R ^ 2 := by
                      
  have h1 := lem_ineq_R_plus_r_lt_2R hr_lt_R
                  
  have h2 := lem_R_plus_r_is_positive hr_pos hr_lt_R
                                                                    
  have h3 := lem_square_inequality_strict h2 h1
                                                          
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
  have h4 := lem_2R_sq_is_4R_sq hR_pos
  rw [h4] at h3
  exact h3

lemma lem_ineq_R_plus_r_sqM {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
4 * (R + r) ^ 2 * M < 16 * R ^ 2 * M := by
                                                              
  have h_ineq := lem_ineq_R_plus_r_sq hr_pos hr_lt_R
                        
  have h_4M_pos : 0 < 4 * M := by
    apply mul_pos
    · norm_num
    · exact hM_pos
                                 
  have h_mult := mul_lt_mul_of_pos_right h_ineq h_4M_pos
                                      
  nlinarith [h_mult]

lemma lem_simplify_final_bound {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) < (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
                                                                
  have h_num_ineq := lem_ineq_R_plus_r_sqM hM_pos hr_pos hr_lt_R
                            
  have h_denom_pos : 0 < (R - r) ^ 3 := by
    apply pow_pos
    linarith [hr_lt_R]
                                
  exact div_lt_div_of_pos_right h_num_ineq h_denom_pos

lemma lem_bound_after_substitution {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
                           
  dsimp only
                                                      
  have h1 := lem_frac_simplify3 hM_pos hr_pos hr_lt_R
                                 
  dsimp only at h1
  rw [h1]
                                                            
  have h2 := lem_simplify_final_bound hM_pos hr_pos hr_lt_R
                                  
  exact le_of_lt h2

open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped Interval

lemma continuous_vertical_line (a : ℂ) :
  Continuous (fun τ : ℝ => ((a.re : ℂ) + Complex.I * (τ : ℂ))) := by
  have hconst : Continuous (fun _ : ℝ => (a.re : ℂ)) := continuous_const
  have hmul : Continuous (fun τ : ℝ => (Complex.I : ℂ) * (τ : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  convert (preTransparency := .instances) hconst.add hmul using 1
  all_goals try with_reducible_and_instances rfl

lemma norm_re_add_I_mul_le_norm (a : ℂ) {τ : ℝ} (hτ : |τ| ≤ |a.im|) :
  ‖((a.re : ℂ) + Complex.I * (τ : ℂ))‖ ≤ ‖a‖ := by
                                                                              
  set z1 : ℂ := ((a.re : ℂ) + Complex.I * (τ : ℂ)) with hz1
                                       
  have hsq_z1 : ‖z1‖ ^ 2 = z1.re ^ 2 + z1.im ^ 2 := by
    have hx : ‖z1‖ ^ 2 - z1.re ^ 2 = z1.im ^ 2 := Complex.sq_norm_sub_sq_re z1
    have hx' := congrArg (fun t : ℝ => t + z1.re ^ 2) hx
                                          
    have : ‖z1‖ ^ 2 = z1.im ^ 2 + z1.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
  have hsq_a : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    have hx : ‖a‖ ^ 2 - a.re ^ 2 = a.im ^ 2 := Complex.sq_norm_sub_sq_re a
    have hx' := congrArg (fun t : ℝ => t + a.re ^ 2) hx
    have : ‖a‖ ^ 2 = a.im ^ 2 + a.re ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [add_comm] using this
                             
  have hz1_re : z1.re = a.re := by
    simp [hz1, mul_comm]
  have hz1_im : z1.im = τ := by
    simp [hz1, mul_comm]
                                                  
  have hτ_sq : τ ^ 2 ≤ a.im ^ 2 := by
    simpa using (sq_le_sq.mpr hτ)
                    
  have hsq_le : ‖z1‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    have : a.re ^ 2 + τ ^ 2 ≤ a.re ^ 2 + a.im ^ 2 := add_le_add_right hτ_sq _
    simpa [hsq_z1, hz1_re, hz1_im, hsq_a] using this
                               
  have hnonneg : 0 ≤ ‖a‖ := norm_nonneg _
  exact le_of_sq_le_sq hsq_le hnonneg

lemma closedBall_mono_center0 {r1 R : ℝ} (h : r1 ≤ R) :
  Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
  intro z hz
  have hz' : dist z (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp hz)
  exact Metric.mem_closedBall.mpr (le_trans hz' h)

lemma abs_le_abs_of_mem_uIcc_zero {b t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) b) : |t| ≤ |b| := by
  classical
  by_cases hb : 0 ≤ b
  ·                                  
    have ht' : t ∈ Set.Icc (0 : ℝ) b := by
      simpa [Set.uIcc_of_le hb] using ht
    have ht0 : 0 ≤ t := ht'.1
    have htb : t ≤ b := ht'.2
    have htabs : |t| = t := abs_of_nonneg ht0
    have hbabs : |b| = b := abs_of_nonneg hb
    simpa [htabs, hbabs] using htb
  ·                                  
    have ht' : t ∈ Set.Icc b 0 := by
      simpa [Set.uIcc_of_not_le hb] using ht
    have hb_le : b ≤ 0 := le_trans ht'.1 ht'.2
    have ht_le0 : t ≤ 0 := ht'.2
    have hbabs : |b| = -b := abs_of_nonpos hb_le
    have htabs : |t| = -t := abs_of_nonpos ht_le0
    have hneg : -t ≤ -b := neg_le_neg ht'.1
    simpa [htabs, hbabs] using hneg

lemma vertical_intervalIntegrable_of_mem_ball
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {a : ℂ}
    (ha : a ∈ Metric.closedBall (0 : ℂ) r1) :
    IntervalIntegrable (fun τ : ℝ => f (((a.re : ℂ)) + Complex.I * τ)) volume (0 : ℝ) a.im := by
  classical
                                              
  have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
                                 
  let g : ℝ → ℂ := fun τ => ((a.re : ℂ) + Complex.I * (τ : ℂ))
                                                        
  have hg_cont : ContinuousOn g (Set.uIcc (0 : ℝ) a.im) := by
    simpa [g] using (continuous_vertical_line a).continuousOn
                                                                  
  have hg_maps : Set.MapsTo g (Set.uIcc (0 : ℝ) a.im) (Metric.closedBall (0 : ℂ) R) := by
    intro τ hτ
    have hτabs : |τ| ≤ |a.im| := abs_le_abs_of_mem_uIcc_zero hτ
    have hnorm_le_a : ‖g τ‖ ≤ ‖a‖ := by
      simpa [g] using norm_re_add_I_mul_le_norm a hτabs
    have ha_norm : ‖a‖ ≤ r1 := by
      have : dist a (0 : ℂ) ≤ r1 := (Metric.mem_closedBall.mp ha)
      simpa [dist_eq_norm] using this
    have hnorm_le_r1 : ‖g τ‖ ≤ r1 := le_trans hnorm_le_a ha_norm
    have hg_mem_r1 : g τ ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le_r1
    exact (closedBall_mono_center0 (le_of_lt hr1_lt_R)) hg_mem_r1
                                                                          
  have hcomp : ContinuousOn (fun τ : ℝ => f (g τ)) (Set.uIcc (0 : ℝ) a.im) := by
                                                      
    convert (preTransparency := .instances) (ContinuousOn.comp (hg := hf_cont) (hf := hg_cont) (h := hg_maps)) using 1; rfl
                                                           
  have hInt : IntervalIntegrable (fun τ : ℝ => f (g τ)) volume (0 : ℝ) a.im :=
    ContinuousOn.intervalIntegrable (u := fun τ : ℝ => f (g τ)) (a := 0) (b := a.im) hcomp
  simpa [g] using hInt

lemma helper_im_of_w (z h : ℂ) : (((((z + h).re : ℂ) + Complex.I * z.im)).im) = z.im := by
  simp [Complex.add_im]

lemma helper_mul_sub_complex (x y : ℂ) : Complex.I * x - Complex.I * y = Complex.I * (x - y) := by
  simp [mul_sub]

lemma helper_re_of_w (z h : ℂ) : (((((z + h).re : ℂ) + Complex.I * z.im)).re) = (z + h).re := by
  simp

lemma algebraic_rearrangement_four_terms (a b c d : ℂ) :
    a - b + c - d = 0 → c - d = b - a := by
  intro h

  calc c - d
    = (a - b + c - d) - (a - b) := by ring
    _ = 0 - (a - b) := by rw [h]
    _ = -(a - b) := by ring
    _ = b - a := by ring

lemma real_between_as_convex_combination (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ t = (1 - lam) * b₁ + lam * b₂ := by
                                                        
  cases' le_total b₁ b₂ with h₁ h₂
  case inl =>

    have ht : b₁ ≤ t ∧ t ≤ b₂ := by
      cases' h with h_left h_right
      · exact h_left
      ·                                                                           
        exact ⟨le_trans h₁ h_right.1, le_trans h_right.2 h₁⟩

    by_cases heq : b₁ = b₂
    ·                                              
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [heq] at ht ⊢
        have : t = b₂ := le_antisymm ht.2 ht.1
        rw [this]
        ring
    ·                            
      have hlt : b₁ < b₂ := lt_of_le_of_ne h₁ heq
      let lam := (t - b₁) / (b₂ - b₁)
      use lam
      constructor
      ·           
        apply div_nonneg
        · linarith [ht.1]
        · linarith [hlt]
      constructor
      ·                              
        rw [div_le_iff₀]
        · linarith [ht.2]                                         
        · linarith [hlt]                 
      ·                                 
        unfold lam
        have h_nonzero : b₂ - b₁ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero] <;> ring
  case inr =>

    have ht : b₂ ≤ t ∧ t ≤ b₁ := by
      cases' h with h_left h_right
      ·                                                                           
        exact ⟨le_trans h₂ h_left.1, le_trans h_left.2 h₂⟩
      · exact h_right

    by_cases heq : b₁ = b₂
    ·                                              
      use 0
      constructor
      · norm_num
      constructor
      · norm_num
      · rw [← heq] at ht ⊢
        have : t = b₁ := le_antisymm ht.2 ht.1
        rw [this, heq]
        ring
    ·                            
      have hlt : b₂ < b₁ := lt_of_le_of_ne h₂ (Ne.symm heq)
      let lam := (b₁ - t) / (b₁ - b₂)
      use lam
      constructor
      ·           
        apply div_nonneg
        · linarith [ht.2]                           
        · linarith [hlt]                 
      constructor
      ·                              
        rw [div_le_iff₀]
        · linarith [ht.1]                                         
        · linarith [hlt]                 
      ·                                 
        unfold lam
        have h_nonzero : b₁ - b₂ ≠ 0 := ne_of_gt (sub_pos.2 hlt)
        field_simp [h_nonzero] <;> ring

lemma convex_combination_mem_segment {E : Type*} [AddCommGroup E] [Module ℝ E] (x y : E) (t : ℝ)
  (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
  (1 - t) • x + t • y ∈ segment ℝ x y := by

  use (1 - t), t
  constructor
  ·             
    linarith [h₁]
  constructor
  ·         
    exact h₀
  constructor
  ·                   
    ring
  ·                                             
    rfl

lemma vertical_line_in_segment (a : ℂ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  a + Complex.I * t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
                                                
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h

  have h_convex : a + Complex.I * t = (1 - lam) • (a + Complex.I * b₁) + lam • (a + Complex.I * b₂) := by
                                           
    simp only [Complex.real_smul]
                                               
    rw [h_t_eq]
                                 
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
                                                                              
    rw [mul_add]
                                                      
    ring

  rw [h_convex]
  exact convex_combination_mem_segment (a + Complex.I * b₁) (a + Complex.I * b₂) lam h_lam_nonneg h_lam_le_one

lemma horizontal_line_in_segment (a : ℝ) (b₁ b₂ t : ℝ)
  (h : (b₁ ≤ t ∧ t ≤ b₂) ∨ (b₂ ≤ t ∧ t ≤ b₁)) :
  (t : ℂ) + Complex.I * a ∈ segment ℝ ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) := by
                                                     
  obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination b₁ b₂ t h
                                                                        
  have h_convex : (t : ℂ) + Complex.I * a
      = (1 - lam) • ((b₁ : ℂ) + Complex.I * a) + lam • ((b₂ : ℂ) + Complex.I * a) := by
    simp only [Complex.real_smul]
                   
    rw [h_t_eq]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
                                       
  simpa [h_convex] using
    (convex_combination_mem_segment ((b₁ : ℂ) + Complex.I * a) ((b₂ : ℂ) + Complex.I * a) lam h_lam_nonneg h_lam_le_one)

lemma intervalIntegrable_of_continuousOn_range (f : ℂ → ℂ) (g : ℝ → ℂ) (a b : ℝ) (S : Set ℂ)
  (hf : ContinuousOn f S) (hg : Continuous g)
  (hrange : ∀ t ∈ Set.uIcc a b, g t ∈ S) :
  IntervalIntegrable (f ∘ g) volume a b := by
                                                           
  have h_comp : ContinuousOn (f ∘ g) (Set.uIcc a b) := by
    apply ContinuousOn.comp hf (hg.continuousOn) hrange
                                                                     
  exact h_comp.intervalIntegrable

lemma intervalIntegrable_of_analyticOnNhd_of_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {a : ℂ} {b₁ b₂ : ℝ}
  (h₁ : ‖a + Complex.I * b₁‖ ≤ r1) (h₂ : ‖a + Complex.I * b₂‖ ≤ r1) :
  IntervalIntegrable (fun t => f (a + Complex.I * t)) volume b₁ b₂ := by
                                                                    
  apply intervalIntegrable_of_continuousOn_range f (fun t => a + Complex.I * ↑t) b₁ b₂ (Metric.closedBall (0 : ℂ) R)
  ·                                                                              
    exact AnalyticOnNhd.continuousOn hf
  ·                                               
    exact Continuous.add continuous_const (Continuous.mul continuous_const continuous_ofReal)
  ·                                                         
    intro t ht
                                                                       
    have h_in_r1 : ‖a + Complex.I * ↑t‖ ≤ r1 := by
                                                            
      have h_segment : a + Complex.I * ↑t ∈ segment ℝ (a + Complex.I * b₁) (a + Complex.I * b₂) := by
        apply vertical_line_in_segment
        exact Set.mem_uIcc.mp ht
                                                              
      have h₁_mem : a + Complex.I * b₁ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : a + Complex.I * b₂ ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
                                         
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
                                                              
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

lemma intervalIntegrable_of_analyticOnNhd_of_horizontal_endpoints_in_smaller_ball
  {r1 R : ℝ} (hr1_lt_R : r1 < R) {f : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {im_part : ℝ} {a b : ℝ}
  (h₁ : ‖(a : ℂ) + Complex.I * im_part‖ ≤ r1) (h₂ : ‖(b : ℂ) + Complex.I * im_part‖ ≤ r1) :
  IntervalIntegrable (fun t => f ((t : ℂ) + Complex.I * im_part)) volume a b := by
                                                                    
  apply intervalIntegrable_of_continuousOn_range f (fun t => (t : ℂ) + Complex.I * im_part) a b (Metric.closedBall (0 : ℂ) R)
  ·                                                                              
    exact AnalyticOnNhd.continuousOn hf
  ·                                                                     
    exact Continuous.add continuous_ofReal continuous_const
  ·                                                         
    intro t ht
                                                                       
    have h_in_r1 : ‖(t : ℂ) + Complex.I * im_part‖ ≤ r1 := by
                                                            
      have h_segment : (t : ℂ) + Complex.I * im_part ∈ segment ℝ ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) := by

        obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ := real_between_as_convex_combination a b t (Set.mem_uIcc.mp ht)

        have h_convex : (t : ℂ) + Complex.I * im_part = (1 - lam) • ((a : ℂ) + Complex.I * im_part) + lam • ((b : ℂ) + Complex.I * im_part) := by
                                                 
          simp only [Complex.real_smul]
                                                   
          rw [h_t_eq]
                                       
          simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
                                             
          ring

        rw [h_convex]
        exact convex_combination_mem_segment ((a : ℂ) + Complex.I * im_part) ((b : ℂ) + Complex.I * im_part) lam h_lam_nonneg h_lam_le_one

      have h₁_mem : (a : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
      have h₂_mem : (b : ℂ) + Complex.I * im_part ∈ Metric.closedBall (0 : ℂ) r1 := by
        rwa [Metric.mem_closedBall, dist_zero_right]
                                         
      have h_subset := (convex_closedBall (0 : ℂ) r1).segment_subset h₁_mem h₂_mem
      have h_in_ball := h_subset h_segment
      rwa [Metric.mem_closedBall, dist_zero_right] at h_in_ball
                                                              
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans h_in_r1 (le_of_lt hr1_lt_R)

lemma integral_of_constant_over_L_path
    {r1 R R0 : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (_hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (_hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (_hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1) :
    (∫ _t in z.re..(z + h).re, f z) + Complex.I * (∫ _τ in z.im..(z + h).im, f z)
      = f z * h := by
                                                           
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const]

  rw [Complex.add_re, Complex.add_im]
  simp only [add_sub_cancel_left]

  rw [Complex.real_smul, Complex.real_smul]

  rw [← mul_assoc]

  rw [← add_mul]

  rw [mul_comm Complex.I (↑h.im)]

  rw [Complex.re_add_im h]

  rw [mul_comm]

noncomputable def S_horiz (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
        r = ‖f (t + Complex.I * z.im) - f z‖}

noncomputable def S_vert (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
        r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}

noncomputable def S_max (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  max (S_horiz z h f) (S_vert z h f)

lemma S_horiz_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_horiz z h f := by
                                                         
  unfold S_horiz
  apply Real.sSup_nonneg
  intro r hr; rcases hr with ⟨t, ht, rfl⟩; exact norm_nonneg _

lemma S_max_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_max z h f := by
  unfold S_max
  have h1 : 0 ≤ S_horiz z h f := S_horiz_nonneg z h f
  exact le_trans h1 (le_max_left _ _)

open _root_.Filter Topology

lemma abs_horizontal_diff_eq_abs_real (z : ℂ) (t : ℝ) : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := by
                                                           
  have h : (t : ℂ) + Complex.I * z.im - z = (t - z.re : ℂ) := by
    apply Complex.ext_iff.mpr
    constructor
    ·                                      
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
                 Complex.I_re, Complex.I_im, Complex.ofReal_im]
      ring
    ·                                       
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
                 Complex.I_re, Complex.I_im, Complex.ofReal_re]
      ring

  rw [h]
                                                                         
  rw [← Complex.ofReal_sub]
                                                                             
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma abs_sub_le_of_mem_uIcc (a b t : ℝ) (ht : t ∈ Set.uIcc a b) : |t - a| ≤ |b - a| ∧ |b - t| ≤ |b - a| := by
                                                  
  have h1 : a ≤ b ∨ b ≤ a := le_total a b
  rcases h1 with hle | hle
  ·                             
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : a ≤ t ∧ t ≤ b := by simpa using ht'
    constructor
    · have h_ta : |t - a| = t - a := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.left)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_right h_bounds.right a
    · have h_bt : |b - t| = b - t := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.right)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_left h_bounds.left b
  ·                         
    have ht' : t ∈ Set.Icc b a := by
      rw [Set.uIcc_comm] at ht
      simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : b ≤ t ∧ t ≤ a := by simpa using ht'
    constructor
    · have h_ta : |t - a| = a - t := by simp [abs_of_nonpos (sub_nonpos.mpr h_bounds.right)]
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_left h_bounds.left a
    · have h_bt : |b - t| = t - b := by
        rw [abs_of_nonpos (sub_nonpos.mpr h_bounds.left)]
        ring
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_right h_bounds.right b

lemma abs_vertical_core (z h : ℂ) (τ : ℝ) : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| := by
                                                                           
  have h1 : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |((h.re : ℝ) + Complex.I * (τ - z.im)).re| + |((h.re : ℝ) + Complex.I * (τ - z.im)).im| := by
    apply Complex.norm_le_abs_re_add_abs_im

  have h2 : ((h.re : ℝ) + Complex.I * (τ - z.im)).re = h.re := by simp
  have h3 : ((h.re : ℝ) + Complex.I * (τ - z.im)).im = τ - z.im := by simp

  rw [h2, h3] at h1
  exact h1

lemma mem_closedBall_mono_radius {z : ℂ} {r R : ℝ} (hz : z ∈ Metric.closedBall (0 : ℂ) r) (h : r ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using le_trans (by simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz) h

lemma tendsto_of_nonneg_local_bound {g : ℂ → ℝ}
  (h_nonneg : ∀ h, 0 ≤ g h)
  (h_loc : ∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ < δ → g h ≤ ε) :
  Tendsto g (𝓝 (0:ℂ)) (𝓝 (0:ℝ)) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
                                                       
  have hε_half : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨δ, hδ_pos, hδ⟩ := h_loc (ε / 2) hε_half
  use δ
  exact ⟨hδ_pos, fun h hh_dist => by
    rw [Real.dist_eq, sub_zero]
    rw [abs_of_nonneg (h_nonneg h)]
    have : g h ≤ ε / 2 := hδ h (by rwa [Complex.dist_eq, sub_zero] at hh_dist)
    linarith⟩

lemma sum_abs_le_two_mul {x y A : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ A) : |x| + |y| ≤ (2:ℝ) * A := by
  have := add_le_add hx hy
  simpa [two_mul] using this

lemma two_norm_lt_of_norm_lt_half {h : ℂ} {δ : ℝ} (_hpos : 0 < δ) (hbound : ‖h‖ < δ/2) : (2:ℝ) * ‖h‖ < δ := by
  have := mul_lt_mul_of_pos_left hbound (by norm_num : (0:ℝ) < 2)
  simpa [two_mul, add_halves] using this

lemma limit_of_S_is_zero
    {r1 R R0 : ℝ}
  (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) := by
                                                                  
  have f_cont_at_z : ContinuousAt f z := by
                                                                     
    have hz_in_R : z ∈ Metric.closedBall (0 : ℂ) R :=
      mem_closedBall_mono_radius hz (le_of_lt hr1_lt_R)
                                        
    exact (hf z hz_in_R).continuousAt

  apply tendsto_of_nonneg_local_bound
  ·                                  
    exact fun h => S_max_nonneg z h f
  ·                                                                   
    intro ε hε_pos
                                        
    rw [Metric.continuousAt_iff] at f_cont_at_z
    obtain ⟨δ₁, hδ₁_pos, hf_bound⟩ := f_cont_at_z ε hε_pos

    use δ₁ / 2
    constructor
    · exact half_pos hδ₁_pos
    · intro h hh_norm

      unfold S_max
      apply max_le

      · unfold S_horiz
                                                 
        apply Real.sSup_le
        ·                                        
          intro r hr
          obtain ⟨t, ht, rfl⟩ := hr

          have key_dist : dist ((t : ℂ) + Complex.I * z.im) z < δ₁ := by
                                                                     
            rw [dist_eq]
                                                                         
            have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := abs_horizontal_diff_eq_abs_real z t
            simp [eq_transform]
                                                                
            have t_bound : |t - z.re| ≤ |(z + h).re - z.re| := (abs_sub_le_of_mem_uIcc z.re (z + h).re t ht).1
            have re_diff_le : |(z + h).re - z.re| ≤ ‖h‖ := by
                                       
              simpa [Complex.add_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (Complex.abs_re_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            calc |t - z.re|
              _ ≤ |(z + h).re - z.re| := t_bound
              _ ≤ ‖h‖ := re_diff_le
              _ < δ₁ / 2 := h_bound
              _ < δ₁ := by linarith
                                              
          have f_dist := hf_bound key_dist
                                                         
          rw [dist_eq] at f_dist
                                 
          exact le_of_lt f_dist
        ·              
          exact le_of_lt hε_pos

      · unfold S_vert
        apply Real.sSup_le
        ·                                        
          intro r hr
          obtain ⟨τ, hτ, rfl⟩ := hr
                                                    
          have key_dist : dist (((z + h).re : ℂ) + Complex.I * τ) z < δ₁ := by
            rw [dist_eq]

            have h_eq : (((z + h).re : ℂ) + Complex.I * τ - z) = (h.re : ℝ) + Complex.I * (τ - z.im) := by
              apply Complex.ext_iff.mpr
              constructor
              · simp [Complex.add_re, Complex.sub_re]
              · simp [Complex.add_im, Complex.sub_im]
            rw [h_eq]
                                                             
            have τ_bound0 : |τ - z.im| ≤ |(z + h).im - z.im| := (abs_sub_le_of_mem_uIcc z.im (z + h).im τ hτ).1
            have im_diff_eq : |(z + h).im - z.im| = |h.im| := by
              simp [Complex.add_im, sub_eq_add_neg, add_assoc]
            have τ_bound : |τ - z.im| ≤ |h.im| := by simpa [im_diff_eq] using τ_bound0
                                                                 
            have vertical_bound : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| :=
              abs_vertical_core z h τ
            have sum_bound : |h.re| + |τ - z.im| ≤ |h.re| + |h.im| := by
              exact add_le_add_right τ_bound _
            have norm_bound := sum_abs_le_two_mul (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            have final_bound := two_norm_lt_of_norm_lt_half hδ₁_pos h_bound
            calc ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖
              _ ≤ |h.re| + |τ - z.im| := vertical_bound
              _ ≤ |h.re| + |h.im| := sum_bound
              _ ≤ (2 : ℝ) * ‖h‖ := norm_bound
              _ < δ₁ := final_bound
                                              
          have f_dist := hf_bound key_dist
          rw [dist_eq] at f_dist
                                 
          exact le_of_lt f_dist
        ·              
          exact le_of_lt hε_pos

lemma eventually_corner_and_sum_in_closedBall {z : ℂ} {R' : ℝ}
  (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    (z + h) ∈ Metric.closedBall (0 : ℂ) R' ∧
    (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) R' := by
                         
  have hρ_pos : 0 < R' - ‖z‖ := sub_pos.mpr hz
  have h_small : ∀ᶠ h in 𝓝 (0:ℂ), h ∈ Metric.ball (0 : ℂ) (R' - ‖z‖) :=
    Metric.ball_mem_nhds (0 : ℂ) hρ_pos
  refine h_small.mono ?_
  intro h hhball
  have hnorm_lt : ‖h‖ < R' - ‖z‖ := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hhball
                                              
  have hsum_lt : ‖z‖ + ‖h‖ < R' := by
    have htemp : ‖z‖ + ‖h‖ < ‖z‖ + (R' - ‖z‖) := add_lt_add_right hnorm_lt _
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htemp
  have hzph_le : ‖z + h‖ ≤ R' :=
    le_of_lt (lt_of_le_of_lt (norm_add_le _ _) hsum_lt)
  have hzph_mem : (z + h) ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hzph_le
                                                                       
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
                                                           
  have tri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    have := norm_add_le (w - z) z
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
                                                            
  let t : ℝ := (z + h).re
  have hwz_eq : w - z = (t : ℂ) + Complex.I * z.im - z := by
    simp [w, t, sub_eq_add_neg, add_assoc]
  have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| :=
    abs_horizontal_diff_eq_abs_real z t
  have t_sub_re : t - z.re = h.re := by
    simp [t, Complex.add_re, sub_eq_add_neg, add_assoc]
  have hwz_abs2 : ‖w - z‖ = |h.re| := by
    simpa [hwz_eq, t_sub_re] using eq_transform
  have hwz_le : ‖w - z‖ ≤ ‖h‖ := by
    simpa [hwz_abs2] using (Complex.abs_re_le_norm h)
  have hw_le'' : ‖w‖ ≤ ‖h‖ + ‖z‖ := by
    exact le_trans tri (add_le_add_left hwz_le _)
  have hw_lt : ‖w‖ < R' := by
    have : ‖h‖ + ‖z‖ < R' := by simpa [add_comm] using hsum_lt
    exact lt_of_le_of_lt hw_le'' this
  have hw_mem : w ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [w, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using (le_of_lt hw_lt)
  exact And.intro hzph_mem hw_mem

open Classical

lemma hasDerivWithinAt_congr_eqOn {f g : ℂ → ℂ} {s : Set ℂ} {z f' : ℂ}
  (hEq : Set.EqOn f g s) (hz : z ∈ s) :
  HasDerivWithinAt g f' s z → HasDerivWithinAt f f' s z := by
  intro hg
  have hfg : ∀ x ∈ s, f x = g x := fun x hx => hEq hx
  simpa using (HasDerivWithinAt.congr_of_mem (h := hg) (hs := hfg) (hx := hz))

lemma differentiableOn_of_hasDerivWithinAt {f : ℂ → ℂ} {s : Set ℂ} {F : ℂ → ℂ}
  (h : ∀ z ∈ s, HasDerivWithinAt f (F z) s z) : DifferentiableOn ℂ f s := by
  intro z hz
  exact (h z hz).differentiableWithinAt

lemma hasDerivAt_of_local_decomposition' (g : ℂ → ℂ) (z F : ℂ)
  (Err_func : ℂ → ℂ)
  (hdecomp : ∀ᶠ h in 𝓝 (0:ℂ), g (z + h) - g z = F * h + Err_func h)
  (hErr : Tendsto (fun h => Err_func h / h) (𝓝 (0:ℂ)) (𝓝 (0:ℂ))) :
  HasDerivAt g F z := by
                                                             
  have hdecomp_within : ∀ᶠ h in 𝓝[≠] (0:ℂ), g (z + h) - g z = F * h + Err_func h :=
    (hdecomp.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ)))
                                                                 
  have h_ne0 : ∀ᶠ h in 𝓝[≠] (0:ℂ), h ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℂ)) (s := ({0}ᶜ : Set ℂ))] with h hh
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh
                                                   
  have h_eq_slope : ∀ᶠ h in 𝓝[≠] (0:ℂ),
      h⁻¹ • (g (z + h) - g z) = F + Err_func h / h := by
    refine (hdecomp_within.and h_ne0).mono ?_
    intro h hh
    rcases hh with ⟨hEq, hne⟩
                                                   
    have H0 : h⁻¹ • (g (z + h) - g z) = h⁻¹ • (F * h + Err_func h) := by
      simpa using congrArg (fun x => h⁻¹ • x) hEq
                                     
    have h1 : h⁻¹ * (F * h) = F := by
      have hne' : h ≠ 0 := hne
      calc
        h⁻¹ * (F * h) = F * (h⁻¹ * h) := by
          ac_rfl
        _ = F * 1 := by simp [hne']
        _ = F := by simp
    have h2 : h⁻¹ * Err_func h = Err_func h / h := by
      simp [div_eq_mul_inv, mul_comm]
    calc
      h⁻¹ • (g (z + h) - g z)
          = h⁻¹ • (F * h + Err_func h) := H0
      _ = h⁻¹ * (F * h + Err_func h) := by simp [smul_eq_mul]
      _ = h⁻¹ * (F * h) + h⁻¹ * (Err_func h) := by simp [mul_add]
      _ = F + Err_func h / h := by simp [h1, h2]
                                        
  have hErr_within : Tendsto (fun h => Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) :=
    hErr.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
  have h_const : Tendsto (fun _ : ℂ => F) (𝓝[≠] (0:ℂ)) (𝓝 F) := tendsto_const_nhds
  have h_sum : Tendsto (fun h => F + Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (F + 0)) :=
    h_const.add hErr_within
  have h_target : Tendsto (fun h => h⁻¹ • (g (z + h) - g z)) (𝓝[≠] (0:ℂ)) (𝓝 F) := by
    have := (Filter.tendsto_congr' h_eq_slope).2 h_sum
    simpa [zero_add] using this
                                                             
  exact (hasDerivAt_iff_tendsto_slope_zero).2 h_target

lemma uniqueDiffWithinAt_convex_complex {s : Set ℂ} (hconv : Convex ℝ s)
    (hs : (interior s).Nonempty) {x : ℂ} (hx : x ∈ closure s) :
    UniqueDiffWithinAt ℂ s x := by
                                                                   
  have hR : UniqueDiffWithinAt ℝ s x :=
    uniqueDiffWithinAt_convex (E := ℂ) (conv := hconv) (hs := hs) (x := x) (hx := hx)
                                                       
  have dR : Dense ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ) := by
    simpa using (hR.dense_tangentConeAt)
                                                                  
  have h_tc_subset : tangentConeAt ℝ s x ⊆ tangentConeAt ℂ s x :=
    tangentConeAt_mono_field
                                                                             
  set TC : Set ℂ := tangentConeAt ℂ s x
  set Sℂ : Submodule ℂ ℂ := Submodule.span ℂ TC
  set Sℝ : Submodule ℝ ℂ := Sℂ.restrictScalars ℝ
  have h_span_le : (Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) ≤ Sℝ := by
                                                   
    refine Submodule.span_le.mpr ?_
    intro v hv
    have hv' : v ∈ TC := h_tc_subset hv
    have : v ∈ Sℂ := Submodule.subset_span hv'
    simpa [Sℝ] using this
                                                                            
  have hsubset_sets :
      ((Submodule.span ℝ (tangentConeAt ℝ s x) : Submodule ℝ ℂ) : Set ℂ)
        ⊆ ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := by
    intro z hz
    have hz' : z ∈ Sℝ := h_span_le hz
    simpa [Sℝ] using hz'
  have dC : Dense ((Sℂ : Submodule ℂ ℂ) : Set ℂ) := dR.mono hsubset_sets
                                 
  exact ⟨dC, hx⟩

lemma interior_closedBall_nonempty_of_pos {R : ℝ} (hR_pos : 0 < R) :
    (interior (Metric.closedBall (0 : ℂ) R)).Nonempty := by
                                                               
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hR_pos
                                                                  
  have hsub : Metric.ball (0 : ℂ) R ⊆ interior (Metric.closedBall (0 : ℂ) R) :=
    Metric.ball_subset_interior_closedBall
                                   
  exact ⟨0, hsub h0mem⟩

lemma mem_closure_of_mem_closedBall {R : ℝ} {z : ℂ}
  (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  z ∈ closure (Metric.closedBall (0 : ℂ) R) := by
  exact subset_closure hz

lemma uniqueDiffWithinAt_closedBall_complex_of_mem {R : ℝ} {z : ℂ}
  (hR_pos : 0 < R) (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
  UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) R) z :=
by
                              
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) R) :=
    convex_closedBall (0 : ℂ) R
                                         
  have hnonempty : (interior (Metric.closedBall (0 : ℂ) R)).Nonempty :=
    interior_closedBall_nonempty_of_pos (R := R) hR_pos
                                                
  have hz_cl : z ∈ closure (Metric.closedBall (0 : ℂ) R) :=
    mem_closure_of_mem_closedBall (R := R) (z := z) hz
                                              
  exact uniqueDiffWithinAt_convex_complex hconv hnonempty hz_cl

open scoped Topology

lemma modulus_of_exp_I
    {r1 R' R : ℝ}
    (_hr1_pos : 0 < r1) (_hr1_lt_R' : r1 < R') (_hR'_lt_R : R' < R) (_hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (_hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (_hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (_hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (_hJ_zero : J 0 = 0)
    (_hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (Complex.exp (J z)) = Real.exp (Complex.re (J z)) := by
  intro z hz
  exact Complex.norm_exp (J z)

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT2_LogDerivative
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


lemma lem_bolzano_weierstrass {D : Set ℂ} (hD : IsCompact D) {Z : Set ℂ} (hZ_inf : Z.Infinite) (hZ_sub_D : Z ⊆ D) :
    ∃ ρ₀ ∈ D, AccPt ρ₀ (Filter.principal Z) :=
  Set.Infinite.exists_accPt_of_subset_isCompact hZ_inf hD hZ_sub_D

open _root_.Filter Metric _root_.Set Bornology _root_.Function

lemma lem_identity_theorem (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
                                                 
  have h_subset : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall
                                                        
  have hf_open : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := AnalyticOnNhd.mono hf h_subset
                                                         
  have h_conn : IsConnected (Metric.ball (0 : ℂ) 1) := Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) := h_conn.isPreconnected
                                                     
  have h_zeros_subset : {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} ⊆ {z | f z = 0} := by
    intro z hz
    exact hz.2
                                                                                           
  have h_acc_zero : AccPt ρ₀ (Filter.principal ({z | f z = 0})) := by
    exact AccPt.mono h_acc (principal_mono.2 h_zeros_subset)
                                                                                                  
  have h_closure : ρ₀ ∈ closure ({z | f z = 0} \ {ρ₀}) := by
                                                                                
    have h_cluster : ClusterPt ρ₀ (Filter.principal ({z | f z = 0} \ {ρ₀})) :=
      (accPt_principal_iff_clusterPt).mp h_acc_zero
    exact (mem_closure_iff_clusterPt).2 h_cluster
                               
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hf_open h_preconn hρ₀_in_D1 h_closure

open Classical

lemma lem_mod_pos_iff_ne_zero (z : ℂ) : z ≠ 0 → norm z > 0 :=
  lem_abspos z

lemma lem_inv_mono_decr (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : 1 / x ≥ 1 / y := by
                                   
  have hy : 0 < y := lt_of_lt_of_le hx hxy
                                                       
  exact one_div_le_one_div_of_le hx hxy

theorem lem_mod_of_prod2 {ι : Type*} (K : Finset ι) (w : ι → ℂ) :
    ‖∏ ρ ∈ K, w ρ‖ = ∏ ρ ∈ K, ‖w ρ‖ := by
  classical
  refine Finset.induction_on K ?h0 ?hstep
  · simp
  · intro a s ha ih
                                                       
    simp [Finset.prod_insert ha, ih]

lemma lem_abs_pow (w : ℂ) (n : ℕ) : ‖w ^ n‖ = ‖w‖ ^ n := by
  simp

lemma lem_mod_div_ (w1 w2 : ℂ) (_hw2_ne_zero : w2 ≠ 0) : ‖w1 / w2‖ = ‖w1‖ / ‖w2‖ := by
  simp

lemma lem_mod_div_and_neg (R : ℝ) (hR_pos : 0 < R) (ρ : ℂ) (h_rho_ne_zero : ρ ≠ 0) :
  ‖(R : ℂ) / (-ρ)‖ = R / ‖ρ‖ := by
                                                              
  have hden : (-ρ) ≠ 0 := by simpa using neg_ne_zero.mpr h_rho_ne_zero
  have hdiv := lem_mod_div_ (R : ℂ) (-ρ) hden
  calc
    ‖(R : ℂ) / (-ρ)‖ = ‖(R : ℂ)‖ / ‖-ρ‖ := hdiv
    _ = ‖(R : ℂ)‖ / ‖ρ‖ := by simp [norm_neg]
    _ = |R| / ‖ρ‖ := by simp
    _ = R / ‖ρ‖ := by simp [abs_of_pos hR_pos]

lemma lem_prod_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
    (h_nonneg : ∀ ρ ∈ K, 0 ≤ a ρ) (h_le : ∀ ρ ∈ K, a ρ ≤ b ρ) :
    ∏ ρ ∈ K, a ρ ≤ ∏ ρ ∈ K, b ρ := by
  exact Finset.prod_le_prod h_nonneg h_le

lemma complex_mul_star_eq_norm_sq (z : ℂ) : z * star z = (‖z‖ ^ 2 : ℂ) := by
                                                      
  rw [Complex.star_def]
                                                    
  exact Complex.mul_conj' z

lemma mem_closedBall_of_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  have : dist z (0 : ℂ) ≤ R := by simpa [Complex.dist_eq, sub_zero] using hz
  simpa [Metric.closedBall] using this

lemma closure_ball_eq_closedBall_center (R : ℝ) (hR : 0 < R) :
  closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := by
  simpa using (closure_ball (x := (0 : ℂ)) (r := R) (ne_of_gt hR))

lemma lem_max_mod_principle_for_Bf (B R : ℝ) (hB : 1 < B) (hR_pos : 0 < R)
    (fB : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ fB (Metric.closedBall (0 : ℂ) R))
  (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R → ‖fB z‖ ≤ B) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖fB z‖ ≤ B := by
  intro z hz
                               
  have hB0 : 0 ≤ B := le_of_lt (lt_trans zero_lt_one hB)
                                                                 
  have h_an_on_closure : AnalyticOn ℂ fB (closure (ballDR R)) := by
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using h_analytic.analyticOn
                                                                        
  have h_le :=
    lem_HardMMP R B hR_pos hB0 fB h_an_on_closure (by
      intro z hzR; exact h_bd_boundary z hzR)
                                                                                 
  have hz_cl : z ∈ closure (ballDR R) := by
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_of_norm_le hz
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using hz_closed
  exact h_le z hz_cl

lemma lem_log_mono_inc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy

lemma lem_three_gt_e : (3 : ℝ) > Real.exp 1 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
  exact lt_trans h1 h2

variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)

lemma logDerivconst {a : ℂ} {g : ℂ → ℂ} (ha : a ≠ 0) :
    ∀ z, logDeriv (fun w ↦ a * g w) z = logDeriv g z := by
  intro z
  exact logDeriv_const_mul z a ha

lemma deriv_over_fun_is_logDeriv {g : ℂ → ℂ} : ∀ z, deriv g z / g z = logDeriv g z := by
  intro z
  rfl

lemma logDerivmul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hf_ne : f z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ f w * g w) z = logDeriv f z + logDeriv g z := by
  exact logDeriv_mul z hf_ne hg_ne hf hg

lemma logDerivprod {K : Finset ℂ} {g : ℂ → ℂ → ℂ} {z : ℂ}
    (hg_diff : ∀ ρ ∈ K, DifferentiableAt ℂ (g ρ) z)
    (hg_ne : ∀ ρ ∈ K, g ρ z ≠ 0) :
    logDeriv (fun w ↦ ∏ ρ ∈ K, g ρ w) z = ∑ ρ ∈ K, logDeriv (g ρ) z := by
  simpa only [Finset.prod_fn] using logDeriv_prod hg_ne hg_diff

lemma logDerivdiv {h g : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (hg : DifferentiableAt ℂ g z)
    (hh_ne : h z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ h w / g w) z = logDeriv h z - logDeriv g z := by
  exact logDeriv_div z hh_ne hg_ne hh hg

lemma logDerivfunpow {g : ℂ → ℂ} {z : ℂ} {m : ℕ}
    (hg : DifferentiableAt ℂ g z) :
    logDeriv (fun w ↦ (g w) ^ m) z = m * logDeriv g z := by
  exact logDeriv_fun_pow hg m

lemma div_mul_eq_mul_mul_inv_fun {α} (f A B : α → ℂ) :
  (fun w => (f w / A w) * B w) = (fun w => f w * (B w * (A w)⁻¹)) := by
  funext w
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

lemma prod_num_mul_inv_den_eq_prod_ratio_fun_mem
  (K : Finset ℂ) (N D : ℂ → ℂ → ℂ) (m : ℂ → ℕ) :
  (fun w ↦ (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹)
  = (fun w ↦ ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ))) := by
  funext w
  classical
  calc
    (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) / (∏ ρ ∈ K, (D ρ w) ^ (m ρ)) := by
          simp [div_eq_mul_inv]
    _ = ∏ ρ ∈ K, ((N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ)) := by
          simp
    _ = ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ)) := by
          refine Finset.prod_congr rfl ?_
          intro ρ hρ
          have hpow_div :
              (N ρ w / D ρ w) ^ (m ρ)
                = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
            calc
              (N ρ w / D ρ w) ^ (m ρ)
                  = (N ρ w * (D ρ w)⁻¹) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
              _ = (N ρ w) ^ (m ρ) * ((D ρ w)⁻¹) ^ (m ρ) := by
                        simpa using (mul_pow (N ρ w) ((D ρ w)⁻¹) (m ρ))
              _ = (N ρ w) ^ (m ρ) * ((D ρ w) ^ (m ρ))⁻¹ := by
                        simp
              _ = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
          simpa using hpow_div.symm

lemma logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
  (hfg : f =ᶠ[nhds z] g) : logDeriv f z = logDeriv g z := by
                                                                                         
  have hval : f z = g z := Filter.EventuallyEq.eq_of_nhds hfg
  have hderiv_eq_ev : deriv f =ᶠ[nhds z] deriv g := hfg.deriv
  have hderiv : deriv f z = deriv g z := Filter.EventuallyEq.eq_of_nhds hderiv_eq_ev
                                                      
  have hf := deriv_over_fun_is_logDeriv (g := f) z
  have hg := deriv_over_fun_is_logDeriv (g := g) z
  simp [hf.symm, hg.symm, hval, hderiv]

lemma logDeriv_def_as_frac {f : ℂ → ℂ} {z : ℂ}
    (_hf : DifferentiableAt ℂ f z) (_hf_ne : f z ≠ 0) :
    logDeriv f z = deriv f z / f z := by
  simp [logDeriv]

theorem ball_containment {r R1 : ℝ} (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (z : ℂ) (hz : z ∈ Metric.closedBall 0 r) : z ∈ Metric.closedBall 0 R1 := by
  simp at *
  exact le_trans hz (le_of_lt hr_lt_R1)

lemma logDeriv_linear {a b : ℂ} {z : ℂ} (_ha : a ≠ 0) (_hz : z ≠ -b/a) :
    logDeriv (fun w ↦ a * w + b) z = a / (a * z + b) := by
                                 
  have h_id : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id _
  have h_mul' : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa [one_mul] using (h_id.const_mul a)
  have h_deriv_mul : deriv (fun w : ℂ => a * w) z = a := h_mul'.deriv
                                
  simp [logDeriv]

lemma logDeriv_denominator {ρ : ℂ} {z : ℂ} (hz : z ≠ ρ) :
    logDeriv (fun w ↦ w - ρ) z = 1 / (z - ρ) := by
  have h :=
    logDeriv_linear (a := (1 : ℂ)) (b := -ρ) (z := z)
      (_ha := by simp)
      (_hz := by simpa using hz)
  simpa [one_mul, sub_eq_add_neg] using h

lemma logDeriv_numerator_pre {R : ℝ} {ρ : ℂ} {z : ℂ} :
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = -(star ρ) / R / (R - (star ρ) * z / R) := by
  classical
                                                  
  let a : ℂ := -(star ρ) / (R : ℂ)
  let b : ℂ := (R : ℂ)
  have hlin : (fun w : ℂ ↦ (R : ℂ) - (star ρ) * w / (R : ℂ)) = (fun w : ℂ ↦ b + a * w) := by
    funext w
                         
    simp [a, b, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm]
                                        
  have hderiv_add : deriv (fun w : ℂ => b + a * w) z =
      deriv (fun _ : ℂ => b) z + deriv (fun y : ℂ => a * y) z := by
    simp
  have hderiv_ab : deriv (fun w : ℂ => b + a * w) z = a := by
    simp [deriv_const, mul_comm]
                                                            
  simp [logDeriv, sub_eq_add_neg, div_eq_mul_inv,
         mul_comm, mul_left_comm, mul_assoc, add_comm]

lemma star_ne_zero_of_ne_zero {ρ : ℂ} (hρ : ρ ≠ 0) : star ρ ≠ 0 := by

  intro h
                                          
  have : ρ = 0 := (star_eq_zero).1 h
  exact hρ this

lemma field_identity_general {K : Type*} [Field K] {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (_hden : a - c*b/a ≠ 0) : (-(b/a)) / (a - c*b/a) = (1 : K) / (c - a^2/b) := by
                                               
  have hmul : (-(a / b) : K) ≠ 0 := by
    have hdiv_ne : a / b ≠ 0 := div_ne_zero ha hb
    exact neg_ne_zero.mpr hdiv_ne
  have hnum : (-(b/a) * (-(a/b))) = (1 : K) := by
    calc
      (-(b/a) * (-(a/b))) = (b/a) * (a/b) := by simp
      _ = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have hOne : (b/a) * (a/b) = (1 : K) := by
    calc
      (b/a) * (a/b) = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have haab : a * (a / b) = a^2 / b := by
    simp [div_eq_mul_inv, pow_two, mul_assoc]
  have hcbab : (c * b / a) * (a / b) = c := by
    calc
      (c * b / a) * (a / b) = (c * (b / a)) * (a / b) := by simp [div_eq_mul_inv, mul_assoc]
      _ = c * ((b / a) * (a / b)) := by simp [mul_assoc]
      _ = c * 1 := by simp [hOne]
      _ = c := by simp
  have hdenom : ((a - c*b/a) * (-(a/b))) = c - a^2 / b := by
    calc
      ((a - c*b/a) * (-(a/b))) = -((a - c*b/a) * (a / b)) := by simp [mul_neg]
      _ = -(a * (a / b) - (c * b / a) * (a / b)) := by simp [sub_mul]
      _ = (c * b / a) * (a / b) - a * (a / b) := by simp [neg_sub]
      _ = c - a^2 / b := by simp [hcbab, haab]
  calc
    (-(b/a)) / (a - c*b/a)
        = (-(b/a) * (-(a/b))) / ((a - c*b/a) * (-(a/b))) := by
          simpa using
            (mul_div_mul_right (a := (-(b / a))) (b := (a - c * b / a)) (c := (-(a / b))) hmul).symm
    _ = 1 / ((a - c*b/a) * (-(a/b))) := by simp [hnum]
    _ = 1 / (c - a^2/b) := by simp [hdenom]

lemma complex_identity_from_field {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hρ : ρ ≠ 0) (hden : (R:ℂ) - (star ρ) * z / R ≠ 0) : (-(star ρ) / (R:ℂ)) / ((R:ℂ) - (star ρ) * z / R) = (1 : ℂ) / (z - (R:ℂ)^2 / (star ρ)) := by
  have ha : (R : ℂ) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr hR)
  have hb : star ρ ≠ 0 := star_ne_zero_of_ne_zero hρ
  have hden' : (R : ℂ) - z * (star ρ) / (R : ℂ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hden
  have h := field_identity_general (K := ℂ) (a := (R : ℂ)) (b := star ρ) (c := z) ha hb hden'
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h

lemma logDeriv_numerator_rearranged {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hrho : ρ ≠ 0) (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0) : -(star ρ) / R / ((R : ℂ) - (star ρ) * z / R) = 1 / (z - (R : ℂ)^2 / (star ρ)) := by
  simpa using (complex_identity_from_field (R:=R) (ρ:=ρ) (z:=z) (hR:=hR) (hρ:=hrho) (hden:=h_denom_ne_zero))

lemma logDeriv_numerator {R : ℝ} {ρ : ℂ} {z : ℂ}
    (hR : R ≠ 0)
    (hrho : ρ ≠ 0)
    (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0):
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = 1 / (z - R^2 / (star ρ)) := by
  rw [logDeriv_numerator_pre, logDeriv_numerator_rearranged]
  <;> assumption

lemma norm_div_eq (a b : ℂ) (_hb : b ≠ 0) : ‖a / b‖ = ‖a‖ / ‖b‖ := by
  calc
    ‖a / b‖ = ‖a * b⁻¹‖ := by simp [div_eq_mul_inv]
    _ = ‖a‖ * ‖b⁻¹‖ := norm_mul _ _
    _ = ‖a‖ * ‖b‖⁻¹ := by simp [norm_inv]
    _ = ‖a‖ / ‖b‖ := by simp [div_eq_mul_inv]

lemma norm_Rsq_div_conj (R : ℝ) (ρ : ℂ) (hρ : ρ ≠ 0) : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ := by
  have hb : star ρ ≠ 0 := by
    intro h
    have h' := congrArg star h
                                     
    have : ρ = 0 := by simpa [star_star] using h'
    exact hρ this
  have hnormR : ‖(R^2 : ℂ)‖ = (R^2 : ℝ) := by
    have h := (RCLike.norm_ofReal (K:=ℂ) (R^2))
    simp
  calc
    ‖((R^2 : ℂ) / (star ρ))‖
        = ‖(R^2 : ℂ)‖ / ‖star ρ‖ := norm_div_eq _ _ hb
    _ = (R^2 : ℝ) / ‖ρ‖ := by
      simp [hnormR]

lemma norm_sub_ge_norm_sub (x y : ℂ) : ‖x - y‖ ≥ ‖y‖ - ‖x‖ := by
  have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_add_le (y - x) x
  have h' : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := (sub_le_iff_le_add).mpr htri
  have hsymm : ‖y - x‖ = ‖x - y‖ := by
    simpa [sub_eq_add_neg, add_comm] using (norm_neg (x - y))
  simpa [hsymm] using h'

lemma sq_div_sub_pos (a b : ℝ) (ha_pos : 0 < a) (hab : a < b) : 0 < b^2/a - a := by
                                        
  rw [sub_pos]
                                                        
  rw [lt_div_iff₀ ha_pos]
                         
  rw [← pow_two]
                                                                         
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  apply pow_lt_pow_left₀ hab ha_nonneg
  norm_num

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT3_RiemannZeta
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open scoped BigOperators Topology
abbrev ℙ := Nat.Primes

lemma p_s_abs_1 (p : ℙ) (s : ℂ) (hs : 1 < s.re) : norm (((p : ℕ) : ℂ) ^ (-s : ℂ)) < 1 := by
                        
  have hx1 : 1 < ((p : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
      exact_mod_cast (p.2.two_le : 2 ≤ (p : ℕ))
    exact lt_of_lt_of_le one_lt_two h2
  have hx0 : 0 < ((p : ℕ) : ℝ) := lt_trans zero_lt_one hx1
                                                                  
  have hnorm_eq : ‖(((p : ℕ) : ℂ) ^ (-s : ℂ))‖ = ((p : ℕ) : ℝ) ^ ((-s : ℂ).re) := by
    simpa using (Complex.norm_cpow_eq_rpow_re_of_pos hx0 (-s : ℂ))
                                                
  have hz : ((-s : ℂ).re) < 0 := by
    have h0 : 0 < s.re := lt_trans zero_lt_one hs
    have : -s.re < 0 := neg_lt_zero.mpr h0
    simpa using this
                                                           
  have hlt : ((p : ℕ) : ℝ) ^ ((-s : ℂ).re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hx1 hz
                                                   
  have : ‖(((p : ℕ) : ℂ) ^ (-s : ℂ))‖ < 1 := by simpa [hnorm_eq] using hlt
  simpa [norm] using this

lemma zetaEulerprod (s : ℂ) (hs : 1 < s.re) : Multipliable (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) ∧ riemannZeta s = ∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹ := by
  have hprod : HasProd (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) (riemannZeta s) := by
    simpa using (riemannZeta_eulerProduct_hasProd (s := s) hs)
  refine And.intro ?_ ?_
  · exact hprod.multipliable
  · simpa using (hprod.tprod_eq.symm)

lemma abs_of_tprod {P : Type*} (w : P → ℂ) (hw : Multipliable w) : norm (∏' p : P, w p) = ∏' p : P, norm (w p) := by exact Multipliable.norm_tprod hw

lemma abs_P_prod (s : ℂ) (hs : 1 < s.re) : norm (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) = ∏' p : ℙ, norm ((1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have hw : Multipliable (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := (zetaEulerprod s hs).1
  simpa using abs_of_tprod (fun p : ℙ => (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) hw

lemma abs_zeta_prod (s : ℂ) (hs : 1 < s.re) : norm (riemannZeta s) = ∏' p : ℙ, norm ((1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  rw [zetaEulerprod s hs |>.2, abs_P_prod s hs]

lemma abs_of_inv (z : ℂ) (_hz : z ≠ 0) : norm (z⁻¹) = (norm z)⁻¹ := norm_inv z

lemma one_minus_p_s_neq_0 (p : ℙ) (s : ℂ) (hs : 1 < s.re) : 1 - ((p : ℕ) : ℂ) ^ (-s : ℂ) ≠ 0 := by
  intro h
  have hz : ((p : ℕ) : ℂ) ^ (-s : ℂ) = 1 := by
    simpa using (sub_eq_zero.mp h).symm
  have : (1 : ℝ) < 1 := by
    simpa [hz] using (p_s_abs_1 p s hs)
  exact (lt_irrefl (1 : ℝ)) this

lemma abs_zeta_prod_prime (s : ℂ) (hs : 1 < s.re) :
  norm (riemannZeta s) = ∏' p : ℙ, (norm (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)))⁻¹ := by
  rw [abs_zeta_prod s hs]
  congr 1
  ext p
  rw [abs_of_inv (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ)) (one_minus_p_s_neq_0 p s hs)]

lemma Re2s (s : ℂ) : (2 * s).re = 2 * s.re := by simp

lemma Re2sge1 (s : ℂ) (hs : 1 < s.re) : 1 < (2 * s).re := by
  rw [Re2s]
  linarith

lemma zeta_ratio_prod (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹) / (∏' p : ℙ, (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have h2 := (zetaEulerprod (2 * s) (Re2sge1 s hs)).2
  have h1 := (zetaEulerprod s hs).2
  simp [h2, h1]

local notation "ι" => fun (z : ℂˣ) ↦ (z : ℂ)

theorem tprod_commutes_with_inclusion_infinite {α : Type*} (f : α → ℂˣ) (h : Multipliable f) :
    ι (tprod f) = tprod (fun i ↦ ι (f i)) :=
by
  change ((tprod f : ℂˣ) : ℂ) = tprod (fun i ↦ ((f i : ℂˣ) : ℂ))
  have hcont : Continuous (Units.coeHom ℂ) := by
    simpa using! (Units.continuous_val : Continuous (fun u : ℂˣ => ((u : ℂˣ) : ℂ)))
  simpa [Units.coeHom] using
    (Multipliable.map_tprod (f := f) (γ := ℂ) h (g := Units.coeHom ℂ) hcont)

theorem inclusion_commutes_with_division (a b : ℂˣ) :
    ι (a / b) = ι a / ι b := by
  exact Units.val_div_eq_div_val a b

lemma lift_multipliable_of_nonzero {P : Type*} (a : P → ℂ) (ha : Multipliable a) (h_a_nonzero : ∀ p, a p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0):
  Multipliable (fun p ↦ Units.mk0 (a p) (h_a_nonzero p)) := by

  obtain ⟨A, hA⟩ := ha
  have hA_nonzero := hA_nonzero' A hA
  refine ⟨Units.mk0 A hA_nonzero, ?_⟩
  simp [HasProd, tendsto_nhds] at hA ⊢
  intro sU h_sU_open hA_mem
  have hA_im_mem : ι (Units.mk0 A hA_nonzero) ∈ ι '' sU := Set.mem_image_of_mem ι hA_mem
  have sU_im_open : IsOpen (ι '' sU) := by
    apply (Topology.IsOpenEmbedding.isOpen_iff_image_isOpen ?_).mp
    assumption
    exact Units.isOpenEmbedding_val
  have := hA (ι '' sU) sU_im_open hA_im_mem
  obtain ⟨a1, ha⟩ := this
  use a1
  intro b ha1
  obtain ⟨x', x'_spec_mem, x'_spec_eq⟩ := ha b ha1
  suffices x' = ∏ b ∈ b, Units.mk0 (a b) (by simp [*]) by
    rwa [← this]
  have : Units.mk0 (ι x') (Units.ne_zero x') = x' :=
    Units.mk0_val x' (Units.ne_zero x')
  have this2 : (Units.mk0 (∏ b ∈ b, a b)
    (Finset.prod_ne_zero_iff.mpr fun a a_1 => h_a_nonzero a)) = x' :=
      Units.ext (id (Eq.symm x'_spec_eq))
  rw [Units.mk0_prod] at this2
  rw [←this2]
  conv =>
    rhs
    rw [← Finset.prod_attach]

lemma prod_of_ratios_simplified {P : Type*} (a b : P → ℂ)
(ha : Multipliable a) (hb : Multipliable b)
    (h_a_nonzero : ∀ p, a p ≠ 0) (h_b_nonzero : ∀ p, b p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) (hB_nonzero' : ∀ A, HasProd b A → A ≠ 0):
  (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
                                                                      
  let a' : P → ℂˣ := fun p ↦ Units.mk0 (a p) (h_a_nonzero p)
  let b' : P → ℂˣ := fun p ↦ Units.mk0 (b p) (h_b_nonzero p)

  have h_multipliable_a' : Multipliable a' := lift_multipliable_of_nonzero a ha h_a_nonzero hA_nonzero'
  have h_multipliable_b' : Multipliable b' := lift_multipliable_of_nonzero b hb h_b_nonzero hB_nonzero'
  have h_multipliable_a'_div_b' : Multipliable (fun p ↦ a' p / b' p) := Multipliable.div h_multipliable_a' h_multipliable_b'

  calc
    (∏' p, a p) / (∏' p, b p)
                                                         
    _ = (∏' p, ι (a' p)) / (∏' p, ι (b' p)) := by simp [a', b']
                                                                             
    _ = ι (∏' p, a' p) / ι (∏' p, b' p) := by simp [tprod_commutes_with_inclusion_infinite, *]
                                                              
    _ = ι ((∏' p, a' p) / (∏' p, b' p)) := by rw [← inclusion_commutes_with_division]
                                                                                                        
    _ = ι (∏' p, a' p / b' p) := by simp [Multipliable.tprod_div, *]
                                                                           
    _ = ∏' p, ι (a' p / b' p) := by simp [tprod_commutes_with_inclusion_infinite, *]
                                                                                   
    _ = ∏' p, (ι (a' p) / ι (b' p)) := by simp
                                                                         
    _ = ∏' p, a p / b p := by simp [a', b']

lemma prod_of_ratios {P : Type*} (a b : P → ℂ) (ha : Multipliable a) (hb : Multipliable b) (h_b_nonzero : ∀ p, b p ≠ 0) (hA_nonzero' : ∀ A, HasProd a A → A ≠ 0) (hB_nonzero' : ∀ B, HasProd b B → B ≠ 0):
  (∏' p : P, a p) / (∏' p : P, b p) = ∏' p : P, (a p / b p) := by
                                                         
  by_cases h_a_zero : ∃ p, a p = 0
  case pos =>

    have lhs_zero : ∏' p : P, a p = 0 := by
                                                                      
      exact tprod_of_exists_eq_zero h_a_zero
    have rhs_zero : ∏' p : P, (a p / b p) = 0 := by
                                                        
      obtain ⟨p₀, hp₀⟩ := h_a_zero
      have h_div_zero : ∃ p, (a p / b p) = 0 := by
        use p₀
        simp [hp₀]
      exact tprod_of_exists_eq_zero h_div_zero
    simp [lhs_zero, rhs_zero]
  case neg =>
                                  
    push Not at h_a_zero
                                                                          
    exact prod_of_ratios_simplified a b ha hb h_a_zero h_b_nonzero hA_nonzero' hB_nonzero'

lemma simplify_prod_ratio (s : ℂ) (hs : 1 < s.re) : (∏' p : ℙ, (1 - (p : ℂ) ^ (-(2 * s) : ℂ))⁻¹) / (∏' p : ℙ, (1 - (p : ℂ) ^ (-s : ℂ))⁻¹) = ∏' p : ℙ, ((1 - (p : ℂ) ^ (-(2 * s) : ℂ))⁻¹ / (1 - (p : ℂ) ^ (-s : ℂ))⁻¹) := by
                                                                                   
  let a := fun p : ℙ => (1 - (p : ℂ) ^ (-(2 * s) : ℂ))⁻¹
  let b := fun p : ℙ => (1 - (p : ℂ) ^ (-s : ℂ))⁻¹

  have ha : Multipliable a := (zetaEulerprod (2 * s) (Re2sge1 s hs)).1
  have hb : Multipliable b := (zetaEulerprod s hs).1

  have h_b_nonzero : ∀ p, b p ≠ 0 := by
    intro p
    exact inv_ne_zero (one_minus_p_s_neq_0 p s hs)

  exact prod_of_ratios a b ha hb h_b_nonzero (by
    intro A hA
                                 
    have h_eq : A = riemannZeta (2 * s) := by
      have h : HasProd a (riemannZeta (2 * s)) := by
        simpa [a] using riemannZeta_eulerProduct_hasProd (s := 2 * s) (by simp <;> linarith)
      exact HasProd.unique hA h
    rw [h_eq]
    exact riemannZeta_ne_zero_of_one_lt_re (by simp <;> linarith)
  ) (by
  intro B hB
                                      
  have h_eq : B = riemannZeta s := by
    have h : HasProd b (riemannZeta s) := by
      simpa [b] using riemannZeta_eulerProduct_hasProd (s := s) hs
    exact HasProd.unique hB h
  rw [h_eq]
  exact riemannZeta_ne_zero_of_one_lt_re hs
  )

lemma zeta_ratios (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = ∏' p : ℙ, ((1 - ((p : ℕ) : ℂ) ^ (-(2 * s) : ℂ))⁻¹ / (1 - ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹) := by
  have h1 := zeta_ratio_prod s hs
  have h2 := simplify_prod_ratio s hs
  exact h1.trans h2

lemma diff_of_squares (z : ℂ) : 1 - z^2 = (1 - z) * (1 + z) := by ring

lemma one_sub_ne_zero_of_abs_lt_one (z : ℂ) (hz : norm z < 1) : 1 - z ≠ 0 := by
  intro h
  have h1 : 1 = z := by
    have := congrArg (fun w : ℂ => w + z) h
    simpa [sub_add_cancel, zero_add] using this
  have habs1lt : norm (1 : ℂ) < 1 := by simpa [h1] using hz
  have hnorm1lt : ‖(1 : ℂ)‖ < 1 := by simp [norm] at habs1lt
  have : (1 : ℝ) < 1 := by simp [norm_one] at hnorm1lt
  exact (lt_irrefl _) this

lemma inv_mul_div_cancel_right_of_ne_zero (a b : ℂ) (ha : a ≠ 0) : ((a * b)⁻¹) / a⁻¹ = b⁻¹ := by
  simp [div_eq_mul_inv, inv_inv, mul_inv_rev, mul_comm, ha]

lemma ratio_invs (z : ℂ) (hz : norm z < 1) : (1 - z^2)⁻¹ / (1 - z)⁻¹ = (1 + z)⁻¹ := by
  have hz1 : 1 - z ≠ 0 := one_sub_ne_zero_of_abs_lt_one z hz
  simpa [diff_of_squares z] using
    inv_mul_div_cancel_right_of_ne_zero (1 - z) (1 + z) hz1

lemma complex_cpow_neg_two_mul (z w : ℂ) (_hz : z ≠ 0) : z^(-(2*w)) = (z^(-w))^2 := by
  have h1 : -(2*w) = 2*(-w) := by ring
  rw [h1]
  have h2 : (2 : ℂ)*(-w) = ((2 : ℕ) : ℂ)*(-w) := by norm_cast
  rw [h2, Complex.cpow_nat_mul]

theorem zeta_ratio_identity (s : ℂ) (hs : 1 < s.re) : riemannZeta (2 * s) / riemannZeta s = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-s : ℂ))⁻¹ := by
  rw [zeta_ratios s hs]; congr 1; ext p
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by rw [ne_eq, Nat.cast_eq_zero]; exact Nat.Prime.ne_zero p.2
  have h1 : ((p : ℕ) : ℂ) ^ (-(2 * s)) = (((p : ℕ) : ℂ) ^ (-s))^2 := complex_cpow_neg_two_mul ((p : ℕ) : ℂ) s hp
  have h2 : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := p_s_abs_1 p s hs
  rw [h1]; exact ratio_invs (((p : ℕ) : ℂ) ^ (-s)) h2

lemma two_mul_ofReal_div_two (r : ℝ) : (2 : ℂ) * ((r : ℝ) / 2 : ℂ) = (r : ℂ) := by
  have hreal : (2 : ℝ) * (r / 2) = r := by
    calc
      (2 : ℝ) * (r / 2) = (2 : ℝ) * r / 2 := by
        have h : (2 : ℝ) * r / 2 = (2 : ℝ) * (r / 2) := by
          simpa using (mul_div_assoc (2 : ℝ) r (2 : ℝ))
        simpa using h.symm
      _ = r := by
        simp
  calc
    (2 : ℂ) * ((r : ℝ) / 2 : ℂ)
        = ((2 * (r / 2) : ℝ) : ℂ) := by
              simp
    _ = (r : ℂ) := by simp [hreal]

lemma zeta_ratio_identity_ofReal_div_two (r : ℝ) (hr : 1 < ( ((r : ℝ) / 2 : ℂ) ).re) : riemannZeta (r : ℂ) / riemannZeta ((r / 2 : ℝ) : ℂ) = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-(((r : ℝ) / 2) : ℂ)))⁻¹ := by
  have h := zeta_ratio_identity (((r : ℝ) / 2 : ℂ)) hr
  simpa [two_mul_ofReal_div_two r] using h

lemma zeta_ratio_at_3_2 : riemannZeta 3 / riemannZeta ((3 : ℝ) / 2) = ∏' p : ℙ, (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹ := by
  have hr : 1 < (((3 : ℝ) / 2 : ℂ)).re := by
    simpa using (by norm_num : (1 : ℝ) < (3 : ℝ) / 2)
  simpa using zeta_ratio_identity_ofReal_div_two (3 : ℝ) hr

lemma triangle_inequality_specific (z : ℂ) : norm (1 - z) ≤ 1 + norm z := by
  simpa [sub_eq_add_neg, norm_one, norm_neg] using (norm_add_le (1 : ℂ) (-z))

lemma re_neg_eq_neg_re (s : ℂ) : (-s).re = - s.re := by
  simp

lemma abs_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : norm ((x : ℂ) ^ y) = x ^ y.re := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hx y

lemma abs_p_pow_s (p : ℙ) (s : ℂ) : norm (((p : ℕ) : ℂ) ^ (-s : ℂ)) = ((p : ℕ) : ℝ) ^ (-s.re : ℝ) := by
  have hx : 0 < ((p : ℕ) : ℝ) := by
    exact_mod_cast (p.property.pos : 0 < (p : ℕ))
  simpa [Complex.ofReal_natCast, re_neg_eq_neg_re] using
    (abs_cpow_eq_rpow_re_of_pos hx (-s))

lemma abs_term_bound (p : ℙ) (t : ℝ) :
  norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) ≤ 1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by
                                                              
  have h1 := triangle_inequality_specific (((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)))
                                                                                    
  have h2 := abs_p_pow_s p (((3 : ℝ) / 2) + t * Complex.I)
                                  
  have h3 : (((3 : ℝ) / 2) + t * Complex.I).re = ((3 : ℝ) / 2) := by simp [Complex.add_re, Complex.ofReal_re]
                                    
  have h4 : -(((3 : ℝ) / 2) + t * Complex.I).re = -((3 : ℝ) / 2) := by rw [h3]
                       
  have h5 : norm (((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))) = ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by
    rw [h2, h4]
                
  rw [h5] at h1
  exact h1

lemma inv_inequality {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  simpa [one_div] using (one_div_le_one_div_of_le ha hab)

lemma eq_of_one_sub_eq_zero (z : ℂ) (h : 1 - z = 0) : z = 1 := by
  rw [sub_eq_zero] at h
  exact h.symm

lemma condp32 (p : ℙ) (t : ℝ) : 1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) ≠ 0 := by
  intro h
  have hp_eq_one : ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) = 1 := eq_of_one_sub_eq_zero _ h
  let s := ((3 : ℝ) / 2) + t * Complex.I
  have hs : 1 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero]
    norm_num
  have h_abs_lt : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := p_s_abs_1 p s hs
  have h_s_eq : ((p : ℕ) : ℂ) ^ (-s) = ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I)) := by simp only [s]
  rw [h_s_eq, hp_eq_one] at h_abs_lt
  have : norm (1 : ℂ) = 1 := by simp [norm]
  rw [this] at h_abs_lt
  exact lt_irrefl 1 h_abs_lt

lemma abs_term_inv_bound (p : ℙ) (t : ℝ) : (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ ≤ (norm (1 - ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) + t * Complex.I))))⁻¹ := by
  have h1 := abs_term_bound p t
  have h2 := condp32 p t
  have h3 := lem_abspos _ h2
  exact inv_inequality h3 h1

open NNReal in
lemma prod_inequality {P : Type*} (a b : P → ℝ≥0) (ha : Multipliable a) (hb : Multipliable b)
  (hab : ∀ p : P, a p ≤ b p) :
  ∏' p : P, a p ≤ ∏' p : P, b p := by
  exact Multipliable.tprod_le_tprod hab ha hb

lemma multipliable_complex_abs_inv {i : Type*} (g : i → ℂ) (h_mult : Multipliable (fun i => (1 - g i)⁻¹)) (_h_nonzero : ∀ i, 1 - g i ≠ 0) : Multipliable (fun i => (norm (1 - g i))⁻¹) := by
                                                       
  have h_eq : (fun i => (norm (1 - g i))⁻¹) = (fun i => ‖1 - g i‖⁻¹) := by
    ext i
    simp
  rw [h_eq]
                                       
  have h_norm_mult : Multipliable (fun i => ‖(1 - g i)⁻¹‖) := Multipliable.norm h_mult
  have h_norm_eq : (fun i => ‖(1 - g i)⁻¹‖) = (fun i => ‖1 - g i‖⁻¹) := by
    ext i
    rw [norm_inv]
  rwa [← h_norm_eq]

lemma multipliable_positive_inv_powers (r : ℝ) (hr : 1 < r) : Multipliable (fun p : ℙ => (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹) := by
                                                                   
  have h_sum : Summable (fun p : ℙ => ((p : ℕ) : ℝ) ^ (-r)) := by
    rw [Nat.Primes.summable_rpow]
    linarith

  have h_log_sum : Summable (fun p : ℙ => Real.log (1 + ((p : ℕ) : ℝ) ^ (-r))) := by
    exact Real.summable_log_one_add_of_summable h_sum

  have h_log_inv_sum : Summable (fun p : ℙ => Real.log ((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹)) := by
    have h_eq : (fun p : ℙ => Real.log ((1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹)) =
                (fun p : ℙ => -(Real.log (1 + ((p : ℕ) : ℝ) ^ (-r)))) := by
      ext p
      rw [Real.log_inv]
    rw [h_eq]
    exact Summable.neg h_log_sum

  have h_pos : ∀ p : ℙ, 0 < (1 + ((p : ℕ) : ℝ) ^ (-r))⁻¹ := by
    intro p
    apply inv_pos.mpr
    have h_ge : 0 ≤ ((p : ℕ) : ℝ) ^ (-r) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith

  exact Real.multipliable_of_summable_log h_pos h_log_inv_sum

lemma hasProd_nonneg_of_pos {i : Type*} (f : i → ℝ) (hpos : ∀ i, 0 < f i) (a : ℝ) (ha : HasProd f a) : 0 ≤ a := by
                                     
  have h_pos : ∀ s : Finset i, 0 < ∏ i ∈ s, f i := fun s => Finset.prod_pos (fun i _ => hpos i)
                                                         
  have h_nonneg : ∀ s : Finset i, 0 ≤ ∏ i ∈ s, f i := fun s => le_of_lt (h_pos s)
                                                 
  exact ge_of_tendsto ha (Filter.Eventually.of_forall h_nonneg)

lemma nnreal_coe_tprod_eq_tprod_coe {i : Type*} (f : i → NNReal) (hf : Multipliable f) :
  ∏' i, (↑(f i) : ℝ) = ↑(∏' i, f i) := by
                                                                  
  have h_prod : HasProd f (∏' i, f i) := Multipliable.hasProd hf
                                                                               
  have h_map : HasProd (NNReal.toRealHom ∘ f) (NNReal.toRealHom (∏' i, f i)) :=
    HasProd.map h_prod NNReal.toRealHom NNReal.continuous_coe
                                                                                                     
  have h_comp : NNReal.toRealHom ∘ f = fun i => (↑(f i) : ℝ) := by
    ext i
    rfl
  have h_val : NNReal.toRealHom (∏' i, f i) = ↑(∏' i, f i) := rfl
                              
  rw [h_comp, h_val] at h_map
                                             
  exact HasProd.tprod_eq h_map

lemma nnreal_tprod_le_coe {i : Type*} (f g : i → NNReal) (hf : Multipliable f) (hg : Multipliable g) (h : ∏' i, f i ≤ ∏' i, g i) : ∏' i, (f i : ℝ) ≤ ∏' i, (g i : ℝ) := by
                                                               
  rw [nnreal_coe_tprod_eq_tprod_coe f hf, nnreal_coe_tprod_eq_tprod_coe g hg]
                                                                                               
  exact NNReal.coe_le_coe.mpr h

lemma abs_zeta_ratio_eval : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := by
                                                 
  have hratio := zeta_ratio_at_3_2
                                          
  let w : ℙ → ℂ := fun p => (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹
  let u : ℙ → ℝ := fun p => (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹
                                        
  have hu_mult : Multipliable u :=
    multipliable_positive_inv_powers ((3 : ℝ) / 2) (by norm_num : 1 < (3 : ℝ) / 2)
                                        
  have hw_eq : w = fun p : ℙ => (u p : ℂ) := by
    funext p
                                                                               
    have hx : 0 ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (p : ℕ))
    have hcpow : (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ)
        = ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)) := by
      simpa using (Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (hx := hx) (y := -((3 : ℝ) / 2)))
    calc
      w p = (1 + ((p : ℕ) : ℂ) ^ (-(((3 : ℝ) / 2) : ℂ)))⁻¹ := rfl
      _ = (1 + (((((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2))) : ℝ) : ℂ))⁻¹ := by
        simp [hcpow]
      _ = (((1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ : ℝ) : ℂ) := by
        simp [Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one]
                                                                 
  have hw_mult : Multipliable w := by
    have hmap : Multipliable ((fun x : ℝ => (x : ℂ)) ∘ u) :=
      Multipliable.map (hf := hu_mult) Complex.ofRealHom Complex.continuous_ofReal
    simpa [hw_eq] using! hmap
                                            
  have h_abs_tprod : norm (∏' p : ℙ, w p) = ∏' p : ℙ, norm (w p) :=
    abs_of_tprod w hw_mult
                                                               
  have h_abs_eq_fun : (fun p : ℙ => norm (w p)) = u := by
    funext p
              
    have hge : 0 ≤ ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) :=
      Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (p : ℕ))) _
    have hpos : 0 < 1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)) := by linarith
    have hnonneg : 0 ≤ u p := by
      have : 0 < (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := inv_pos.mpr hpos
      exact this.le
               
    simp [hw_eq, Complex.norm_real, abs_of_nonneg hnonneg]
                                                        
  have h_abs_ratio : norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
      = norm (∏' p : ℙ, w p) := by
    simpa [w] using congrArg norm hratio
  calc
    norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2))
        = norm (∏' p : ℙ, w p) := h_abs_ratio
    _ = ∏' p : ℙ, norm (w p) := h_abs_tprod
    _ = ∏' p : ℙ, u p := by simp [h_abs_eq_fun]
    _ = ∏' p : ℙ, (1 + ((p : ℕ) : ℝ) ^ (-((3 : ℝ) / 2)))⁻¹ := rfl

lemma summable_one_div_nat_add_rpow' {x : ℝ} (hx : 1 < x) : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)) := by
  have h := (Real.summable_one_div_nat_add_rpow (1 : ℝ) x).2 hx
  have h' : Summable (fun n : ℕ => (|((n : ℝ) + 1)| ^ x)⁻¹) := by
    simpa [one_div] using h
  have h2 : (fun n : ℕ => (|((n : ℝ) + 1)| ^ x)⁻¹) = (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
    funext n
    have hn : 0 ≤ (n : ℝ) + 1 := by
      have : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      exact add_nonneg this (show 0 ≤ (1 : ℝ) from zero_le_one)
    simp [abs_of_nonneg hn]
  have h'' : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) := by
    simpa [h2] using h'
  have h''' : Summable (fun n : ℕ => ((n + 1 : ℝ) ^ x)⁻¹) := by
    simpa [Nat.cast_add] using h''
  simpa [one_div] using h'''

lemma tsum_pos_of_pos_first_term {f : ℕ → ℝ} (hf : Summable f) (h0 : 0 < f 0) (hnonneg : ∀ n, 0 ≤ f n) : 0 < ∑' n, f n := by
  have hsum0 : ∑ n ∈ Finset.range 1, f n = f 0 := by
    simp
  have hpos_partial : 0 < ∑ n ∈ Finset.range 1, f n := by
    simpa [hsum0] using h0
  have hsumle : ∑ n ∈ Finset.range 1, f n ≤ ∑' n, f n := by
    have hnonneg' : ∀ n ∉ Finset.range 1, 0 ≤ f n := by
      intro n hn
      exact hnonneg n
    simpa using (hf.sum_le_tsum (s := Finset.range 1) hnonneg')
  exact lt_of_lt_of_le hpos_partial hsumle

lemma terms_nonneg (x : ℝ) : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n + 1 : ℝ) ^ x) := by
  intro n
  have hposb' : 0 < ((n : ℝ) + 1) :=
    add_pos_of_nonneg_of_pos (show 0 ≤ (n : ℝ) from by exact_mod_cast (Nat.zero_le n)) zero_lt_one
  have hposb : 0 < ((n + 1 : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hposb'
  have hdenpos : 0 < ((n + 1 : ℝ) ^ x) := by
    simpa using (Real.rpow_pos_of_pos hposb x)
  have hden_nonneg : 0 ≤ ((n + 1 : ℝ) ^ x) := le_of_lt hdenpos
  have hnum_nonneg : 0 ≤ (1 : ℝ) := le_of_lt (zero_lt_one : 0 < (1 : ℝ))
  exact div_nonneg hnum_nonneg hden_nonneg

lemma term_eq_ofRealC (x : ℝ) (n : ℕ) : (1 / ((n + 1 : ℂ) ^ (x : ℂ))) = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
  have hbase_nonneg : 0 ≤ (n + 1 : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have : 0 ≤ (n : ℝ) + 1 := add_nonneg hn (show 0 ≤ (1 : ℝ) from zero_le_one)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hpow' : ((n + 1 : ℂ) ^ (x : ℂ)) = (((n + 1 : ℝ) ^ x : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow (x := (n + 1 : ℝ)) (hx := hbase_nonneg) (y := x)).symm
  have hdiv : (1 : ℂ) / (((n + 1 : ℝ) ^ x : ℝ) : ℂ) = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := by
    simp
  calc
    1 / ((n + 1 : ℂ) ^ (x : ℂ))
        = (1 : ℂ) / (((n + 1 : ℝ) ^ x : ℝ) : ℂ) := by simp [hpow']
    _ = ((1 / ((n + 1 : ℝ) ^ x) : ℝ) : ℂ) := hdiv

lemma im_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).im = 0 := by
  have him := congrArg Complex.im (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
  have hz : (((∑' n : ℕ, g n) : ℝ) : ℂ).im = 0 := by
    simp
  exact Eq.trans him hz

lemma re_tsum_ofReal (g : ℕ → ℝ) : (∑' n : ℕ, (g n : ℂ)).re = ∑' n : ℕ, g n := by
  have h := congrArg Complex.re (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := g)).symm
  simpa [Complex.ofReal_re] using h

lemma zetapos (x : ℝ) (hx : 1 < x) : (riemannZeta x).im = 0 ∧ 0 < (riemannZeta x).re := by
  have hxC : 1 < (Complex.ofReal x).re := by simpa [Complex.ofReal_re] using hx
  have hz : riemannZeta (x : ℂ) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow (s := (x : ℂ)) hxC
  have him : (riemannZeta x).im = 0 := by
    simpa [hz, term_eq_ofRealC x] using
      (im_tsum_ofReal (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)))
  have hre : (riemannZeta x).re = ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ x) := by
    simpa [hz, term_eq_ofRealC x] using
      (re_tsum_ofReal (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)))
  have hsum : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)) :=
    summable_one_div_nat_add_rpow' (x := x) hx
  have hpos0 : 0 < 1 / ((Nat.cast 0 + 1 : ℝ) ^ x) := by
    simp [zero_add]
  have hnonneg : ∀ n : ℕ, 0 ≤ 1 / ((n + 1 : ℝ) ^ x) := terms_nonneg x
  have hpos : 0 < ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ x) :=
    tsum_pos_of_pos_first_term hsum hpos0 hnonneg
  exact ⟨him, by simpa [hre] using hpos⟩

lemma zeta332pos : 0 < norm (riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)) := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  have h32 : (1 : ℝ) < (3 : ℝ) / 2 := by norm_num
  obtain ⟨h3im, h3repos⟩ := zetapos 3 h3
  obtain ⟨h32im, h32repos⟩ := zetapos ((3 : ℝ) / 2) h32
  have h3ne : riemannZeta (3 : ℝ) ≠ 0 := by
    intro hz
    exact (ne_of_gt h3repos) (by simpa using congrArg Complex.re hz)
  have h32ne : riemannZeta ((3 : ℝ) / 2) ≠ 0 := by
    intro hz
    exact (ne_of_gt h32repos) (by simpa using congrArg Complex.re hz)
  have hdivne : riemannZeta (3 : ℝ) / riemannZeta ((3 : ℝ) / 2) ≠ 0 :=
    div_ne_zero h3ne h32ne
  simpa using (norm_pos_iff.mpr hdivne)

open _root_.Real _root_.Set _root_.Filter Topology _root_.MeasureTheory
open scoped BigOperators Topology

lemma one_div_nat_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) : 1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · have hcalc : 1 / (n : ℂ) ^ s = (n : ℂ) ^ (-s) := by
      calc
        1 / (n : ℂ) ^ s = ((n : ℂ) ^ s)⁻¹ := by simp [one_div]
        _ = (n : ℂ) ^ (-s) := by simpa using (Complex.cpow_neg (n : ℂ) s).symm
    simpa [h] using hcalc

lemma lem_zetaLimit (s : ℂ) (hs : 1 < s.re) : riemannZeta s = ∑' n : ℕ, if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  classical
  have hsne : s ≠ 0 := by
    intro h
    have hpos : 0 < s.re := lt_trans (show (0 : ℝ) < 1 from zero_lt_one) hs
    have hne : s.re ≠ 0 := ne_of_gt hpos
    simp [h] at hne
  have hz : riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := zeta_eq_tsum_one_div_nat_cpow (s := s) hs
  simpa [one_div_nat_cpow_eq_ite_cpow_neg s hsne] using hz

noncomputable def zetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

lemma sum_Icc1_eq_sum_range_succ (N : ℕ) (g : ℕ → ℂ) :
  (∑ k ∈ Finset.Icc 1 N, g k) = ∑ n ∈ Finset.range N, g (n + 1) := by
  classical
                                                                  
  symm
  refine Finset.sum_bij (s := Finset.range N) (t := Finset.Icc 1 N)
    (f := fun n => g (n + 1)) (g := fun k => g k)
    (i := fun n (_hn : n ∈ Finset.range N) => n + 1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N := Finset.mem_range.mp hn
    have h1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have h2 : n + 1 ≤ N := Nat.succ_le_of_lt hlt
    exact (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  · intro a ha b hb h
                             
    simpa using Nat.succ_injective h
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine ⟨k - 1, ?_, ?_⟩
    ·                      
      have hsucc : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      have hle : (k - 1) + 1 ≤ N := by simpa [hsucc] using hk2
      have hlt : k - 1 < N := lt_of_lt_of_le (Nat.lt_succ_self (k - 1)) hle
      exact Finset.mem_range.mpr hlt
    ·                  
      simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl

lemma sum_Icc0_eq_sum_Icc1_of_zero (N : ℕ) (g : ℕ → ℂ) (h0 : g 0 = 0) :
  (∑ k ∈ Finset.Icc 0 N, g k) = ∑ k ∈ Finset.Icc 1 N, g k := by
  classical
  have hdecomp : insert (0 : ℕ) (Finset.Icc 1 N) = Finset.Icc 0 N := by
    simpa [Nat.succ_eq_add_one] using
      (Finset.insert_Icc_succ_left_eq_Icc (a := 0) (b := N) (h := Nat.zero_le N))
  have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 N := by
    intro h
    rcases Finset.mem_Icc.mp h with ⟨h1, _h2⟩
    have : ¬ (1 ≤ (0 : ℕ)) := by decide
    exact this h1
  calc
    (∑ k ∈ Finset.Icc 0 N, g k)
        = ∑ k ∈ insert 0 (Finset.Icc 1 N), g k := by
            simp [hdecomp]
    _ = g 0 + ∑ k ∈ Finset.Icc 1 N, g k := by
            simp
    _ = ∑ k ∈ Finset.Icc 1 N, g k := by simp [h0]

lemma sum_Icc0_shifted_eq_sum_range (a : ℕ → ℂ) (m : ℕ) :
  (∑ k ∈ Finset.Icc 0 m, (if k = 0 then 0 else a k)) = ∑ n ∈ Finset.range m, a (n + 1) := by
  classical
  calc
    (∑ k ∈ Finset.Icc 0 m, (if k = 0 then 0 else a k))
        = ∑ k ∈ Finset.Icc 1 m, (if k = 0 then 0 else a k) := by
          simpa using
            (sum_Icc0_eq_sum_Icc1_of_zero (N := m)
              (g := fun k => (if k = 0 then 0 else a k)) (h0 := by simp))
    _ = ∑ n ∈ Finset.range m, (if n + 1 = 0 then 0 else a (n + 1)) := by
          simpa using
            (sum_Icc1_eq_sum_range_succ (N := m) (g := fun k => (if k = 0 then 0 else a k)))
    _ = ∑ n ∈ Finset.range m, a (n + 1) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp

lemma sum_Icc0_shifted_floor_eq (a : ℕ → ℂ) (t : ℝ) :
  (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then 0 else a k)) = ∑ n ∈ Finset.range ⌊t⌋₊, a (n + 1) := by
  simpa using (sum_Icc0_shifted_eq_sum_range a ⌊t⌋₊)

lemma lem_fDeriv (s : ℂ) (u : ℝ) (hu : 0 < u) :
    (let f := fun u : ℝ => (u : ℂ) ^ (-s)
     deriv f u = -s * (u : ℂ) ^ (-s - 1)) := by
                             
  show deriv (fun u : ℝ => (u : ℂ) ^ (-s)) u = -s * (u : ℂ) ^ (-s - 1)
  have hu_ne_zero : u ≠ 0 := ne_of_gt hu
  by_cases h : s = 0
  ·                                
    simp [h]
  ·                                
    have hneg_s_ne_zero : -s ≠ 0 := neg_ne_zero.mpr h
    exact Complex.deriv_ofReal_cpow_const hu_ne_zero hneg_s_ne_zero

lemma differentiable_integrable_cpow_on_Icc (s : ℂ) (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) :
  (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun u : ℝ => (u : ℂ) ^ (-s)) t)
  ∧ IntegrableOn (deriv (fun u : ℝ => (u : ℂ) ^ (-s))) (Set.Icc a b) :=
by
  classical
                                                       
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  set g : ℝ → ℂ := fun u => -s * (u : ℂ) ^ (-s - 1)
                            
  have hpos_of_mem : ∀ {t : ℝ}, t ∈ Set.Icc a b → 0 < t := by
    intro t ht; exact lt_of_lt_of_le h0 ht.1
                                    
  have hdiff_at : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t := by
    intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt (hpos_of_mem ht)
    by_cases hs : s = 0
    ·                   
      simp [f, hs]
    ·                                                        
      have hr : (-s) ≠ 0 := by simpa using (neg_ne_zero.mpr hs)
      have hhas : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * t ^ ((-s) - 1)) t :=
        hasDerivAt_ofReal_cpow_const (x := t) (hx := ht_ne) (r := -s) (hr := hr)
      exact hhas.differentiableAt
                             
  have hcont_pow : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) := by
    intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt (hpos_of_mem ht)
    by_cases hzero : (-s - 1) = 0
    ·                       
      have : (fun u : ℝ => (u : ℂ) ^ (-s - 1)) = fun _ : ℝ => (1 : ℂ) := by
        funext u; simp [hzero]
      simpa [this] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℂ)) t).continuousWithinAt
    ·                                             
      have hr : (-s - 1) ≠ 0 := hzero
      have hcpow : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1)) ((-s - 1) * t ^ ((-s - 1) - 1)) t :=
        hasDerivAt_ofReal_cpow_const (x := t) (hx := ht_ne) (r := -s - 1) (hr := hr)
      have hcont_at : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-s - 1)) t :=
        hcpow.differentiableAt.continuousAt
      simpa using hcont_at.continuousWithinAt
  have hcont_g : ContinuousOn g (Set.Icc a b) := by
    have hconst : ContinuousOn (fun _ : ℝ => (-s : ℂ)) (Set.Icc a b) := continuousOn_const
    simpa only [g, Pi.mul_def, neg_mul] using! hconst.mul hcont_pow
                                                                                  
  have hEqOn : EqOn (deriv f) g (Set.Icc a b) := by
    intro u hu
    have hu_pos : 0 < u := hpos_of_mem hu
    simpa [f, g] using (lem_fDeriv s u hu_pos)
                                                                                                            
  have hcont_deriv : ContinuousOn (deriv f) (Set.Icc a b) := by
                                            
    have hg_restr : Continuous ((Set.Icc a b).domRestrict g) := hcont_g.domRestrict
    have hEqRestr : (Set.Icc a b).domRestrict (deriv f) = (Set.Icc a b).domRestrict g := by
      funext x; exact hEqOn x.property
    have hderiv_restr : Continuous ((Set.Icc a b).domRestrict (deriv f)) := by
      simpa [hEqRestr] using hg_restr
    simpa [continuousOn_iff_continuous_domRestrict] using hderiv_restr
                                                              
  have hInt : IntegrableOn (deriv f) (Set.Icc a b) :=
    hcont_deriv.integrableOn_compact isCompact_Icc
  exact And.intro hdiff_at hInt

lemma intervalIntegral_congr_of_Ioc_eq (a b : ℝ) (h : a ≤ b)
  (f g : ℝ → ℂ)
  (hpt : ∀ u ∈ Set.Ioc a b, f u = g u) :
  (∫ u in a..b, f u) = ∫ u in a..b, g u := by
                                                                                
  have h1 : (∀ᵐ u ∂(MeasureTheory.volume), u ∈ Set.Ioc a b → f u = g u) := by
    refine Filter.Eventually.of_forall ?_;
    intro u hu; exact hpt u hu
  have hIocEmpty : Set.Ioc b a = (∅ : Set ℝ) := by
    simpa using! (Set.Ioc_eq_empty_of_le h)
  have h2 : (∀ᵐ u ∂(MeasureTheory.volume), u ∈ Set.Ioc b a → f u = g u) := by
    refine Filter.Eventually.of_forall ?_;
    intro u hu
    have : u ∈ (∅ : Set ℝ) := by simp [hIocEmpty] at hu
    exact this.elim
  simpa using
    (intervalIntegral.integral_congr_ae' (a := a) (b := b) (μ := MeasureTheory.volume)
      (f := f) (g := g) h1 h2)

lemma lem_applyAbel (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) * (N : ℂ) ^ (-s)
        - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
  classical
                   
  set f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s)
  let c : ℕ → ℂ := fun k => if k = 0 then 0 else (1 : ℂ)
                                             
  have hle : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdiff_int :=
    differentiable_integrable_cpow_on_Icc (s := s) (a := (1 : ℝ)) (b := (N : ℝ))
      (h0 := by exact zero_lt_one) (_hle := hle)
  rcases hdiff_int with ⟨hdiff, hint⟩
                                                         
  have habel :=
    sum_mul_eq_sub_integral_mul₀' (c := c) (f := f) (m := N)
      (hc := by simp [c])
      (hf_diff := by intro t ht; simpa [f] using (hdiff t ht))
      (hf_int := by simpa [f] using hint)
                                         
  have hLHS : (∑ k ∈ Finset.Icc 0 N, f k * c k) = zetaPartialSum s N := by
                                    
    have h0 :
        (∑ k ∈ Finset.Icc 0 N, f k * c k) = ∑ k ∈ Finset.Icc 1 N, f k * c k := by
      simpa [c] using
        (sum_Icc0_eq_sum_Icc1_of_zero (N := N)
          (g := fun k => f k * c k) (h0 := by simp [c]))
    have h1 : (∑ k ∈ Finset.Icc 1 N, f k * c k)
                = ∑ n ∈ Finset.range N, f (n + 1) * c (n + 1) := by
      simpa using (sum_Icc1_eq_sum_range_succ (N := N) (g := fun k => f k * c k))
    have h2 : (∑ n ∈ Finset.range N, f (n + 1) * c (n + 1))
                = ∑ n ∈ Finset.range N, f (n + 1) := by
      apply Finset.sum_congr rfl; intro n hn; simp [c]
    calc
      (∑ k ∈ Finset.Icc 0 N, f k * c k)
          = ∑ k ∈ Finset.Icc 1 N, f k * c k := by simpa using h0
      _ = ∑ n ∈ Finset.range N, f (n + 1) * c (n + 1) := by simpa using h1
      _ = ∑ n ∈ Finset.range N, f (n + 1) := by simpa using h2
      _ = zetaPartialSum s N := by simp [zetaPartialSum, f]
                                                     
  have hset_to_interval :
      (∫ t in Set.Ioc (1 : ℝ) N, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
    simpa using
      (intervalIntegral.integral_of_le
        (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        (μ := volume) hle).symm
  have hstep1 :
      zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
          - ∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k := by
    simpa [hLHS, hset_to_interval] using habel
                                                
  have hInt_congr :
      (∫ u in (1 : ℝ)..N, deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
        = ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
                                                                             
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hle)
      (f := fun u => deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k)
      (g := fun u => (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)))
    intro u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu.1
    have hderiv : deriv f u = -s * (u : ℂ) ^ (-s - 1) := by
      simpa [f] using (lem_fDeriv s u hu_pos)
                                          
    have hsumfloor : (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k) = (Nat.floor u : ℂ) := by
      have hshift := sum_Icc0_shifted_floor_eq (a := fun _ => (1 : ℂ)) (t := u)
      have hsum : (∑ n ∈ Finset.range ⌊u⌋₊, (1 : ℂ)) = (Nat.floor u : ℂ) := by
        simp [Finset.sum_const, Finset.card_range]
      simpa [c, hsum] using hshift
    calc
      deriv f u * ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, c k
          = deriv f u * (Nat.floor u : ℂ) := by simp [hsumfloor]
      _ = (Nat.floor u : ℂ) * deriv f u := by simp [mul_comm]
      _ = (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by simp [hderiv]
                                     
  have hstep2 :
      zetaPartialSum s N
        = f N * (∑ k ∈ Finset.Icc 0 N, c k)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    simpa [hInt_congr] using hstep1
                                                      
  have hMain : f N * (∑ k ∈ Finset.Icc 0 N, c k) = (N : ℂ) * f N := by
    have hs : (∑ k ∈ Finset.Icc 0 N, c k) = ∑ n ∈ Finset.range N, (1 : ℂ) := by
      simpa [c] using (sum_Icc0_shifted_eq_sum_range (a := fun _ => (1 : ℂ)) (m := N))
    have hsumN : (∑ n ∈ Finset.range N, (1 : ℂ)) = (N : ℂ) := by
      simp [Finset.sum_const, Finset.card_range]
    calc
      f N * (∑ k ∈ Finset.Icc 0 N, c k)
          = f N * (∑ n ∈ Finset.range N, (1 : ℂ)) := by simp [hs]
      _ = f N * (N : ℂ) := by simp [hsumN]
      _ = (N : ℂ) * f N := by simp [mul_comm]
                                     
  have hfinal :
      zetaPartialSum s N
        = (N : ℂ) * (N : ℂ) ^ (-s)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
    calc
      zetaPartialSum s N
          = f N * (∑ k ∈ Finset.Icc 0 N, c k)
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simpa using hstep2
      _ = (N : ℂ) * f N
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simp [hMain]
      _ = (N : ℂ) * (N : ℂ) ^ (-s)
              - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
            simp [f]
  exact hfinal

lemma helper_cpow_mul_cpow_neg_eq_cpow_sub (x s : ℂ) (hx : x ≠ 0) : x * x ^ (-s) = x ^ (1 - s) := by
  calc
    x * x ^ (-s) = x ^ (1 : ℂ) * x ^ (-s) := by
      simp [Complex.cpow_one]
    _ = x ^ (1 + (-s)) := by
      simpa using (Complex.cpow_add (x := x) (y := (1 : ℂ)) (z := (-s)) hx).symm
    _ = x ^ (1 - s) := by
      simp [sub_eq_add_neg]

lemma lem_zetaNsimplified1 (s : ℂ) (N : ℕ) (hN : 1 ≤ N) : zetaPartialSum s N = (N : ℂ) ^ (1 - s) + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have happly := lem_applyAbel s N hN
                                               
  have hInt :
      ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1))
        = (-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
    simp [mul_left_comm]
  calc
    zetaPartialSum s N
        = (N : ℂ) * (N : ℂ) ^ (-s)
          - ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (-s * (u : ℂ) ^ (-s - 1)) := by
          simpa using happly
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          - ((-s) * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)) := by
          rw [hInt]
    _ = (N : ℂ) * (N : ℂ) ^ (-s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          simp [sub_eq_add_neg, neg_mul]
    _ = (N : ℂ) ^ (1 - s)
          + s * ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1) := by
          have hpos : 0 < N := (Nat.succ_le_iff).mp hN
          have hNz : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hpos)
          have hpow := helper_cpow_mul_cpow_neg_eq_cpow_sub (x := (N : ℂ)) (s := s) hNz
          simp [hpow]

lemma lem_floorUdecomp (u : ℝ) : (Int.floor u : ℝ) = u - Int.fract u := by exact (eq_sub_iff_add_eq).2 (Int.floor_add_fract u)

lemma lem_fracPartBound (u : ℝ) : 0 ≤ Int.fract u ∧ Int.fract u < 1 ∧ |Int.fract u| ≤ (1 : ℝ) := by
  constructor
  · exact Int.fract_nonneg u
  · constructor
    · exact Int.fract_lt_one u
    · have hnonneg : 0 ≤ Int.fract u := Int.fract_nonneg u
      have hle : Int.fract u ≤ (1 : ℝ) := le_of_lt (Int.fract_lt_one u)
      simpa [abs_of_nonneg hnonneg] using hle

lemma helper_continuousOn_cpow (r : ℂ) {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) := by
  classical
  intro t ht
  have ht_pos : 0 < t := lt_of_lt_of_le ha ht.1
  by_cases hr : r = 0
  ·              
    have hconst : (fun u : ℝ => (u : ℂ) ^ r) = fun _ => (1 : ℂ) := by
      funext u; simp [hr]
    simpa [hconst] using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℂ)) t).continuousWithinAt
  ·                                        
    have hderiv : HasDerivAt (fun u : ℝ => (u : ℂ) ^ r) (r * t ^ (r - 1)) t :=
      hasDerivAt_ofReal_cpow_const (x := t) (hx := ne_of_gt ht_pos) (r := r) (hr := hr)
    exact hderiv.differentiableAt.continuousAt.continuousWithinAt

lemma helper_intervalIntegrable_mul_cpow_id (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  classical
                          
  have hcont1 : ContinuousOn (fun u : ℝ => (u : ℂ)) (Set.Icc a b) :=
    (Complex.continuous_ofReal).continuousOn
  have hcont2 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    helper_continuousOn_cpow (-s - 1) (lt_of_lt_of_le zero_lt_one ha) hab
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont1.mul hcont2
                                                            
  have hint_on : IntegrableOn (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Icc a b) :=
    hcont.integrableOn_compact isCompact_Icc
  have hint : IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
    simpa using
      (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
        (f := fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) hab).2 hint_on
  exact hint

lemma helper_aestronglyMeasurable_kernel_Icc (s : ℂ) {a b : ℝ} :
  AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
    (volume.restrict (Icc a b)) := by
                                
  have hmeas_fract : Measurable (Int.fract : ℝ → ℝ) := by simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
  have h1 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) (volume.restrict (Icc a b)) :=
    (Complex.measurable_ofReal.comp hmeas_fract).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (volume.restrict (Icc a b)) := by
    have hmeas : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by measurability
    exact hmeas.aestronglyMeasurable
  simpa using! (MeasureTheory.AEStronglyMeasurable.mul h1 h2)

lemma helper_intervalIntegrable_frac_kernel (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume a b := by
  classical
                                             
  let μ := volume.restrict (Icc a b)
  set f : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
                       
  have hmeas : AEStronglyMeasurable f μ := by simpa [μ, f] using helper_aestronglyMeasurable_kernel_Icc (s := s) (a := a) (b := b)
                                  
  have hbound_ae : ∀ᵐ u ∂μ, ‖f u‖ ≤ g u := by
                                                  
    refine ((ae_restrict_iff' (μ := volume) (s := Icc a b)
      (p := fun u : ℝ => ‖f u‖ ≤ g u) measurableSet_Icc)).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro u hu
                    
    have hfract_le1 : ‖(Int.fract u : ℝ)‖ ≤ (1 : ℝ) := by
      simpa using (lem_fracPartBound u).2.2
                           
    have : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ ‖(Int.fract u : ℝ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
      simp
    have : ‖f u‖ ≤ ‖(Int.fract u : ℝ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by
      simp [f]
    have : ‖f u‖ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ :=
      le_trans this (mul_le_mul_of_nonneg_right hfract_le1 (by exact norm_nonneg _))
    simpa [g] using (by simpa [one_mul] using this)
                                             
  have hcont : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Icc a b) :=
    helper_continuousOn_cpow (-s - 1) (lt_of_lt_of_le zero_lt_one ha) hab
  have hg_int_on : IntegrableOn g (Icc a b) := by
    have hcont_norm : ContinuousOn g (Icc a b) := by
      simpa [g] using (hcont.norm)
    exact hcont_norm.integrableOn_compact isCompact_Icc
                    
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  have hg : Integrable g μ := by simpa [μ] using! hg_int_on
                                                        
  have hf : Integrable f μ :=
    MeasureTheory.integrable_of_norm_sub_le (μ := μ) hmeas hf0 hg
      (by
                                    
        have : ∀ᵐ u ∂μ, ‖(0 : ℂ) - f u‖ ≤ g u := by
          simpa [sub_eq_add_neg, norm_neg, μ, f, g] using hbound_ae
        simpa using this)
                                         
  have hf_on : IntegrableOn f (Icc a b) := by simpa [μ, f] using! hf
  simpa using
    (intervalIntegrable_iff_integrableOn_Icc_of_le (μ := volume) (a := a) (b := b)
      (f := f) hab).2 hf_on

lemma lem_integralSplit (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
      = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  have hab : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
                                          
  have hcongr1 :
      (∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
    intro u hu
    have hu0 : 0 ≤ u := le_trans (by norm_num) (le_of_lt hu.1)
    have hfloorR : (Nat.floor u : ℝ) = (Int.floor u : ℝ) := by
      simpa using (natCast_floor_eq_intCast_floor (R := ℝ) (a := u) hu0)
    have hfloorC : (Nat.floor u : ℂ) = ((Int.floor u : ℝ) : ℂ) := by
      simpa using congrArg (fun x : ℝ => (x : ℂ)) hfloorR
    have hIFR : (Int.floor u : ℝ) = u - Int.fract u := lem_floorUdecomp u
    have hIFC : ((Int.floor u : ℝ) : ℂ) = ((u - Int.fract u : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hIFR
    have : (Nat.floor u : ℂ) = ((u - Int.fract u : ℝ) : ℂ) := hfloorC.trans hIFC
    simp [this, sub_eq_add_neg]
                               
  have hcongr2 :
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
        = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    have hI1 : IntervalIntegrable (fun u : ℝ => (u : ℂ) * (u : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) :=
      helper_intervalIntegrable_mul_cpow_id (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have hI2 : IntervalIntegrable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) volume (1 : ℝ) (N : ℝ) :=
      helper_intervalIntegrable_frac_kernel (s := s) (a := (1 : ℝ)) (b := (N : ℝ)) (ha := le_rfl) (hab := hab)
    have :
        (∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1)
                - ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := by
      apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
      intro u hu; simp [sub_mul]
    calc
      (∫ u in (1 : ℝ)..N,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1))
          = ∫ u in (1 : ℝ)..N,
              ((u : ℂ) * (u : ℂ) ^ (-s - 1)
                - ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) := this
      _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
            - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) :=
        (intervalIntegral.integral_sub (μ := volume) (a := (1 : ℝ)) (b := (N : ℝ)) hI1 hI2)
                                              
  have hpow :
      (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
        = ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) := by
    apply intervalIntegral_congr_of_Ioc_eq (a := (1 : ℝ)) (b := (N : ℝ)) (h := hab)
    intro u hu
    have hu_pos : 0 < u := lt_trans zero_lt_one hu.1
    have hux0 : (u : ℝ) ≠ 0 := ne_of_gt hu_pos
    have hcx0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hux0
    calc
      (u : ℂ) * (u : ℂ) ^ (-s - 1)
          = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [Complex.cpow_one]
      _ = (u : ℂ) ^ (1 + (-s - 1)) := by
        simpa using
          (Complex.cpow_add (x := (u : ℂ)) (y := (1 : ℂ)) (z := (-s - 1)) hcx0).symm
      _ = (u : ℂ) ^ (-s) := by
        simp [add_left_comm, sub_eq_add_neg]
             
  calc
    ∫ u in (1 : ℝ)..N, (Nat.floor u : ℂ) * (u : ℂ) ^ (-s - 1)
        = ∫ u in (1 : ℝ)..N,
            ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := hcongr1
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) * (u : ℂ) ^ (-s - 1))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := hcongr2
    _ = (∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
          - ∫ u in (1 : ℝ)..N, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
      simp [hpow]

lemma lem_zetaNsimplified2 (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s)
        + (s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s))
        - (s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) := by
  have hstep1: _ := lem_zetaNsimplified1 s N hN
  rw [lem_integralSplit] at hstep1
  rw [mul_sub] at hstep1
  rw [hstep1]
  exact (add_sub_assoc _ _ _).symm
  exact hN

lemma lem_evalMainIntegral (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) : s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
  have h01leN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h0notIcc : (0 : ℝ) ∉ Set.Icc (1 : ℝ) (N : ℝ) := by
    intro hx
    exact (not_le.mpr (by norm_num : (0 : ℝ) < 1)) hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    simp [uIcc_of_le h01leN]
  have hrne : -s ≠ (-1 : ℂ) := by
    intro h
    apply hs
    simpa using congrArg Neg.neg h
  have hint : ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = ((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1) := by
    have hcond : (-1 < (-s).re) ∨ (-s ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ)) := by
      exact Or.inr ⟨hrne, h0not⟩
    simpa using (integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s) hcond)
  have hmul : s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := by
    simpa using congrArg (fun x => s * x) hint
  have hrewrite :
      s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
        = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := by
    have : s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1))
          = s * (((N : ℂ) ^ (1 - s) - (1 : ℂ) ^ (1 - s)) / (1 - s)) := by
      simp [add_comm, sub_eq_add_neg]
    have h1pow : (1 : ℂ) ^ (1 - s) = 1 := by simp
    simpa [h1pow] using this
  have hsplit : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
      = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
    have h1 : s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s))
        = (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s) := by
      simpa using (mul_div_assoc s ((N : ℂ) ^ (1 - s) - 1) (1 - s)).symm
    have h2 : (s * ((N : ℂ) ^ (1 - s) - 1)) / (1 - s)
        = (s / (1 - s)) * ((N : ℂ) ^ (1 - s) - 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_mul_eq_mul_div (a := s) (b := (1 - s)) (c := ((N : ℂ) ^ (1 - s) - 1))).symm
    exact h1.trans h2
  calc
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
        = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := hmul
    _ = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := hrewrite
    _ = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := hsplit

lemma lem_zetaNfinal (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
                                                                         
  have hstep := lem_zetaNsimplified2 s N hN
                                                       
  rw [lem_evalMainIntegral s hs N hN] at hstep

  have hden : (1 - s) ≠ 0 := by
    intro h
    have h1 : 1 = s := by simpa [sub_eq_zero] using h
    have h2 : s = 1 := h1.symm
    exact hs h2
  let A := (N : ℂ) ^ (1 - s)
                                                                             
  have h1 : (1 - s) * (A + s / (1 - s) * (A - 1)) = A - s := by
    calc
      (1 - s) * (A + s / (1 - s) * (A - 1))
          = (1 - s) * A + (1 - s) * (s / (1 - s) * (A - 1)) := by ring
      _ = (1 - s) * A + s * (A - 1) := by field_simp [hden]
      _ = A - s := by ring
  have h2 : (1 - s) * (A / (1 - s) + 1 + 1 / (s - 1)) = A - s := by
    have hne : s - 1 ≠ 0 := by simpa [sub_eq_zero] using hs
    field_simp [hden, hne] <;> ring
  have halg : A + s / (1 - s) * (A - 1) = A / (1 - s) + 1 + 1 / (s - 1) :=
    mul_left_cancel₀ hden (h1.trans h2.symm)

  rw [halg] at hstep
  exact hstep

lemma complex_tendsto_zero_iff_norm_tendsto_zero {α : Type*} {f : α → ℂ} {l : Filter α} :
    Tendsto f l (𝓝 0) ↔ Tendsto (fun x => ‖f x‖) l (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_zero_right]

lemma complex_norm_natCast_cpow (N : ℕ) (w : ℂ) (hN : 0 < N) :
    ‖(N : ℂ) ^ w‖ = (N : ℝ) ^ w.re := by
  have hNnz : (N : ℂ) ≠ 0 := by
    simp [Ne, Nat.cast_eq_zero]
    exact ne_of_gt hN
  rw [Complex.norm_cpow_of_ne_zero hNnz]
  rw [Complex.norm_natCast]
  rw [Complex.natCast_arg]
  simp [Real.exp_zero]

lemma tendsto_natCast_cpow_zero_of_neg_re (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [complex_tendsto_zero_iff_norm_tendsto_zero]
                                
  have h1 : ∀ᶠ (N : ℕ) in atTop, ‖(N : ℂ) ^ w‖ = (N : ℝ) ^ w.re := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact complex_norm_natCast_cpow N w hN
  rw [tendsto_congr' h1]

  have hw_pos : 0 < -w.re := neg_pos.mpr hw
                                 
  have h_eq : w.re = -(-w.re) := by ring
  rw [h_eq]
                                                                                               
  have h_comp : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h_rpow : Tendsto (fun x : ℝ => x ^ (-(-w.re))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hw_pos
  exact Tendsto.comp h_rpow h_comp

lemma lem_limitTerm1 (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  apply tendsto_natCast_cpow_zero_of_neg_re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma lem_integrandBound (u : ℝ) (hu : 1 ≤ u) (s : ℂ) : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                  
  set a : ℂ := ((Int.fract u : ℝ) : ℂ)
  set b : ℂ := (u : ℂ) ^ (-s - 1)
                  
  have hfract_le1 : ‖a‖ ≤ (1 : ℝ) := by
    simpa [a, Complex.norm_real] using (lem_fracPartBound u).2.2
                          
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
                                                     
  have h₁ : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := by simp
  have h₂ : ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ :=
    mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
  have h₃ : ‖a * b‖ ≤ 1 * ‖b‖ := le_trans h₁ h₂
  have hle : ‖a * b‖ ≤ ‖b‖ := by simpa [one_mul] using h₃
                                                                   
  have hb : ‖b‖ = u ^ ((-s - 1).re) := by
    simpa [b] using
      Complex.norm_cpow_eq_rpow_re_of_pos (x := u) (hx := hu0) (y := -s - 1)
                                           
  have hexp : (-s - 1).re = -s.re - 1 := by
    simp [sub_eq_add_neg]
                                                       
  calc
    ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖
        = ‖a * b‖ := rfl
    _ ≤ ‖b‖ := hle
    _ = u ^ ((-s - 1).re) := hb
    _ = u ^ (-s.re - 1) := by simp [hexp]

lemma lem_integrandBoundeps (ε : ℝ) (_hε : 0 < ε) (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (hs : ε ≤ s.re) : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε) := by
  have h1 : ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := lem_integrandBound u hu s
  have h2 : -s.re - 1 ≤ -1 - ε := by linarith [hs]
  have h3 : u ^ (-s.re - 1) ≤ u ^ (-1 - ε) := Real.rpow_le_rpow_of_exponent_le hu h2
  exact le_trans h1 h3

lemma lem_triangleInequality_add (z₁ z₂ : ℂ) :
    ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := by
  exact norm_add_le z₁ z₂

lemma helper_integral_interval_sub_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b c : ℝ}
    (hab : IntervalIntegrable f volume a b) (hac : IntervalIntegrable f volume a c) :
    ((∫ x in a..b, f x) - ∫ x in a..c, f x) = ∫ x in c..b, f x := by
  simpa using
    (intervalIntegral.integral_interval_sub_left (μ := volume) (f := f) (a := a) (b := b) (c := c)
      hab hac)

lemma helper_integral_rpow_eval {ε : ℝ} (hε : 0 < ε) {m n : ℝ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) = (m ^ (-ε) - n ^ (-ε)) / ε := by
                                         
  have h0notIcc : (0 : ℝ) ∉ Set.Icc m n := by
    intro hx
    have : ¬ m ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one hm)
    exact this hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc m n := by
    simpa [uIcc_of_le hmn] using h0notIcc
                              
  have hrne : (-1 - ε) ≠ (-1 : ℝ) := by
    intro h
    have hplus := congrArg (fun t => t + 1) h
    have hminus : -ε = 0 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hplus
    have hε0 : ε = 0 := by simpa using congrArg Neg.neg hminus
    exact (ne_of_gt hε) hε0
                                               
  have hint : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ ((-1 - ε) + 1) - m ^ ((-1 - ε) + 1)) / ((-1 - ε) + 1) := by
    have hcond : (-1 < (-1 - ε)) ∨ ((-1 - ε) ≠ -1 ∧ (0 : ℝ) ∉ Set.uIcc m n) := by
      exact Or.inr ⟨hrne, h0not⟩
    simpa using (integral_rpow (a := m) (b := n) (r := -1 - ε) hcond)
                                                      
  have h1 : ((-1 - ε) + 1) = -ε := by
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  have : ∫ u in m..n, u ^ (-1 - ε)
      = (n ^ (-ε) - m ^ (-ε)) / (-ε) := by
    simpa [h1]
      using hint
  have hnegnum : -(n ^ (-ε) - m ^ (-ε)) = m ^ (-ε) - n ^ (-ε) := by
    simp
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (n ^ (-ε) - m ^ (-ε)) / (-ε) := this
    _ = (n ^ (-ε) - m ^ (-ε)) * ((-ε)⁻¹) := by simp [div_eq_mul_inv]
    _ = (n ^ (-ε) - m ^ (-ε)) * (-(ε⁻¹)) := by simp [inv_neg]
    _ = -((n ^ (-ε) - m ^ (-ε)) * ε⁻¹) := by simp [mul_neg]
    _ = (-(n ^ (-ε) - m ^ (-ε))) * ε⁻¹ := by
      simpa using (neg_mul (n ^ (-ε) - m ^ (-ε)) (ε⁻¹)).symm
    _ = (m ^ (-ε) - n ^ (-ε)) * ε⁻¹ := by
      simp
    _ = (m ^ (-ε) - n ^ (-ε)) / ε := by simp [div_eq_mul_inv]

lemma helper_integral_rpow_le {ε : ℝ} (hε : 0 < ε) {m n : ℝ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∫ u in m..n, u ^ (-1 - ε) ≤ (1 / ε) * m ^ (-ε) := by
  have heval := helper_integral_rpow_eval (ε := ε) hε hm hmn
  have hn0 : 0 ≤ n := by
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    exact le_trans h01 (le_trans hm hmn)
  have hsub_le : m ^ (-ε) - n ^ (-ε) ≤ m ^ (-ε) := by
    exact sub_le_self _ (Real.rpow_nonneg hn0 (-ε))
  have hinv_nonneg : 0 ≤ ε⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hε)
  have hdiv_le : ((m ^ (-ε) - n ^ (-ε)) / ε) ≤ (m ^ (-ε) / ε) := by
    have := mul_le_mul_of_nonneg_right hsub_le hinv_nonneg
    simpa [div_eq_mul_inv, mul_comm] using this
  calc
    ∫ u in m..n, u ^ (-1 - ε)
        = (m ^ (-ε) - n ^ (-ε)) / ε := heval
    _ ≤ m ^ (-ε) / ε := hdiv_le
    _ = (1 / ε) * m ^ (-ε) := by simp [div_eq_mul_inv, mul_comm]

lemma helper_tendsto_nat_rpow_neg (ε : ℝ) (hε : 0 < ε) :
  Tendsto (fun m : ℕ => (m : ℝ) ^ (-ε)) atTop (𝓝 0) := by
                                                                              
  have hcont : Tendsto (fun x : ℝ => x ^ (-ε)) atTop (𝓝 0) := by
                                                                              
    simpa using (tendsto_rpow_neg_atTop (y := ε) hε)

  have hcoe : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop

  have : Tendsto ((fun x : ℝ => x ^ (-ε)) ∘ fun n : ℕ => (n : ℝ)) atTop (𝓝 0) :=
    hcont.comp hcoe
                                       
  simpa using! this

lemma helper_exists_limit_of_tail_bound (a : ℕ → ℂ) (b : ℕ → ℝ)
    (hb_nonneg : ∀ m, 0 ≤ b m)
    (hb_tendsto : Tendsto b atTop (𝓝 0))
    (hbound : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → ‖a n - a m‖ ≤ b m) :
    ∃ l : ℂ, Tendsto a atTop (𝓝 l) := by
  classical
                                              
  have hCauchy : CauchySeq a := by
                                      
    refine (Metric.cauchySeq_iff).2 ?_
    intro ε hε
                                                               
    have h_ball : ∀ᶠ m in atTop, dist (b m) 0 < ε / 2 := by
      exact hb_tendsto (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
    have h_b_lt : ∀ᶠ m in atTop, b m < ε / 2 := by
      refine h_ball.mono ?_
      intro m hm
      have : |b m| < ε / 2 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hm
      simpa [abs_of_nonneg (hb_nonneg m)] using this
                                  
    rcases eventually_atTop.1 hbound with ⟨M1, hM1⟩
    rcases eventually_atTop.1 h_b_lt with ⟨M2, hM2⟩
    let M := max M1 M2
    have hPM : ∀ᶠ n in atTop, M ≤ n → ‖a n - a M‖ ≤ b M := by
      have h' := hM1 M (le_max_left _ _)
      exact h'
    have hMb : b M < ε / 2 := hM2 M (le_max_right _ _)
    rcases eventually_atTop.1 hPM with ⟨N0, hN0⟩
    refine ⟨max N0 M, ?_⟩
    intro n hn k hk
    have hMn : M ≤ n := le_trans (le_max_right _ _) hn
    have hMk : M ≤ k := le_trans (le_max_right _ _) hk
    have hN0n : N0 ≤ n := le_trans (le_max_left _ _) hn
    have hN0k : N0 ≤ k := le_trans (le_max_left _ _) hk
    have h1 : ‖a n - a M‖ ≤ b M := (hN0 n hN0n) hMn
    have h2 : ‖a k - a M‖ ≤ b M := (hN0 k hN0k) hMk
                                           
    have htri : ‖a n - a k‖ ≤ ‖a n - a M‖ + ‖a M - a k‖ := by
      have h := norm_add_le (a n - a M) (a M - a k)
      simpa [sub_add_sub_cancel (a n) (a M) (a k)] using h
    have h2' : ‖a M - a k‖ ≤ b M := by simpa [norm_sub_rev] using h2
    have hsumle : ‖a n - a k‖ ≤ b M + b M :=
      le_trans htri (add_le_add h1 h2')
    have hsumlt : b M + b M < ε := by
      have := add_lt_add hMb hMb
      simpa [add_halves] using this
    have : ‖a n - a k‖ < ε := lt_of_le_of_lt hsumle hsumlt
    simpa [dist_eq_norm] using this
                                                 
  rcases cauchySeq_tendsto_of_complete (u := a) hCauchy with ⟨l, hl⟩
  exact ⟨l, hl⟩

lemma helper_intervalIntegrable_rpow_neg {ε : ℝ} {a b : ℝ} (_hε : 0 < ε)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ (-1 - ε)) volume a b := by
  have h0notIcc : (0 : ℝ) ∉ Set.Icc a b := by
    intro hx
    have : ¬ a ≤ 0 := not_le.mpr (lt_of_lt_of_le zero_lt_one ha)
    exact this hx.1
  have h0not : (0 : ℝ) ∉ Set.uIcc a b := by
    simpa [uIcc_of_le hab] using h0notIcc
  simpa using
    (intervalIntegral.intervalIntegrable_rpow (μ := volume) (a := a) (b := b) (r := -1 - ε)
      (Or.inr h0not))

lemma helper_one_le_of_mem_Ioc {m n u : ℝ} (hm : 1 ≤ m) (hu : u ∈ Ioc m n) : 1 ≤ u := by
  exact le_trans hm (le_of_lt hu.1)

lemma helper_integrableOn_of_bound_Ioc {m n : ℝ} {f : ℝ → ℂ} {g : ℝ → ℝ}
  (hmeas : AEStronglyMeasurable f (volume.restrict (Ioc m n)))
  (hbound : ∀ᵐ u ∂(volume.restrict (Ioc m n)), ‖f u‖ ≤ g u)
  (hg : IntegrableOn g (Ioc m n) volume) :
  IntegrableOn f (Ioc m n) volume := by
                                                                    
  let μ := volume.restrict (Ioc m n)
                    
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by
    simp
                             
  have hg' : Integrable g μ := by
    simpa [μ] using! hg
                                           
  have hmeas' : AEStronglyMeasurable f μ := by
    simpa [μ] using hmeas
                                               
  have hineq : ∀ᵐ u ∂μ, ‖(0 : ℂ) - f u‖ ≤ g u := by
    simpa [μ, sub_eq_add_neg, norm_neg] using hbound
                                                        
  have hf : Integrable f μ :=
    MeasureTheory.integrable_of_norm_sub_le (μ := μ) hmeas' hf0 hg' hineq
                                     
  simpa [μ] using! hf

lemma helper_aestronglyMeasurable_kernel_Ioc (s : ℂ) {m n : ℝ} :
  AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
    (volume.restrict (Ioc m n)) := by
                                                           
  have h1 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) (volume.restrict (Ioc m n)) := by
    have hmeas_fract : Measurable (Int.fract : ℝ → ℝ) := by
      simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
    have hmeas_coe : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) :=
      (Complex.measurable_ofReal.comp hmeas_fract)
    exact hmeas_coe.aestronglyMeasurable
                                                        
  have h2 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (volume.restrict (Ioc m n)) := by
    have hmeas : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by
      measurability
    exact hmeas.aestronglyMeasurable
                                             
  simpa using! (MeasureTheory.AEStronglyMeasurable.mul h1 h2)

lemma helper_aebound_kernel_Ioc {ε : ℝ} (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re)
    {m n : ℝ} (hm : 1 ≤ m) (_hmn : m ≤ n) :
    ∀ᵐ u ∂(volume.restrict (Ioc m n)),
      ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε) := by
                                                                                             
  refine
    ((ae_restrict_iff' (μ := volume) (s := Ioc m n)
        (p := fun u : ℝ => ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-1 - ε))
        measurableSet_Ioc)).2 ?_
                                                  
  refine Filter.Eventually.of_forall ?_
  intro u hu
  have hu1 : 1 ≤ u := helper_one_le_of_mem_Ioc hm hu
  simpa using (lem_integrandBoundeps ε hε u hu1 s hs)

lemma helper_integrableOn_rpow_neg_Ioc {ε : ℝ} (hε : 0 < ε)
    {m n : ℝ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    IntegrableOn (fun u : ℝ => u ^ (-1 - ε)) (Ioc m n) volume := by
  have hInt : IntervalIntegrable (fun u : ℝ => u ^ (-1 - ε)) volume m n :=
    helper_intervalIntegrable_rpow_neg (ε := ε) hε hm hmn
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (f := fun u : ℝ => u ^ (-1 - ε)) hmn).1 hInt

lemma helper_tendsto_const_mul_zero (c : ℝ) {f : ℕ → ℝ}
  (h : Tendsto f atTop (𝓝 0)) : Tendsto (fun n => c * f n) atTop (𝓝 0) := by
  simpa using (Filter.Tendsto.const_mul (b := c) h)

lemma helper_limit_norm_le_of_eventual_bound {a : ℕ → ℂ} {l : ℂ} {B : ℝ}
  (h : Tendsto a atTop (𝓝 l)) (hbound : ∀ᶠ n in atTop, ‖a n‖ ≤ B) : ‖l‖ ≤ B := by
  have hnorm : Tendsto (fun n => ‖a n‖) atTop (𝓝 ‖l‖) := (Filter.Tendsto.norm h)
  exact le_of_tendsto hnorm hbound

lemma lem_integralConvergence (ε : ℝ) (hε : 0 < ε) (s : ℂ) (hs : ε ≤ s.re) :
    ∃ I : ℂ,
      Tendsto
        (fun N : ℕ =>
          ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))
        atTop (𝓝 I)
      ∧ ‖I‖ ≤ (1 / ε) := by
  classical
                
  let fC : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  let gR : ℝ → ℝ := fun u => u ^ (-1 - ε)
  let a : ℕ → ℂ := fun N => ∫ u in (1 : ℝ)..(N : ℝ), fC u
  let b : ℕ → ℝ := fun m => (1 / ε) * (m : ℝ) ^ (-ε)
          
  have hb_nonneg : ∀ m, 0 ≤ b m := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    have hpow : 0 ≤ (m : ℝ) ^ (-ε) := Real.rpow_nonneg hm0 _
    have hpos : 0 ≤ 1 / ε := by exact le_of_lt (one_div_pos.mpr hε)
    have := mul_le_mul_of_nonneg_left hpow hpos
    simpa [b] using this
          
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    have hpow := helper_tendsto_nat_rpow_neg (ε := ε) hε
    have hmul := helper_tendsto_const_mul_zero (c := (1 / ε)) hpow
    simpa [b] using hmul
                                    
  have h_tail_pointwise : ∀ m n : ℕ, 1 ≤ m → m ≤ n → ‖a n - a m‖ ≤ b m := by
    intro m n hm1 hmn
                        
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
                                                                                     
    have hInt_f_1n : IntervalIntegrable fC volume (1 : ℝ) (n : ℝ) := by
                              
      have h1nNat : 1 ≤ n := le_trans hm1 hmn
      have h1nR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1nNat
      have hmeas := helper_aestronglyMeasurable_kernel_Ioc (s := s) (m := (1 : ℝ)) (n := (n : ℝ))
      have hgIntOn : IntegrableOn gR (Ioc (1 : ℝ) (n : ℝ)) volume :=
        helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (n : ℝ)) (hm := by norm_num) (hmn := h1nR)
      have hbound := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (n : ℝ)) (hm := by norm_num) (_hmn := h1nR)
      have hintOn := helper_integrableOn_of_bound_Ioc (m := (1 : ℝ)) (n := (n : ℝ)) (f := fC) (g := gR)
        (hmeas := hmeas) (hbound := hbound) (hg := hgIntOn)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (n : ℝ)) (f := fC) h1nR).2 hintOn
    have hInt_f_1m : IntervalIntegrable fC volume (1 : ℝ) (m : ℝ) := by
      have hmeas := helper_aestronglyMeasurable_kernel_Ioc (s := s) (m := (1 : ℝ)) (n := (m : ℝ))
      have hgIntOn : IntegrableOn gR (Ioc (1 : ℝ) (m : ℝ)) volume :=
        helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (m : ℝ)) (hm := by norm_num) (hmn := hmR)
      have hbound := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (m : ℝ)) (hm := by norm_num) (_hmn := hmR)
      have hintOn := helper_integrableOn_of_bound_Ioc (m := (1 : ℝ)) (n := (m : ℝ)) (f := fC) (g := gR)
        (hmeas := hmeas) (hbound := hbound) (hg := hgIntOn)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (m : ℝ)) (f := fC) hmR).2 hintOn
    have hdiff := helper_integral_interval_sub_left
      (E := ℂ) (f := fC) (a := (1 : ℝ)) (b := (n : ℝ)) (c := (m : ℝ))
      (hab := hInt_f_1n) (hac := hInt_f_1m)
    have hsub : a n - a m = ∫ u in (m : ℝ)..(n : ℝ), fC u := by
      simpa [a] using hdiff
                                                                      
    have hbound_Ioc := helper_aebound_kernel_Ioc (ε := ε) hε s hs
      (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (_hmn := hmnR)
    have hbound_Ioc_imp : ∀ᵐ t ∂(volume), t ∈ Ioc (m : ℝ) (n : ℝ) → ‖fC t‖ ≤ gR t := by
      simpa [fC, gR] using
        ((ae_restrict_iff' (μ := volume) (s := Ioc (m : ℝ) (n : ℝ)) measurableSet_Ioc).1 hbound_Ioc)
                                     
    have hgInt_mn : IntervalIntegrable gR volume (m : ℝ) (n : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (m : ℝ)) (b := (n : ℝ)) (f := gR) hmnR).2
        (helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (hmn := hmnR))
                                      
    have h1 : ‖∫ u in (m : ℝ)..(n : ℝ), fC u‖ ≤ ∫ u in (m : ℝ)..(n : ℝ), gR u := by
      simpa using
        (intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (a := (m : ℝ)) (b := (n : ℝ)) (f := fC) (g := gR)
          (hab := hmnR) (h := hbound_Ioc_imp) (hbound := hgInt_mn))
                                            
    have h3 : ∫ u in (m : ℝ)..(n : ℝ), gR u ≤ (1 / ε) * (m : ℝ) ^ (-ε) :=
      helper_integral_rpow_le (ε := ε) hε (m := (m : ℝ)) (n := (n : ℝ)) (hm := hmR) (hmn := hmnR)
              
    have : ‖∫ u in (m : ℝ)..(n : ℝ), fC u‖ ≤ (1 / ε) * (m : ℝ) ^ (-ε) :=
      le_trans h1 h3
    simpa [hsub, b] using this
                        
  have hbound : ∀ᶠ m in atTop, ∀ᶠ n in atTop, m ≤ n → ‖a n - a m‖ ≤ b m := by
    have h_m_ge1 : ∀ᶠ m in atTop, 1 ≤ m := eventually_ge_atTop 1
    refine h_m_ge1.mono ?_
    intro m hm1
    have h_n_ge_m : ∀ᶠ n in atTop, m ≤ n := eventually_ge_atTop m
    exact h_n_ge_m.mono (fun n hmn => by intro hle; exact h_tail_pointwise m n hm1 hle)
                           
  rcases helper_exists_limit_of_tail_bound a b hb_nonneg hb_tendsto hbound with ⟨I, hT⟩
                                    
  have h_eventual_bound : ∀ᶠ N in atTop, ‖a N‖ ≤ (1 / ε) := by
    have hN1 : ∀ᶠ N in atTop, 1 ≤ N := eventually_ge_atTop 1
    refine hN1.mono ?_
    intro N hNge1
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge1
                                                                      
    have hbound_Ioc := helper_aebound_kernel_Ioc (ε := ε) hε s hs (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (_hmn := h1N)
    have hbound_Ioc_imp : ∀ᵐ t ∂(volume), t ∈ Ioc (1 : ℝ) (N : ℝ) → ‖fC t‖ ≤ gR t := by
      simpa [fC, gR] using
        ((ae_restrict_iff' (μ := volume) (s := Ioc (1 : ℝ) (N : ℝ)) measurableSet_Ioc).1 hbound_Ioc)
                                     
    have hgInt_1N : IntervalIntegrable gR volume (1 : ℝ) (N : ℝ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
        (a := (1 : ℝ)) (b := (N : ℝ)) (f := gR) h1N).2
        (helper_integrableOn_rpow_neg_Ioc (ε := ε) hε (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (hmn := h1N))
                                      
    have h1 : ‖∫ u in (1 : ℝ)..(N : ℝ), fC u‖ ≤ ∫ u in (1 : ℝ)..(N : ℝ), gR u := by
      simpa [a] using
        (intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
          (a := (1 : ℝ)) (b := (N : ℝ)) (f := fC) (g := gR)
          (hab := h1N) (h := hbound_Ioc_imp) (hbound := hgInt_1N))
                                    
    have h3 : ∫ u in (1 : ℝ)..(N : ℝ), gR u ≤ (1 / ε) := by
      have := helper_integral_rpow_le (ε := ε) hε (m := (1 : ℝ)) (n := (N : ℝ)) (hm := by norm_num) (hmn := h1N)
      simpa [one_div, Real.one_rpow, one_mul] using this
    have : ‖a N‖ ≤ (1 / ε) := by exact le_trans h1 h3
    exact this
                                              
  have hIle : ‖I‖ ≤ (1 / ε) :=
    helper_limit_norm_le_of_eventual_bound (a := a) (l := I) (B := 1 / ε) hT h_eventual_bound
                                                   
  refine ⟨I, ?_, hIle⟩
  simpa [a, fC] using hT

lemma helper_tendsto_zetaPartialSum_to_zeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) := by
  classical
                                                                                    
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
  set h : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (-s)
                          
  have hsne : s ≠ 0 := by
    intro h0
    have : (0 : ℝ) < s.re := lt_trans (show (0 : ℝ) < 1 by norm_num) hs
    simpa [h0] using (ne_of_gt this)
                                                          
  have hsum_div : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have hgSumm : Summable g := by
    simpa [g, one_div_nat_cpow_eq_ite_cpow_neg s hsne] using hsum_div
                                                   
  have h_eq_tail : (fun n => g (n + 1)) = h := by
    funext n; simp [g, h]
  have hhSumm : Summable h := by
    have : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff (f := g) (k := 1)).2 hgSumm
    simpa [h_eq_tail] using this
                                                                         
  have hg0 : g 0 = 0 := by simp [g]
  have h_tsum_eq : (∑' n : ℕ, h n) = ∑' n : ℕ, g n := by
    have hzero_add := (Summable.tsum_eq_zero_add (f := g) hgSumm)
                                                         
    have : (∑' n : ℕ, g n) = ∑' n : ℕ, g (n + 1) := by
      simpa [hg0, add_comm] using hzero_add
    simpa [h_eq_tail] using this.symm
                                             
  have hzeta : riemannZeta s = ∑' n : ℕ, g n := by
    simpa [g] using lem_zetaLimit s hs
                                                                         
  have h_tendsto : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, h n) atTop (𝓝 (∑' n, h n)) :=
    (Summable.tendsto_sum_tsum_nat hhSumm)
                                                               
  have htsumeq : (∑' n, h n) = riemannZeta s := h_tsum_eq.trans hzeta.symm
  simpa [zetaPartialSum, htsumeq, h] using h_tendsto

lemma integrableOn_of_ae_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {g : ℝ → ℝ} {s : Set ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict s))
    (hgint : IntegrableOn g s)
    (hbound : ∀ᵐ x ∂(volume.restrict s), ‖f x‖ ≤ g x) :
    IntegrableOn f s := by
  have hg' : Integrable g (volume.restrict s) := by
    simpa [IntegrableOn] using hgint
  have hf' : Integrable f (volume.restrict s) :=
    MeasureTheory.Integrable.mono' (μ := volume.restrict s) hg' hfm hbound
  simpa [IntegrableOn] using hf'

lemma kernel_aestronglyMeasurable_on_Ioi (s : ℂ) (a : ℝ) :
  AEStronglyMeasurable (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (volume.restrict (Ioi a)) := by
                                                                                                           
  have hmeas_fract : Measurable (fun u : ℝ => (Int.fract u : ℝ)) := by
    simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
  have hmeas_fractC : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) :=
    hmeas_fract.complex_ofReal
  have hmeas_cpow : Measurable (fun u : ℝ => (u : ℂ) ^ (-s - 1)) := by
    have hmeas_ofReal : Measurable (fun u : ℝ => (u : ℂ)) := Complex.measurable_ofReal
    simpa using hmeas_ofReal.pow_const (-s - 1)
  have hmeas : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) :=
    hmeas_fractC.mul hmeas_cpow
                                                                                                  
  simpa using hmeas.aestronglyMeasurable

lemma kernel_ae_bound_on_Ioi (s : ℂ) :
  ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
    ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                                                          
  let p : ℝ → Prop := fun u => ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1)
                             
  have hAll : ∀ u ∈ Ioi (1 : ℝ), p u := by
    intro u hu
    have hu' : (1 : ℝ) ≤ u := le_of_lt hu
    dsimp [p]
    simpa using (lem_integrandBound u hu' s)
                                                          
  have hAE : ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → p u :=
    MeasureTheory.ae_of_all _ hAll
                                                              
  have hiff :
      (∀ᵐ u ∂volume.restrict (Ioi (1 : ℝ)), p u) ↔ ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → p u :=
    (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Ioi (1 : ℝ)) (p := p)) measurableSet_Ioi
  exact hiff.mpr hAE

lemma helper_intervalIntegral_tendstoIoi_kernel (s : ℂ) (hs : 1 < s.re) :
  Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
    (𝓝 (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) := by
                                                                    
  have hfm : AEStronglyMeasurable (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))
      (volume.restrict (Ioi (1 : ℝ))) := by
    simpa using kernel_aestronglyMeasurable_on_Ioi (s := s) (a := (1 : ℝ))
  have hbound' : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖(Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ ≤ u ^ (-s.re - 1) := by
                                                                      
    simpa using kernel_ae_bound_on_Ioi (s := s)
  have hlt : (-s.re - 1) < (-1 : ℝ) := by linarith
  have hpos : 0 < (1 : ℝ) := by norm_num
  have hgint : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Ioi (1 : ℝ)) := by
    simpa using integrableOn_Ioi_rpow_of_lt (a := (-s.re - 1)) (c := (1 : ℝ)) hlt hpos
  have hint : IntegrableOn (fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (Ioi (1 : ℝ)) := by
                              
    exact integrableOn_of_ae_bound (s := Ioi (1 : ℝ)) hfm hgint hbound'
                                                   
  have hb : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  simpa using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := volume)
      (f := fun u : ℝ => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) (a := (1 : ℝ))
      (b := fun N : ℕ => (N : ℝ)) hint hb)

lemma helper_zetaNfinal (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  simpa using (lem_zetaNfinal s hs N hN)

lemma helper_eventually_eq_from_zetaNfinal (s : ℂ) (hs : s ≠ 1) :
  ∀ᶠ N in atTop,
    zetaPartialSum s N
      = (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
        - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  have hEv : ∀ᶠ N : ℕ in atTop, 1 ≤ N := Filter.eventually_ge_atTop (1 : ℕ)
  refine hEv.mono ?_
  intro N hN
  simpa using (helper_zetaNfinal s hs N hN)

lemma helper_limit_scaled_cpow (s : ℂ) (hs : 1 < s.re) (_hsne : s ≠ 1) :
  Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) := by
  have h := lem_limitTerm1 s hs
  have h' := (Filter.Tendsto.const_mul (b := (1 / (1 - s))) h)
  simpa [div_eq_mul_inv, mul_comm] using h'

lemma helper_tendsto_const_mul {f : ℕ → ℂ} {l : ℂ} (c : ℂ)
  (h : Tendsto f atTop (𝓝 l)) : Tendsto (fun n => c * f n) atTop (𝓝 (c * l)) := by
  exact h.const_mul c

lemma helper_tendsto_add {f g : ℕ → ℂ} {a b : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
  Tendsto (fun n => f n + g n) atTop (𝓝 (a + b)) := by
                                                   
  have hpair : Tendsto (fun n => (f n, g n)) atTop (𝓝 (a, b)) := by
    simpa using (hf.prodMk_nhds hg)
  have hadd : Continuous (fun p : ℂ × ℂ => p.1 + p.2) := by
    simpa using! (continuous_fst.add continuous_snd)
  simpa using! ((hadd.tendsto (a, b)).comp hpair)

lemma helper_tendsto_neg {f : ℕ → ℂ} {a : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) : Tendsto (fun n => - f n) atTop (𝓝 (-a)) := by
  simpa only [Function.comp_def] using! ((continuous_neg.tendsto a).comp hf)

lemma helper_tendsto_sub {f g : ℕ → ℂ} {a b : ℂ}
  (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
  Tendsto (fun n => f n - g n) atTop (𝓝 (a - b)) := by
  have hneg : Tendsto (fun n => - g n) atTop (𝓝 (-b)) :=
    helper_tendsto_neg (f := g) (a := b) hg
  simpa [sub_eq_add_neg] using
    helper_tendsto_add (f := f) (g := fun n => - g n) hf hneg

lemma lem_zetaFormula (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s
      = 1 + 1 / (s - 1)
        - s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) := by
  classical
                          
  have hsne : s ≠ 1 := by
    intro h
    have hlt : 1 < (1 : ℝ) := by simp [h, Complex.one_re] at hs
    exact (lt_irrefl _ ) hlt
                                                           
  let G : ℕ → ℂ := fun N =>
    (N : ℂ) ^ (1 - s) / (1 - s) + 1 + 1 / (s - 1)
      - s * ∫ u in (1 : ℝ)..N, (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
                                          
  have hEv : ∀ᶠ N in atTop, zetaPartialSum s N = G N := by
    simpa [G] using helper_eventually_eq_from_zetaNfinal s hsne
                                  
  have h_ps : Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) :=
    helper_tendsto_zetaPartialSum_to_zeta s hs
                                      
  have hG_to_zeta : Tendsto G atTop (𝓝 (riemannZeta s)) := by
    have hcongr := (Filter.tendsto_congr' (hl := hEv) :
      Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) ↔
      Tendsto G atTop (𝓝 (riemannZeta s)))
    exact hcongr.mp h_ps

  have hA : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) atTop (𝓝 0) :=
    helper_limit_scaled_cpow s hs hsne
                                  
  have hK : Tendsto (fun _ : ℕ => (1 : ℂ) + 1 / (s - 1)) atTop (𝓝 ((1 : ℂ) + 1 / (s - 1))) :=
    tendsto_const_nhds
                                             
  have hInt : Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) :=
    helper_intervalIntegral_tendstoIoi_kernel s hs
                           
  have hIntMul : Tendsto (fun N : ℕ => s * ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) atTop
      (𝓝 (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) :=
    helper_tendsto_const_mul (c := s) hInt
                                             
  set Aseq : ℕ → ℂ := fun N => (N : ℂ) ^ (1 - s) / (1 - s)
  set Kseq : ℕ → ℂ := fun _ => (1 : ℂ) + 1 / (s - 1)
  have hA2 : Tendsto Aseq atTop (𝓝 0) := by simpa [Aseq] using hA
  have hK2 : Tendsto Kseq atTop (𝓝 ((1 : ℂ) + 1 / (s - 1))) := by simp [Kseq]
  have hSum : Tendsto (fun N => Aseq N + Kseq N) atTop (𝓝 (0 + ((1 : ℂ) + 1 / (s - 1)))) :=
    helper_tendsto_add (hf := hA2) (hg := hK2)
  set Iseq : ℕ → ℂ := fun N => s * ∫ u in (1 : ℝ)..N,
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
  have hIseq : Tendsto Iseq atTop (𝓝 (s * ∫ u in Ioi (1 : ℝ),
      (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))) := by
    simpa [Iseq] using hIntMul
  have hG_limit : Tendsto G atTop
      (𝓝 ((0 + ((1 : ℂ) + 1 / (s - 1)))
        - (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)))) := by
    have hSub := helper_tendsto_sub (hf := hSum) (hg := hIseq)
                                            
    have hGdef : (fun N => (Aseq N + Kseq N) - Iseq N) = G := by
      funext N; simp [Aseq, Kseq, Iseq, G, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    simpa [hGdef]
      using hSub
                                                    
  have huniq :=
    tendsto_nhds_unique (f := G) (l := atTop)
      (a := riemannZeta s)
      (b := ((0 + ((1 : ℂ) + 1 / (s - 1)))
        - (s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1))))
      (ha := hG_to_zeta) (hb := hG_limit)
                                     
  simpa [zero_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using huniq

lemma lem_zetaanalOnnot1 : AnalyticOn ℂ riemannZeta {s : ℂ | s ≠ 1} := by
                                                                             
  have hset : {s : ℂ | s ≠ 1} = ({1} : Set ℂ)ᶜ := by
    ext z; simp
  have hopen : IsOpen ({s : ℂ | s ≠ 1}) := by
    simp [hset]
                                               
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := by
    intro z hz

    simpa using (differentiableAt_riemannZeta (by simpa [Set.mem_ofPred_eq] using hz)).differentiableWithinAt
  simpa [Complex.analyticOn_iff_differentiableOn hopen] using hdiff

lemma lem_zetaanalS : (let S := {s : ℂ | s ≠ 1}; AnalyticOn ℂ riemannZeta S) := by exact lem_zetaanalOnnot1

lemma lem_S_isOpen : (let S := {s : ℂ | s ≠ 1}; IsOpen S) := by
                                                            
  have h : {s : ℂ | s ≠ 1} = {(1 : ℂ)}ᶜ := by
    ext s; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [h]
  exact isOpen_compl_singleton

lemma lem_T_isOpen : (let S := {s : ℂ | s ≠ 1}; let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}; IsOpen T) := by
                                      
  show IsOpen {s : ℂ | s ≠ 1 ∧ 1/10 < s.re}

  apply IsOpen.and
  ·                           
    exact lem_S_isOpen
  ·                                 
                                                             
    have h_eq : {s : ℂ | 1/10 < s.re} = Complex.re ⁻¹' (Set.Ioi (1/10)) := by
      ext s
      simp [Set.mem_preimage, Set.mem_Ioi]
    rw [h_eq]
    exact Complex.continuous_re.isOpen_preimage (Set.Ioi (1/10)) isOpen_Ioi

lemma T_eq_inter_S_half (S T : Set ℂ) (_hS : S = {s : ℂ | s ≠ 1}) (hT : T = {s : ℂ | s ∈ S ∧ (1/10 : ℝ) < s.re}) :
  T = S ∩ {s : ℂ | (1/10 : ℝ) < s.re} := by
  classical
  ext z
  simp [hT, Set.inter_def]

lemma inter_compl_singleton_eq_diff {α : Type*} [DecidableEq α] (A : Set α) (x : α) :
  A ∩ ({x} : Set α)ᶜ = A \ ({x} : Set α) := by
  ext z; simp [Set.mem_inter_iff, Set.mem_singleton_iff]

lemma isPathConnected_punctured_halfplane_re_gt (a : ℝ) (p : ℂ) (hp : a < p.re) :
  IsPathConnected ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) := by
  classical
                                                                 
  let S1 : Set ℂ := {z : ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ := {z : ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ := {z : ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ := {z : ℂ | p.re < z.re}
                            
  have hS1conv : Convex ℝ S1 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.im < p.im} := convex_halfSpace_im_lt (r := p.im)
    simpa [S1, Set.ofPred_and] using h1.inter h2
  have hS2conv : Convex ℝ S2 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.re < p.re} := convex_halfSpace_re_lt (r := p.re)
    simpa [S2, Set.ofPred_and] using h1.inter h2
  have hS3conv : Convex ℝ S3 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | p.im < z.im} := convex_halfSpace_im_gt (r := p.im)
    simpa [S3, Set.ofPred_and] using h1.inter h2
  have hS4conv : Convex ℝ S4 := by
    simpa [S4] using (convex_halfSpace_re_gt (r := p.re))
                    
  have hS1ne : S1.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im := by linarith
    simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS2ne : S2.Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im : ℝ) * Complex.I, ?_⟩
    have h1 : a < (a + p.re) / 2 := by linarith
    have h2 : (a + p.re) / 2 < p.re := by linarith
    simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS3ne : S3.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im + 1) := by linarith
    simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS4ne : S4.Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (0 : ℝ) * Complex.I, ?_⟩
    have : p.re < p.re + 1 := by linarith
    simp [S4, Complex.add_re]
                           
  have hS1pc : IsPathConnected S1 := (hS1conv.isPathConnected hS1ne)
  have hS2pc : IsPathConnected S2 := (hS2conv.isPathConnected hS2ne)
  have hS3pc : IsPathConnected S3 := (hS3conv.isPathConnected hS3ne)
  have hS4pc : IsPathConnected S4 := (hS4conv.isPathConnected hS4ne)
                          
  let A : Set ℂ := S1 ∪ S2
  let B : Set ℂ := S3 ∪ S4
                               
  have hS1S2_int : (S1 ∩ S2).Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im - (1/2)) * Complex.I, ?_⟩
    have h1a : a < (a + p.re) / 2 := by linarith
    have h1b : (p.im - (1/2)) < p.im := by linarith
    have h2a : a < (a + p.re) / 2 := by linarith
    have h2b : (a + p.re) / 2 < p.re := by linarith
    constructor
    ·         
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1a h1b
    ·         
      simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h2a h2b
  have hApc : IsPathConnected A :=
    IsPathConnected.union (U := S1) (V := S2) hS1pc hS2pc (by
      rcases hS1S2_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hS3S4_int : (S3 ∩ S4).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h3a : a < p.re + 1 := lt_trans hp (by linarith)
    have h3b : p.im < p.im + 1 := by linarith
    have h4 : p.re < p.re + 1 := by linarith
    constructor
    ·         
      simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h3a h3b
    ·         
      simp [S4, Complex.add_re, Complex.mul_re]
  have hBpc : IsPathConnected B :=
    IsPathConnected.union (U := S3) (V := S4) hS3pc hS4pc (by
      rcases hS3S4_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
                      
  have hABint : (A ∩ B).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    constructor
    ·               
      refine Or.inl ?_
      have h1 : a < p.re + 1 := lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im := by linarith
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1 h2
    ·               
      refine Or.inr ?_
      have h4 : p.re < p.re + 1 := by linarith
      simp [S4, Complex.add_re, Complex.mul_re]
                                      
  have hUnionPC : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U := A) (V := B) hApc hBpc (by
      rcases hABint with ⟨z, hz⟩; exact ⟨z, hz⟩)
                                                 
  have hcover : ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH, hznot⟩
                            
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      ·                        
        exact Or.inl (Or.inr ⟨hzH, hlt⟩)
      ·                                             
        rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        ·                    
          exact Or.inl (Or.inl ⟨hzH, himlt⟩)
        ·                                                
          have hz_eq : z = p := by
                                              
            have hzdecomp : (z.re : ℂ) + (z.im : ℝ) * Complex.I = z := by
              simp
            have hpdecomp : (p.re : ℂ) + (p.im : ℝ) * Complex.I = p := by
              simp
            have : (z.re : ℂ) + (z.im : ℝ) * Complex.I = (p.re : ℂ) + (p.im : ℝ) * Complex.I := by
                                            
              simp [heq, himeq]
                                
            simpa [hzdecomp, hpdecomp] using this
          have : z ∈ ({p} : Set ℂ) := by simp [Set.mem_singleton_iff, hz_eq]
          exact (hznot this).elim
        ·                    
          exact Or.inr (Or.inl ⟨hzH, himgt⟩)
      ·                         
        exact Or.inr (Or.inr hgt)
    · intro hz
                        
      have hzH : a < z.re := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have hzneq : z ≠ p := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          ·             
            intro h
            have : z.im = p.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS1.2
            exact lt_irrefl _ this
          ·             
            intro h
            have : z.re = p.re := by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          ·             
            intro h
            have : p.im = z.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS3.2
            exact lt_irrefl _ this
          ·             
            intro h
            have : p.re = z.re := by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact hzneq (by simpa [Set.mem_singleton_iff] using hzmem))
             
  simpa [hcover] using hUnionPC

lemma lem_T_isPreconnected : (let S := {s : ℂ | s ≠ 1}; let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}; IsPreconnected T) := by
  classical
                              
  let S : Set ℂ := {s : ℂ | s ≠ 1}
  let T : Set ℂ := {s : ℂ | s ∈ S ∧ (1/10 : ℝ) < s.re}
                                 
  have hTinter : T = S ∩ {s : ℂ | (1/10 : ℝ) < s.re} := by
    simpa using (T_eq_inter_S_half S T (by rfl) (by rfl))
                                       
  have hScompl : S = ({(1 : ℂ)} : Set ℂ)ᶜ := by
    ext z; simp [S]
                                            
  have hTdiff : T = {s : ℂ | (1/10 : ℝ) < s.re} \ (({(1 : ℂ)} : Set ℂ)) := by
    have : T = {s : ℂ | (1/10 : ℝ) < s.re} ∩ S := by
      simpa [Set.inter_comm] using hTinter
                                                                    
    simpa [hScompl, inter_compl_singleton_eq_diff] using this
                     
  have hp : (1/10 : ℝ) < (1 : ℂ).re := by
    simpa using (by norm_num : (1/10 : ℝ) < (1 : ℝ))
                                               
  have hpc : IsPathConnected ({z : ℂ | (1/10 : ℝ) < z.re} \ (({(1 : ℂ)} : Set ℂ))) :=
    isPathConnected_punctured_halfplane_re_gt (a := (1/10 : ℝ)) (p := (1 : ℂ)) (hp := hp)
                                              
  have hpcT : IsPathConnected T := by
    simpa [hTdiff] using hpc
                                                         
  have hconnT : IsConnected T := hpcT.isConnected
  exact (IsConnected.isPreconnected (s := T) hconnT)

lemma aestronglyMeasurable_kernel_param_deriv (z : ℂ) :
  AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1))) (volume.restrict (Ioi (1 : ℝ))) := by
                                                                  
  let μ := volume.restrict (Ioi (1 : ℝ))
                                                                                                 
  have hmeas_logR : Measurable (fun u : ℝ => Real.log u) := Real.measurable_log
  have hmeas_logC : Measurable (fun u : ℝ => ((Real.log u) : ℂ)) := hmeas_logR.complex_ofReal
  have hmeas_neg : Measurable (fun u : ℝ => -((Real.log u) : ℂ)) := hmeas_logC.neg
  have h1 : AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ)) μ := by
    simpa [μ] using hmeas_neg.aestronglyMeasurable
                                                                                 
  have h2 : AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) μ := by
    simpa [μ] using kernel_aestronglyMeasurable_on_Ioi (s := z) (a := (1 : ℝ))
                                      
  have hmul : AEStronglyMeasurable
      (fun u : ℝ => (-((Real.log u) : ℂ)) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)))
      μ := (MeasureTheory.AEStronglyMeasurable.mul h1 h2)
  simpa [μ] using hmul

lemma kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
  ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖ ≤ Real.log u * u ^ (-1 - ε) := by
                                       
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
                                                                  
  have hinner1 : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ ≤ u ^ (-x.re - 1) := by
    simpa using (lem_integrandBound u hu1 x)
  have hexp_le : -x.re - 1 ≤ -1 - ε := by linarith
  have hmono : u ^ (-x.re - 1) ≤ u ^ (-1 - ε) :=
    Real.rpow_le_rpow_of_exponent_le hu1 hexp_le
  have hinner : ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ ≤ u ^ (-1 - ε) :=
    le_trans hinner1 hmono
                      
  have hmul : ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖
      = ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ := by
    simp
  have hnorm_nonneg : 0 ≤ ‖-((Real.log u) : ℂ)‖ := by simp
  have hmul_le : ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖
      ≤ ‖-((Real.log u) : ℂ)‖ * (u ^ (-1 - ε)) := by
    exact mul_le_mul_of_nonneg_left hinner hnorm_nonneg
                                                                  
  have hlognorm_neg : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
             
  calc
    ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1))‖
        = ‖-((Real.log u) : ℂ)‖ * ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-x - 1)‖ := hmul
    _ ≤ ‖-((Real.log u) : ℂ)‖ * (u ^ (-1 - ε)) := hmul_le
    _ = (Real.log u) * u ^ (-1 - ε) := by simp [hlognorm_neg, mul_comm]

lemma exists_radius_ball_two_step_subset_halfspace (s : ℂ) {ε : ℝ} (hε : ε < s.re) :
  ∃ δ > 0, ∀ x, dist x s < δ → ∀ y, dist y x < δ → ε ≤ y.re := by
                                  
  set δ : ℝ := (s.re - ε) / 2 with hδdef
  have hpos : 0 < s.re - ε := sub_pos.mpr hε
  have hδpos : 0 < δ := by simpa [hδdef] using (half_pos hpos)
  refine ⟨δ, hδpos, ?_⟩
  intro x hx y hy
                                                                           
  have htri : dist y s ≤ dist y x + dist x s := by
    simpa using (dist_triangle y x s)
  have hsumlt : dist y x + dist x s < δ + δ := add_lt_add hy hx
  have hnorm_lt : ‖y - s‖ < δ + δ := by
    have := lt_of_le_of_lt htri hsumlt
    simpa [dist_eq_norm] using this
  have hdeltaSum : δ + δ = s.re - ε := by
    simp [hδdef, add_halves]
  have hnorm_lt_re : ‖y - s‖ < s.re - ε := by simpa [hdeltaSum] using hnorm_lt
                                  
  have h_eps_lt : ε < s.re - ‖y - s‖ := by
    have hsum' : ε + ‖y - s‖ < s.re := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
        (add_lt_add_right hnorm_lt_re ε)
    simpa [lt_sub_iff_add_lt] using hsum'
                                       
  have hre_abs : |(y - s).re| ≤ ‖y - s‖ := by
    simpa using (Complex.abs_re_le_norm (y - s))
  have hre_lower : -‖y - s‖ ≤ (y - s).re := by
                                                  
    have hpair := (abs_le.mp hre_abs)
    exact hpair.left
  have hyge : s.re - ‖y - s‖ ≤ y.re := by
    have h' : s.re + (-‖y - s‖) ≤ s.re + (y - s).re := add_le_add_right hre_lower s.re
    have h'' : s.re + (y - s).re = y.re := by
      simp [sub_eq_add_neg]
    simpa [sub_eq_add_neg, h''] using h'
                                            
  have hygt : ε < y.re := lt_of_lt_of_le h_eps_lt hyge
  exact le_of_lt hygt

lemma integrable_kernel_at_param (s : ℂ) (hs : 0 < s.re) :
  Integrable ((fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))) (volume.restrict (Ioi (1 : ℝ))) := by
  classical
                                                
  set f : ℝ → ℂ := fun u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
  set ε : ℝ := s.re / 2
  set g1 : ℝ → ℝ := fun u => u ^ (-s.re - 1)
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
                                           
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [f] using kernel_aestronglyMeasurable_on_Ioi (s := s) (a := (1 : ℝ))
                       
  have hε : 0 < ε := by
    have : 0 < s.re := hs
    simpa [ε] using (half_pos this)
  have hεle : ε ≤ s.re := by
    have hnonneg : 0 ≤ s.re := le_of_lt hs
    simpa [ε] using (half_le_self hnonneg)
                                            
  have hbound1 : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖f u‖ ≤ g1 u := by
    simpa [f, g1] using (kernel_ae_bound_on_Ioi (s := s))
                                             
  have hpow_ae : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), g1 u ≤ g u := by
                                      
    have hAll : ∀ u ∈ Ioi (1 : ℝ), g1 u ≤ g u := by
      intro u hu
      have hx : (1 : ℝ) ≤ u := le_of_lt hu
      have hlexp : (-s.re - 1) ≤ (-1 - ε) := by linarith
      have := Real.rpow_le_rpow_of_exponent_le hx hlexp
      simpa [g1, g] using this
                                           
    have hAE : ∀ᵐ u ∂volume, u ∈ Ioi (1 : ℝ) → g1 u ≤ g u :=
      MeasureTheory.ae_of_all _ hAll
    have hiff :=
      (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Ioi (1 : ℝ))
        (p := fun u => g1 u ≤ g u) measurableSet_Ioi)
    exact hiff.mpr hAE
                   
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖f u‖ ≤ g u := by
    filter_upwards [hbound1, hpow_ae] with u hu1 hu2
    exact le_trans hu1 hu2
                                               
  have hgint : IntegrableOn g (Ioi (1 : ℝ)) := by
    have ha_lt : (-1 - ε) < (-1 : ℝ) := by linarith
    have hc : 0 < (1 : ℝ) := by norm_num
    simpa [g] using (integrableOn_Ioi_rpow_of_lt (a := (-1 - ε)) (ha := ha_lt) (c := (1 : ℝ)) (hc := hc))
                                        
  have hint : IntegrableOn f (Ioi (1 : ℝ)) :=
    integrableOn_of_ae_bound (s := Ioi (1 : ℝ)) (f := f) (g := g)
      (hfm := hfm) (hgint := hgint) (hbound := hbound)
  simpa [IntegrableOn, f] using hint

lemma eventually_aestronglyMeasurable_kernel_param (s : ℂ) :
  ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) (volume.restrict (Ioi (1 : ℝ))) := by
  refine Filter.Eventually.of_forall ?_
  intro z
                                
  have hmeas_fract : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ)) := by
    have hmeas_fr : Measurable (Int.fract : ℝ → ℝ) := by
      simpa using (measurable_fract : Measurable (Int.fract : ℝ → ℝ))
    exact (Complex.measurable_ofReal.comp hmeas_fr)
  have hmeas_cpow : Measurable (fun u : ℝ => (u : ℂ) ^ (-z - 1)) := by
                                                                                
    measurability
  have hmeas : Measurable (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) :=
    hmeas_fract.mul hmeas_cpow
  simpa using hmeas.aestronglyMeasurable

lemma hasDerivAt_kernel_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
  HasDerivAt (fun w : ℂ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1))
    ( -((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)) ) z := by
                       
  set c0 : ℂ := ((Int.fract u : ℝ) : ℂ)
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hux0 : (u : ℝ) ≠ 0 := ne_of_gt hu0
  have hcz : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hux0
                                      
  have hfneg : HasDerivAt (fun w : ℂ => -w) (-1) z := (hasDerivAt_id z).neg
  have hf : HasDerivAt (fun w : ℂ => -w - 1) (-1) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfneg.sub_const (1 : ℂ)
                                         
  have hbase : HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-w - 1))
      ((u : ℂ) ^ (-z - 1) * Complex.log (u : ℂ) * (-1)) z :=
    HasDerivAt.const_cpow (c := (u : ℂ)) (hf := hf) (h0 := Or.inl hcz)
  have hbase' : HasDerivAt (fun w : ℂ => (u : ℂ) ^ (-w - 1))
      (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1)) z := by
                        
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
                            
  have hmul : HasDerivAt (fun w : ℂ => c0 * ((u : ℂ) ^ (-w - 1)))
      (c0 * (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1))) z :=
    HasDerivAt.const_mul c0 hbase'
                                             
  have hlog : (Real.log u : ℂ) = Complex.log (u : ℂ) := by
    simpa using (Complex.ofReal_log (x := u) (hx := le_of_lt hu0))
                        
  simpa [c0, hlog, mul_comm, mul_left_comm, mul_assoc] using hmul

lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ)
  (hbound_int : Integrable bound (MeasureTheory.volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, HasDerivAt (fun w => F w u) (F' z u) z)
  :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
                                                                                                 
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume.restrict (Ioi (1 : ℝ)))
      (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (hs := Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint)
      (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int)
      (h_diff := hderiv)
  rcases h with ⟨_hint, hDeriv⟩
                                                                                 
  simpa using hDeriv

lemma analyticAt_of_eventually_differentiableAt {f : ℂ → ℂ} {s : ℂ}
  (h : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ f z) : AnalyticAt ℂ f s := by
  simpa using
    (Complex.analyticAt_iff_eventually_differentiableAt (f := f) (c := s)).2 h

lemma lem_integralAnalytic (s : ℂ) (hs : 1/10 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
  classical
                                                            
  have hspos : 0 < s.re := lt_trans (by norm_num : (0 : ℝ) < 1/10) hs
  set ε : ℝ := s.re / 2 with hεdef
  have hεpos : 0 < ε := by simpa [ε] using (half_pos hspos)
  have hεlt : ε < s.re := by
    have : s.re / 2 < s.re := by simpa [ε] using (half_lt_self hspos)
    simpa [ε] using this
                                                                        
  rcases exists_radius_ball_two_step_subset_halfspace (s := s) (ε := ε) hεlt with ⟨δ, hδpos, hδprop⟩
                                                            
  let F : ℂ → ℝ → ℂ := fun z u => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1)
  let F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
                                                 
  let bound : ℝ → ℝ := fun u => (2/ε) * u ^ (-1 - (ε/2))
                                                     
  have hbound_int : Integrable bound (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
    have hlt : (-1 - (ε/2)) < (-1 : ℝ) := by
      have : 0 < ε/2 := by simpa using (half_pos hεpos)
      linarith
    have hpos1 : 0 < (1 : ℝ) := by norm_num
    have hpow_int : IntegrableOn (fun u : ℝ => u ^ (-1 - (ε/2))) (Ioi (1 : ℝ)) := by
      simpa using (integrableOn_Ioi_rpow_of_lt (a := (-1 - (ε/2))) hlt (c := (1 : ℝ)) hpos1)
    have hconst : IntegrableOn (fun u : ℝ => (2/ε) * u ^ (-1 - (ε/2))) (Ioi (1 : ℝ)) :=
      hpow_int.const_mul (2/ε)
    simpa [IntegrableOn, bound] using hconst
                                                                                  
  have hDiff_eventually : ∀ᶠ z in 𝓝 s,
      DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
                                              
    have hball : Metric.ball s (δ/2) ∈ 𝓝 s := Metric.ball_mem_nhds _ (by simpa using (half_pos hδpos))
    refine Filter.eventually_of_mem hball ?_
    intro z hz
                                                                                            
    have hz_lt_δ : dist z s < δ := lt_trans (by simpa [Metric.mem_ball] using hz) (by simpa using (half_lt_self hδpos))
    have hRe_inner : ∀ y, y ∈ Metric.ball z (δ/2) → ε ≤ y.re := by
      intro y hy
      have hy_lt_δ : dist y z < δ := lt_trans (by simpa [Metric.mem_ball] using hy) (by simpa using (half_lt_self hδpos))
      exact hδprop z hz_lt_δ y hy_lt_δ
                                              
    have hmeas_z : ∀ᶠ w in 𝓝 z,
        AEStronglyMeasurable (F w) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) :=
      eventually_aestronglyMeasurable_kernel_param (s := z)
                                                                     
    have hzRe_ge : ε ≤ z.re := by
                                                      
      have hss : dist s s < δ := by simpa [dist_self] using hδpos
      have hz_lt_δ' : dist z s < δ := hz_lt_δ
      exact hδprop s hss z hz_lt_δ'
    have hzpos : 0 < z.re := lt_of_lt_of_le hεpos hzRe_ge
    have hFint_z : Integrable (F z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F] using integrable_kernel_at_param (s := z) hzpos
                                      
    have hF'meas_z : AEStronglyMeasurable (F' z) (MeasureTheory.volume.restrict (Ioi (1 : ℝ))) := by
      simpa [F, F'] using aestronglyMeasurable_kernel_param_deriv (z := z)
                                                       
    have hbound_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u := by
                                                                                           
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u := by
        intro u hu w hw
        have hu1 : 1 < u := hu
        have hu0 : 0 < u := lt_trans zero_lt_one hu1
                                                             
        have hwRe : ε ≤ w.re := hRe_inner w hw
        have hker : ‖-((Real.log u) : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1))‖
              ≤ Real.log u * u ^ (-1 - ε) :=
          kernel_deriv_norm_bound_on_ball (ε := ε) (u := u) (hu := hu1) (x := w) (hx := hwRe)
        have hF'le : ‖F' w u‖ ≤ Real.log u * u ^ (-1 - ε) := by
          simpa [F, F', mul_comm, mul_left_comm, mul_assoc] using hker
                                                    
        have hx' := Real.add_one_le_exp ((ε/2) * Real.log u)
        have hx : 1 + (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) := by
          simpa [add_comm] using hx'
        have hsub : (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) - 1 := by
          have := sub_le_sub_right hx 1
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        have hle_exp : (ε/2) * Real.log u ≤ Real.exp ((ε/2) * Real.log u) := by
          have hnonneg : 0 ≤ (1 : ℝ) := by norm_num
          have : Real.exp ((ε/2) * Real.log u) - 1 ≤ Real.exp ((ε/2) * Real.log u) :=
            sub_le_self _ hnonneg
          exact le_trans hsub this
        have hεne : (ε : ℝ) ≠ 0 := ne_of_gt hεpos
        have hpos_inv : 0 < ε⁻¹ := inv_pos.mpr hεpos
        have hpos_coeff : 0 < (2/ε) := by
          have : 0 < (2 : ℝ) := by norm_num
          simpa [one_div, div_eq_mul_inv] using (mul_pos this hpos_inv)
        have hlog_bound : Real.log u ≤ (2/ε) * Real.exp ((ε/2) * Real.log u) := by
          have hmul := mul_le_mul_of_nonneg_left hle_exp (le_of_lt hpos_coeff)
                                            
          have hleft : (2/ε) * ((ε/2) * Real.log u) = Real.log u := by
            have h2ne : (2 : ℝ) ≠ 0 := by norm_num
            calc
              (2/ε) * ((ε/2) * Real.log u)
                  = ((2/ε) * (ε/2)) * Real.log u := by ring
              _ = ((2 * ε⁻¹) * (ε * (2)⁻¹)) * Real.log u := by simp [div_eq_mul_inv]
              _ = ((2 * (2)⁻¹) * (ε⁻¹ * ε)) * Real.log u := by ring
              _ = (1 * 1) * Real.log u := by simp [hεne, h2ne]
              _ = Real.log u := by simp
          simpa [hleft]
            using hmul
                                                
        have hexp_rpow : Real.exp ((ε/2) * Real.log u) = u ^ (ε/2) := by
          have : 0 < u := hu0
          simp [Real.rpow_def_of_pos this, mul_comm]
                                                 
        have hmul : Real.log u * u ^ (-1 - ε)
              ≤ ((2/ε) * u ^ (ε/2)) * u ^ (-1 - ε) := by
          have hqpos : 0 < u ^ (-1 - ε) := Real.rpow_pos_of_pos hu0 _
          have hq : 0 ≤ u ^ (-1 - ε) := le_of_lt hqpos
          exact mul_le_mul_of_nonneg_right (by simpa [hexp_rpow] using hlog_bound) hq
                                                                    
        have hpow_mul : u ^ (ε/2) * u ^ (-1 - ε) = u ^ (-1 - (ε/2)) := by
          have hu0' : 0 < u := hu0
          have h1 : Real.exp ((ε/2) * Real.log u) * Real.exp ((-1 - ε) * Real.log u)
              = Real.exp (((ε/2) * Real.log u) + ((-1 - ε) * Real.log u)) := by
            simpa using (Real.exp_add ((ε/2) * Real.log u) ((-1 - ε) * Real.log u)).symm
          calc
            u ^ (ε/2) * u ^ (-1 - ε)
                = Real.exp ((ε/2) * Real.log u) * Real.exp ((-1 - ε) * Real.log u) := by
                    simp [Real.rpow_def_of_pos hu0', mul_comm]
            _ = Real.exp (((ε/2) * Real.log u) + ((-1 - ε) * Real.log u)) := by
                    simpa using h1
            _ = Real.exp (((ε/2) + (-1 - ε)) * Real.log u) := by
                    ring_nf
            _ = u ^ (-1 - (ε/2)) := by
                    have : (ε/2) + (-1 - ε) = -1 - (ε/2) := by ring
                    simp [this, Real.rpow_def_of_pos hu0', mul_comm]
        have hmul' : ((2/ε) * u ^ (ε/2)) * u ^ (-1 - ε) = (2/ε) * u ^ (-1 - (ε/2)) := by
          simp [mul_assoc, hpow_mul]
                      
        have : ‖F' w u‖ ≤ bound u := by
          refine le_trans hF'le ?_
          simpa [bound, hmul'] using hmul
        simpa [F, F', bound]
          using this
                                             
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2), ‖F' w u‖ ≤ bound u) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
                                                                           
    have hderiv_z : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Ioi (1 : ℝ))),
        ∀ w ∈ Metric.ball z (δ/2), HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
                                                  
      have hAll : ∀ u ∈ Ioi (1 : ℝ), ∀ w ∈ Metric.ball z (δ/2),
          HasDerivAt (fun w0 => F w0 u) (F' w u) w := by
        intro u hu w hw
        simpa [F, F', mul_comm, mul_left_comm, mul_assoc]
          using hasDerivAt_kernel_in_param (u := u) (hu := hu) (z := w)
                                             
      have hiff :=
        (MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) (s := Ioi (1 : ℝ))
          (p := fun u : ℝ => ∀ w ∈ Metric.ball z (δ/2),
            HasDerivAt (fun w0 => F w0 u) (F' w u) w) measurableSet_Ioi)
      exact hiff.mpr (MeasureTheory.ae_of_all _ hAll)
                                                                         
    have hD := hasDerivAt_integral_param_dominated_Ioi
      (F := F) (F' := F') (s := z) (δ := δ/2) (hδ := by simpa using (half_pos hδpos))
      (hmeas := hmeas_z) (hFint := hFint_z) (hF'meas := hF'meas_z)
      (bound := bound) (hbound_int := hbound_int) (hbound := hbound_z) (hderiv := hderiv_z)
                                      
    simpa using hD.differentiableAt
                                                               
  exact analyticAt_of_eventually_differentiableAt hDiff_eventually

lemma lem_zetaFormulaAC :
    (let S := {s : ℂ | s ≠ 1}
     let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}
     let F := fun z : ℂ =>
       z / (z - 1)
       - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)
     AnalyticOn ℂ F T) := by
                                    
  simp only [AnalyticOn]
  intro s hs
  simp at hs
  obtain ⟨hs_ne_1, hs_re⟩ := hs

  apply AnalyticAt.analyticWithinAt

  have h1 : AnalyticAt ℂ (fun z => z / (z - 1)) s := by
    apply AnalyticAt.div
    · exact analyticAt_id
    · exact analyticAt_id.sub analyticAt_const
    ·                             
      rw [sub_ne_zero]
      exact hs_ne_1

  have hs_re_eq : (10 : ℝ)⁻¹ = (1 : ℝ) / 10 := by norm_num
  have hs_re_correct : (1 : ℝ) / 10 < s.re := by rwa [← hs_re_eq]

  have hconv := lem_integralConvergence (1/10) (by norm_num) s (le_of_lt hs_re_correct)

  obtain ⟨I, hI_tendsto, hI_bound⟩ := hconv

  have hI_bound_10 : ‖I‖ ≤ 10 := by
    convert (preTransparency := .instances) hI_bound
    norm_num

  have h_integral : AnalyticAt ℂ (fun z => ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
    apply lem_integralAnalytic s hs_re_correct

  have h2 : AnalyticAt ℂ (fun z => z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) s := by
    exact analyticAt_id.mul h_integral

  exact h1.sub h2

lemma lem_div_eq_one_plus_one_div (z : ℂ) (hz : z ≠ 1) : z / (z - 1) = 1 + 1 / (z - 1) := by
  have h : z - 1 ≠ 0 := by
    intro h0
    have : z = 1 := by
      rw [sub_eq_zero] at h0
      exact h0
    exact hz this
  calc z / (z - 1)
    = ((z - 1) + 1) / (z - 1) := by ring_nf
    _ = (z - 1) / (z - 1) + 1 / (z - 1) := by rw [add_div]
    _ = 1 + 1 / (z - 1) := by simp [div_self h]

lemma lem_zetaAnalyticContinuation :
    (let S := {s : ℂ | s ≠ 1}
     let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}
     ∀ s ∈ T,
       riemannZeta s
         = 1 + 1 / (s - 1)
           - s * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)) := by
                              
  simp only [Set.mem_ofPred_eq]
  intro s h_s
                          
  have hs_ne_1 : s ≠ 1 := h_s.1
  have hs_re : 1/10 < s.re := h_s.2

  let F := fun z : ℂ => 1 + 1 / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)

  let S := {s : ℂ | s ≠ 1}
  let T := {s : ℂ | s ∈ S ∧ 1/10 < s.re}

  have hs_in_T : s ∈ T := by
    simp only [T, S, Set.mem_ofPred_eq]
    exact ⟨hs_ne_1, hs_re⟩

  have h_T_open := lem_T_isOpen
  have h_T_preconnected := lem_T_isPreconnected

  have h_zeta_analytic_S := lem_zetaanalS
  have h_zeta_analytic_T : AnalyticOn ℂ riemannZeta T := by
    apply AnalyticOn.mono h_zeta_analytic_S
    intro x hx; exact hx.1
  have h_zeta_analyticOnNhd_T : AnalyticOnNhd ℂ riemannZeta T := by
    rwa [← h_T_open.analyticOn_iff_analyticOnNhd]

  have h_F_orig_analytic := lem_zetaFormulaAC
                                                                                 
  have h_F_eq : EqOn F (fun z => z / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1)) T := by
    intro z hz
    simp only [F]
    rw [lem_div_eq_one_plus_one_div z hz.1]

  have h_F_analytic_T : AnalyticOn ℂ F T :=
    AnalyticOn.congr h_F_orig_analytic h_F_eq
  have h_F_analyticOnNhd_T : AnalyticOnNhd ℂ F T := by
    rwa [← h_T_open.analyticOn_iff_analyticOnNhd]

  have ⟨s₀, hs₀_T, hs₀_re⟩ : ∃ s₀, s₀ ∈ T ∧ 1 < s₀.re := by
    use 2
    constructor
    · simp only [T, S, Set.mem_ofPred_eq]
      norm_num
    · norm_num

  have h_eventually_eq : riemannZeta =ᶠ[𝓝 s₀] F := by
                                                                                 
    have h_re_cont : ContinuousAt Complex.re s₀ := Complex.continuous_re.continuousAt
    have h_nhd_re : ∀ᶠ s in 𝓝 s₀, 1 < s.re :=
      ContinuousAt.eventually_lt continuousAt_const h_re_cont hs₀_re
                                            
    have h_nhd_T : ∀ᶠ s in 𝓝 s₀, s ∈ T := h_T_open.mem_nhds hs₀_T

    filter_upwards [h_nhd_re, h_nhd_T] with w hw_re hw_T
                                            
    have h_formula := lem_zetaFormula w hw_re
    simp only [F]
    exact h_formula

  have h_eqOn_global := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    h_zeta_analyticOnNhd_T h_F_analyticOnNhd_T h_T_preconnected hs₀_T h_eventually_eq

  exact h_eqOn_global hs_in_T

lemma lem_zetaBound1 (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)‖ := by
  classical
  set S : Set ℂ := {z : ℂ | z ≠ 1}
  set T : Set ℂ := {z : ℂ | z ∈ S ∧ 1/10 < z.re}
  set Iint : ℂ := ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1)
  have hT : s ∈ T := by
    have hsS : s ∈ S := by simpa [S, Set.mem_ofPred_eq] using hs_ne
    simpa [T, Set.mem_ofPred_eq] using And.intro hsS hs_re
  have hAC : ∀ z ∈ T, riemannZeta z = 1 + 1 / (z - 1) - z * ∫ u in Ioi (1 : ℝ), (Int.fract u : ℝ) * (u : ℂ) ^ (-z - 1) := by
    simpa [S, T] using lem_zetaAnalyticContinuation
  have hzeta : riemannZeta s = 1 + 1 / (s - 1) - s * Iint := by
    simpa [Iint] using hAC s hT
  have h1 : ‖riemannZeta s‖ ≤ ‖1 + 1 / (s - 1)‖ + ‖-s * Iint‖ := by
    simpa [hzeta, sub_eq_add_neg] using (lem_triangleInequality_add (1 + 1 / (s - 1)) (-s * Iint))
  have hA : ‖1 + 1 / (s - 1)‖ ≤ ‖(1 : ℂ)‖ + ‖1 / (s - 1)‖ := by
    simpa using (lem_triangleInequality_add (1 : ℂ) (1 / (s - 1)))
  have hmul : ‖-s * Iint‖ = ‖-s‖ * ‖Iint‖ := by
    simp
  have hB : ‖-s * Iint‖ ≤ ‖s‖ * ‖Iint‖ := by
    have : ‖-s * Iint‖ = ‖s‖ * ‖Iint‖ := by simp
    exact this.le
  have h2 : ‖riemannZeta s‖ ≤ (‖(1 : ℂ)‖ + ‖1 / (s - 1)‖) + (‖s‖ * ‖Iint‖) :=
    le_trans h1 (add_le_add hA hB)
  have h1norm : ‖(1 : ℂ)‖ = 1 := by simp
  simpa [Iint, h1norm, add_comm, add_left_comm, add_assoc] using h2

lemma lem_integralBoundValue (s : ℂ) (hs : 0 < s.re) : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = 1 / s.re := by
  have ha : (-s.re - 1) < -1 := by linarith
  have hc : 0 < (1 : ℝ) := by exact zero_lt_one
  have h := integral_Ioi_rpow_of_lt (a := (-s.re - 1)) ha (c := (1 : ℝ)) hc
  have h' : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = - (1 : ℝ) ^ (-s.re) / (-s.re) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1)
        = - (1 : ℝ) ^ (-s.re) / (-s.re) := h'
    _ = - (1 : ℝ) / (-s.re) := by simp [Real.one_rpow]
    _ = 1 / s.re := by simp

lemma lem_zetaBound2 (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
                                            
  set f : ℝ → ℂ := fun u => (Int.fract u : ℝ) * (u : ℂ) ^ (-s - 1) with hfdef
  set g : ℝ → ℝ := fun u => u ^ (-s.re - 1) with hgdef
                               
  have hζ : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖ := by
    simpa [hfdef] using lem_zetaBound1 s hs_re hs_ne
                                               
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioi (1 : ℝ))
                                   
  have h_ae_bound : ∀ᵐ u ∂μ, ‖f u‖ ≤ g u := by
    have hforall : ∀ u ∈ Ioi (1 : ℝ), ‖f u‖ ≤ g u := by
      intro u hu
      have := lem_integrandBound u (le_of_lt hu) s
      simpa [hfdef, hgdef] using this
    have hmeas : MeasurableSet (Ioi (1 : ℝ)) := measurableSet_Ioi
    simpa [μ] using
      (MeasureTheory.ae_restrict_of_forall_mem (μ := volume) (s := Ioi (1 : ℝ)) hmeas hforall)
                                                                               
  have hg_intOn : IntegrableOn g (Ioi (1 : ℝ)) := by
    classical
    by_contra hnot
    have hnot' : ¬ Integrable g μ := by simpa [μ, IntegrableOn] using hnot
    have hint0 : (∫ u, g u ∂μ) = 0 := by
      simpa using (integral_undef (μ := μ) (f := g) hnot')
    have hval : ∫ u in Ioi (1 : ℝ), g u = 1 / s.re := by
      simpa [hgdef] using lem_integralBoundValue s (by linarith [hs_re])
    have hne : (1 / s.re) ≠ 0 := by exact one_div_ne_zero (ne_of_gt (by linarith [hs_re]))
    have : (∫ u in Ioi (1 : ℝ), g u) = 0 := by simpa [μ] using hint0
    exact hne (by simpa [hval] using this)
  have hg_int : Integrable g μ := by simpa [μ, IntegrableOn] using hg_intOn
                                                             
  have h_int_bound : ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ ∫ u in Ioi (1 : ℝ), g u := by
    have :=
      (MeasureTheory.norm_integral_le_of_norm_le (μ := μ) (f := f) (g := g) hg_int h_ae_bound)
    simpa [μ] using this
                                                                      
  have h_g_val : ∫ u in Ioi (1 : ℝ), g u = 1 / s.re := by
    simpa [hgdef] using lem_integralBoundValue s (by linarith [hs_re])
  have h_int_bound_conc : ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ 1 / s.re := by
    simpa [h_g_val] using h_int_bound
                        
  have hmul : ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖ ≤ ‖s‖ * (1 / s.re) := by
    exact mul_le_mul_of_nonneg_left h_int_bound_conc (by exact norm_nonneg s)
                        
  have hsum0 : (1 + ‖1 / (s - 1)‖) + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖
      ≤ (1 + ‖1 / (s - 1)‖) + ‖s‖ * (1 / s.re) := by
    exact add_le_add_right hmul (1 + ‖1 / (s - 1)‖)
  have hsum : 1 + ‖1 / (s - 1)‖ + ‖s‖ * ‖∫ u in Ioi (1 : ℝ), f u‖
      ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * (1 / s.re) := by
    simpa [add_assoc] using hsum0
                                                          
  have hfinal1 : ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ * (1 / s.re) :=
    le_trans hζ hsum
  simpa [div_eq_mul_inv] using hfinal1

lemma lem_sOverSminus1Bound (s : ℂ) (_hs : s ≠ 1) : ‖(1 / (s - 1))‖ = 1 / ‖s - 1‖ := by simp [one_div]

lemma lem_zetaBound3 (s : ℂ) (hs_re : 1/10 < s.re) (hs_ne : s ≠ 1) : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
  simpa [lem_sOverSminus1Bound s hs_ne] using lem_zetaBound2 s hs_re hs_ne

lemma helper_normsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simpa [Complex.normSq, pow_two] using (Complex.normSq_eq_norm_sq z).symm

lemma helper_three_abs_sq (t : ℝ) : (3 : ℝ) ^ 2 + t ^ 2 ≤ (3 + |t|) ^ 2 := by
  have hnonneg : 0 ≤ (6 : ℝ) * |t| := by
    have h6 : (0 : ℝ) ≤ 6 := by norm_num
    exact mul_nonneg h6 (abs_nonneg t)
  have hmul : |t| * |t| = t * t := by
    simp
  calc
    (3 : ℝ) ^ 2 + t ^ 2 = (3 : ℝ) ^ 2 + t * t := by simp [pow_two]
    _ = (3 : ℝ) ^ 2 + |t| * |t| := by simp [hmul]
    _ ≤ (3 : ℝ) ^ 2 + |t| * |t| + (6 : ℝ) * |t| := by exact le_add_of_nonneg_right hnonneg
    _ = (3 + |t|) ^ 2 := by ring

lemma lem_sBound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) : ‖s‖ < (3 : ℝ) + |s.im| := by
  have hnegthree_lt_re : (- (3 : ℝ)) < s.re := by
    have hlt : (- (3 : ℝ)) < (1 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le hlt hs.1
  have hlt3 : s.re < (3 : ℝ) := hs.2
  have h_re_sq_lt : s.re ^ 2 < (3 : ℝ) ^ 2 := by
    simpa using (sq_lt_sq' hnegthree_lt_re hlt3)
  have hsumlt : s.re ^ 2 + s.im ^ 2 < (3 : ℝ) ^ 2 + s.im ^ 2 := by
    exact add_lt_add_left h_re_sq_lt _
  have hsq : ‖s‖ ^ 2 < (3 + |s.im|) ^ 2 := by
    have h := lt_of_lt_of_le hsumlt (helper_three_abs_sq s.im)
    simpa [helper_normsq s] using h
  have hnormnn : 0 ≤ ‖s‖ := norm_nonneg _
  have hpos : 0 ≤ (3 : ℝ) + |s.im| := add_nonneg (by norm_num) (abs_nonneg _)
  exact (sq_lt_sq₀ hnormnn hpos).1 hsq

lemma lem_invReSbound (s : ℂ) (hs : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) :
    1 / s.re ≤ (2 : ℝ) := by
  have h_pos : (0 : ℝ) < s.re := by
    linarith [hs.1]
  have h_half_pos : (0 : ℝ) < (1/2 : ℝ) := by norm_num
  have h_recip : 1 / s.re ≤ 1 / (1/2 : ℝ) := one_div_le_one_div_of_le h_half_pos hs.1
  have h_simplify : 1 / (1/2 : ℝ) = (2 : ℝ) := by norm_num
  rw [h_simplify] at h_recip
  exact h_recip

lemma lem_invSminus1bound (s : ℂ) (_hs_re : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : (1 : ℝ) ≤ ‖s - 1‖ := by
  have h2 : |s.im| ≤ ‖s - 1‖ := by
    have : (s - (1 : ℂ)).im = s.im := by
      simp [Complex.sub_im, Complex.one_im]
    simpa [this] using Complex.abs_im_le_norm (s - 1)
  exact le_trans hs_im h2

lemma reciprocal_le_one_of_one_le {x : ℝ} (hx_pos : 0 < x) (hx_ge : 1 ≤ x) : 1 / x ≤ 1 := by
                                                            
  have h_div_pos : 0 < 1 / x := one_div_pos.mpr hx_pos
                                     
  have h1 : (1 / x) * 1 ≤ (1 / x) * x := by
    exact mul_le_mul_of_nonneg_left hx_ge (le_of_lt h_div_pos)
                                                
  rw [mul_one] at h1
  rw [one_div_mul_cancel (ne_of_gt hx_pos)] at h1
  exact h1

lemma div_le_mul_of_one_div_le {a c d : ℝ} (ha : 0 ≤ a) (_hc : 0 < c) (h : 1 / c ≤ d) : a / c ≤ a * d := by
                                 
  rw [div_eq_mul_one_div]
                                                                  
  exact mul_le_mul_of_nonneg_left h ha

lemma lem_finalBoundCombination (s : ℂ) (hs_re : (1/2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) (hs_im : (1 : ℝ) ≤ |s.im|) : ‖riemannZeta s‖ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by
                                                                                   
  have hs_ne : s ≠ 1 := by
    intro h
    rw [h] at hs_im
    simp at hs_im
    linarith
                                  
  have hs_re_pos : 0 < s.re := by linarith [hs_re.1]
                                               
  have h1 : ‖riemannZeta s‖ ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := lem_zetaBound3 s (by linarith [hs_re_pos]) hs_ne
                                                   
  have h2 : (1 : ℝ) ≤ ‖s - 1‖ := lem_invSminus1bound s hs_re hs_im
  have h3 : 1 / ‖s - 1‖ ≤ 1 := reciprocal_le_one_of_one_le (by linarith [h2]) h2
                                             
  have h4 : ‖s‖ < (3 : ℝ) + |s.im| := lem_sBound s hs_re
                                            
  have h5 : 1 / s.re ≤ (2 : ℝ) := lem_invReSbound s hs_re
                                  
  calc ‖riemannZeta s‖
    ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := h1
    _ ≤ 1 + 1 + ‖s‖ / s.re := by linarith [h3]
    _ ≤ 1 + 1 + ‖s‖ * 2 := by
      have s_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
      exact add_le_add_right (div_le_mul_of_one_div_le s_nonneg hs_re_pos h5) _
    _ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by linarith [h4]

lemma lem_finalAlgebra (t : ℝ) : 1 + 1 + ((3 : ℝ) + |t|) * 2 = (8 : ℝ) + 2 * |t| := by ring

lemma lem_zetaUppBd (z : ℂ) (hz_re : z.re ∈ Ico (1/2 : ℝ) (3 : ℝ)) (hz_im : (1 : ℝ) ≤ |z.im|) : ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| := by
  have hz_re' : (1/2 : ℝ) ≤ z.re ∧ z.re < (3 : ℝ) := by
    simpa [Ico] using hz_re
  have h := lem_finalBoundCombination z hz_re' hz_im
  simpa [lem_finalAlgebra] using h

lemma lem_abs_im_bound (s : ℂ) (t : ℝ) (hs : ‖s‖ ≤ 1) : |s.im + t| ≤ 1 + |t| := by
  have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ 1 := le_trans h1 hs
  have h3 : |s.im + t| ≤ |s.im| + |t| := abs_add_le s.im t
  linarith

open Metric _root_.Set _root_.Filter _root_.Asymptotics BigOperators

noncomputable def logDerivZeta (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

lemma zetadiffAtnot1 : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ riemannZeta s :=
  fun _ => differentiableAt_riemannZeta

lemma sigmageq1 (s : ℂ) (hs : s.re > 1) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

lemma fc_analytic_normalized (c : ℂ) (f : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0) :
    (AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (closedBall (0 : ℂ) 1)) ∧ (fun z => f (z + c) / f c) 0 = 1 := by
  constructor
  ·                                  
    apply AnalyticOnNhd.div
    ·                                                  
      apply AnalyticOnNhd.comp h_analytic
      ·                          
        intro z _
        exact analyticAt_id.add analyticAt_const
      ·                                                    
        intro z hz
        rw [mem_closedBall] at hz ⊢
        rw [Complex.dist_eq] at hz ⊢
                                                   
        convert (preTransparency := .instances) hz using 1
        all_goals try with_reducible_and_instances rfl
        ring_nf
    ·                                          
      exact analyticOnNhd_const
    ·                           
      intro z _
      exact h_nonzero
  ·                                              
    simpa using h_nonzero

lemma frac_cancel_const {x y c : ℂ} (hc : c ≠ 0) (hy : y ≠ 0) : (x / c) / (y / c) = x / y := by
  field_simp [hc, hy]

lemma fc_bound (B : ℝ) (_hB : B > 1) (R : ℝ) (_hRpos : 0 < R) (_hR : R < 1) (c : ℂ) (f : ℂ → ℂ) (_h_nonzero : f c ≠ 0)
    (h_bound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ := by
  intro z hz
  have hz' : ‖z‖ ≤ R := by
    simpa [mem_closedBall, Complex.dist_eq] using hz
  have hz_plus : z + c ∈ closedBall c R := by
    have : ‖(z + c) - c‖ ≤ R := by simpa [add_sub_cancel] using hz'
    simpa [mem_closedBall, Complex.dist_eq] using this
  have hfb : ‖f (z + c)‖ ≤ B := h_bound (z + c) hz_plus
  have hnorm : ‖f (z + c) / f c‖ = ‖f (z + c)‖ / ‖f c‖ := by
    simp [div_eq_mul_inv, norm_inv]
  have : ‖f (z + c)‖ / ‖f c‖ ≤ B / ‖f c‖ :=
    div_le_div_of_nonneg_right hfb (norm_nonneg _)
  simpa [hnorm] using this

lemma analyticOrderAt_mul_const_eq (f : ℂ → ℂ) (a z0 : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z => f z * a) z0 = analyticOrderAt f z0 := by
  classical
                                                             
  have hcomm : (fun z => f z * a) = (fun z => a * f z) := by
    funext z; simp [mul_comm]
  have hrew : analyticOrderAt (fun z => f z * a) z0 =
      analyticOrderAt (fun z => a * f z) z0 := by
    simp [hcomm]
  by_cases hf : AnalyticAt ℂ f z0
  ·                                                                        
    have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0)
    have hadd : analyticOrderAt (fun z => a * f z) z0
        = analyticOrderAt (fun _ : ℂ => a) z0 + analyticOrderAt f z0 := by
      simpa using! (analyticOrderAt_mul hconst hf)
                                          
    have hconst_zero : analyticOrderAt (fun _ : ℂ => a) z0 = 0 := by
      have hiff := (AnalyticAt.analyticOrderAt_eq_zero hconst)
      have hval : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
      exact hiff.mpr hval
    calc
      analyticOrderAt (fun z => f z * a) z0
          = analyticOrderAt (fun z => a * f z) z0 := hrew
      _ = analyticOrderAt (fun _ : ℂ => a) z0 + analyticOrderAt f z0 := hadd
      _ = 0 + analyticOrderAt f z0 := by simp [hconst_zero]
      _ = analyticOrderAt f z0 := by simp
  ·                                                               
    have hnot : ¬ AnalyticAt ℂ (fun z => a * f z) z0 := by
      intro hmul
      have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
        simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0)
      have hval : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
                                                                
      have hiff := (analyticAt_iff_analytic_fun_smul (h₁f := hconst) (h₂f := hval)
                        (g := f) (z := z0))
      have hsmul : AnalyticAt ℂ (fun z => (fun _ : ℂ => a) z • f z) z0 := by
                                       
        simpa [smul_eq_mul] using hmul
      have : AnalyticAt ℂ f z0 := hiff.mpr hsmul
      exact hf this
    calc
      analyticOrderAt (fun z => f z * a) z0
          = analyticOrderAt (fun z => a * f z) z0 := hrew
      _ = 0 := by simp [analyticOrderAt, hnot]
      _ = analyticOrderAt f z0 := by simp [analyticOrderAt, hf]

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_ResidueCalcOnRectangles
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

open _root_.Complex BigOperators _root_.Nat Classical _root_.Real Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral _root_.Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)

noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (preTransparency := .instances) (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_ZetaBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open _root_.Complex Topology _root_.Filter Interval _root_.Set _root_.Asymptotics

local notation "ζ" => riemannZeta

lemma ZetaCont : ContinuousOn ζ (univ \ {1}) := by
  apply continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  apply DifferentiableAt.continuousAt (𝕜 := ℂ)
  convert (preTransparency := .instances) differentiableAt_riemannZeta ?_
  simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and] at hx
  exact hx

lemma ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  by_contra! h
  have hn (n : ℕ) := h (1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra! hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    use sub_zero (1: ℝ)▸tendsto_order.2 ⟨fun A B=>? _,fun A B=>?_⟩
    · apply (((tendsto_inv_atTop_nhds_zero_nat.comp
        (Filter.tendsto_add_atTop_nat (1))).congr (by norm_num)).const_sub 1).eventually_const_lt
          B|>.mono (hσ'_ge ·|>.trans_lt')
    · norm_num[(hσ'_le _).trans_lt, B.trans_le']

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by omega, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert (preTransparency := .instances) hζ (subseq n) using 3
    all_goals try with_reducible_and_instances rfl
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      simp_all only [ge_iff_le, one_div, tsub_le_iff_right, Function.comp_def, ofReal_zero,
        mul_zero, add_zero, norm_eq_sqrt_real_inner, Complex.inner, mul_re, conj_re, conj_im,
        mul_neg, sub_neg_eq_add, Real.one_le_sqrt, eventually_nhdsWithin_iff, mem_compl_iff,
        mem_singleton_iff]
      contrapose! h
      simp_all only [ne_eq]
      delta abs at*
      exfalso
      simp_rw [Metric.nhds_basis_ball.frequently_iff]at*
      choose! I A B using h
      choose a s using exists_seq_strictAnti_tendsto (0: ℝ)
      apply ((isCompact_closedBall _ _).isSeqCompact
        fun and=>(A _ (s.2.1 and)).le.trans (s.2.2.bddAbove_range.some_mem ⟨and, rfl⟩)).elim
      simp only [Metric.mem_ball, dist_eq_norm_sub] at A
      refine fun and ⟨a, H, S, M⟩=> ?_
      refine absurd (tendsto_nhds_unique M (tendsto_sub_nhds_zero_iff.1
        (( squeeze_zero_norm fun and=>le_of_lt (A _ (s.2.1 _) ) )
          (s.2.2.comp S.tendsto_atTop)))) fun and=>?_
      norm_num[*,Function.comp_def] at M
      have:=@riemannZeta_residue_one
      use one_ne_zero (tendsto_nhds_unique (this.comp (tendsto_nhdsWithin_iff.2
        ⟨ M,.of_forall (by norm_num[*])⟩)) ( squeeze_zero_norm ?_
          ((M.sub_const 1).norm.trans (by rw [sub_self,norm_zero]))))
      use fun and =>.trans (norm_mul_le_of_le ↑(le_rfl) (Complex.norm_def _▸Real.sqrt_le_one.mpr
        (B ↑_ (s.2.1 ↑_)).right.le)) (by rw [mul_one])

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have cont := @ZetaCont
      use isClosed_singleton.isSeqClosed
        this
        (.comp
          (cont.continuousAt.comp (eventually_ne_nhds (by field_simp; simp [ht₀])).mono
            fun and=>.intro ⟨⟩)
          (ToOneT0.trans (inf_le_left)))

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero

open _root_.ArithmeticFunction (vonMangoldt)

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_PNT4_ZeroFreeRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


lemma lem_Re1zge0 (z : ℂ) : z.re > 0 → (1 / z).re > 0 := by
  intro h
                          
  have hz_ne_zero : z ≠ 0 := by
    intro hz_eq_zero
    rw [hz_eq_zero] at h
    simp at h
                                
  rw [one_div]
                                               
  rw [Complex.inv_re]
                                                                                                     
  apply div_pos h
                             
  rwa [Complex.normSq_pos]

lemma lem_sigmage1 (sigma t : ℝ) (hsigma : sigma > 1) : riemannZeta (sigma + t * Complex.I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_le_re
  simp [Complex.add_re, Complex.mul_re, Complex.I_re]
  linarith

lemma lem_sigmale1 (sigma1 t1 : ℝ) : riemannZeta (sigma1 + t1 * Complex.I) = 0 → sigma1 ≤ 1 := by
  intro h
                                       
  by_contra h_not_le
                                                   
  push Not at h_not_le
                                                                             
  have h_nonzero := lem_sigmage1 sigma1 t1 h_not_le
                                                              
  exact h_nonzero h

lemma complex_abs_of_real (x : ℝ) : ‖(x : ℂ)‖ = abs x := by
  rw [Complex.norm_real, Real.norm_eq_abs]

lemma complex_abs_real_cast (r : ℝ) : ‖(r : ℂ)‖ = abs r := Complex.norm_real r

lemma center_eq_comm (t : ℝ) :
  ((3/2 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) = ((3/2 : ℂ) + (t : ℂ) * Complex.I) := by
  have h : (Complex.I : ℂ) * (t : ℂ) = (t : ℂ) * Complex.I := by
    simpa using mul_comm (Complex.I : ℂ) (t : ℂ)
  simp [h]

lemma log_abs_le_log_abs_add_two {t : ℝ} (ht : 2 < |t|) :
  Real.log (abs t) ≤ Real.log (abs t + 2) := by
  have hpos : 0 < |t| := lt_trans (by norm_num) ht
  have hle : |t| ≤ |t| + 2 := by nlinarith
  simpa using Real.log_le_log hpos hle

lemma norm_sub_comm' (x y : ℂ) : ‖x - y‖ = ‖y - x‖ := by
  calc
    ‖x - y‖ = ‖-(x - y)‖ := by simpa using (norm_neg (x - y)).symm
    _ = ‖y - x‖ := by simp [neg_sub]

lemma s_in_closedBall_12 (δ t : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
  ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) ∈
    Metric.closedBall ((3 / 2 : ℂ) + (t : ℝ) * Complex.I) (1 / 2) := by
                                         
  have hdiff :
      ((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)
        = ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) := by
    simp
  have hreal :
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ) = ((δ - (1 / 2 : ℝ)) : ℂ) := by
    have h' : ((1 + δ : ℝ) - (3 / 2 : ℝ)) = δ - (1 / 2 : ℝ) := by
      calc
        (1 + δ) - (3 / 2 : ℝ) = δ + 1 - (3 / 2 : ℝ) := by ac_rfl
        _ = δ + (1 - (3 / 2 : ℝ)) := by simp [add_sub_assoc]
        _ = δ + (- (1 / 2 : ℝ)) := by norm_num
        _ = δ - (1 / 2 : ℝ) := by simp [sub_eq_add_neg]
    calc
      ((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)
          = ((1 + δ : ℝ) : ℂ) - (3 / 2 : ℂ) := by
              simp [add_comm]
      _ = (↑((1 + δ : ℝ) - (3 / 2 : ℝ)) : ℂ) := by
              simp [Complex.ofReal_sub]
      _ = ((δ - (1 / 2 : ℝ)) : ℂ) := by simp [h']
  have hnormle :
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
        ≤ (1 / 2 : ℝ) := by
    calc
      ‖((1 : ℂ) + (δ : ℝ) + (t : ℝ) * Complex.I) - ((3 / 2 : ℂ) + (t : ℝ) * Complex.I)‖
          = ‖((1 : ℂ) + (δ : ℝ)) - (3 / 2 : ℂ)‖ := by simp [hdiff]
      _ = ‖((δ - (1 / 2 : ℝ)) : ℂ)‖ := by simp [hreal]
      _ = |δ - (1 / 2 : ℝ)| := by simpa using complex_abs_real_cast (δ - (1 / 2 : ℝ))
      _ ≤ 1 / 2 := by
        have hleft : - (1 / 2 : ℝ) ≤ δ - 1 / 2 := by linarith [hδ_pos]
        have hright : δ - 1 / 2 ≤ 1 / 2 := by linarith [hδ_lt]
        simpa using (abs_le.mpr ⟨hleft, hright⟩)
                                           
  simpa [Metric.mem_closedBall, Complex.dist_eq] using hnormle

lemma lem_Realsum {α : Type*} (s : Finset α) (f : α → ℂ) : (Finset.sum s f).re = Finset.sum s (fun i => (f i).re) := by
  exact Complex.re_sum s f

lemma re_ofReal_div_ge_one (a : ℝ) (z : ℂ) (ha : 1 ≤ a) (hz : 0 ≤ (1 / z).re) : ((a : ℂ) / z).re ≥ (1 / z).re := by
  have hrepr : ((a : ℂ) / z).re = a * (1 / z).re := by
    simp [div_eq_mul_inv, Complex.mul_re]
  have hmul : (1 : ℝ) * (1 / z).re ≤ a * (1 / z).re :=
    mul_le_mul_of_nonneg_right ha hz
  calc
    ((a : ℂ) / z).re = a * (1 / z).re := hrepr
    _ ≥ 1 * (1 / z).re := by exact hmul
    _ = (1 / z).re := by simp [one_mul]

lemma analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
                                                                  
  refine (Complex.analyticAt_iff_eventually_differentiableAt).2 ?_
                                                                                          
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact differentiableAt_riemannZeta hz

lemma riemannZeta_not_eventually_zero_of_ne_one {s : ℂ} (hs : s ≠ 1) :
  ¬ (∀ᶠ z in nhds s, riemannZeta z = 0) := by
  intro hEvZero
                                                                                            
  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1
                                                    
  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    ·                                   
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                                 
                                                                 
        filter_upwards [self_mem_nhdsWithin] with t ht
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta t := by
                                               
          exact differentiableAt_riemannZeta ht
        have hdiff := h1.mul h2
                                                           
        apply hdiff.congr_of_eventuallyEq
        filter_upwards [eventually_ne_nhds ht] with u hu
        simp [H, Function.update_of_ne hu]
      ·                                        
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                     
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := by
        exact differentiableAt_riemannZeta hz
      have hdiff := h1.mul h2
                                                      
      apply hdiff.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with u hu
      simp [H, Function.update_of_ne hu]
                                                                            
  have hH_analytic : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff
                                             
  have h0_analytic : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ := by
    intro z _; simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
                                                                                         
  have hEv_ne1 : ∀ᶠ z in nhds s, z ≠ 1 := eventually_ne_nhds hs
  have hEv_H0 : ∀ᶠ z in nhds s, H z = 0 := by
    filter_upwards [hEvZero, hEv_ne1] with z hz_zero hz_ne1
                                        
    have : H z = (z - 1) * riemannZeta z := by simp [H, Function.update_of_ne hz_ne1]
    simp [this, hz_zero]
                                                                              
  have hEqOn : Set.EqOn H (fun _ : ℂ => (0 : ℂ)) Set.univ := by
                           
    have hU : IsPreconnected (Set.univ : Set ℂ) := by simpa using isPreconnected_univ
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hH_analytic h0_analytic hU (by simp) hEv_H0
  have hHeq : H = fun _ : ℂ => (0 : ℂ) := by
    funext z; simpa using hEqOn (by simp : z ∈ (Set.univ : Set ℂ))
                                         
  have h2ne1 : (2 : ℂ) ≠ 1 := by norm_num
  have hH2 : H (2 : ℂ) = (2 - 1) * riemannZeta (2 : ℂ) := by
    simp [H]
  have hzeta2_ne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hprod_zero' : 0 = (2 - 1) * riemannZeta (2 : ℂ) := by
    simpa [hHeq] using hH2
  have hprod_zero : (2 - 1) * riemannZeta (2 : ℂ) = 0 := hprod_zero'.symm
  have hnonzero : (2 - 1) * riemannZeta (2 : ℂ) ≠ 0 := by
    have hcoeff : (2 : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr h2ne1
    exact mul_ne_zero hcoeff hzeta2_ne
  exact hnonzero hprod_zero

lemma analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero {f : ℂ → ℂ} {z0 : ℂ}
  (hf : AnalyticAt ℂ f z0) (hzero : f z0 = 0)
  (hnot : ¬ (∀ᶠ z in nhds z0, f z = 0)) :
  1 ≤ (analyticOrderAt f z0).toNat := by
  classical
                                                 
  have hne0 : analyticOrderAt f z0 ≠ 0 := by
    intro h0
    have hzne : f z0 ≠ 0 := (AnalyticAt.analyticOrderAt_eq_zero hf).1 h0
    exact hzne hzero
                                                                         
  have hneTop : analyticOrderAt f z0 ≠ ⊤ := by
    intro htop
    have hall : (∀ᶠ z in nhds z0, f z = 0) := (analyticOrderAt_eq_top).1 htop
    exact hnot hall
                                          
  rcases WithTop.ne_top_iff_exists.mp hneTop with ⟨n, hn⟩
                             
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hne0
                                            
    simp [hn.symm, hn0]
    rfl
                    
  have hposn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero)
                                         
  simpa [hn.symm] using! hposn

lemma absorb_pos_constant_into_log {L A c : ℝ} (hL : 1 ≤ L) (hc : 0 ≤ c) : A * L + c ≤ (A + c) * L := by
                                             
  have hc_le : c ≤ L * c := by
    have h := mul_le_mul_of_nonneg_right hL hc
    simpa [one_mul] using h
                                        
  have h0 : A * L + c ≤ A * L + L * c := by
    exact add_le_add_right hc_le (A * L)
  calc
    A * L + c ≤ A * L + L * c := h0
    _ = A * L + c * L := by simp [mul_comm]
    _ = (A + c) * L := by simp [right_distrib]

lemma neg_logDeriv_zeta_eq_vonMangoldt_sum (s : ℂ) (hs : 1 < s.re) : -(deriv riemannZeta s / riemannZeta s) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
                                                                                     
  have h1 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

  have h2 : -deriv riemannZeta s / riemannZeta s = LSeries (fun n => ↑(ArithmeticFunction.vonMangoldt n)) s := h1.symm
                                                                                                                 
  have h3 : -(deriv riemannZeta s / riemannZeta s) = -deriv riemannZeta s / riemannZeta s := by ring
  rw [h3, h2]

  rw [LSeries]
  congr 1
  ext n
  rw [LSeries.term_def]
  split_ifs with h_zero
  ·                                
    simp [h_zero]
  ·                                                                     
    rw [div_eq_mul_inv, Complex.cpow_neg]

lemma zeta1zetaseries {s : ℂ} (hs : 1 < s.re) :
-logDerivZeta s = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold logDerivZeta
                                                                                                                       
  exact neg_logDeriv_zeta_eq_vonMangoldt_sum s hs

lemma vonMangoldt_LSeriesSummable (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
                                                                            
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs

lemma summable_of_support_singleton {α : Type*} [SeminormedAddCommGroup α] (f : ℕ → α) (n₀ : ℕ) (h : ∀ n : ℕ, n ≠ n₀ → f n = 0) : Summable f := by
                                                     
  have h_finite_support : Set.Finite (Function.support f) := by
                                       
    have h_subset : Function.support f ⊆ {n₀} := by
      intro n hn

      by_contra h_ne
                                                 
      have h_zero : f n = 0 := h n h_ne
                                     
      simp [Function.mem_support] at hn
      exact hn h_zero
                                                                 
    exact Set.Finite.subset (Set.finite_singleton n₀) h_subset

  exact summable_of_hasFiniteSupport h_finite_support

lemma summable_of_summable_add_sub {α : Type*} [SeminormedAddCommGroup α] (f g h : ℕ → α) (h_eq : f = g + h) (hf : Summable f) (hh : Summable h) : Summable g := by

  have g_eq_f_sub_h : g = f - h := by
                                           
    rw [← sub_eq_iff_eq_add] at h_eq
    exact h_eq.symm

  rw [g_eq_f_sub_h]

  exact hf.sub hh

lemma LSeriesSummable_to_summable (f : ℕ → ℂ) (s : ℂ) (h : LSeriesSummable f s) : Summable (fun n => f n * (n : ℂ) ^ (-s)) := by
                                                          
  have h_term_summable : Summable (LSeries.term f s) := h

  have h_eq_nonzero : ∀ n : ℕ, n ≠ 0 → LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, Complex.cpow_neg]

  let diff := fun n => LSeries.term f s n - f n * (n : ℂ) ^ (-s)

  have h_diff_support : ∀ n : ℕ, n ≠ 0 → diff n = 0 := by
    intro n hn
    simp only [diff]
    rw [h_eq_nonzero n hn]
    simp

  have h_diff_summable : Summable diff := by
                                              
    apply summable_of_support_singleton diff 0 h_diff_support

  have h_rw : LSeries.term f s = (fun n => f n * (n : ℂ) ^ (-s)) + diff := by
    ext n
    simp only [diff, Pi.add_apply]
    ring

  exact summable_of_summable_add_sub (LSeries.term f s) (fun n => f n * (n : ℂ) ^ (-s)) diff h_rw h_term_summable h_diff_summable

lemma lem_realnx (n : ℕ) (x : ℝ) (_hn : n ≥ 1) (_hx : x ≥ 1) :
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x) ≥ 0 := by
  apply mul_nonneg
  ·                                             
    exact ArithmeticFunction.vonMangoldt_nonneg
  ·                           
    apply Real.rpow_nonneg
                       
    exact Nat.cast_nonneg n

lemma complex_cpow_neg_real (n : ℕ) (x : ℝ) (_hn : n ≥ 1) : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
                                     
  have h_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
                                   
  rw [Complex.cpow_eq_pow]
                                                   
  rw [Complex.ofReal_cpow h_nonneg (-x)]
                                          
  congr 1
                                 
  simp

lemma lem_cost0 (n : ℕ) (_hn : n ≥ 1) (t : ℝ) (ht : t = 0) : Real.cos (t * Real.log (n : ℝ)) = 1 := by
  rw [ht]
  simp

lemma tsum_nonneg_of_nonneg {f : ℕ → ℝ} (hnon : ∀ n, 0 ≤ f n) : 0 ≤ ∑' n, f n := by
  simpa using (tsum_nonneg hnon)

lemma vonMangoldt_rpow_nonneg (x : ℝ) : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) := by
  intro n
  have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ (n : ℝ) ^ (-x) := by
    exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n) _
  simpa using mul_nonneg h1 h2

lemma norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt (x : ℝ) (hx : 1 < x) :
  ‖-logDerivZeta (x : ℂ)‖ = |∑' n, ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x))| := by
                                                    
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  have hseries := zeta1zetaseries (s := (x : ℂ)) hx'
                                                                                      
  let g : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
  have hterm : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)) = (g n : ℂ) := by
    intro n
    by_cases h : n = 0
    ·                                               
      have hv0C : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
        simp
      have hv0R : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
        simp
      simp [g, h, hv0R]
    ·                                               
      have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      have hcp : (n : ℂ) ^ (-(x : ℂ)) = Complex.ofReal ((n : ℝ) ^ (-x)) :=
        complex_cpow_neg_real n x hn
                                              
      have : (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ))
              = Complex.ofReal (ArithmeticFunction.vonMangoldt n) * Complex.ofReal ((n : ℝ) ^ (-x)) := by
        simp [hcp]
      simpa [g, Complex.ofReal_mul] using this
                                                          
  have hsum_eq : (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = ∑' n, (g n : ℂ) := by
                                             
    have hfun : (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = (fun n => (g n : ℂ)) := funext hterm
    simp [hfun]
                                                                     
  have hsum_ofReal : (∑' n, (g n : ℂ)) = Complex.ofReal (∑' n, g n) := by
    simpa using (Complex.ofReal_tsum g).symm
                                                                                               
  have hval : -logDerivZeta (x : ℂ) = Complex.ofReal (∑' n, g n) := by
                                         
    simpa [hsum_eq, hsum_ofReal] using hseries
                                                                            
  calc
    ‖-logDerivZeta (x : ℂ)‖ = ‖Complex.ofReal (∑' n, g n)‖ := by simp [hval]
    _ = |∑' n, g n| := by
      exact (RCLike.norm_ofReal (K := ℂ) (∑' n, g n))

lemma tsum_le_of_nonneg_of_le {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) (_hnonneg : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ g n) : (∑' n, f n) ≤ (∑' n, g n) := by
  classical
  exact Summable.tsum_le_tsum hle hf hg

lemma rpow_neg_antitone {a x y : ℝ} (ha : 1 ≤ a) (hxy : x ≥ y) : a ^ (-x) ≤ a ^ (-y) := by

  simpa using (Real.rpow_le_rpow_of_exponent_le ha (neg_le_neg hxy))

lemma bounded_on_compact_interval (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) : ∃ Cmid ≥ 0, ∀ δ : ℝ, a ≤ δ → δ ≤ b → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid := by
                                      
  let s : Set ℝ := Set.Icc a b
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))

  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1

  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    ·                                                 
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                                           
        filter_upwards [self_mem_nhdsWithin] with t ht
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      ·                                                     
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                                        
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) z := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hz] with u hu using by
        simp [H, Function.update_of_ne hu]

  let G : ℂ → ℂ := fun z => - (deriv H z) / H z

  have h_eq_on_pos : ∀ ⦃δ : ℝ⦄, 0 < δ →
      (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) = G ((1 : ℂ) + δ) := by
    intro δ hδ
                    
    let z : ℂ := (1 : ℂ) + δ
    have hz_ne_one : z ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ : ℝ) = 1 := by
        simpa [z, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ = 0 := by linarith
      exact (ne_of_gt hδ) this
    have hzeta_ne : riemannZeta z ≠ 0 := by
      have : 1 < z.re := by simpa [z, Complex.add_re, Complex.ofReal_re] using by linarith
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt this)

    have h_id_deriv : deriv (fun u : ℂ => u - 1) z = 1 := by
      exact ((hasDerivAt_id z).sub_const 1).deriv
    have h_log_id : logDeriv (fun u : ℂ => u - 1) z = 1 / (z - 1) := by
      simp [logDeriv_apply, h_id_deriv]
    have hz1 : z - 1 ≠ 0 := by simpa using sub_ne_zero.mpr hz_ne_one
    have hζ : riemannZeta z ≠ 0 := hzeta_ne

    have h_deriv_mul : deriv (fun u : ℂ => (u - 1) * riemannZeta u) z
          = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2).deriv

    have h_prodLog :
        logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z =
          logDeriv (fun u : ℂ => u - 1) z + logDerivZeta z := by
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz_ne_one)
      have hfnz : (fun u : ℂ => u - 1) z ≠ 0 := by simpa using hz1
      have hgnz : riemannZeta z ≠ 0 := hζ
      simpa [logDerivZeta] using!
        (logDeriv_mul (x := z) (f := fun u : ℂ => u - 1) (g := riemannZeta) hfnz hgnz h1 h2)

    have h_step : -logDerivZeta z - (1 / (z - 1))
        = - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z := by
      have : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
            = 1 / (z - 1) + logDerivZeta z := by
        simpa [h_log_id, add_comm] using h_prodLog
      have hneg : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
                 = - (1 / (z - 1) + logDerivZeta z) := by
        simpa using congrArg Neg.neg this
      simpa [sub_eq_add_neg, add_comm] using hneg.symm

    have h_H_eq : H z = (z - 1) * riemannZeta z := by
      simp [H, Function.update_of_ne hz_ne_one]

    have h_eq_event : (fun u : ℂ => H u) =ᶠ[nhds z] (fun u : ℂ => (u - 1) * riemannZeta u) := by
      filter_upwards [eventually_ne_nhds hz_ne_one] with u hu
      simp [H, Function.update_of_ne hu]

    have h_hasDeriv_prod :
        HasDerivAt (fun u : ℂ => (u - 1) * riemannZeta u)
          (riemannZeta z + (z - 1) * deriv riemannZeta z) z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2)

    have h_hasDeriv_H :
        HasDerivAt H (riemannZeta z + (z - 1) * deriv riemannZeta z) z :=
      h_hasDeriv_prod.congr_of_eventuallyEq h_eq_event

    have h_dH : deriv H z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      simpa using h_hasDeriv_H.deriv

    have h_log_to_G : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = G z := by
      have h' : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = (deriv H z) / H z := by
        simp [logDeriv_apply, h_H_eq, h_dH, h_deriv_mul]
      have hneg' := congrArg (fun w => -w) h'
      simpa [G, neg_div] using hneg'

    have : -logDerivZeta z - (1 / (z - 1)) = G z := by
      simpa using h_step.trans h_log_to_G

    simpa [z] using this

  let F : ℝ → ℂ := fun δ => G ((1 : ℂ) + δ)

  have hH_analytic_univ : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff

  have hF_contOn : ContinuousOn F s := by
    intro δ0 hδ0
                           
    let s0 : ℂ := (1 : ℂ) + δ0
    have hδ0pos : 0 < δ0 := lt_of_lt_of_le h0 hδ0.1
    have hs0_ne_one : s0 ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ0 : ℝ) = 1 := by
        simpa [s0, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ0 = 0 := by linarith
      exact (ne_of_gt hδ0pos) this
    have hs0_re_gt_one : 1 < s0.re := by
      simpa [s0, Complex.add_re, Complex.ofReal_re] using by linarith
    have hζ_ne : riemannZeta s0 ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (le_of_lt hs0_re_gt_one)
    have hHs0_eq : H s0 = (s0 - 1) * riemannZeta s0 := by
      simp [H, Function.update_of_ne hs0_ne_one]
    have hHs0_ne : H s0 ≠ 0 := by
      have hs0m1_ne : s0 - 1 ≠ 0 := sub_ne_zero.mpr hs0_ne_one
      have : (s0 - 1) * riemannZeta s0 ≠ 0 := mul_ne_zero hs0m1_ne hζ_ne
      simpa [hHs0_eq] using this
                                                                                
    have hH_an_at_s0 : AnalyticAt ℂ H s0 := hH_analytic_univ s0 (by simp)
    have hH'_an_at_s0 : AnalyticAt ℂ (fun z => deriv H z) s0 := hH_an_at_s0.deriv
    have hG_an_at_s0 : AnalyticAt ℂ (fun z => G z) s0 := by
      have h_div : AnalyticAt ℂ (fun z => (deriv H z) / H z) s0 :=
        hH'_an_at_s0.div hH_an_at_s0 (by simpa using hHs0_ne)
      have h_neg : AnalyticAt ℂ (fun z => -((deriv H z) / H z)) s0 := h_div.neg
      simpa [G, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using h_neg
    have hG_cont_s0 : ContinuousAt (fun z : ℂ => G z) s0 := hG_an_at_s0.continuousAt
                                               
    let affine : ℝ → ℂ := fun δ => (1 : ℂ) + (δ : ℂ)
    have h_affine_at : ContinuousAt affine δ0 :=
      (continuousAt_const).add Complex.continuous_ofReal.continuousAt
                           
    have hy : affine δ0 = s0 := by simp [affine, s0]
    have hG_at : ContinuousAt (fun z : ℂ => G z) (affine δ0) := by simpa [hy] using hG_cont_s0
    have h_comp_at : ContinuousAt (fun δ : ℝ => G (affine δ)) δ0 := hG_at.comp h_affine_at
    simpa [F, s, affine] using h_comp_at.continuousWithinAt

  have h_eq_on_s : ∀ ⦃δ : ℝ⦄, δ ∈ s → f δ = F δ := by
    intro δ hδ
    have hδpos : 0 < δ := lt_of_lt_of_le h0 hδ.1
    simpa [f, F] using h_eq_on_pos hδpos

  have hK : IsCompact s := isCompact_Icc
  have hNorm_contOn : ContinuousOn (fun δ => ‖F δ‖) s := hF_contOn.norm
  have hBdd : BddAbove ((fun δ => ‖F δ‖) '' s) := IsCompact.bddAbove_image hK hNorm_contOn
  rcases hBdd with ⟨C, hC⟩

  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro δ hδa hδb
                                                               
  change ‖f δ‖ ≤ max C 0
  have hδmem : δ ∈ s := ⟨hδa, hδb⟩
  have himg : (fun δ => ‖F δ‖) δ ∈ (fun δ => ‖F δ‖) '' s := ⟨δ, hδmem, rfl⟩
  have hbound : ‖F δ‖ ≤ C := hC himg
  have hbound' : ‖F δ‖ ≤ max C 0 := le_trans hbound (le_max_left _ _)
                                       
  have hfδ_eq : f δ = F δ := h_eq_on_s hδmem
  calc
    ‖f δ‖ = ‖F δ‖ := by simp [hfδ_eq]
    _ ≤ max C 0 := hbound'

lemma norm_one_div_coe_real_le_one_of_one_le {δ : ℝ} (h : 1 ≤ δ) : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := by
                                                
  have hδpos : 0 < δ := lt_of_lt_of_le zero_lt_one h
  calc
    ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      exact norm_div (1 : ℂ) (δ : ℂ)
    _ = 1 / ‖(δ : ℂ)‖ := by simp
    _ = 1 / |δ| := by simp
    _ = 1 / δ := by simp [abs_of_nonneg (le_of_lt hδpos)]
    _ ≤ 1 := by
                                                           
      simpa using (one_div_le_one_div_of_le (ha := (zero_lt_one)) (h := h))

lemma lem_Lambda_pos_trig_sum (n : ℕ) (delta : ℝ) (t : ℝ) (hn : n ≥ 1) (hdelta : delta > 0) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply mul_nonneg
  ·                                                                        
    apply lem_realnx n (1 + delta) hn
                         
    linarith [hdelta]
  ·                                                                                          
    exact lem_postriglogn n hn t

lemma lem_seriespos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply tsum_nonneg
  intro n
  by_cases h : n = 0
  ·                                                            
    simp [h]
  ·                                             
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact lem_Lambda_pos_trig_sum n delta t hn hdelta

lemma log_abs_add_two_pos (t : ℝ) : 0 < Real.log (abs t + 2) := by
                                                    
  have h0 : 0 ≤ abs t + 2 := by
    have h' : 0 ≤ abs t := abs_nonneg t
    linarith
  have hge : (2 : ℝ) ≤ abs t + 2 := by
    have h' : 0 ≤ abs t := abs_nonneg t
    have := add_le_add_left h' (2 : ℝ)
    simp
  have hgt : 1 < abs t + 2 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hge
                                                                
  exact (Real.log_pos_iff h0).2 hgt

lemma pos_delta_from_C_L {C L : ℝ} (hC : 0 < C) (hL : 0 < L) : 0 < 1 / (2 * C * L) := by
  have hCL : 0 < C * L := mul_pos hC hL
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hpos : 0 < 2 * C * L := by
    have : 0 < 2 * (C * L) := mul_pos h2 hCL
    simpa [mul_assoc] using this
  exact one_div_pos.mpr hpos

lemma log_abs_two_pos (t : ℝ) : 0 < Real.log (|t| + 2) := by
  simpa using log_abs_add_two_pos t

lemma two_C_log_pos {C t : ℝ} (hC : 0 < C) : 0 < 2 * C * Real.log (|t| + 2) := by
  have hL : 0 < Real.log (|t| + 2) := log_abs_two_pos t
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hCL : 0 < C * Real.log (|t| + 2) := mul_pos hC hL
  have : 0 < 2 * (C * Real.log (|t| + 2)) := mul_pos h2 hCL
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

lemma rhs_eval_of_inv (C L δ : ℝ) (h : 1 / δ = 2 * C * L) : 3 / δ + C * L = 7 * C * L := by
  calc
    3 / δ + C * L
        = 3 * (1 / δ) + C * L := by simp [div_eq_mul_inv]
    _   = 3 * (2 * C * L) + C * L := by simp [h]
    _   = 6 * C * L + C * L := by ring
    _   = 7 * C * L := by ring

lemma div_le_to_le_mul (x y z : ℝ) (hy : 0 < y) (h : x / y ≤ z) : x ≤ z * y := by
  rwa [div_le_iff₀ hy] at h

lemma le_mul_to_le_div (x y z : ℝ) (hy : 0 < y) (h : x ≤ z * y) : x / y ≤ z := by
  rw [div_le_iff₀ hy]
  exact h

lemma reciprocal_div_inequality (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : 4 / a ≤ b) : a ≥ 4 / b := by
                                                                
  have h1 : 4 ≤ b * a := div_le_to_le_mul 4 a b ha h
                                       
  have h2 : 4 ≤ a * b := by
    rwa [mul_comm] at h1
                                                              
  have h3 : 4 / b ≤ a := le_mul_to_le_div 4 b a hb h2
                                                                           
  exact h3

lemma simplify_4_7_2 (C L : ℝ) : 4 / (7 * C * L) - 1 / (2 * C * L) = 1 / (14 * C * L) := by
                                             
  have h1 : (4 : ℝ) / (7 * (C * L)) = (4 : ℝ) / (7 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (4 : ℝ)) (b := (7 : ℝ)) (c := C * L))
  have h2 : (1 : ℝ) / (2 * (C * L)) = (1 : ℝ) / (2 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (1 : ℝ)) (b := (2 : ℝ)) (c := C * L))
                                                     
  have h3' : ((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹ = (14 : ℝ)⁻¹ := by
    have h3 : ((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (14 : ℝ) := by
      norm_num
    simpa [one_div] using h3
  calc
    4 / (7 * C * L) - 1 / (2 * C * L)
        = (4 : ℝ) / (7 * (C * L)) - (1 : ℝ) / (2 * (C * L)) := by
          simp [mul_assoc]
    _ = (4 : ℝ) / (7 : ℝ) / (C * L) - (1 : ℝ) / (2 : ℝ) / (C * L) := by
          simp [h1, h2]
    _ = (((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ))) / (C * L) := by
          simpa using (sub_div (a := ((4 : ℝ) / (7 : ℝ))) (b := ((1 : ℝ) / (2 : ℝ))) (c := C * L)).symm
    _ = (((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹) / (C * L) := by
          simp [one_div]
    _ = (14 : ℝ)⁻¹ / (C * L) := by
          simp [h3']
    _ = 1 / (14 * (C * L)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc, one_div] using
            (div_mul_eq_div_div (a := (1 : ℝ)) (b := (14 : ℝ)) (c := C * L)).symm
    _ = 1 / (14 * C * L) := by simp [mul_assoc]

lemma fraction_diff_lower_bound (C L a : ℝ) : 4 / (7 * C * L) ≤ a + 1 / (2 * C * L) → 1 / (14 * C * L) ≤ a := by
  intro h
  have h' : 4 / (7 * C * L) - 1 / (2 * C * L) ≤ a := (sub_le_iff_le_add).mpr h
  have hdiff : 1 / (14 * C * L) = 4 / (7 * C * L) - 1 / (2 * C * L) := by
    symm
    exact simplify_4_7_2 C L
  calc
    1 / (14 * C * L)
        = 4 / (7 * C * L) - 1 / (2 * C * L) := hdiff
    _ ≤ a := h'

lemma closedBall_compact_complex (c : ℂ) (r : ℝ) :
    IsCompact (Metric.closedBall c r) := by
                                                                           
  exact ProperSpace.isCompact_closedBall c r

lemma riemannZeta_no_zeros_accumulate_at_one :
  ∀ Z : Set ℂ, (∀ z ∈ Z, riemannZeta z = 0) → ¬AccPt 1 (Filter.principal Z) := by
  intro Z hZ
                           
  by_contra h_acc

  have h_residue := riemannZeta_residue_one

  rw [Metric.tendsto_nhdsWithin_nhds] at h_residue
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := h_residue (1/2) (by norm_num : (0 : ℝ) < 1/2)

  rw [accPt_iff_nhds] at h_acc

  obtain ⟨y, ⟨hy_ball, hy_Z⟩, hy_ne⟩ := h_acc (Metric.ball 1 δ) (Metric.ball_mem_nhds 1 hδ_pos)

  have hy_zero : riemannZeta y = 0 := hZ y hy_Z

  have hy_in_compl : y ∈ ({1} : Set ℂ)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hy_ne

  have hy_dist : dist y 1 < δ := hy_ball

  have h_bound := hδ_bound hy_in_compl hy_dist

  rw [hy_zero, mul_zero] at h_bound

  have h_dist_eq : dist (0 : ℂ) (1 : ℂ) = 1 := by
    rw [Complex.dist_eq]
    norm_num

  rw [h_dist_eq] at h_bound
                                                 
  norm_num at h_bound

lemma complex_minus_singleton_connected : IsPreconnected ({s : ℂ | s ≠ 1} : Set ℂ) := by
                                                                   
  have h_eq : {s : ℂ | s ≠ 1} = ({1} : Set ℂ)ᶜ := by
    ext x
    simp [Set.mem_compl_iff, Set.mem_singleton_iff]

  rw [h_eq]

  have h_rank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
                                         
    norm_num

  have h_connected := isConnected_compl_singleton_of_one_lt_rank h_rank (1 : ℂ)

  exact h_connected.isPreconnected

lemma eventually_eq_zero_implies_frequently_eq_zero_punctured (f : ℂ → ℂ) (z₀ : ℂ) :
  (∀ᶠ z in nhds z₀, f z = 0) → (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0) := by
  intro h_eventually

  have h_nebot : Filter.NeBot (nhdsWithin z₀ {z₀}ᶜ) := by
                                                                                
    exact NormedField.nhdsNE_neBot z₀

  have h_eventually_punctured : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0 := by
                                                        
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds h_eventually

  exact h_eventually_punctured.frequently

lemma complex_sub_ofReal_I_real_eq_ofReal (z : ℂ) (a t : ℝ) (him : z.im = t) :
  z - ((a : ℂ) + Complex.I * t) = ((z.re - a) : ℂ) := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
  · simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, him]

lemma lem_abszrhoReRe (z ρ : ℂ) : ‖z - ρ‖ ≥ z.re - ρ.re := by
  have h1 : (z - ρ).re ≤ ‖z - ρ‖ := Complex.re_le_norm (z - ρ)
  have h2 : (z - ρ).re = z.re - ρ.re := Complex.sub_re z ρ
  rw [← h2]
  exact h1

lemma lem_DImt2d :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| ≤ |t| + 5/6 := by
  intro t ht z hz
                                                                  
  rw [Metric.mem_closedBall] at hz
                                    
  have center_im : (3/2 + t * Complex.I).im = t := by simp [Complex.add_im, Complex.mul_im]
                                  
  have diff_im : (z - (3/2 + t * Complex.I)).im = z.im - t := by
    rw [Complex.sub_im, center_im]
                                      
  have h1 : |z.im - t| ≤ ‖z - (3/2 + t * Complex.I)‖ := by
    rw [← diff_im]
    exact Complex.abs_im_le_norm _
                                       
  have h2 : |z.im - t| ≤ 5/6 := le_trans h1 (by simpa only [dist_eq_norm] using! hz)
                                                                                            
  have h3 : |z.im| ≤ |z.im - t| + |t| := by
    conv_lhs => rw [show z.im = (z.im - t) + t by ring]
    exact abs_add_le (z.im - t) t
  linarith

lemma lem_DIMt2 :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| + 2 ≤ (|t| + 2)^3 := by
  intro t ht z hz
                                                
  have h1' := lem_DImt2d t ht z hz
                                     
  have h1a : |z.im| + 2 ≤ |t| + 17/6 := by
    simpa [show |t| + 5/6 + 2 = |t| + 17/6 by ring] using! add_le_add_left h1' 2
                                
  have h17le3 : |t| + 17/6 ≤ |t| + 3 := by
    have : (17 : ℝ) / 6 ≤ 3 := by norm_num
    exact add_le_add_right this _
                                                                    
  have h_nonneg_poly : 0 ≤ |t|^3 + 6 * |t|^2 + 11 * |t| + 5 := by
    have h0 : 0 ≤ |t|^3 := by exact pow_nonneg (abs_nonneg _) 3
    have h1 : 0 ≤ 6 * |t|^2 := by
      have : 0 ≤ (6 : ℝ) := by norm_num
      exact mul_nonneg this (sq_nonneg _)
    have h2 : 0 ≤ 11 * |t| := by
      have : 0 ≤ (11 : ℝ) := by norm_num
      exact mul_nonneg this (abs_nonneg _)
    have h3 : 0 ≤ (5 : ℝ) := by norm_num
    exact add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3
  have h_add : |t| + 3 ≤ (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    simpa using (le_add_of_nonneg_right (a := |t| + 3) h_nonneg_poly)
  have h_expand : (|t| + 2)^3 = (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    ring
  have h3 : |t| + 3 ≤ (|t| + 2)^3 := by
    simpa [h_expand] using h_add
                           
  exact le_trans (le_trans h1a h17le3) h3

lemma lem_DlogImlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    Real.log (|z.im| + 2) ≤ 3 * Real.log (|t| + 2) := by
  intro t ht z hz
                                                                           
  have h1 : |z.im| + 2 ≤ (|t| + 2)^3 := lem_DIMt2 t ht z hz
                                           
  have h2 : 0 < |z.im| + 2 := by
    have : 0 ≤ |z.im| := abs_nonneg _
    linarith
                        
  have hlog := Real.log_le_log h2 h1
                                  
  simpa [Real.log_pow] using hlog

lemma lem_D1logtlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    (1 : ℝ) / Real.log (|t| + 2) ≤ 3 / Real.log (|z.im| + 2) := by
  intro t ht z hz
  have h1 := lem_DlogImlog t ht z hz
                                                     
  have ht_pos : |t| + 2 > 1 := by linarith [abs_nonneg t]
  have hz_pos : |z.im| + 2 > 1 := by linarith [abs_nonneg z.im]
  have log_t_pos : Real.log (|t| + 2) > 0 := Real.log_pos ht_pos
  have log_z_pos : Real.log (|z.im| + 2) > 0 := Real.log_pos hz_pos

  rw [div_le_div_iff₀ log_t_pos log_z_pos]
  simp only [one_mul]
  exact h1

lemma helper_analyticOnNhd_shift_div (f : ℂ → ℂ) (c : ℂ)
    (h : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z)
    (_hc : f c ≠ 0) :
    AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (Metric.closedBall (0 : ℂ) 1) := by
                                                                                     
  intro z hz
                                                 
  have hz_norm : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
                                                                   
  have hz_addc_mem : z + c ∈ Metric.closedBall c 1 := by
                                           
    have : dist (z + c) c ≤ 1 := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz_norm
    simpa [Metric.mem_closedBall] using this
                                               
  have h_f_at : AnalyticAt ℂ f (z + c) := h (z + c) hz_addc_mem
                                               
  have h_addc : AnalyticAt ℂ (fun w => w + c) z := by
    simpa using! (analyticAt_id.add analyticAt_const)
                                                              
  have h_comp : AnalyticAt ℂ (fun w => f (w + c)) z :=
    (AnalyticAt.fun_comp h_f_at h_addc)
                                                                                            
  have h_mul_const : AnalyticAt ℂ (fun w => (1 / f c) * f (w + c)) z :=
    (analyticAt_const.mul h_comp)
                                
  simpa [div_eq_mul_inv, mul_comm] using h_mul_const

lemma helper_bound_shifted (B R : ℝ) (_hB : 1 < B) (_hRpos : 0 < R) (_hRlt1 : R < 1)
    (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
    (h_bound : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ :=
by
  intro z hz
                                            
  have hz_norm : ‖z‖ ≤ R := by
    have hz' : dist z (0 : ℂ) ≤ R := by simpa [Metric.mem_closedBall] using hz
    simpa [Complex.dist_eq] using hz'
                                 
  have hz_ballc : z + c ∈ Metric.closedBall c R := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel] using hz_norm
                                                  
  have hfb : ‖f (z + c)‖ ≤ B := h_bound (z + c) hz_ballc
                                        
  have hpos : 0 < ‖f c‖ := (norm_pos_iff).2 hc
                                   
  have hdiv : ‖f (z + c)‖ / ‖f c‖ ≤ B / ‖f c‖ := (div_le_div_iff_of_pos_right hpos).2 hfb
                                              
  have hnorm_eq : ‖(fun w => f (w + c) / f c) z‖ = ‖f (z + c)‖ / ‖f c‖ := by
    change ‖f (z + c) / f c‖ = ‖f (z + c)‖ / ‖f c‖
    simp
  simpa [hnorm_eq] using hdiv

lemma helper_g_zero_eq_one (f : ℂ → ℂ) (c : ℂ) (hc : f c ≠ 0) :
  (fun z => f (z + c) / f c) 0 = 1 := by
  simp [hc]

lemma helper_AnalyticOnNhd_to_pointwise {S : Set ℂ} {f : ℂ → ℂ}
  (h : AnalyticOnNhd ℂ f S) : ∀ z ∈ S, AnalyticAt ℂ f z := by
  intro z hz
  exact h z hz

lemma no_zero_of_bound_one_and_center_one
  (R : ℝ) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_one : g 0 = 1)
  (hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1) :
  ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 := by
  intro z hz
  by_cases hRpos : 0 < R
  ·
                                             
    have hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) := by
      intro x hx
      have hxlt : ‖x‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans (le_of_lt hxlt) (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact ((h_g_analytic x hx_in1).differentiableAt).differentiableWithinAt
                                                
    have hcont : ContinuousOn g (Metric.closedBall (0 : ℂ) R) := by
      intro x hx
      have hxleR : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans hxleR (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact (h_g_analytic x hx_in1).continuousAt.continuousWithinAt
    have hdcc : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) :=
      DiffContOnCl.mk_ball hdiff hcont
                                                               
    have hIsMax : IsMaxOn (fun z => ‖g z‖) (Metric.ball (0 : ℂ) R) 0 := by
      intro y hy
      have hynormlt : ‖y‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hy
      have hyle : ‖y‖ ≤ R := le_of_lt hynormlt
      have hgy : ‖g y‖ ≤ 1 := hg_le_one y hyle
      simpa [hg0_one] using hgy
                                                         
    have hEqOn :=
      Complex.eqOn_closedBall_of_isMaxOn_norm (z := (0 : ℂ)) (r := R) hdcc hIsMax
    have hz_eq : g z = (fun _ => g 0) z := hEqOn hz
    have hz_eq1 : g z = g 0 := by simpa using hz_eq
    have gz_one : g z = 1 := by simpa [hg0_one] using hz_eq1
    simp [gz_one]
  ·
                                                                           
    have hRle : R ≤ 0 := le_of_not_gt hRpos
    have hz_le : ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
    have hz_norm_eq : ‖z‖ = 0 :=
      le_antisymm (le_trans hz_le hRle) (norm_nonneg z)
    have hz_zero : z = 0 := by
      simpa [norm_eq_zero] using hz_norm_eq
    simp [hz_zero, hg0_one]

lemma helper_sum_over_equal_finite_sets_orders
  {S T : Set ℂ} (g : ℂ → ℂ)
  (hS : S.Finite) (hT : T.Finite) (hST : S = T) :
  (∑ x ∈ hS.toFinset, ((analyticOrderAt g x).toNat : ℝ))
  = (∑ x ∈ hT.toFinset, ((analyticOrderAt g x).toNat : ℝ)) := by
  classical
  have hF : hS.toFinset = hT.toFinset := by
    ext x
    simp [Set.Finite.mem_toFinset, hST]
  simp [hF]

lemma helper_bound_on_ball_to_norm_imp
  {R : ℝ} {g : ℂ → ℂ} {M : ℝ}
  (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ M) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ M := by
  intro z hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R := by
    have : dist z (0 : ℂ) ≤ R := by
      simpa [dist_eq_norm] using hz
    simpa [Metric.mem_closedBall] using this
  exact hg z hz'

lemma helper_pointwise_to_AnalyticOnNhd {S : Set ℂ} {f : ℂ → ℂ}
  (h : ∀ z ∈ S, AnalyticAt ℂ f z) : AnalyticOnNhd ℂ f S := by
  simpa using! h

lemma lem_term_real_nonneg (n : ℕ) (σ : ℝ) (_hσ : 1 < σ) : ∃ r ≥ (0:ℝ), ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r : ℂ) := by
                                                     
  let r : ℝ := (ArithmeticFunction.vonMangoldt n) / ((n : ℝ) ^ σ)
  refine ⟨r, ?_, ?_⟩
  ·                                                                                      
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_nonneg : 0 ≤ (n : ℝ) ^ σ := by
      simpa using (Real.rpow_nonneg hbase_nonneg σ)
                                          
    have hv_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n) := by
      simp
    have : 0 ≤ (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ σ)⁻¹ :=
      mul_nonneg hv_nonneg (inv_nonneg.mpr hden_nonneg)
    simpa [r, div_eq_mul_inv] using this
  ·                                            
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_eq : (((n : ℝ) ^ σ : ℝ) : ℂ) = (n : ℂ) ^ (σ : ℂ) := by
      simpa using (Complex.ofReal_cpow (x := (n : ℝ)) (hx := hbase_nonneg) (y := σ))
    calc
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ)))
          = ((ArithmeticFunction.vonMangoldt n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) := by
              simp [hden_eq.symm]
      _ = (((ArithmeticFunction.vonMangoldt n : ℝ) / ((n : ℝ) ^ σ)) : ℝ) := by
              simp
      _ = (r : ℂ) := by rfl

lemma lem_norm_logDeriv_le_tsum (s : ℂ) (hs : 1 < s.re) :
  ‖deriv riemannZeta s / riemannZeta s‖ ≤ ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := by
  classical
                                                      
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                                                  
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) := by
    simpa [f] using! (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs)
                                                                                
  have hsum_norm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    (summable_norm_iff).mpr hsum_term
                                                                            
  have hEq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s := by
    simpa [f] using! (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs)
                                                                                         
  have hpoint : (fun n : ℕ => ‖LSeries.term f s n‖)
                = (fun n : ℕ => ‖f n / ((n : ℂ) ^ s)‖) := by
    funext n
    by_cases h0 : n = 0
    ·                              
      subst h0
                                                
      have hf0r : ArithmeticFunction.vonMangoldt 0 = 0 := by
        simp
      have hf0 : f 0 = 0 := by simp [f, hf0r]
      simp [LSeries.term, f, hf0]
    ·                                              
      simp [LSeries.term, f, h0]
                                                      
  calc
    ‖deriv riemannZeta s / riemannZeta s‖
        = ‖- deriv riemannZeta s / riemannZeta s‖ := by simp [norm_neg]
    _ = ‖∑' n : ℕ, LSeries.term f s n‖ := by simp [hEq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ :=
          norm_tsum_le_tsum_norm (f := fun n : ℕ => LSeries.term f s n) hsum_norm
    _ = ∑' n : ℕ, ‖f n / ((n : ℂ) ^ s)‖ := by simp [hpoint]
    _ = ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := rfl

lemma lem_tsum_norm_vonMangoldt_depends_on_Re_cast (s : ℂ) (σ : ℝ)
  (hσ : σ = s.re) (hs : 1 < s.re) :
  (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
    = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
                       
  have hre_ne_zero : s.re ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  have hσ_ne_zero : σ ≠ 0 := by
    have : 0 < σ := by simpa [hσ] using (lt_trans zero_lt_one hs)
    exact ne_of_gt this
                                                                                
  have hterm : (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
      = (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n
                                                             
    have hden_s : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n hre_ne_zero
    have hden_σ : ‖(n : ℂ) ^ (σ : ℂ)‖ = (n : ℝ) ^ (σ : ℂ).re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa [Complex.ofReal_re] using hσ_ne_zero)
    calc
      ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖
          = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ s‖ := by simp
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ s.re) := by
            simp [hden_s, Complex.norm_real]
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ σ) := by simp [hσ]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ (σ : ℂ)‖ := by
            simp [hden_σ, Complex.ofReal_re, Complex.norm_real]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖ := by simp
  simpa using congrArg (fun f : ℕ → ℝ => ∑' n, f n) hterm

lemma helper_norm_neg_logDeriv_eq_tsum_norm (σ : ℝ) (hσ : 1 < σ) :
  ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ =
    (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
  classical
                                  
  let s : ℂ := (σ : ℂ)
                                                                             
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                                                     
  let u : ℕ → ℂ := fun n => LSeries.term f s n
                                                   
  have hs_re : 1 < s.re := by simpa using! hσ
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) := by
    simpa [f] using! (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs_re)
                       
  have hsum_u : Summable u := hsum_term
                                                        
  have hL_eq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs_re)
  have hsum_eq : (∑' n, u n) = - deriv riemannZeta s / riemannZeta s := by
    simpa [u] using hL_eq

  have hterm_as_div : ∀ n,
      u n = ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) := by
    intro n; by_cases h0 : n = 0
    ·         
      subst h0; simp [u, LSeries.term, f, s]
    ·         
      simp [u, LSeries.term, f, s, h0]
                                                           
  let r : ℕ → ℝ := fun n => Classical.choose (lem_term_real_nonneg n σ hσ)
  have hr_nonneg : ∀ n, 0 ≤ r n := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ hσ)).1
  have hr_cast : ∀ n,
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r n : ℂ) := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ hσ)).2
  have hr_eq' : ∀ n, u n = (r n : ℂ) := by
    intro n; simpa [hterm_as_div n] using (hr_cast n)
                                       
  have hsum_rc : Summable (fun n => (r n : ℂ)) := by
    simpa [u, hr_eq'] using hsum_u
  have hsum_r : Summable r := (Complex.summable_ofReal).1 hsum_rc
                                                         
  have hsum_u_as_real : (∑' n, u n) = ((∑' n, r n) : ℝ) := by
    have hru : (fun n => (r n : ℂ)) = u := by
      funext n; symm; exact hr_eq' n
    have := (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := r))

    simpa [hru] using this.symm
                                                             
  have hpoint_norm : (fun n : ℕ => ‖u n‖)
        = (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n; by_cases h0 : n = 0
    · subst h0; simp [u, LSeries.term, f, s]
    · simp [u, LSeries.term, f, s, h0]
  have hnorm_fun : (fun n : ℕ => ‖u n‖) = r := by
    funext n; simp [hr_eq' n, Complex.norm_real, abs_of_nonneg (hr_nonneg n)]
  have hsum_norm : Summable (fun n : ℕ => ‖u n‖) := by
    simpa [hnorm_fun] using hsum_r
                                                        
  have hineq : ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ :=
    norm_tsum_le_tsum_norm (f := u) hsum_norm
                                                  
  set S : ℝ := ∑' n, r n
  have hS_le : ‖((S : ℝ) : ℂ)‖ ≤ S := by
    simpa [S, hsum_u_as_real, hnorm_fun] using hineq
                              
  have hS_nonneg : 0 ≤ S := by
    have habs_le : |S| ≤ S := by simpa [Complex.norm_real] using hS_le
    exact (abs_nonneg S).trans habs_le
                                                
  have h_left : ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
      = ‖∑' n, u n‖ := by
    have : - deriv riemannZeta s / riemannZeta s = ∑' n, u n := by simpa [hsum_u_as_real] using hsum_eq.symm
    simp [s, this]
  have h_mid : ‖∑' n, u n‖ = S := by
                                               
    have : ‖((S : ℝ) : ℂ)‖ = S := by simp [Complex.norm_real, abs_of_nonneg hS_nonneg]
    simpa [S, hsum_u_as_real] using this
  have h_right : (∑' n : ℕ, ‖u n‖) = S := by simp [S, hnorm_fun]
                                            
  calc
    ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = ‖∑' n, u n‖ := h_left
    _ = S := h_mid
    _ = (∑' n : ℕ, ‖u n‖) := h_right.symm
    _ = (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
          simp [hpoint_norm]

theorem lem_zetacenterbd :
  ∀ t : ℝ,
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤
      ‖deriv riemannZeta σ / riemannZeta σ‖ := by
  intro t σ hσge
                   
  set s : ℂ := Complex.mk σ t
                                                  
  have hs : 1 < s.re := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
  have hσgt1 : 1 < σ := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
                                                           
  have h_le_sum := lem_norm_logDeriv_le_tsum s hs
  have h1 : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := by
    simpa [norm_div, Complex.norm_real] using h_le_sum
                                                                                       
  have h_dep :
      (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
                    
    have hre : σ = s.re := by simp [s]
    simpa using (lem_tsum_norm_vonMangoldt_depends_on_Re_cast s σ hre hs)
  have h_dep_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖)
        = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := by
    simpa [norm_div, Complex.norm_real] using h_dep
                                                            
  have h_sum_eq_norm :
      ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) :=
    helper_norm_neg_logDeriv_eq_tsum_norm σ hσgt1
  have h_sum_eq_norm_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖)
        = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    simpa [norm_div, Complex.norm_real] using h_sum_eq_norm.symm
                                      
  have h_main : ‖deriv riemannZeta s / riemannZeta s‖ ≤ ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    calc
      ‖deriv riemannZeta s / riemannZeta s‖
          ≤ (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := h1
      _ = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := h_dep_ratio
      _ = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := h_sum_eq_norm_ratio
                                                          
  simpa [s, norm_neg] using h_main

open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_SmoothExistence
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970


open _root_.MeasureTheory _root_.Set _root_.Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Erdos970_ZetaZeroFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

open _root_.Complex Topology _root_.Filter Interval _root_.Set _root_.Asymptotics
local notation "ζ" => riemannZeta

local notation "I" => Complex.I

lemma ZetaNoZerosInBox' (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  by_contra h
  push Not at h

  have hn (n : ℕ) := h (σ := 1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra hσn
    push Not at hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n + 1)) atTop (𝓝 1) := by
      simpa using! (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hσ'_ge hσ'_le

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by valid, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert (preTransparency := .instances) hζ (subseq n) using 3
    all_goals try with_reducible_and_instances rfl
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      have hprod : Tendsto (fun s : ℂ => ‖(s - 1) * ζ s‖) (𝓝[≠] 1) (𝓝 1) := by
        simpa only [norm_one] using! riemannZeta_residue_one.norm
      have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] 1) (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hdist : Tendsto (fun s : ℂ => ‖s - 1‖) (𝓝[≠] 1) (𝓝 0) := by
        simpa only [sub_self, norm_zero] using! (hid.sub_const 1).norm
      filter_upwards [hprod.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
        hdist.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with s hp hs
      by_contra h
      have hlt : ‖ζ s‖ < 1 := lt_of_not_ge h
      have hm := mul_le_mul_of_nonneg_left hlt.le (norm_nonneg (s - 1))
      rw [norm_mul] at hp
      rw [mul_one] at hm
      linarith

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have hpoint : (1 + Complex.I * t₀ : ℂ) ≠ 1 := by
        intro heq
        have him := congrArg Complex.im heq
        have htzero : t₀ = 0 := by simpa using him
        exact ht₀ htzero
      have hcont := (differentiableAt_riemannZeta hpoint).continuousAt
      have hlim : Tendsto (fun n : ℕ => ζ (σ' (subseq n) + I * t (subseq n))) atTop
          (𝓝 (ζ (1 + I * t₀))) := by
        simpa only [Function.comp_def] using!
          hcont.tendsto.comp (ToOneT0.mono_right nhdsWithin_le_nhds)
      have hfun : (fun n : ℕ => ζ (σ' (subseq n) + I * t (subseq n))) = (fun _ => 0) :=
        funext this
      rw [hfun] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero

end Erdos970
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

noncomputable def MellinInverseTransform (F : ℂ → ℂ) (σ : ℝ) (x : ℝ) : ℂ :=
  VerticalIntegral' (fun s ↦ x ^ (-s) * F s) σ

lemma MellinInverseTransform_eq (σ : ℝ) (f : ℂ → ℂ) :
    MellinInverseTransform f σ = mellinInv σ f := by
  unfold mellinInv MellinInverseTransform VerticalIntegral' VerticalIntegral
  beta_reduce; ext x
  rw [← smul_assoc, smul_eq_mul (b := Complex.I), div_mul]; simp

local notation "Λ" => vonMangoldt

theorem LogDerivativeDirichlet (s : ℂ) (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s = ∑' n, Λ n / (n : ℂ) ^ s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  dsimp [LSeries, LSeries.term]
  nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
  · simp
  · have := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    dsimp [LSeriesSummable] at this
    convert! (preTransparency := .instances) this using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    by_cases h : n = 0 <;> simp [LSeries.term, h]

open ComplexConjugate

open _root_.MeasureTheory

attribute [fun_prop] Continuous.const_cpow

lemma interval_membership (r : ℝ)(a b: ℝ)(h1 : r ∈ Set.Icc (min a b) (max a b)) (h2 : a < b) :
  a ≤ r ∧ r ≤ b := by
                                                       
  have min_eq : min a b = a := min_eq_left (le_of_lt h2)
  have max_eq : max a b = b := max_eq_right (le_of_lt h2)
  rw [min_eq, max_eq] at h1
  rw [← @mem_Icc]
  exact h1

lemma log_pow_over_xsq_integral_bounded :
  ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ T >3, ∫ x in Ioo 3 T, (Real.log x)^n / x^2 < C := by
  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]
  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3
  intro n
  induction n with
  | zero =>
    use 1
    constructor
    · norm_num
    · intro T hT
      have Tgt3 : (3 : ℝ) < T := hT
      simp only [pow_zero]
      have h1 :(0 ≤ (-2) ∨ (-2) ≠ (-1) ∧ 0 ∉ Set.uIcc 3 T) := by
        right
        constructor
        · linarith
        · refine notMem_uIcc_of_lt ?_ ?_
          · exact three_pos
          · linarith
      have integral := integral_zpow h1
      ring_nf at integral

      have swap_int_kind : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), 1 / x ^ 2 = ∫ (x : ℝ) in Ioo 3 T, 1 / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      rw [← swap_int_kind]
      have change_int_power : ∫ (x : ℝ) in (3 : ℝ)..T, (1 : ℝ) / x ^ (↑ 2)
                            = ∫ (x : ℝ) in (3 : ℝ).. T, x ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp
      rw [change_int_power, integral]
      have : T ^ (-1 : ℤ) > 0 := by
        refine zpow_pos ?_ (-1)
        linarith
      linarith
  | succ d ih =>
    obtain ⟨Cd, Cdpos, IH⟩ := ih
    use ((Real.log 3)^(d+1) / 3) + (d+1) * Cd
    constructor
    · have logpowpos : (Real.log 3) ^ (d + 1) > 0 := by
        refine pow_pos ?_ (d + 1)
        linarith
      have :  0 < (Real.log 3) ^ (d + 1) / 3 := by
        exact div_pos logpowpos (by norm_num)
      have dbound : d + 1 ≥ 1 := by
        exact Nat.le_add_left 1 d
      have : Real.log 3 ^ (d + 1) / 3 + (↑d + 1) * Cd > 0 / 3 + 0 := by
        have term1_pos : 0 < Real.log 3 ^ (d + 1) / 3 := this
        have term2_pos : 0 < (↑d + 1) * Cd := by
          refine (mul_pos_iff_of_pos_right Cdpos).mpr ?_
          exact Nat.cast_add_one_pos d
        refine add_lt_add ?_ term2_pos
        refine div_lt_div₀ logpowpos ?_ ?_ ?_
        linarith
        linarith
        linarith
      ring_nf at this
      ring_nf
      exact this
    · intro T Tgt3
      let u := fun x : ℝ ↦ (Real.log x) ^ (d + 1)
      let v := fun x : ℝ ↦ -1 / x
      let u' := fun x : ℝ ↦ (d + 1 : ℝ) * (Real.log x)^d / x
      let v' := fun x : ℝ ↦ 1 / x^2

      have swap_int_type : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2
                          = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ (d + 1) / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw [← swap_int_type]

      have uIcc_is_Icc : Set.uIcc 3 T = Set.Icc 3 T := by
        exact uIcc_of_lt Tgt3

      have cont_u : ContinuousOn u (Set.uIcc 3 T) := by
        unfold u
        rw[uIcc_is_Icc]
        refine ContinuousOn.pow ?_ (d + 1)
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        refine continuousAt_log ?_
        linarith [hx.1]

      have cont_v : ContinuousOn v (Set.uIcc 3 T) := by
        unfold v
        rw[uIcc_is_Icc]
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        have cont1 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) x := by
          refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
          · exact continuousAt_const
          · linarith [hx.1]
        have cont2 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) (-x) := by
          refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
          · exact continuousAt_const
          · linarith [hx.1]
        have fun1 : (fun (x : ℝ) ↦ -1 / x) = (fun (x : ℝ) ↦ 1 / (-x)) := by
          ext x
          ring_nf
        rw [fun1]
        exact ContinuousAt.comp cont2 (HasDerivAt.neg (hasDerivAt_id x)).continuousAt

      have deriv_u : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt u (u' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        unfold u u'
        have xne0 : x ≠ 0 := by linarith [hx.1]
        have deriv1 := Real.deriv_log x
        have deriv2 := (Real.hasDerivAt_log xne0).pow (d + 1)
        have fun1 : (fun x ↦ (↑d + 1) * Real.log x ^ d / x) = (fun x ↦ (↑d + 1) * Real.log x ^ d * x⁻¹) := by
          exact rfl
        have fun2 : (↑d + 1) * Real.log x ^ d / x =  (↑d + 1) * Real.log x ^ d * x⁻¹:= by
          exact rfl
        rw [fun2]
        simpa [Nat.cast_add, Nat.cast_one] using! deriv2

      have deriv_v : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt v (v' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        have xne0 : x ≠ 0 := by linarith [hx.1]
        unfold v v'
        have deriv1 := hasDerivAt_inv xne0
        have fun1 : (fun (x : ℝ) ↦ x⁻¹) = (fun (x : ℝ) ↦ 1 / x) := by
          ext x
          exact inv_eq_one_div x
        rw [fun1] at deriv1
        have fun2 : -(x ^ 2)⁻¹ = - 1 / x ^ 2 := by
          field_simp
        rw [fun2] at deriv1
        simpa [neg_div, neg_neg] using! HasDerivAt.neg deriv1

      have cont_u' : ContinuousOn u' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold u'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · refine ContinuousOn.mul ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.pow ?_ d
            refine continuousOn_of_forall_continuousAt ?_
            intro x hx
            refine continuousAt_log ?_
            linarith [hx.1]
        · exact continuousOn_id' (Icc 3 T)
        · intro x hx
          linarith [hx.1]

      have cont_v' : ContinuousOn v' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold v'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · exact continuousOn_const
        · exact continuousOn_pow 2
        · intro x hx
          refine pow_ne_zero 2 ?_
          linarith [hx.1]

      have int_u': IntervalIntegrable u' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_u'

      have int_v': IntervalIntegrable v' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_v'

      have IBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt cont_u cont_v deriv_u deriv_v int_u' int_v'

      unfold u u' v v' at IBP

      have int1 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) * (1 / x ^ 2)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2 := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          field_simp

      rw[int1] at IBP
      rw[IBP]

      have int2 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = -(↑d + 1) * ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2 := by
        have : ∀ x, (↑d + 1) * Real.log x ^ d / x * (-1 / x)
         = -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          intro x
          field_simp
        have : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          exact intervalIntegral.integral_congr fun ⦃x⦄ a ↦ this x
        rw [this]
        rw [←intervalIntegral.integral_const_mul]
        ring_nf

      rw[int2]

      have int3 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2
                = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw[int3]

      have IHbound : ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := by
        exact IH T Tgt3

      ring_nf
      have bound2 : (Real.log T * Real.log T ^ d * T⁻¹) ≥ 0 := by
        have logTpos : Real.log T ≥ 0 := by
          refine log_nonneg ?_
          linarith
        apply mul_nonneg
        · apply mul_nonneg
          · exact logTpos
          · exact pow_nonneg logTpos d
        · positivity

      have bound3 : -(Real.log T * Real.log T ^ d * T⁻¹) ≤ 0 := by
        exact Right.neg_nonpos_iff.mpr bound2
      let S := Real.log T * Real.log T ^ d * T⁻¹
      have Spos : S ≥ 0 := by
        unfold S
        exact bound2

      have : (-(Real.log T * Real.log T ^ d * T⁻¹) + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 = (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        unfold S
        rfl
      rw [this]

      have GetRidOfS : (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2
                      ≤ ( Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        linarith [Spos]
      apply lt_of_le_of_lt GetRidOfS
      rw [add_assoc]

      have bound4 : ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := IHbound

      have bound5 : ↑d * ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 ≤ ↑d * Cd := by
        apply (mul_le_mul_of_nonneg_left bound4.le)
        exact Nat.cast_nonneg d

      have bound_sum : ↑d * (∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2)
                       + ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < ↑d * Cd + Cd := by
        linarith [bound4, bound5]
      rw[add_assoc]
      apply add_lt_add_right
      field_simp
      linarith [bound_sum]

open _root_.Filter Topology

end Erdos970
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

abbrev EvenState := {s : ℝ // 198 / 100 ≤ s}
abbrev OddState := {s : ℝ // 95 / 100 ≤ s}

end NumberTheoryLean.TransitionKernels

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Paths_FiniteHistorySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePathGeometry

open Set
open TransitionKernels

inductive Side | even | odd deriving DecidableEq

noncomputable def cost (t : ℝ) : ℝ := Real.log (1 + 1 / t)

end NumberTheoryLean.FinitePathGeometry



namespace NumberTheoryLean.FinitePathMeasures

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry

abbrev State := EvenState ⊕ OddState
abbrev CostState := State × ℝ

def stateRatio : State → ℝ := Sum.elim Subtype.val Subtype.val

end NumberTheoryLean.FinitePathMeasures



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_FirstHitKernels
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FirstHitKernels

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open FinitePathMeasures

def regenerationStateSet : Set State :=
  fun z => Sum.elim (fun _ : TransitionKernels.EvenState => False)
    (fun s : TransitionKernels.OddState => s.1 ≤ 3) z

def regenerationSet : Set CostState := Prod.fst ⁻¹' regenerationStateSet

@[simp] theorem regeneration_even (s : TransitionKernels.EvenState) (T : ℝ) :
    (.inl s, T) ∉ regenerationSet := by change ¬False; exact not_false

@[simp] theorem regeneration_odd (s : TransitionKernels.OddState) (T : ℝ) :
    (.inr s, T) ∈ regenerationSet ↔ s.1 ≤ 3 := Iff.rfl

end NumberTheoryLean.FirstHitKernels

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

namespace NumberTheoryLean.PairedCostProcess

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures

abbrev OddCost := OddState × ℝ

end NumberTheoryLean.PairedCostProcess

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

open Set MeasureTheory ProbabilityTheory
namespace Erdos970Dependency.RawStateCost
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures

noncomputable def stateCost (s : State) : ℝ := cost (stateRatio s)

end Erdos970Dependency.RawStateCost

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ReducedFractions
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open Set
open scoped BigOperators

namespace AdditiveLargeSieve

def reducedFractions (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q) ×ˢ Finset.range Q).filter fun z => z.2 < z.1 ∧ z.2.Coprime z.1

@[simp] theorem mem_reducedFractions {Q : ℕ} {z : ℕ × ℕ} :
    z ∈ reducedFractions Q ↔ 1 ≤ z.1 ∧ z.1 ≤ Q ∧ z.2 < z.1 ∧ z.2.Coprime z.1 := by
  simp only [reducedFractions, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨hq, hQ⟩, _⟩, ha, hc⟩
    exact ⟨hq, hQ, ha, hc⟩
  · rintro ⟨hq, hQ, ha, hc⟩
    exact ⟨⟨⟨hq, hQ⟩, ha.trans_le hQ⟩, ha, hc⟩

noncomputable def fractionValue (z : ℕ × ℕ) : ℝ := (z.2 : ℝ) / z.1

end AdditiveLargeSieve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RepresentativeAdmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.RepresentativeAdmission

open FinitePathGeometry

noncomputable def representativeGap (rep : ℕ → ℝ) (r : ℝ) (ps : List ℕ) : ℝ :=
  r-(ps.map rep).sum

end NumberTheoryLean.RepresentativeAdmission

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_FourierDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate

namespace AdditiveLargeSieve

noncomputable def monomial (n : ℤ) (x : ℝ) : ℂ := fourier n (x : AddCircle (1 : ℝ))
noncomputable def polynomial (s : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ s, b n * monomial n x

end AdditiveLargeSieve

end

section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate RealInnerProductSpace

namespace AdditiveLargeSieve

noncomputable def derivativeCoefficients (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  (2 * Real.pi * I * n) * b n

end AdditiveLargeSieve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_IntegerResidueVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate

namespace AdditiveLargeSieve

noncomputable def exponential (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * x)

end AdditiveLargeSieve

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_RealCoprimeResidueCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970



namespace Erdos66Dependency.SingleResidueCount

open Finset

noncomputable def residueClass (a b Q r : ℤ) : Finset ℤ :=
  (Ico a b).filter (fun x => Int.ModEq Q x r)

end Erdos66Dependency.SingleResidueCount



namespace Erdos66Dependency.ResidueLifts

open Finset SingleResidueCount

noncomputable def liftsOn (J : Finset ℤ) (Q : ℤ) (A : Finset ℤ) : Finset ℤ :=
  J.filter (fun x => x % Q ∈ A)

end Erdos66Dependency.ResidueLifts



end Erdos970

end OAI
end


