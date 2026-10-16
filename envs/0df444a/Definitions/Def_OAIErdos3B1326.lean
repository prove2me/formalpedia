-- Prove2me | Definitions.Def_OAIErdos3B1326
-- name    : OAIErdos3B1326
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T17:28:15.610848+00:00
-- url     : https://prove2.me/theorems/8aa2511f-0cde-4954-bc66-fd69442ce613
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1327 of 1329
-- statement:
--   Definitions bundle 1327 of 1329 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1325`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1327 available.
--
--   Modules: `OAI.Erdos3.HasFixedTargetCubeIntervals`, `OAI.Erdos3.HasFixedTargetCubeIntervals.mono`, `OAI.Erdos3.HasWeightedTargetCubeIntervals`, `OAI.Erdos3.NativeMixedCorrelation.exists_cube_carry_intervals`, `OAI.Erdos3.NativeMixedCorrelation.exists_cube_residual_fourier_profiles`, `OAI.Erdos3.NativeMixedCorrelation.exists_cube_unwrapped_intervals`, `OAI.Erdos3.NativeMixedCorrelation.exists_fixed_target_cube_intervals`, `OAI.Erdos3.NativeMixedCorrelation.exists_full_difference_correlation`, `OAI.Erdos3.NativeMixedPairPartition.casesOn`, `OAI.Erdos3.NativeMixedPairPartition.cellVector`, `OAI.Erdos3.NativeMixedPairPartition.cellVector_norm`, `OAI.Erdos3.NativeMixedPairPartition.cellWeight`, `OAI.Erdos3.NativeMixedPairPartition.cellWeight_nonneg`, `OAI.Erdos3.NativeMixedPairPartition.cellWeight_total`, `OAI.Erdos3.NativeMixedPairPartition.mono`, `OAI.Erdos3.NativeMixedPointwisePartition.mono`, `OAI.Erdos3.NativeMixedPointwisePartition.rec`, `OAI.Erdos3.NativeMixedPointwisePartition.sampled_error`, `OAI.Erdos3.NativeMixedPointwisePartition.two_variable_exchange_approximation`, `OAI.Erdos3.NativeMixedPointwisePartition.weighted_two_variable_error`, `OAI.Erdos3.NativeMixedPointwisePartition.weighted_two_variable_exchange_error`, `OAI.Erdos3.NativePolynomialOrbitFactors.HasMixedPairFrozenEquivalence`, `OAI.Erdos3.NativePolynomialOrbitFactors.HasMixedPairFrozenReduction`, `OAI.Erdos3.NativePolynomialOrbitFactors.HasMixedPairLocalApproximation`, `OAI.Erdos3.NativePolynomialOrbitFactors.hasMixedPairFrozenEquivalence_mono`, `OAI.Erdos3.NativePolynomialOrbitFactors.mixedPairAnchoredVector`, `OAI.Erdos3.NativePolynomialOrbitFactors.mixedPairAnchoredVector_norm`, `OAI.Erdos3.NativePolynomialOrbitFactors.mixedPairFrozenEquivalence_at`, `OAI.Erdos3.NativePolynomialOrbitFactors.mixedPairFrozenVector`, `OAI.Erdos3.NativePolynomialOrbitFactors.mixedPairFrozenVector_diagonal`, `OAI.Erdos3.NativePolynomialOrbitFactors.mixedPairFrozenVector_error`, `OAI.Erdos3.NativePolynomialOrbitFactors.mixed_original_pair_comparison_invariant`, `OAI.Erdos3.NativePolynomialOrbitFactors.mixed_original_pair_top_agreement`, `OAI.Erdos3.NativePolynomialOrbitFactors.select_mixed_pointwise_partition`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairComparisonNiltest`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairComparisonNiltest_complexity`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairComparisonNiltest_observable`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairComparisonNiltest_vertical`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairComparisonTests`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairComparisonTests_complexity`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairComparisonTests_vertical`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairComparison_component_cost`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairFrequencies`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairFrequency_apply`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairFrequency_real`, `OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairProjection`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairCoordinateNiltest`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairCoordinateNiltest_complexity`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairCoordinateNiltest_eval`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairCoordinateNiltest_observable`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairCoordinateNiltest_orbit`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairCoordinateTests`, `OAI.Erdos3.NativeSampleCorrelation.mixedPairCoordinateTests_complexity`, `OAI.Erdos3.cyclicRealLinearPhase`, `OAI.Erdos3.cyclicRealLinearPhase_unit_shift_error`, `OAI.Erdos3.exists_fourier_of_real_linear_phase`, `OAI.Erdos3.exists_fourier_of_stepOne_expansion`, `OAI.Erdos3.exists_fourier_of_twisted_unit_shift`, `OAI.Erdos3.exists_mixed_diagonal_partition`, `OAI.Erdos3.exists_mixed_frozen_equivalence_budget`, `OAI.Erdos3.exists_mixed_pair_frozen_equivalence`, `OAI.Erdos3.exists_mixed_pair_frozen_reduction`, `OAI.Erdos3.exists_mixed_pair_local_approximation`, `OAI.Erdos3.exists_mixed_pointwise_partition`, `OAI.Erdos3.exists_mixed_precise_sampled_exchange`, `OAI.Erdos3.exists_mixed_sampled_exchange`, `OAI.Erdos3.exists_retained_target_cube_intervals`, `OAI.Erdos3.mean_twisted_nat_translate_error`, `OAI.Erdos3.mixedDifferencePoint`, `OAI.Erdos3.mixedDifferenceShifts`, `OAI.Erdos3.norm_cyclicRealLinearPhase`, `OAI.Erdos3.norm_derivative_correlation_mul_addChar`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B071

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MixedOriginalPairFrequency
namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} [NeZero m] {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

variable (V) in
noncomputable def _root_.OAI.Erdos3.NativeSampleCorrelation.mixedOriginalPairProjection (k : Fin 2) :
    V.MixedPairAlgebra →ₗ⁅ℚ⁆ W.L := liePiEval (some k)

theorem mixed_original_pair_top_agreement (x : ℝ ⊗[ℚ] V.MixedPairAlgebra)
    (hx : x ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) :
    realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 0) x) =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 1) x) := by
  have cancel (a b : ℝ ⊗[ℚ] W.L)
      (h : realifyFunctional (m • W.vertical.frequency) a =
        realifyFunctional (m • W.vertical.frequency) b) :
      realifyFunctional W.vertical.frequency a = realifyFunctional W.vertical.frequency b := by
    rw [realifyFunctional_nsmul, realifyFunctional_nsmul] at h
    simp only [nsmul_eq_mul] at h
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℝ) ≠ 0) h
  exact cancel _ _ (R.mixed_pair_top_agreement x hx)

end Erdos3.NativePolynomialOrbitFactors

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairFrozenEquivalence
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {n m : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

include V in
theorem mixedOriginalPairComparison_component_cost : p + 4 ≤ mixedPairBudget (tensorPowerBudget m p) q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : p ≤ tensorPowerBudget m p := (tensorPowerBudget_bounds m hp).1
  have hcost := V.mixedPairComparison_component_cost
  linarith only [hpow, hcost]

noncomputable def mixedOriginalPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => (W.tensorPower m).L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![W.vertical.frequency, -W.vertical.frequency] k

theorem mixedOriginalPairFrequency_apply (x : V.MixedPairAlgebra) :
    piFrequency V.mixedOriginalPairFrequencies x =
      W.vertical.frequency (V.mixedOriginalPairProjection 0 x) -
        W.vertical.frequency (V.mixedOriginalPairProjection 1 x) := by
  have h (x₀ x₁ : W.L) :
      0 + (W.vertical.frequency x₀ + (-W.vertical.frequency) x₁) =
        W.vertical.frequency x₀ - W.vertical.frequency x₁ := by
    simp only [LinearMap.neg_apply]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem mixedOriginalPairFrequency_real (x : ℝ ⊗[ℚ] V.MixedPairAlgebra) :
    realifyFunctional (piFrequency V.mixedOriginalPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 0) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 1) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.mixedOriginalPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

noncomputable def mixedOriginalPairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.mixedPairModels k).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega :
      n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).oneOnOrbit
  | some k => ![W.mixedPairComponent a id, (W.mixedPairComponent b (mixedExchangeCoordinate n)).conjugate] k

theorem mixedOriginalPairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.mixedOriginalPairComparisonTests a b k).ComplexityLE (mixedPairBudget (tensorPowerBudget m p) q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
      (V.mixedPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact (W.mixedPairComponent_complexity a id).mono V.mixedOriginalPairComparison_component_cost
    · exact (W.mixedPairComponent_complexity b (mixedExchangeCoordinate n)).mono V.mixedOriginalPairComparison_component_cost

theorem mixedOriginalPairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.mixedPairModels k).RealGroup)
    (hz : z ∈ (V.mixedPairModels k).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (V.mixedPairModels k).Space) :
    (V.mixedOriginalPairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.mixedOriginalPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.mixedOriginalPairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact W.mixedPairComponent_vertical a id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.mixedPairComponent_vertical b (mixedExchangeCoordinate n)) z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

noncomputable def mixedOriginalPairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels (V.mixedOriginalPairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget (tensorPowerBudget m p) q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    (V.mixedOriginalPairComparisonTests_complexity a b)

theorem mixedOriginalPairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.mixedOriginalPairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) :=
  piNiltest_complexity V.mixedPairModels (V.mixedOriginalPairComparisonTests a b) _ _ _

theorem mixedOriginalPairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.mixedPairModels).Space) :
    (V.mixedOriginalPairComparisonNiltest a b).observable x =
      W.vertical.observable a (productProjection V.mixedPairModels (some 0) x) *
        star (W.vertical.observable b (productProjection V.mixedPairModels (some 1) x)) := by
  change (∏ k, (V.mixedOriginalPairComparisonTests a b k).observable
    (productProjection V.mixedPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (W.vertical.observable a
    (productProjection V.mixedPairModels (some 0) x) *
      star (W.vertical.observable b (productProjection V.mixedPairModels (some 1) x))) = _
  exact one_mul _

theorem mixedOriginalPairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.mixedPairModels).RealGroup)
    (hz : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (pi V.mixedPairModels).Space) :
    (V.mixedOriginalPairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.mixedOriginalPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.mixedOriginalPairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.mixedPairModels (V.mixedOriginalPairComparisonTests a b)
    V.mixedOriginalPairFrequencies _ _ _ (V.mixedOriginalPairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} [NeZero m] {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixed_original_pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.mixedPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (pi V.mixedPairModels).Space) :
    (V.mixedOriginalPairComparisonNiltest a b).observable (z • x) =
      (V.mixedOriginalPairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1) :=
    (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.mixedOriginalPairComparisonNiltest_vertical a b z htop,
    V.mixedOriginalPairFrequency_real, R.mixed_original_pair_top_agreement z.coord hz,
    sub_self]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

noncomputable def mixedPairFrozenVector (k : Fin 2)
    (a b : (pi V.mixedPairModels).RealGroup) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ℤ) : ℂ :=
  W.vertical.observable out (productProjection V.mixedPairModels (some k)
    (QuotientGroup.mk (R.frozenMiddleValue a b x)))

def HasMixedPairFrozenEquivalence (u b : ℝ) : Prop :=
  ∀ den : ℕ, 0 < den → (den : ℝ) ≤ Real.exp u →
    ∀ a r : (pi V.mixedPairModels).RealGroup,
      (∀ i, |((pi V.mixedPairModels).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp u) →
      ((pi V.mixedPairModels).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid den →
      NativeIntegerVectorEquivalence (n + 1) b (R.mixedPairFrozenVector 0 a r) (R.mixedPairFrozenVector 1 a r)

end NativePolynomialOrbitFactors

theorem exists_mixed_frozen_equivalence_budget (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p q r u : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ r → 0 ≤ u →
      ∃ t : ℝ, 0 ≤ t ∧ r ≤ t ∧ u ≤ t ∧ p ≤ t ∧
        productNiltestBudget (mixedPairBudget p q) ≤ t ∧
        t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r u hp hq hr hu
  let v := p + q + r + u
  let b := 4 * (v + 1) + raisedNiltestBudget v + 6
  let t := productNiltestBudget b + v + 3
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hBt : mixedPairBudget p q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget p q := by
    unfold mixedPairBudget raisedNiltestBudget
    positivity
  have hprodmono : productNiltestBudget (mixedPairBudget p q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  exact ⟨t, ht, hrt, hut, hpt, htest, hsum⟩

theorem exists_mixed_pair_frozen_equivalence (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)],
      0 ≤ r → 0 ≤ u → R.HasMixedPairFrozenEquivalence u ((tensorPowerBudget m p + q + r + u + C) ^ C) := by
  obtain ⟨a, _, hfrozen⟩ := exists_native_frozen_middle_expansion (n + 1)
  have hdegree : n + 1 + 1 = ∑ _ : MixedReplicatedIndex (n + 1), 1 :=
    (mixedReplicated_totalDegree n).symm
  rw [hdegree] at hfrozen
  obtain ⟨C, hC, hbudget⟩ := exists_mixed_frozen_equivalence_budget a
  refine ⟨C, hC, ?_⟩
  intro p q r u m _ W N _ i j V R _ _ _ _ hr hu den hm hmb left right hleft hright
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpk : p ≤ tensorPowerBudget m p := (tensorPowerBudget_bounds m hp).1
  obtain ⟨t, ht, hrt, hut, hpt, htest, hsum⟩ :=
    hbudget (tensorPowerBudget m p) q r u (hp.trans hpk) hq hr hu
  have htC : t ≤ (tensorPowerBudget m p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((tensorPowerBudget m p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpk.trans (hpt.trans htC)))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨F⟩ := hfrozen (pi V.mixedPairModels) (R.mono hrt hN)
    (V.mixedOriginalPairComparisonNiltest out₀ out₁) ht ((V.mixedOriginalPairComparisonNiltest_complexity out₀ out₁).mono htest)
    (R.mixed_original_pair_comparison_invariant out₀ out₁) den hm (hmb.trans (Real.exp_le_exp.mpr hut)) left right
    (fun k => (hleft k).trans (Real.exp_le_exp.mpr hut)) hright
  have hF : Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1)
      ((tensorPowerBudget m p + q + r + u + C) ^ C) (fun x =>
        (V.mixedOriginalPairComparisonNiltest out₀ out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue left right x)))) :=
    ⟨F.mono hcost⟩
  have heq : (fun x : Fin (n + 2) → ℤ =>
      (V.mixedOriginalPairComparisonNiltest out₀ out₁).observable
        (QuotientGroup.mk (R.frozenMiddleValue left right x))) =
      (fun x => R.mixedPairFrozenVector 0 left right out₀ x *
        star (R.mixedPairFrozenVector 1 left right out₁ x)) := by
    funext x
    rw [V.mixedOriginalPairComparisonNiltest_observable]
    rfl
  exact (congrArg (fun f : (Fin (n + 2) → ℤ) → ℂ =>
    Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1)
      ((tensorPowerBudget m p + q + r + u + C) ^ C) f)) heq).mp hF

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NativeMixedFourierProfiles
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def cyclicRealLinearPhase {N : ℕ} (β : ℝ) (n : ZMod N) : ℂ :=
  CircleFourier.character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle)

@[simp] theorem norm_cyclicRealLinearPhase {N : ℕ} (β : ℝ) (n : ZMod N) :
    ‖cyclicRealLinearPhase β n‖ = 1 := CircleFourier.norm_character _

theorem cyclicRealLinearPhase_unit_shift_error {N : ℕ} [NeZero N] (β : ℝ) :
    (𝔼 n : ZMod N, ‖cyclicRealLinearPhase β (n + 1) -
      CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n‖) ≤ 2 / N := by
  classical
  let b : ZMod N := ((N - 1 : ℕ) : ZMod N)
  have hpoint (n : ZMod N) :
      ‖cyclicRealLinearPhase β (n + 1) -
        CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n‖ ≤
        if n = b then 2 else 0 := by
    by_cases hn : n = b
    · rw [if_pos hn]
      calc
        _ ≤ ‖cyclicRealLinearPhase β (n + 1)‖ +
            ‖CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n‖ := norm_sub_le _ _
        _ = 2 := by simp only [norm_mul, norm_cyclicRealLinearPhase, CircleFourier.norm_character]; norm_num
    · rw [if_neg hn]
      have hnlt : n.val + 1 < N := by
        have hv := n.val_lt
        by_contra h
        have he : n.val = N - 1 := by omega
        apply hn
        rw [← ZMod.natCast_zmod_val n, he]
      have hval : (n + 1).val = n.val + 1 := by
        have he : n + 1 = ((n.val + 1 : ℕ) : ZMod N) := by simp
        rw [he, ZMod.val_natCast_of_lt hnlt]
      have heq : cyclicRealLinearPhase β (n + 1) =
          CircleFourier.character (β : CircleFourier.Circle) * cyclicRealLinearPhase β n := by
        simp only [cyclicRealLinearPhase, hval, Nat.cast_add, Nat.cast_one, add_mul,
          one_mul, AddCircle.coe_add, CircleFourier.character_add]
        ring
      rw [heq, sub_self, norm_zero]
  calc
    _ ≤ 𝔼 n : ZMod N, if n = b then (2 : ℝ) else 0 :=
      Finset.expect_le_expect (fun n _ => hpoint n)
    _ = 2 / N := by rw [Fintype.expect_eq_sum_div_card]; simp

theorem mean_twisted_nat_translate_error {N : ℕ} [NeZero N]
    (q : ZMod N → ℂ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) {ε : ℝ}
    (hstep : (𝔼 n : ZMod N, ‖q (n + 1) - ζ * q n‖) ≤ ε) (m : ℕ) :
    (𝔼 n : ZMod N, ‖q (n + m) - ζ ^ m * q n‖) ≤ (m : ℝ) * ε := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpoint (n : ZMod N) :
        ‖q (n + (m + 1 : ℕ)) - ζ ^ (m + 1) * q n‖ ≤
          ‖q ((n + m) + 1) - ζ * q (n + m)‖ + ‖q (n + m) - ζ ^ m * q n‖ := by
      calc
        _ = ‖(q ((n + m) + 1) - ζ * q (n + m)) +
            ζ * (q (n + m) - ζ ^ m * q n)‖ := by
          simp only [Nat.cast_add, Nat.cast_one, add_assoc, pow_succ]
          congr 1
          ring
        _ ≤ ‖q ((n + m) + 1) - ζ * q (n + m)‖ +
            ‖ζ * (q (n + m) - ζ ^ m * q n)‖ := norm_add_le _ _
        _ ≤ _ := by
          rw [norm_mul]
          exact add_le_add le_rfl (mul_le_of_le_one_left (norm_nonneg _) hζ)
    have hshift : (𝔼 n : ZMod N, ‖q ((n + m) + 1) - ζ * q (n + m)‖) =
        𝔼 n : ZMod N, ‖q (n + 1) - ζ * q n‖ := by
      exact Fintype.expect_equiv (Equiv.addRight (m : ZMod N)) _ _ (fun _ => rfl)
    calc
      _ ≤ (𝔼 n : ZMod N, ‖q ((n + m) + 1) - ζ * q (n + m)‖) +
          (𝔼 n : ZMod N, ‖q (n + m) - ζ ^ m * q n‖) := by
        rw [← Finset.expect_add_distrib]
        exact Finset.expect_le_expect (fun n _ => hpoint n)
      _ ≤ ε + (m : ℝ) * ε := by rw [hshift]; exact add_le_add hstep ih
      _ = ((m + 1 : ℕ) : ℝ) * ε := by push_cast; ring

theorem exists_fourier_of_twisted_unit_shift {N : ℕ} [NeZero N]
    (q f : ZMod N → ℂ) (ζ : ℂ) (hq : ∀ n, ‖q n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hζ : ‖ζ‖ = 1) (hstep : (𝔼 n : ZMod N, ‖q (n + 1) - ζ * q n‖) ≤ 2 / N)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 n, f n * star (q n)‖) :
    ∃ χ : AddChar (ZMod N) ℂ, ρ ^ 2 / 16 ≤ ‖finiteFourierCoeff f χ‖ := by
  let C (h : ZMod N) := 𝔼 n : ZMod N, q n * star (f (n + h))
  let c := 𝔼 n : ZMod N, q n * star (f n)
  have hc : ρ ≤ ‖c‖ := by
    have heq : c = star (𝔼 n : ZMod N, f n * star (q n)) := by
      rw [← expect_star]
      apply Finset.expect_congr rfl
      intro n _
      simp only [star_mul, star_star]
    rw [heq, norm_star]
    exact hcorr
  have hrow (m : ℕ) : ρ - (m : ℝ) * (2 / N) ≤ ‖C (m : ZMod N)‖ := by
    have hshift : c = 𝔼 n : ZMod N, q (n + m) * star (f (n + m)) :=
      (Fintype.expect_equiv (Equiv.addRight (m : ZMod N)) _ _ (fun _ => rfl)).symm
    have hmul : ζ ^ m * C (m : ZMod N) =
        𝔼 n : ZMod N, (ζ ^ m * q n) * star (f (n + m)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      ring
    have herr : ‖c - ζ ^ m * C (m : ZMod N)‖ ≤ (m : ℝ) * (2 / N) := by
      rw [hshift, hmul, ← Finset.expect_sub_distrib]
      apply (RCLike.norm_expect_le (K := ℂ)).trans
      apply le_trans _ (mean_twisted_nat_translate_error q ζ hζ.le hstep m)
      apply Finset.expect_le_expect
      intro n _
      rw [← sub_mul, norm_mul, norm_star]
      exact mul_le_of_le_one_right (norm_nonneg _) (hf _)
    have hnorm : ‖ζ ^ m * C (m : ZMod N)‖ = ‖C (m : ZMod N)‖ := by
      rw [norm_mul, norm_pow, hζ, one_pow, one_mul]
    have htriangle : ‖c‖ ≤ ‖c - ζ ^ m * C (m : ZMod N)‖ + ‖C (m : ZMod N)‖ := by
      rw [← hnorm]
      exact norm_le_norm_sub_add _ _
    linarith
  let δ := ρ / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
  obtain ⟨K, hK, hKN, hsmall, hratio⟩ := exists_smoothing_scale (NeZero.pos N) hδ hδ1
  let H := cyclicInterval (0 : ZMod N) K
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hdense : (ρ / 8) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    have hh := (div_le_div_iff₀ hKpos hδ).mp hratio
    dsimp only [δ] at hh
    rw [show H.card = K from cyclicInterval_card 0 hKN, ZMod.card]
    nlinarith
  have hlarge (h : ZMod N) (hh : h ∈ H) : ρ / 2 ≤ ‖C h‖ := by
    obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hh
    have hmK : m ≤ K - 1 := by have := Finset.mem_range.mp hm; omega
    have hmreal : (m : ℝ) ≤ δ * N := (Nat.cast_le.mpr hmK).trans hsmall
    have he' : (m : ZMod N) = h := by simpa using he
    have heps : (m : ℝ) * (2 / N) ≤ ρ / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hNpos).mpr
      dsimp only [δ] at hmreal
      nlinarith
    rw [← he']
    linarith [hrow m]
  have hmass := dense_set_mean_lower_bound H (fun h => ‖C h‖) (fun _ => norm_nonneg _)
    (show 0 ≤ ρ / 2 by positivity) hdense hlarge
  obtain ⟨χ, hχ⟩ := exists_large_fourier_of_mean_cross_correlation q f hq
  refine ⟨χ, ?_⟩
  have heq : (ρ / 8) * (ρ / 2) = ρ ^ 2 / 16 := by ring
  rw [heq] at hmass
  exact hmass.trans hχ

theorem exists_fourier_of_real_linear_phase {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (β : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 n, f n * star (cyclicRealLinearPhase β n)‖) :
    ∃ χ : AddChar (ZMod N) ℂ, ρ ^ 2 / 16 ≤ ‖finiteFourierCoeff f χ‖ :=
  exists_fourier_of_twisted_unit_shift (cyclicRealLinearPhase β) f
    (CircleFourier.character (β : CircleFourier.Circle))
    (fun n => (norm_cyclicRealLinearPhase β n).le) hf (CircleFourier.norm_character _)
    (cyclicRealLinearPhase_unit_shift_error β) hρ hρ1 hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_fourier_of_stepOne_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ {g : (Unit → ℤ) → ℂ} (_E : NativeIntegerExpansion (fun _ : Unit => 1) 1 p g)
        (f : ZMod N → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 n : ZMod N, f n * star (g (fun _ => (n.val : ℤ)))‖ →
      ∃ χ : AddChar (ZMod N) ℂ, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff f χ‖ := by
  obtain ⟨A, _, hphase⟩ := exists_stepOne_scalar_phase_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * (2 * X + Polynomial.C A) ^ A + 16)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp g E f hf hc
  obtain ⟨i, hi⟩ := E.select_sample_correlation Finset.univ
    (fun n : ZMod N => fun _ => (n.val : ℤ)) f hc
  obtain ⟨β, hβ⟩ := hphase (E.model i) (by positivity : 0 ≤ 2 * p) (E.test i)
    ((E.complexity i).mono (by linarith)) f hf (by
      change Real.exp (-(2 * p)) ≤
        ‖𝔼 n : ZMod N, f n * star ((E.test i).eval (fun _ => (n.val : ℤ)))‖
      simpa only [two_mul] using hi)
  let t := (2 * p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  obtain ⟨χ, hχ⟩ := exists_fourier_of_real_linear_phase f hf β
    (Real.exp_pos (-t)) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) hβ
  have hsmall : Real.exp (-(2 * t + 16)) ≤ Real.exp (-t) ^ 2 / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    calc
      _ ≤ Real.exp (-(2 * t + 16)) * Real.exp 16 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (16 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; norm_num
  have hcost : 2 * t + 16 ≤ (p + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨χ, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hsmall.trans hχ)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_cube_residual_fourier_profiles (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim, ∃ Q : Finset (Fin (d + 1) → ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 1) ≤ (Q.card : ℝ) ∧
        ∃ χ : (Fin (d + 1) → ZMod N) → AddChar (ZMod N) ℂ,
          ∀ u ∈ Q, u 0 ∈ M.shifts ∧ Real.exp (-((p + C) ^ C)) ≤
            ‖finiteFourierCoeff (nativeMixedCubeResidual f M.mixed i u) (χ u)‖ := by
  obtain ⟨a, _, hresidual⟩ := exists_degree_one_cube_residuals d
  obtain ⟨b, _, hfourier⟩ := exists_fourier_of_stepOne_expansion
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  classical
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hresidual hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  have hchar (u : Fin (d + 1) → ZMod N) (hu : u ∈ Q) :
      ∃ χ : AddChar (ZMod N) ℂ, Real.exp (-r) ≤
        ‖finiteFourierCoeff (nativeMixedCubeResidual f M.mixed i u) χ‖ := by
    obtain ⟨V⟩ := (hcorr u hu).2
    let E := NativeIntegerExpansion.ofTest V.test V.complexity (fun _ => rfl)
    exact hfourier hq E (nativeMixedCubeResidual f M.mixed i u)
      (nativeMixedCubeResidual_norm_le_one f hf M.mixed i u) V.correlation
  let χ (u : Fin (d + 1) → ZMod N) : AddChar (ZMod N) ℂ :=
    if hu : u ∈ Q then Classical.choose (hchar u hu) else 1
  refine ⟨i, Q, hQ, ?_, χ, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro u hu
    refine ⟨(hcorr u hu).1, ?_⟩
    dsimp only [χ]
    rw [dif_pos hu]
    exact (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (Classical.choose_spec (hchar u hu))

end Erdos3.NativeMixedCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_derivative_correlation_mul_addChar {G : Type*} [AddCommGroup G] [Fintype G]
    (f u : G → ℂ) (χ : AddChar G ℂ) (h : G) :
    ‖finiteCorrelation Finset.univ f (multiplicativeDerivative (fun x => u x * χ x) h)‖ =
      ‖finiteCorrelation Finset.univ f (multiplicativeDerivative u h)‖ := by
  have hcancel (x : G) : χ x * star (χ x) = 1 := by
    change χ x * (starRingEnd ℂ) (χ x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, AddChar.norm_apply]
    norm_num
  have hder (x : G) : multiplicativeDerivative (fun y => u y * χ y) h x =
      star (χ h) * multiplicativeDerivative u h x := by
    simp only [multiplicativeDerivative, AddChar.map_add_eq_mul, star_mul]
    calc
      _ = (χ x * star (χ x)) * (star (χ h) * (u x * star (u (x + h)))) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have heq : finiteCorrelation Finset.univ f (multiplicativeDerivative (fun x => u x * χ x) h) =
      χ h * finiteCorrelation Finset.univ f (multiplicativeDerivative u h) := by
    unfold finiteCorrelation
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    rw [hder, star_mul, star_star]
    ring
  rw [heq, norm_mul, AddChar.norm_apply, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

theorem exists_full_difference_correlation (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, u.1 0 ∈ M.shifts ∧ Real.exp (-((p + C) ^ C)) ≤
          ‖finiteCorrelation Finset.univ
            (cubeProduct f (u.2 :: List.ofFn u.1))
            (cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u.1 0) x))
              (u.2 :: List.ofFn (Fin.tail u.1)))‖ := by
  obtain ⟨a, _, hfourier⟩ := exists_cube_residual_fourier_profiles d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  classical
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 3 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨i, H, _hH, hdense, χ, hcorr⟩ := hfourier hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  let F (u : Fin (d + 1) → ZMod N) := cubeProduct f (List.ofFn u)
  let V (u : Fin (d + 1) → ZMod N) :=
    cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u 0) x))
      (List.ofFn (Fin.tail u))
  let G (u : Fin (d + 1) → ZMod N) (x : ZMod N) := V u x * χ u x
  have hF (u : Fin (d + 1) → ZMod N) (x : ZMod N) : ‖F u x‖ ≤ 1 :=
    cubeProduct_norm_le_one f hf _ x
  have hV (u : Fin (d + 1) → ZMod N) (x : ZMod N) : ‖V u x‖ ≤ 1 :=
    cubeProduct_norm_le_one _ (fun _ => M.mixed.norm_eval i _) _ x
  have hG (u : Fin (d + 1) → ZMod N) (x : ZMod N) : ‖G u x‖ ≤ 1 := by
    dsimp only [G]
    rw [norm_mul, AddChar.norm_apply, mul_one]
    exact hV u x
  have hc (u : Fin (d + 1) → ZMod N) (hu : u ∈ H) :
      Real.exp (-q) ≤ ‖finiteCorrelation Finset.univ (F u) (G u)‖ := by
    have heq (x : ZMod N) : nativeMixedCubeResidual f M.mixed i u x * star (χ u x) =
        F u x * star (G u x) := by
      rw [nativeMixedCubeResidual_eq]
      dsimp only [F, G, V]
      rw [star_mul]
      ring
    simpa only [finiteFourierCoeff, finiteCorrelation, heq] using (hcorr u hu).2
  obtain ⟨Q, hQ, hQsize, hQcorr⟩ := exists_many_family_derivative_correlations F G H hF hG
    (Real.exp_pos (-q)) (Real.exp_pos (-q))
    (by simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow] using hdense) hc
  have hprod : Real.exp (-q) * Real.exp (-q) ^ 2 = Real.exp (-(3 * q)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) * Real.exp (-q) ^ 2 / 2 := by
    rw [hprod]
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -(3 * q) - 1)).trans
      (exp_sub_one_le_half_exp (-(3 * q)))
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · have hsize : Real.exp (-q) * Real.exp (-q) ^ 2 / 2 * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) := by
      convert hQsize using 1
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
      simp only [pow_succ]
      ring
    exact (mul_le_mul_of_nonneg_right hsmall (pow_nonneg (Nat.cast_nonneg N) _)).trans hsize
  · intro u hu
    obtain ⟨hbase, hder⟩ := hQcorr u hu
    refine ⟨(hcorr u.1 hbase).1, ?_⟩
    have h := hsmall.trans hder
    change Real.exp (-((p + C) ^ C)) ≤
      ‖finiteCorrelation Finset.univ (multiplicativeDerivative (F u.1) u.2)
        (multiplicativeDerivative (fun x => V u.1 x * χ u.1 x) u.2)‖ at h
    rw [norm_derivative_correlation_mul_addChar] at h
    have hFder : multiplicativeDerivative (F u.1) u.2 =
        cubeProduct f (u.2 :: List.ofFn u.1) := by
      funext x
      exact (cubeProduct_cons f u.2 (List.ofFn u.1) x).symm
    have hVder : multiplicativeDerivative (V u.1) u.2 =
        cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u.1 0) x))
          (u.2 :: List.ofFn (Fin.tail u.1)) := by
      funext x
      exact (cubeProduct_cons _ u.2 (List.ofFn (Fin.tail u.1)) x).symm
    rw [hFder, hVder] at h
    exact h

end NativeMixedCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedDifferenceShifts {d N : ℕ} (t : (Fin (d + 1) → ZMod N) × ZMod N) :
    Fin (d + 1) → ZMod N := Fin.cons t.2 (Fin.tail t.1)

def mixedDifferencePoint {d N : ℕ} (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
    Fin (d + 3) → ℤ :=
  Fin.cons ((t.1 0).val : ℤ) (Fin.cons n (fun j => ((mixedDifferenceShifts t j).val : ℤ)))

namespace NativeMixedCorrelation

theorem exists_cube_carry_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧
          ∃ (b : (Fin (d + 1) → Bool) → Fin (d + 2)) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
                  star (M.mixed.mixedCubeWithShift (cubeCarryShift (d + 1) N b)
                    (fun _ => i) (mixedDifferencePoint t n))‖ := by
  obtain ⟨A, _, hdifference⟩ := exists_full_difference_correlation d
  let L : ℕ := 2 * (2 ^ (d + 1) + 8)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Polynomial.C L)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  let q := (p + A) ^ A
  have htotal : q + L ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have hLpos : (0 : ℝ) < L := by dsimp [L]; positivity
  have hLexp : (L : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp (L : ℝ)]
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) / (2 * ((2 : ℝ) ^ (d + 1) + 8)) := by
    have hden : (2 * ((2 : ℝ) ^ (d + 1) + 8)) = L := by simp [L]
    rw [hden]
    apply (le_div_iff₀ hLpos).mpr
    calc
      _ ≤ Real.exp (-((p + C) ^ C)) * Real.exp L :=
        mul_le_mul_of_nonneg_left hLexp (Real.exp_nonneg _)
      _ = Real.exp (-((p + C) ^ C) + L) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hdifference hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    refine ⟨(hcorr t ht).1, ?_⟩
    let R (z : ℤ) := M.mixed.eval i (correlationInput ((t.1 0).val : ℤ) z)
    let g := cubeProduct f (t.2 :: List.ofFn t.1)
    have hg : ∀ x, ‖g x‖ ≤ 1 := cubeProduct_norm_le_one f hf _
    have hR : (fun n : ZMod N => R n.val) =
        (fun x => M.mixed.evalCyclic N i (correlationInput (t.1 0) x)) := by
      funext x
      apply congrArg (M.mixed.eval i)
      funext j
      fin_cases j <;> rfl
    have hc : Real.exp (-q) ≤ ‖finiteCorrelation Finset.univ g
        (cubeProduct (fun n : ZMod N => R n.val) (List.ofFn (mixedDifferenceShifts t)))‖ := by
      rw [hR]
      simpa only [mixedDifferenceShifts, List.ofFn_cons] using (hcorr t ht).2
    obtain ⟨b, a, len, hlen, hend, hshort, hcor, hvol⟩ :=
      exists_cyclic_cube_product_interval g R (mixedDifferenceShifts t) (Real.exp_pos (-q))
        hg (fun _ => M.mixed.norm_eval i _) hc
    refine ⟨b, a, len, hlen, hend, hshort, hsmall.trans hvol, ?_⟩
    simpa only [finiteCorrelation, mixedDifferencePoint, M.mixed.mixedCubeWithShift_diagonal]
      using hsmall.trans hcor

end NativeMixedCorrelation
end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_cube_unwrapped_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ E : ∀ b : (Fin (d + 1) → Bool) → Fin (d + 2),
        NativeIntegerVectorEquivalence (d + 2) r
          (M.mixed.mixedCubeWithShift (cubeCarryShift (d + 1) N b))
          (M.mixed.mixedCubeWithShift 0),
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧
          ∃ (b : (Fin (d + 1) → Bool) → Fin (d + 2)) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            ∃ v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim,
            ∃ l : Fin ((E b).selectedExpansion (fun _ => i) v).count,
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
                    star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) *
                    star ((((E b).selectedExpansion (fun _ => i) v).test l).eval (mixedDifferencePoint t n))‖ := by
  obtain ⟨A, _, hinterval⟩ := exists_cube_carry_intervals d
  obtain ⟨B, _, htranslate⟩ := NativeMultidegreeNilcharacter.exists_mixed_cube_translation (d + 2) (d + 1)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let R := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + 2 * R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  let q := (p + A) ^ A
  let r := (p + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + 2 * r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  let E (b : (Fin (d + 1) → Bool) → Fin (d + 2)) := htranslate M.mixed (cubeCarryShift (d + 1) N b)
  refine ⟨r, hr, hrC, E, i, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hshift, b, a, len, hlen, hend, hshort, hvol, hcor⟩ := hcorr t ht
    obtain ⟨v, l, hc⟩ := (E b).transfer_sample_correlation
      (Finset.Ico (a : ℤ) (a + len)) (mixedDifferencePoint t) (fun _ => i)
      (fun n => cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N))
      (fun n _ => M.mixed.mixedCubeWithShift_unit 0 _) hcor
    exact ⟨hshift, b, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      v, l, (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hc⟩

end Erdos3.NativeMixedCorrelation

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasFixedTargetCubeIntervals {J : Type*} [Fintype J] {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin 2 → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ r u : ℝ, 0 ≤ r ∧ r ≤ q ∧ 0 ≤ u ∧ u ≤ q ∧
    ∃ E : ∀ b : (Fin (d + 1) → Bool) → Fin (d + 2),
      NativeIntegerVectorEquivalence (d + 2) r
        (M.mixed.mixedCubeWithShift (cubeCarryShift (d + 1) N b)) (M.mixed.mixedCubeWithShift 0),
    ∃ F : NativeIntegerVectorEquivalence (d + 2) u (M.mixed.mixedCubeWithShift 0)
      (mixedCubeObservable (d := d + 1) η),
    ∃ (i : Fin M.mixed.outputDim) (b : (Fin (d + 1) → Bool) → Fin (d + 2))
      (v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim)
      (l : Fin ((E b).selectedExpansion (fun _ => i) v).count),
    ∃ (w : (Fin (d + 1) → Bool) → J) (z : Fin (F.selectedExpansion v w).count),
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
              star (mixedCubeObservable η w (mixedDifferencePoint t n)) *
              star ((((E b).selectedExpansion (fun _ => i) v).test l).eval (mixedDifferencePoint t n)) *
              star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n))‖

theorem HasFixedTargetCubeIntervals.mono {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q q' : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasFixedTargetCubeIntervals f M η q) (hqq' : q ≤ q') :
    HasFixedTargetCubeIntervals f M η q' := by
  obtain ⟨r, u, hr, hrq, hu, huq, E, F, i, b, v, l, w, z, Q, hQ, hdense, hcorr⟩ := H
  refine ⟨r, u, hr, hrq.trans hqq', hu, huq.trans hqq', E, F, i, b, v, l, w, z, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqq'))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_fixed_target_cube_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ (M : NativeMixedCorrelation (d + 2) N p f) (η : J → (Fin 2 → ℤ) → ℂ),
      (∀ x, ∑ j, ‖η j x‖ ^ 2 = 1) → NativeIntegerVectorEquivalence (d + 2) p M.mixed.eval η →
      HasFixedTargetCubeIntervals f M η ((p + C) ^ C) := by
  obtain ⟨A, _, hinterval⟩ := exists_cube_unwrapped_intervals d
  obtain ⟨B, _, hcube⟩ := NativeIntegerVectorEquivalence.exists_mixed_cube_budget (d + 1)
  let L : ℕ := (d + 2) ^ (2 ^ (d + 1))
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let U := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2 * U + Polynomial.C L)
  refine ⟨C, hC, ?_⟩
  intro J _ N _ p hp hN f hf M η hη Ediag
  classical
  let q := (p + A) ^ A
  let u := (p + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have htotal : 3 * q + 2 * u + L ≤ (p + C) ^ C := by
    simpa [X, P, U, q, u, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by linarith
  have htransfer : q + 2 * u ≤ (p + C) ^ C := by linarith
  obtain ⟨r, hr, hrq, E, i, Q, hQ, hdense, hcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  have F : NativeIntegerVectorEquivalence (d + 2) u (M.mixed.mixedCubeWithShift 0)
      (mixedCubeObservable (d := d + 1) η) := by
    rw [M.mixed.mixedCubeWithShift_zero_eq]
    exact hcube hp Ediag
  let K := Σ b : (Fin (d + 1) → Bool) → Fin (d + 2),
    Σ v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim,
      Fin ((E b).selectedExpansion (fun _ => i) v).count ×
        (Σ w : (Fin (d + 1) → Bool) → J, Fin (F.selectedExpansion v w).count)
  let R (t : (Fin (d + 1) → ZMod N) × ZMod N) (_ : Unit) (c : K) : Prop :=
    t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
      0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-(q + 2 * u)) ≤
        ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
          cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
            star (mixedCubeObservable η c.2.2.2.1 (mixedDifferencePoint t n)) *
            star ((((E c.1).selectedExpansion (fun _ => i) c.2.1).test c.2.2.1).eval (mixedDifferencePoint t n)) *
            star (((F.selectedExpansion c.2.1 c.2.2.2.1).test c.2.2.2.2).eval (mixedDifferencePoint t n))‖
  have hchoice : ∀ t ∈ Q, ∀ j, ∃ c, R t j c := by
    intro t ht _
    obtain ⟨hshift, b, a, len, hlen, hend, hshort, hvol, v, l, hcor⟩ := hcorr t ht
    let D (n : ℤ) := cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N)
    let T (n : ℤ) := (((E b).selectedExpansion (fun _ => i) v).test l).eval (mixedDifferencePoint t n)
    have hc : Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        (D n * star (T n)) * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n))‖ := by
      have hswap (n : ℤ) : D n * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) * star (T n) =
          (D n * star (T n)) * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) :=
        mul_right_comm _ _ _
      change Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        D n * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) * star (T n)‖ at hcor
      simpa only [hswap] using hcor
    obtain ⟨w, z, hw⟩ := F.transfer_sample_correlation (Finset.Ico (a : ℤ) (a + len))
      (mixedDifferencePoint t) v (fun n => D n * star (T n))
      (fun n _ => mixedCubeObservable_unit η hη _) hc
    have horder (n : ℤ) :
        (D n * star (T n)) * star (mixedCubeObservable η w (mixedDifferencePoint t n)) *
          star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n)) =
        D n * star (mixedCubeObservable η w (mixedDifferencePoint t n)) * star (T n) *
          star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n)) :=
      congrArg (fun c : ℂ => c * star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n)))
        (mul_right_comm _ _ _)
    simp only [horder] at hw
    exact ⟨⟨b, v, l, w, z⟩, hshift, a, len, hlen, hend, hshort, hvol, hw⟩
  have hinner (b : (Fin (d + 1) → Bool) → Fin (d + 2)) :=
    (E b).selectedChainedChoice_card_bound F (fun _ => i)
  have hcount : (Fintype.card K : ℝ) ≤ Real.exp (2 * q + 2 * u + L) := by
    change (Fintype.card (Σ b : (Fin (d + 1) → Bool) → Fin (d + 2),
      Σ v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim,
        Fin ((E b).selectedExpansion (fun _ => i) v).count ×
          (Σ w : (Fin (d + 1) → Bool) → J, Fin (F.selectedExpansion v w).count)) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _b : (Fin (d + 1) → Bool) → Fin (d + 2), Real.exp (2 * r + 2 * u) :=
        Finset.sum_le_sum (fun b _ => hinner b)
      _ = (L : ℝ) * Real.exp (2 * r + 2 * u) := by simp [L]
      _ ≤ Real.exp L * Real.exp (2 * r + 2 * u) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (L : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (L + (2 * r + 2 * u)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨c, S, _, hS, hSdense, hfixed⟩ := exists_large_fixed_choices Q hQ R hchoice hcount
  have hsize : Real.exp (-(2 * q + 2 * u + L)) * (Q.card : ℝ) ≤ (S.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSdense
  refine ⟨r, u, hr, hrq.trans hqC, hu, huC, E, F, i, (c ()).1, (c ()).2.1,
    (c ()).2.2.1, (c ()).2.2.2.1, (c ()).2.2.2.2, S, hS, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(3 * q + 2 * u + L)) * (N : ℝ) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (by positivity)
      _ = Real.exp (-(2 * q + 2 * u + L)) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(2 * q + 2 * u + L)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hfixed t ht ()
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg htransfer)).trans hc⟩

end Erdos3.NativeMixedCorrelation

end

section

namespace Erdos3

open scoped BigOperators

def HasWeightedTargetCubeIntervals {J : Type*} [Fintype J] {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin 2 → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (w : (Fin (d + 1) → Bool) → J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            (cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
              star (mixedCubeObservable η w (mixedDifferencePoint t n))) *
              ∏ i, A i (mixedDifferencePoint t n)‖

end Erdos3

end

section

namespace Erdos3

theorem exists_retained_target_cube_intervals (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter
        (fun _ : ReplicatedIndex (mixedCorrelationDegree (d + 2)) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        HasFixedTargetCubeIntervals f M (fun k x => W.eval k (fun j => x j.1)) ((p + C) ^ C) := by
  obtain ⟨a, _, hretained⟩ := exists_retained_inverse_intervals (by omega : 2 ≤ d + 2) hI
  obtain ⟨b, _, hfixed⟩ := NativeMixedCorrelation.exists_fixed_target_cube_intervals d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, V, r₀, hr₀, hr₀q, B, M, hshifts, hdimension, E⟩ :=
    hretained hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  let W := B.mixed.mono hr₀q
  have hdiag : NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
      (fun k x => W.eval k (fun j => x j.1)) := E
  have H := hfixed hq ((Real.exp_le_exp.mpr hrC).trans hN) f hf M
    (fun k x => W.eval k (fun j => x j.1)) (fun x => W.unit_eval _) hdiag
  have hdim : W.dim ≤ 2 ^ (d + 3) * M.mixed.dim := by
    change B.mixed.dim ≤ 2 ^ (d + 3) * M.mixed.dim
    rw [hdimension]
    exact B.mixed_dim
  exact ⟨q, hq, hqC, M, W, hdim, B.mixed_symmetric, hdiag, H.mono hrC⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedPairCoordinateTest
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

noncomputable def mixedPairCoordinateTests (k : Fin 2) (out : Fin W.outputDim) :
    ∀ l, (V.mixedPairModels l).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega :
      n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).oneOnOrbit
  | some l =>
      ![![W.mixedPairComponent out id, (W.mixedPairComponent out (mixedExchangeCoordinate n)).oneOnOrbit],
        ![(W.mixedPairComponent out id).oneOnOrbit, W.mixedPairComponent out (mixedExchangeCoordinate n)]] k l

theorem mixedPairCoordinateTests_complexity (k : Fin 2) (out : Fin W.outputDim) (l : Option (Fin 2)) :
    (V.mixedPairCoordinateTests k out l).ComplexityLE (mixedPairBudget (tensorPowerBudget m p) q) := by
  have htwo : 2 ≤ mixedPairBudget (tensorPowerBudget m p) q :=
    (by norm_num : (2 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  cases l with
  | none => exact Niltest.oneOnOrbit_complexity _ htwo (V.mixedPairTests_complexity none).1
  | some l =>
    fin_cases k <;> fin_cases l
    · exact (W.mixedPairComponent_complexity out id).mono V.mixedOriginalPairComparison_component_cost
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.mixedPairTests_complexity (some 1)).1
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.mixedPairTests_complexity (some 0)).1
    · exact (W.mixedPairComponent_complexity out (mixedExchangeCoordinate n)).mono V.mixedOriginalPairComparison_component_cost

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

noncomputable def mixedPairCoordinateNiltest (k : Fin 2) (out : Fin W.outputDim) :
    (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels (V.mixedPairCoordinateTests k out)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget (tensorPowerBudget m p) q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    (V.mixedPairCoordinateTests_complexity k out)

theorem mixedPairCoordinateNiltest_complexity (k : Fin 2) (out : Fin W.outputDim) :
    (V.mixedPairCoordinateNiltest k out).ComplexityLE
      (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) :=
  piNiltest_complexity V.mixedPairModels (V.mixedPairCoordinateTests k out) _ _ _

theorem mixedPairCoordinateNiltest_observable (k : Fin 2) (out : Fin W.outputDim)
    (x : (pi V.mixedPairModels).Space) :
    (V.mixedPairCoordinateNiltest k out).observable x =
      W.vertical.observable out (productProjection V.mixedPairModels (some k) x) := by
  change (∏ l, (V.mixedPairCoordinateTests k out l).observable
    (productProjection V.mixedPairModels l x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * (W.vertical.observable out
      (productProjection V.mixedPairModels (some 0) x) * 1) = _
    simp only [one_mul, mul_one]
    rfl
  · change 1 * (1 * W.vertical.observable out
      (productProjection V.mixedPairModels (some 1) x)) = _
    simp only [one_mul]
    rfl

theorem mixedPairCoordinateNiltest_orbit (k : Fin 2) (out : Fin W.outputDim) :
    (V.mixedPairCoordinateNiltest k out).orbit = V.mixedPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun l => (V.mixedPairModels l).filtration))
  funext l
  cases l with
  | none => rfl
  | some l => fin_cases k <;> fin_cases l <;> rfl

theorem mixedPairCoordinateNiltest_eval (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) :
    (V.mixedPairCoordinateNiltest k out).eval x =
      W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k))
        (fun j => x j.succ.succ)) := by
  rw [mixedPairCoordinateNiltest, piNiltest_eval, Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * ((W.mixedPairComponent out id).eval x * 1) = _
    rw [one_mul, mul_one, W.mixedPairComponent_eval]
    rfl
  · change 1 * (1 * (W.mixedPairComponent out (mixedExchangeCoordinate n)).eval x) = _
    rw [one_mul, one_mul, W.mixedPairComponent_eval]
    rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairPartitionPrecision
namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

noncomputable def mixedPairAnchoredVector (y : Fin (n + 2) → ℤ)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x

def HasMixedPairLocalApproximation (b : ℝ) : Prop :=
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
    ∀ y : Fin (n + 2) → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
      ∀ (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) -
          R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤ Real.exp b * δ

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixedPairFrozenVector_diagonal (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) :
    W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) =
      R.mixedPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x := by
  have hpoly : V.mixedPairPolynomial =
      ⟨⟨(V.mixedPairCoordinateNiltest k out).orbit.log,
        (V.mixedPairCoordinateNiltest k out).orbit.property⟩⟩ := by
    rw [V.mixedPairCoordinateNiltest_orbit]
    exact V.mixedPairPolynomial_eq_test
  calc
    _ = (V.mixedPairCoordinateNiltest k out).eval x :=
      (V.mixedPairCoordinateNiltest_eval k out x).symm
    _ = _ := (R.eval_niltest (V.mixedPairCoordinateNiltest k out) hpoly x).trans
      (V.mixedPairCoordinateNiltest_observable k out _)

theorem mixedPairFrozenVector_error (k : Fin 2) (out : Fin W.outputDim) (x y : Fin (n + 2) → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) : (pi V.mixedPairModels).Space) =
      QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi V.mixedPairModels).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi V.mixedPairModels).basis.baseChange ℝ)
    ‖W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) -
        R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
  let D := pi V.mixedPairModels
  let T := V.mixedPairCoordinateNiltest k out
  let b := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin (n + 2) => 1) (fun i => (x i : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq T.observable (R.slowValue x) b
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left T.observable T.lipschitz
    (R.slowValue x) (R.slowValue y) b (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (T.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) := by
    have h := T.observable_budget (V.mixedPairCoordinateNiltest_complexity k out)
    linarith [T.normBound.coe_nonneg]
  have hraw : ‖R.mixedPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x -
      R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
    simpa only [T, V.mixedPairCoordinateNiltest_observable, mixedPairFrozenVector, frozenMiddleValue, b] using
      hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)
  simpa only [← R.mixedPairFrozenVector_diagonal k out x] using hraw

end Erdos3.NativePolynomialOrbitFactors

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_local_approximation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasMixedPairLocalApproximation ((tensorPowerBudget m p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_local_control
    (∑ _ : MixedReplicatedIndex (n + 1), 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r m W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget m p := hW.trans (tensorPowerBudget_bounds m hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := tensorPowerBudget m p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + ((n + 2 : ℕ) : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : tensorPowerBudget m p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have htwo : (Fintype.card (Fin (n + 2)) : ℝ) ≤ t := by
    simp only [Fintype.card_fin]
    dsimp [t]
    linarith
  have hBt : mixedPairBudget (tensorPowerBudget m p) q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget (tensorPowerBudget m p) q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : t + (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hlocal : (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.mixedPairModels).basis
  let D := pi V.mixedPairModels
  have hD : D.GeometryComplexityLE t :=
    (V.mixedPairNiltest_complexity).1.mono D htest
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hcontrol (R.mono hrt hN) ht hD htwo hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hlocal), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  let : MetricSpace (pi V.mixedPairModels).RealGroup :=
    rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
  have herror := R.mixedPairFrozenVector_error k out x y (hcosets x y hres).1
  have hdist := hmotion x y δ hδ hx hy hnear
  apply herror.trans
  calc
    _ ≤ Real.exp t * (Real.exp ((t + a) ^ a) * δ) :=
      mul_le_mul (Real.exp_le_exp.mpr htest) hdist
        (@dist_nonneg D.RealGroup
          (rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)).toPseudoMetricSpace (R.slowValue x) (R.slowValue y))
        (Real.exp_nonneg t)
    _ = Real.exp (t + (t + a) ^ a) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem hasMixedPairFrozenEquivalence_mono {u a b : ℝ}
    (h : R.HasMixedPairFrozenEquivalence u a) (hab : a ≤ b) : R.HasMixedPairFrozenEquivalence u b := by
  intro den hm hmb left right hleft hright
  exact (h den hm hmb left right hleft hright).mono hab

def HasMixedPairFrozenReduction (b : ℝ) : Prop :=
  ∃ u : ℝ, 0 ≤ u ∧ u ≤ b ∧ R.HasOuterValueControl u ∧ R.HasMixedPairFrozenEquivalence u b

theorem mixedPairFrozenEquivalence_at {b : ℝ} (h : R.HasMixedPairFrozenReduction b)
    (x : Fin (n + 2) → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ (N : ℝ)) :
    NativeIntegerVectorEquivalence (n + 1) b
      (R.mixedPairFrozenVector 0 (R.slowValue x) (R.rationalValue x))
      (R.mixedPairFrozenVector 1 (R.slowValue x) (R.rationalValue x)) := by
  obtain ⟨u, _hu, _hub, ⟨den, hm, hmb, hrat, hslow⟩, hequiv⟩ := h
  exact hequiv den hm hmb (R.slowValue x) (R.rationalValue x) (hslow x hx) (hrat x)

end NativePolynomialOrbitFactors

theorem exists_mixed_pair_frozen_reduction (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasMixedPairFrozenReduction ((tensorPowerBudget m p + q + r + C) ^ C) := by
  obtain ⟨A, _, houter⟩ := exists_mixed_pair_outer_control n
  obtain ⟨B, _, hfrozen⟩ := exists_mixed_pair_frozen_equivalence n
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (X + U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r m _ W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget m p := hW.trans (tensorPowerBudget_bounds m hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget m p + q + r
  let u := (v + A) ^ A
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (v + u + B) ^ B ≤ (tensorPowerBudget m p + q + r + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget v hv
  have huC : u ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (v + u + B) ^ B ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_left hu).trans hsum
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.mixedPairModels).basis
  exact ⟨u, hu, huC, houter (W := W.tensorPower m) (V := V) R hr,
    R.hasMixedPairFrozenEquivalence_mono (hfrozen (W := W) (V := V) R hr hu) hBC⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem mixedPairAnchoredVector_norm (y : Fin (n + 2) → ℤ) (k : Fin 2)
    (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ‖R.mixedPairAnchoredVector y k out x‖ ≤ 1 :=
  W.vertical.norm out _

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

section Data

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}

structure NativeMixedPairPartition
    (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin (n + 2) → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin (n + 2) → I) → (Fin (n + 2) → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence (n + 1) b
    (R.mixedPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.mixedPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  weighted_approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin (n + 2) → ZMod N,
      ∑ j, (∏ l, weight (j l) (x l) : ℝ) * ‖W.eval out
        (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ)
                  (fun j => ((x j.succ.succ).val : ℤ))) -
          R.mixedPairAnchoredVector (fun l => ((anchor j l).val : ℤ)) k out
            (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativeMixedPairPartition.finite

noncomputable def NativeMixedPairPartition.mono
    {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r} {a b ε δ : ℝ}
    (P : NativeMixedPairPartition R a ε) (hab : a ≤ b) (hεδ : ε ≤ δ) : NativeMixedPairPartition R b δ :=
  { P with
    card_bound := P.card_bound.trans (Real.exp_le_exp.mpr hab)
    positive := fun j => (P.positive j).mono le_rfl hab
    equivalence := fun j => (P.equivalence j).mono hab
    weighted_approximation := fun k out => (P.weighted_approximation k out).trans hεδ }

end Data

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MixedPairPartitionKernel
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ}
  {N : ℕ}
  [NeZero N]
  {shift : ℤ}

namespace NativeCubicPairPartition

variable {b ε : ℝ}

end NativeCubicPairPartition
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ}

end NativeMultidegreeNilcharacter

variable {p q r : ℝ}
  {N : ℕ}
  [NeZero N]

namespace NativeQuarticPairPartition

variable {b ε : ℝ}

end NativeQuarticPairPartition
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}

namespace NativeMixedPairPartition

attribute [local instance] NativeMixedPairPartition.finite

variable {b ε : ℝ}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}
  (P : NativeMixedPairPartition R b ε)

noncomputable def cellWeight (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) : ℝ :=
  ∏ l, P.weight (a l) (x l)

theorem cellWeight_nonneg (a : Fin (n + 2) → P.I) (x : Fin (n + 2) → ZMod N) : 0 ≤ P.cellWeight a x :=
  Finset.prod_nonneg (fun l _ => ((P.positive (a l)).unit_interval (x l)).1)

theorem cellWeight_total (x : Fin (n + 2) → ZMod N) : ∑ a, P.cellWeight a x = 1 :=
  sum_productPartitionWeight (fun _ : Fin (n + 2) => P.weight) (fun _ => P.total) x

noncomputable def cellVector (a : Fin (n + 2) → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ZMod N) : ℂ :=
  R.mixedPairAnchoredVector (fun l => ((P.anchor a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))

theorem cellVector_norm (a : Fin (n + 2) → P.I) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ZMod N) : ‖P.cellVector a k out x‖ ≤ 1 :=
  R.mixedPairAnchoredVector_norm _ _ _ _

end NativeMixedPairPartition
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPreciseSampledExchange
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}

structure NativeMixedPointwisePartition
    (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r) (b δ β : ℝ) where
  partition : NativeMixedPairPartition R b (δ + 2 * ((n + 2 : ℕ) : ℝ) * β)
  error_nonneg : 0 ≤ δ
  density_nonneg : 0 ≤ β
  bad : Finset (ZMod N)
  bad_density : (bad.card : ℝ) / N ≤ β
  pointwise : ∀ a x, (∀ l, x l ∉ bad) → 0 < partition.cellWeight a x →
    ∀ (k : Fin 2) (out : Fin W.outputDim),
      ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) - partition.cellVector a k out x‖ ≤ δ

namespace NativeMixedPointwisePartition

attribute [local instance] NativeMixedPairPartition.finite

variable {b δ β : ℝ} (P : NativeMixedPointwisePartition R b δ β)

noncomputable def mono {b' δ' β' : ℝ} (hb : b ≤ b') (hδ : δ ≤ δ') (hβ : β ≤ β') :
    NativeMixedPointwisePartition R b' δ' β' where
  partition := P.partition.mono hb (add_le_add hδ
    (mul_le_mul_of_nonneg_left hβ (by positivity)))
  error_nonneg := P.error_nonneg.trans hδ
  density_nonneg := P.density_nonneg.trans hβ
  bad := P.bad
  bad_density := P.bad_density.trans hβ
  pointwise := fun a x hx hax k out => (P.pointwise a x hx hax k out).trans hδ

theorem sampled_error {X : Type*} [Fintype X] [Nonempty X]
    (sample : X → Fin (n + 2) → ZMod N) (E : Finset X)
    (hE : ∀ x, x ∉ E → ∀ l, sample x l ∉ P.bad) (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x, ∑ a, P.partition.cellWeight a (sample x) *
      ‖W.eval out (mixedSlotInput ((sample x (![0, 1] k)).val : ℤ) ((sample x (![1, 0] k)).val : ℤ) (fun l => ((sample x l.succ.succ).val : ℤ))) - P.partition.cellVector a k out (sample x)‖) ≤
      δ + 2 * (E.card : ℝ) / Fintype.card X := by
  exact weighted_partition_mean_error E
    (fun a x => P.partition.cellWeight a (sample x))
    (fun a x => P.partition.cellVector a k out (sample x)) _ P.error_nonneg
    (fun a x => P.partition.cellWeight_nonneg a (sample x))
    (fun x => P.partition.cellWeight_total (sample x))
    (fun a x => P.partition.cellVector_norm a k out (sample x))
    (fun x => W.norm_eval out _) (fun a x hx hax => P.pointwise a (sample x) (hE x hx) hax k out)

end NativeMixedPointwisePartition
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem select_mixed_pointwise_partition {b c : ℝ}
    (hlocal : R.HasMixedPairLocalApproximation b) (hred : R.HasMixedPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin (n + 2) → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin (n + 2) → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence (n + 1) c
            (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ a x, (∀ l, x l ∉ B) → 0 < A a x →
            ∀ (k : Fin 2) (out : Fin W.outputDim),
              ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) -
                R.mixedPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
                  (fun l => ((x l).val : ℤ))‖ ≤ Real.exp b * ρ := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin (n + 2) → ZMod N) (i : Fin (n + 2)) => ((x i).val : ℤ)
  have hv (x : Fin (n + 2) → ZMod N) (i : Fin (n + 2)) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin (n + 2) → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.mixedPairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro a x hx hax k out
  obtain ⟨hy', hAy⟩ := hy a x hx hax
  obtain ⟨hres, hnear⟩ := hcells a x (y a) hx hy' hax hAy
  exact hmodel (v (y a)) (hv (y a)) k out (v x) ρ hρ (hv x) hres
    (by simpa only [v, Int.cast_natCast] using hnear)

end NativePolynomialOrbitFactors

theorem exists_mixed_pointwise_partition (n a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      R.HasMixedPairLocalApproximation b → R.HasMixedPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      Nonempty (NativeMixedPointwisePartition R ((t + C) ^ C)
        (Real.exp t * ρ) (6 * ρ + 3 / N)) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 60 + Polynomial.C (n + 2) * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t m W N _ i j V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_mixed_pointwise_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨cells, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 60 + ((n + 2 : ℕ) : ℝ) * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have hdim : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hmul : 0 ≤ ((n + 2 : ℕ) : ℝ) * (t + B) ^ B := mul_nonneg (by linarith) hpow
  have htC : t ≤ (t + C) ^ C := by linarith
  have hdimCost : ((n + 2 : ℕ) : ℝ) * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C :=
    (le_mul_of_one_le_left hpow hdim).trans hdimCost
  let w := productPartitionWeight (fun _ : Fin (n + 2) => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin (n + 2) => A) i j x :=
    fun _ j x => ((hA j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hcells : ∀ j x y, (∀ i, x i ∉ E) → (∀ i, y i ∉ E) → 0 < w j x → 0 < w j y →
      (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ) := by
    intro j x y hx hy hwx hwy
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j y hwy
    exact ⟨fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).2,
      fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).1⟩
  obtain ⟨y, hequiv, hpoint⟩ := hselect E w hρ.le hw hwSum hcells
  let δ := Real.exp t * ρ
  let β := 6 * ρ + 3 / (N : ℝ)
  have hδ : 0 ≤ δ := mul_nonneg (Real.exp_nonneg _) hρ.le
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hbad : (E.card : ℝ) / N ≤ β := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
  have hcard' : (Fintype.card (Fin (n + 2) → Fin cells × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ (n + 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard (n + 2)
      _ = Real.exp (((n + 2 : ℕ) : ℝ) * (t + B) ^ B) := (Real.exp_nat_mul _ (n + 2)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimCost
  have hpoint' (a) (x) (hx : ∀ l, x l ∉ E) (hax : 0 < w a x) (k : Fin 2) (out : Fin W.outputDim) :
      ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) - R.mixedPairAnchoredVector
        (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖ ≤ δ :=
    (hpoint a x hx hax k out).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbt) hρ.le)
  have herr (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin (n + 2) → ZMod N, ∑ a, w a x *
        ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) - R.mixedPairAnchoredVector
          (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖) ≤ δ + 2 * ((n + 2 : ℕ) : ℝ) * β := by
    have h := weighted_partition_mean_error (coordinateExceptional E) w
      (fun a x => R.mixedPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
        (fun l => ((x l).val : ℤ))) _ hδ hw hwSum
      (fun a x => R.mixedPairAnchoredVector_norm _ _ _ _)
      (fun x => W.norm_eval out _) (fun a x hx hax =>
        hpoint' a x ((not_mem_coordinateExceptional E x).mp hx) hax k out)
    have hd : ((coordinateExceptional (ι := Fin (n + 2)) E).card : ℝ) / Fintype.card (Fin (n + 2) → ZMod N) ≤
        ((n + 2 : ℕ) : ℝ) * ((E.card : ℝ) / N) := by
      simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] using
        coordinateExceptional_density_le (ι := Fin (n + 2)) E
    have hbad' : ((n + 2 : ℕ) : ℝ) * ((E.card : ℝ) / N) ≤ ((n + 2 : ℕ) : ℝ) * β :=
      mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg _)
    have hsmall := hd.trans hbad'
    rw [mul_div_assoc] at h
    linarith
  let core : NativeMixedPairPartition R ((t + C) ^ C) (δ + 2 * ((n + 2 : ℕ) : ℝ) * β) := {
    I := Fin cells × ZMod P
    card_bound := hcard'
    weight := A
    positive := fun j => (hA j).mono le_rfl hcost
    total := hsum
    anchor := y
    equivalence := fun j => (hequiv j).mono (hct.trans htC)
    weighted_approximation := herr }
  exact ⟨{
    partition := core
    error_nonneg := hδ
    density_nonneg := hβ
    bad := E
    bad_density := hbad
    pointwise := hpoint' }⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}

namespace NativeMixedPointwisePartition

attribute [local instance] NativeMixedPairPartition.finite

variable {b δ β : ℝ} (P : NativeMixedPointwisePartition R b δ β)

end NativeMixedPointwisePartition

theorem exists_mixed_diagonal_partition (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      R.HasMixedPairLocalApproximation b → R.HasMixedPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      ∃ δ β : ℝ, ∃ _P : NativeMixedPointwisePartition R ((t + e + C) ^ C) δ β,
        δ + 4 * β ≤ Real.exp (-e) := by
  obtain ⟨A, _, hpartition⟩ := exists_mixed_pointwise_partition n 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e m W N _ i j V R hlocal hred ht he hbt hct hN
  let u := t + e + 100
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsum : (u + A) ^ A + 2 * u ≤ (t + e + C) ^ C := by
    simpa [X, T, u, Polynomial.eval₂_pow] using hbudget (t + e) (add_nonneg ht he)
  have hcost : (u + A) ^ A ≤ (t + e + C) ^ C := by linarith
  have hscale : 2 * u ≤ (t + e + C) ^ C := by
    have : 0 ≤ (u + A) ^ A := by positivity
    linarith
  let ρ := Real.exp (-(2 * u))
  have hρ : 0 < ρ := Real.exp_pos _
  have hprec : 1 / ρ ≤ Real.exp ((u + 2) ^ 2) := by
    dsimp [ρ]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  obtain ⟨P⟩ := hpartition R hlocal hred hu
    (hbt.trans (by dsimp [u]; linarith)) (hct.trans (by dsimp [u]; linarith)) hρ hprec
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using h
  have hρle : ρ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have hthree : (3 : ℝ) / N ≤ 3 * ρ := by
    calc
      _ = 3 * (1 / (N : ℝ)) := by ring
      _ ≤ 3 * ρ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  have hδ : Real.exp u * ρ = Real.exp (-u) := by
    dsimp [ρ]
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨Real.exp u * ρ, 6 * ρ + 3 / N, P.mono hcost le_rfl le_rfl, ?_⟩
  calc
    _ ≤ 37 * Real.exp (-u) := by rw [hδ]; linarith
    _ ≤ Real.exp 100 * Real.exp (-u) := by
      gcongr
      linarith [Real.add_one_le_exp (100 : ℝ)]
    _ = Real.exp (100 - u) := by simp only [← Real.exp_add, sub_eq_add_neg]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [u]; linarith)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff NativeMixedPairPartition.finite

namespace NativeMixedPointwisePartition

variable {n m : ℕ} {p q r b δ β : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}
  (P : NativeMixedPointwisePartition R b δ β)

theorem weighted_two_variable_error (π : Fin (n + 2) → Fin 2)
    (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
      ‖W.eval out (mixedSlotInput ((x (π (![0, 1] k))).val : ℤ) ((x (π (![1, 0] k))).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) -
        P.partition.cellVector a k out (fun l => x (π l))‖) ≤ δ + 4 * β := by
  let E := coordinateExceptional (ι := Fin 2) P.bad
  have h := P.sampled_error (fun x l => x (π l)) E
    (fun x hx l => (not_mem_coordinateExceptional P.bad x).mp hx (π l)) k out
  have hd : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * β := by
    have hD := coordinateExceptional_density_le (ι := Fin 2) P.bad
    simp only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] at hD
    exact hD.trans (mul_le_mul_of_nonneg_left P.bad_density (by norm_num))
  rw [mul_div_assoc] at h
  linarith

theorem weighted_two_variable_exchange_error (π : Fin (n + 2) → Fin 2) (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
      ‖W.eval out₀ (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
          star (W.eval out₁ (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
        P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
          star (P.partition.cellVector a 1 out₁ (fun l => x (π l)))‖) ≤ 2 * (δ + 4 * β) := by
  let err := fun (k : Fin 2) (out : Fin W.outputDim) (a : Fin (n + 2) → P.partition.I)
      (x : Fin 2 → ZMod N) =>
    ‖W.eval out (mixedSlotInput ((x (π (![0, 1] k))).val : ℤ) ((x (π (![1, 0] k))).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) -
      P.partition.cellVector a k out (fun l => x (π l))‖
  have hbound (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err k out a x) ≤
        δ + 4 * β := P.weighted_two_variable_error π k out
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
        (err 0 out₀ a x + err 1 out₁ a x) := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (P.partition.cellWeight_nonneg _ _)
      exact norm_mul_star_sub_mul_star_le_of_le_one (W.norm_eval out₁ _)
        (P.partition.cellVector_norm a 0 out₀ _)
    _ = (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err 0 out₀ a x) +
        (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err 1 out₁ a x) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.expect_add_distrib]
    _ ≤ _ := by linarith [hbound 0 out₀, hbound 1 out₁]

theorem two_variable_exchange_approximation (π : Fin (n + 2) → Fin 2) (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out₀ (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
          star (W.eval out₁ (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
        ∑ a, (P.partition.cellWeight a (fun l => x (π l)) : ℂ) *
          (P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
            star (P.partition.cellVector a 1 out₁ (fun l => x (π l))))‖) ≤ 2 * (δ + 4 * β) := by
  apply le_trans _ (P.weighted_two_variable_exchange_error π out₀ out₁)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (fun l => x (π l)))
    (fun a => P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
      star (P.partition.cellVector a 1 out₁ (fun l => x (π l)))) _
    (fun a => P.partition.cellWeight_nonneg a _) (P.partition.cellWeight_total _))

end NativeMixedPointwisePartition
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff NativeMixedPairPartition.finite

theorem exists_mixed_sampled_exchange (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b δ β : ℝ} {m N : ℕ} [NeZero N]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r}
      (P : NativeMixedPointwisePartition R b δ β), 0 ≤ b →
      ∃ G : (Fin (n + 2) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (n + 1)
          ((b + C) ^ C) (G π a c))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), G π a c (fun z => ((x z).val : ℤ)) =
          ∑ cell, (P.partition.cellWeight cell (fun l => x (π l)) : ℂ) *
            (P.partition.cellVector cell 0 a (fun l => x (π l)) *
              star (P.partition.cellVector cell 1 c (fun l => x (π l))))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
              star (W.eval c (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
            G π a c (fun z => ((x z).val : ℤ))‖) ≤ 2 * (δ + 4 * β)) := by
  obtain ⟨A, _, hpartition⟩ := exists_positive_partition_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C (n + 2) + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r b δ β m N _ W i j V R P hb
  classical
  let t := b + ((n + 2 : ℕ) : ℝ)
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hbt : b ≤ t := by dsimp [t]; linarith
  have hσ : (Fintype.card (Fin (n + 2)) : ℝ) ≤ t := by simp only [Fintype.card_fin]; dsimp [t]; linarith
  let v := fun (cell : Fin (n + 2) → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim)
      (x : Fin (n + 2) → ℤ) =>
    R.mixedPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 0 ac.1 x *
      star (R.mixedPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 1 ac.2 x)
  have hv (cell : Fin (n + 2) → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) t (v cell ac)) :=
    ((P.partition.equivalence cell).mono hbt).expansion ac.1 ac.2
  obtain ⟨F, hF, hFeval⟩ := hpartition ht hσ
    (P.partition.card_bound.trans (Real.exp_le_exp.mpr hbt))
    (fun cell k => P.partition.weight (cell k)) v
    (fun cell k => (P.partition.positive (cell k)).mono (by omega : 1 ≤ n + 1) hbt) hv
  let G := fun (π : Fin (n + 2) → Fin 2) (a c : Fin W.outputDim) (x : Fin 2 → ℤ) =>
    F (a, c) (fun l => x (π l))
  have hcost : (t + A) ^ A ≤ (b + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget b hb
  have hexp (π : Fin (n + 2) → Fin 2) (a c : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (n + 1) ((b + C) ^ C) (G π a c)) := by
    let f : Fin (n + 2) → ((Fin 2 → ℤ) →+ ℤ) :=
      fun k => ⟨⟨fun x => x (π k), rfl⟩, fun _ _ => rfl⟩
    exact ⟨((Classical.choice (hF (a, c))).linearPullbackHom f).mono hcost⟩
  have heval (π : Fin (n + 2) → Fin 2) (a c : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      G π a c (fun z => ((x z).val : ℤ)) =
        ∑ cell, (P.partition.cellWeight cell (fun l => x (π l)) : ℂ) *
          (P.partition.cellVector cell 0 a (fun l => x (π l)) *
            star (P.partition.cellVector cell 1 c (fun l => x (π l)))) :=
    hFeval (a, c) (fun l => x (π l))
  refine ⟨G, hexp, heval, ?_, ?_⟩
  · intro π a c x
    rw [heval]
    apply norm_positive_partition_sum_le_one
      (fun cell => P.partition.cellWeight cell (fun l => x (π l)))
      (fun cell => P.partition.cellVector cell 0 a (fun l => x (π l)) *
        star (P.partition.cellVector cell 1 c (fun l => x (π l))))
      (fun cell => P.partition.cellWeight_nonneg cell _) (P.partition.cellWeight_total _)
    intro cell
    rw [norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right (P.partition.cellVector_norm cell 0 a _)
      (norm_nonneg _)).trans (by
        simpa only [one_mul] using P.partition.cellVector_norm cell 1 c _)
  · intro π a c
    simpa only [heval] using P.two_variable_exchange_approximation π a c

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_precise_sampled_exchange (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (_R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      0 ≤ r → 0 ≤ e → Real.exp ((tensorPowerBudget m p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ G : (Fin (n + 2) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (n + 1)
          ((tensorPowerBudget m p + q + r + e + C) ^ C) (G π a c))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
              star (W.eval c (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
            G π a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hlocal⟩ := exists_mixed_pair_local_approximation n
  obtain ⟨b, _, hfrozen⟩ := exists_mixed_pair_frozen_reduction n
  obtain ⟨d, _, hpartition⟩ := exists_mixed_diagonal_partition n
  obtain ⟨c, _, hexchange⟩ := exists_mixed_sampled_exchange n
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b
  let Z := (T + X + 1 + Polynomial.C d) ^ d
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z + (Z + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p q r e m _ W N _ i j V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hk : 0 ≤ tensorPowerBudget m p := hp.trans (tensorPowerBudget_bounds m hp).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget m p + q + r + e
  let t := (v + a) ^ a + (v + b) ^ b
  let z := (t + (e + 1) + d) ^ d
  let zmax := (t + v + 1 + d) ^ d
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzm : 0 ≤ zmax := by dsimp [zmax]; positivity
  have hzz : z ≤ zmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hsum : zmax + (zmax + c) ^ c ≤ (v + C) ^ C := by
    simpa [X, T, Z, zmax, t, Polynomial.eval₂_pow] using hbudget v hv
  have hzC : z ≤ (v + C) ^ C :=
    hzz.trans ((le_add_of_nonneg_right (by positivity)).trans hsum)
  have hcost : (z + c) ^ c ≤ (v + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (by linarith : z + c ≤ zmax + c) c).trans
      ((le_add_of_nonneg_left hzm).trans hsum)
  have ha : (tensorPowerBudget m p + q + r + a) ^ a ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hb : (tensorPowerBudget m p + q + r + b) ^ b ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  obtain ⟨δ, β, P, herr⟩ := hpartition R (hlocal (W := W) R hr) (hfrozen (W := W) R hr)
    ht (by positivity : 0 ≤ e + 1) ha hb ((Real.exp_le_exp.mpr hzC).trans hN)
  obtain ⟨G, hG, _, hcap, herror⟩ := hexchange P hz
  refine ⟨G, fun π a c => ⟨(Classical.choice (hG π a c)).mono hcost⟩, hcap, ?_⟩
  intro π a c
  apply (herror π a c).trans
  have hhalf := exp_sub_one_le_half_exp (-e)
  have hid : -(e + 1) = -e - 1 := by ring
  rw [← hid] at hhalf
  linarith

end Erdos3

end

end OAI

end


